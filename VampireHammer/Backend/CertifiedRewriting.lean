import VampireHammer.Backend.Common
import VampireHammer.Backend.Instantiation
import VampireHammer.Backend.Congruence
import VampireHammer.Backend.Occurrence

/-! Certificate-directed rewriting. The proof splits parent clauses, uses the
selected equality only in its branch, and carries every other literal into the
natural conclusion. Inner rewriting obtains equality by assuming its retained
negative equality is false. Constraints are handled the same way. -/
namespace VampireHammer.Backend
open Lean Meta Elab Tactic
open VampireHammer.ClauseMeta Internal

private abbrev congruence := congruenceWithEquations

private def directedEquality (constraints : Array (Expr × Expr × Expr))
    (equality sourceTerm to : Expr) : MetaM (Option Expr) := do
  let some (_, left, right) := (← whnfR (← inferType equality)).eq? | return none
  let orient (lhs rhs proof : Expr) : MetaM (Option Expr) := do
    let some first ← congruence constraints sourceTerm lhs | return none
    let some last ← congruence constraints rhs to | return none
    some <$> mkEqTrans first (← mkEqTrans proof last)
  if let some proof ← orient left right equality then return some proof
  orient right left (← mkEqSymm equality)

private def injectAt (literals : Array Expr) (index : Nat) (proof : Expr) : MetaM Expr := do
  let literal := literals[index]!
  let mut result := mkApp3 (mkConst ``Or.inl) literal
    (← holdsType (literals.drop (index + 1))) proof
  for i in (List.range index).reverse do
    result := mkApp3 (mkConst ``Or.inr) literals[i]!
      (← holdsType (literals.drop (i + 1))) result
  pure result

private def inject (regular avatar : Array Expr) (isAClause : Bool) (proof : Expr) :
    MetaM (Option Expr) := do
  let literal ← inferType proof
  let part (literals : Array Expr) : MetaM (Option Expr) := do
    for i in [:literals.size] do
      if let some iff ← literalEquivalent? literal literals[i]! then
        let transported ← mkAppM ``Iff.mp #[iff, proof]
        return some (← injectAt literals i transported)
    pure none
  if let some result ← part regular then
    if !isAClause then return some result
    return some (mkApp3 (mkConst ``Or.inl) (← holdsType regular) (← holdsType avatar) result)
  unless isAClause do return none
  let some result ← part avatar | return none
  pure (some (mkApp3 (mkConst ``Or.inr) (← holdsType regular) (← holdsType avatar) result))

private partial def eliminate (proof : Expr) (literals : Array Expr)
    (branch : Nat → Expr → MetaM (Option Expr)) (offset : Nat := 0) : MetaM (Option Expr) := do
  if literals.isEmpty then return some proof
  let literal := literals[0]!
  let tail := literals.drop 1
  let some head ← withLocalDeclD `rewriteLiteral literal fun h => do
    let some result ← branch offset h | return none
    some <$> mkLambdaFVars #[h] result
    | return none
  let some rest ← withLocalDeclD `rewriteTail (← holdsType tail) fun h => do
    let some result ← eliminate h tail branch (offset + 1) | return none
    some <$> mkLambdaFVars #[h] result
    | return none
  some <$> mkAppM ``Or.elim #[proof, head, rest]

private def eliminateView (view : ResolutionClauseView)
    (branch : Nat → Expr → MetaM (Option Expr))
    (avatarBranch : Expr → MetaM (Option Expr)) : MetaM (Option Expr) := do
  if !view.isAClause then return ← eliminate view.proof view.regular branch
  let some first ← withLocalDeclD `regularParent (← holdsType view.regular) fun h => do
    let some result ← eliminate h view.regular branch | return none
    some <$> mkLambdaFVars #[h] result
    | return none
  let some second ← withLocalDeclD `avatarParent (← holdsType view.avatar) fun h => do
    let some result ← eliminate h view.avatar (fun _ => avatarBranch) | return none
    some <$> mkLambdaFVars #[h] result
    | return none
  some <$> mkAppM ``Or.elim #[view.proof, first, second]

/-- Reconstruct backward demodulation, subsumption demodulation, negative
inner rewriting, or superposition modulo explicit disequality constraints. -/
def certifiedRewriting (input : RuleInput) (info : CertifiedRewriteInfo) : MetaM (Option Expr) := do
  let rule := input.step.inference?.map (·.rule) |>.getD ""
  unless #["backward_demodulation", "forward_subsumption_demodulation",
      "backward_subsumption_demodulation",
      "inner_rewriting", "constrained_superposition", "definition_unfolding"].contains rule do return none
  let inner := rule == "inner_rewriting"
  let constrained := rule == "constrained_superposition"
  unless input.sourceProof?.isNone && input.parents.size == (if inner then 1 else 2) &&
      input.parents.all (·.clauseForm) do return none
  unless constrained || info.constraints.isEmpty do return none
  let some substitutions := orderParentSubstitutions input.parents info.substitutions | return none
  let some selected := info.rewrittenLiterals[0]? | return none
  let some mainIndex := input.parents.findIdx? (·.parent.name == selected.parent) | return none
  let sideIndex := if inner then mainIndex else 1 - mainIndex
  let some sideParent := input.parents[sideIndex]? | return none
  unless info.equality.parent == sideParent.parent.name &&
      info.rewrittenLiterals.all (·.parent == selected.parent) do return none
  underConclusionBinders input fun bindings _ => do
    let some scope ← instantiationScope input substitutions bindings | return none
    let some parents ← instantiateParentsIn input substitutions bindings scope | return none
    let some main ← resolutionClauseView parents[mainIndex]!.1 parents[mainIndex]!.2 | return none
    let some side ← resolutionClauseView parents[sideIndex]!.1 parents[sideIndex]!.2 | return none
    let eqIndex := info.equality.index
    let some eqLiteral := side.regular[eqIndex]? | return none
    unless info.rewrittenLiterals.all (·.index < main.regular.size) do return none
    unless inner || info.rewrittenLiterals.size == 1 do return none
    if info.occurrence?.isSome && info.rewrittenLiterals.size != 1 then return none
    if rule == "backward_demodulation" && side.regular.size != 1 then return none
    let mut rawTerms := #[info.fromTerm, info.toTerm]
    for raw in info.constraints do
      let .application "disequality" #[_, lhs, rhs] := raw | return none
      rawTerms := rawTerms.push lhs |>.push rhs
    let some terms ← materializeTermsIn input bindings scope rawTerms | return none
    let sourceTerm := terms[0]!
    let to := terms[1]!
    unless ← isDefEq (← inferType sourceTerm) (← inferType to) do return none
    let mut constraints := #[]
    for i in [:info.constraints.size] do
      let lhs := terms[2 + i * 2]!
      let rhs := terms[3 + i * 2]!
      unless ← isDefEq (← inferType lhs) (← inferType rhs) do return none
      constraints := constraints.push (mkNot (← mkEq lhs rhs))
    let indices := info.rewrittenLiterals.map (·.index)
    let attempt (natural naturalMain : Array Expr) : MetaM (Option Expr) := do
      let avatar := if inner then main.avatar else main.avatar ++ side.avatar
      let isA := main.isAClause || side.isAClause
      let goal ← if isA then
        mkAppM ``VampireHammer.Clause.AClause.Holds
          #[mkPropList natural.toList, mkPropList avatar.toList]
        else
          holdsType natural
      let proof? ← withLocalDeclD `notRewriteResult (mkNot goal) fun noGoal => do
        let contradict (proof : Expr) : MetaM (Option Expr) := do
          let some result ← inject natural avatar isA proof | return none
          pure (some (mkApp noGoal result))
        let mut equations := #[]
        for constraint in constraints do
          let some eq := constraint.not? | return none
          let some (_, lhs, rhs) := eq.eq? | return none
          let negated ← withLocalDeclD `constraint constraint fun h => do
            let some result ← contradict h | return none
            some <$> mkLambdaFVars #[h] result
          let some negated := negated | return none
          let eqProof ← mkAppOptM ``Classical.byContradiction #[eq, negated]
          equations := equations.push (eqProof, lhs, rhs)
        let rewriteMain (eqProof : Expr) : MetaM (Option Expr) := do
          let some directional ← directedEquality equations eqProof sourceTerm to | return none
          eliminateView main (fun i h => do
            let literal := main.regular[i]!
            if literal == naturalMain[i]! then return ← contradict h
            let some equality ← congruence #[(directional, sourceTerm, to)] literal naturalMain[i]!
              | return none
            contradict (← mkEqMP equality h)) contradict
        let contradiction? ← if inner then do
            let some equation ← notArgument? eqLiteral | return none
            unless (← whnfR equation).eq?.isSome do return none
            let negated ← withLocalDeclD `innerDisequality eqLiteral fun h => do
              let some result ← contradict h | return none
              some <$> mkLambdaFVars #[h] result
            let some negated := negated | return none
            let eqProof ← mkAppOptM ``Classical.byContradiction #[equation, negated]
            rewriteMain eqProof
          else
            eliminateView side (fun i h => if i == eqIndex then rewriteMain h else contradict h) contradict
        let some contradiction := contradiction? | return none
        some <$> mkLambdaFVars #[noGoal] contradiction
      let some proof := proof? | return none
      let proof ← mkAppOptM ``Classical.byContradiction #[goal, proof]
      let some target := targetClauseLiterals? input bindings | return none
      let (targetRegular, targetAvatar) := splitAClauseLiterals (avatarAtoms input) target
      normalizeClauseResult proof natural avatar targetRegular targetAvatar isA
    let build (rewriteAll : Bool) : MetaM (Option Expr) := do
      let mut naturalMain := #[]
      for (literal, i) in main.regular.zipIdx do
        if (rewriteAll || indices.contains i) && !(inner && i == eqIndex) then
          let some rewritten ← rewriteTermOccurrences sourceTerm to literal info.occurrence? | return none
          naturalMain := naturalMain.push rewritten
        else naturalMain := naturalMain.push literal
      unless indices.any (fun i => main.regular[i]! != naturalMain[i]!) do return none
      if inner && !indices.all (fun i => i != eqIndex && main.regular[i]! != naturalMain[i]!) then
        return none
      let tails := if constrained then side.regular.eraseIdxIfInBounds eqIndex else #[]
      -- Constrained superposition usually moves the rewritten literal to the
      -- front; higher-order superposition keeps it in place. Both orders are
      -- checked exactly against the displayed child.
      let orderings := if constrained then
        #[#[naturalMain[selected.index]!] ++ naturalMain.eraseIdxIfInBounds selected.index, naturalMain]
        else #[naturalMain]
      for orderedMain in orderings do
        if let some proof ← Meta.withNewMCtxDepth (attempt (orderedMain ++ tails ++ constraints) naturalMain) then
          return some proof
      pure none
    if info.occurrence?.isSome then return ← Meta.withNewMCtxDepth (build false)
    if let some proof ← Meta.withNewMCtxDepth (build constrained) then return some proof
    if constrained then Meta.withNewMCtxDepth (build false) else pure none

/-- Higher-order equality resolution with abstraction. Vampire resolves away
`l ≠ r` whose instance is not reflexive and appends the residual unification
constraints `u ≠ v` after the remaining literals. These are not printed as a
certificate, so the suffix of the displayed child beyond the remaining
literals is taken as the constraint list: assuming each `u = v`, the instance
of `l = r` must follow by checked congruence. -/
def constrainedEqualityResolution (input : RuleInput) (info : EqualityResolutionInfo) :
    MetaM (Option Expr) := do
  unless input.sourceProof?.isNone && input.parents.size == 1 &&
      input.parents.all (·.clauseForm) && info.substitutions.size == 1 do return none
  underConclusionBinders input fun bindings _ => do
    let some parents ← instantiateParents input info.substitutions bindings | return none
    let some view ← resolutionClauseView parents[0]!.1 parents[0]!.2 | return none
    let some target := targetClauseLiterals? input bindings | return none
    let (targetRegular, targetAvatar) := splitAClauseLiterals (avatarAtoms input) target
    for index in [:view.regular.size] do
      let some equation ← notArgument? view.regular[index]! | continue
      let some (_, left, right) := (← whnfR equation).eq? | continue
      let remainder := view.regular.eraseIdxIfInBounds index
      unless remainder.size < targetRegular.size do continue
      let constraints := targetRegular.extract remainder.size targetRegular.size
      let natural := remainder ++ constraints
      let proof? ← Meta.withNewMCtxDepth do
        let goal ← if view.isAClause then
            mkAppM ``VampireHammer.Clause.AClause.Holds
              #[mkPropList natural.toList,
                mkPropList view.avatar.toList]
          else holdsType natural
        let refutation? ← withLocalDeclD `notResolvent (mkNot goal) fun noGoal => do
          let contradict (proof : Expr) : MetaM (Option Expr) := do
            let some result ← inject natural view.avatar view.isAClause proof | return none
            pure (some (mkApp noGoal result))
          let mut equations := #[]
          for constraint in constraints do
            let some eq ← notArgument? constraint | return none
            let some (_, lhs, rhs) := (← whnfR eq).eq? | return none
            let negated ← withLocalDeclD `constraint constraint fun h => do
              let some result ← contradict h | return none
              some <$> mkLambdaFVars #[h] result
            let some negated := negated | return none
            let eqProof ← mkAppOptM ``Classical.byContradiction #[eq, negated]
            equations := equations.push (eqProof, lhs, rhs)
          let some resolved ← congruence equations left right | return none
          let contradiction? ← eliminateView view (fun i h => do
              if i == index then return some (mkApp h resolved)
              contradict h) contradict
          let some contradiction := contradiction? | return none
          some <$> mkLambdaFVars #[noGoal] contradiction
        let some refutation := refutation? | return none
        let proof ← mkAppOptM ``Classical.byContradiction #[goal, refutation]
        normalizeClauseResult proof natural view.avatar targetRegular targetAvatar view.isAClause
      if let some proof := proof? then
        trace[vampire.replay] "constrained equality resolution {input.step.name}: literal {index} with {constraints.size} residual constraint(s)"
        return some proof
    pure none
/-- Higher-order equality factoring with abstraction. From the instance of
`C ∨ s' = t' ∨ s = t`, Vampire derives `t ≠ t' ∨ C ∨ s' = t'` followed by the
residual constraints of unifying `s` with `s'`, which are not printed. As for
equality resolution, they are the suffix beyond the parent's remaining
literals; assuming each, `s' = s` must follow by checked congruence. -/
def constrainedEqualityFactoring (input : RuleInput) (info : EqualityFactoringInfo) :
    MetaM (Option Expr) := do
  unless input.sourceProof?.isNone && input.parents.size == 1 &&
      input.parents.all (·.clauseForm) && info.substitutions.size == 1 do return none
  underConclusionBinders input fun bindings _ => do
    let some parents ← instantiateParents input info.substitutions bindings | return none
    let some view ← resolutionClauseView parents[0]!.1 parents[0]!.2 | return none
    let some target := targetClauseLiterals? input bindings | return none
    let (targetRegular, targetAvatar) := splitAClauseLiterals (avatarAtoms input) target
    let some first := targetRegular[0]? | return none
    let some firstEquation ← notArgument? first | return none
    let some (_, firstLeft, firstRight) := (← whnfR firstEquation).eq? | return none
    let sides (literal : Expr) : MetaM (Option (Expr × Expr)) := do
      let some (_, left, right) := (← whnfR literal).eq? | return none
      pure (some (left, right))
    for selected in [:view.regular.size] do
      let some (a, b) ← sides view.regular[selected]! | continue
      let remainder := view.regular.eraseIdxIfInBounds selected
      unless remainder.size + 1 ≤ targetRegular.size do continue
      let constraints := targetRegular.extract (remainder.size + 1) targetRegular.size
      let natural := #[first] ++ remainder ++ constraints
      for factored in [:view.regular.size] do
        if factored == selected then continue
        let some (c, d) ← sides view.regular[factored]! | continue
        for (s, t, selectedSwapped) in [(a, b, false), (b, a, true)] do
          for (s', t', factoredSwapped) in [(c, d, false), (d, c, true)] do
            -- The first child literal is `t ≠ t'`, in either orientation.
            let firstSwapped ←
              if ← (isDefEq firstLeft t <&&> isDefEq firstRight t') then pure false
              else if ← (isDefEq firstLeft t' <&&> isDefEq firstRight t) then pure true
              else continue
            let proof? ← Meta.withNewMCtxDepth do
              let goal ← if view.isAClause then
                  mkAppM ``VampireHammer.Clause.AClause.Holds
                    #[mkPropList natural.toList,
                      mkPropList view.avatar.toList]
                else holdsType natural
              let refutation? ← withLocalDeclD `notFactor (mkNot goal) fun noGoal => do
                let contradict (proof : Expr) : MetaM (Option Expr) := do
                  let some result ← inject natural view.avatar view.isAClause proof | return none
                  pure (some (mkApp noGoal result))
                let byFalsity (literal equation : Expr) : MetaM (Option Expr) := do
                  let negated ← withLocalDeclD `literal literal fun h => do
                    let some result ← contradict h | return none
                    some <$> mkLambdaFVars #[h] result
                  let some negated := negated | return none
                  some <$> mkAppOptM ``Classical.byContradiction #[equation, negated]
                let mut equations := #[]
                for constraint in constraints do
                  let some eq ← notArgument? constraint | return none
                  let some (_, lhs, rhs) := (← whnfR eq).eq? | return none
                  let some eqProof ← byFalsity constraint eq | return none
                  equations := equations.push (eqProof, lhs, rhs)
                let some firstProof ← byFalsity first firstEquation | return none
                let tt' ← if firstSwapped then mkEqSymm firstProof else pure firstProof
                let some s's ← congruence equations s' s | return none
                let contradiction? ← eliminateView view (fun i h => do
                    unless i == selected do return ← contradict h
                    let st ← if selectedSwapped then mkEqSymm h else pure h
                    let s't' ← mkEqTrans (← mkEqTrans s's st) tt'
                    let factoredProof ← if factoredSwapped then mkEqSymm s't' else pure s't'
                    let some factoredProof ← asExpectedType factoredProof view.regular[factored]!
                      | return none
                    contradict factoredProof) contradict
                let some contradiction := contradiction? | return none
                some <$> mkLambdaFVars #[noGoal] contradiction
              let some refutation := refutation? | return none
              let proof ← mkAppOptM ``Classical.byContradiction #[goal, refutation]
              normalizeClauseResult proof natural view.avatar targetRegular targetAvatar view.isAClause
            if let some proof := proof? then
              trace[vampire.replay] "constrained equality factoring {input.step.name}: literals {selected}, {factored} with {constraints.size} residual constraint(s)"
              return some proof
    pure none
end VampireHammer.Backend
