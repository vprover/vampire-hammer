import VampireHammer.Backend.HigherOrderBoolean
import VampireHammer.Backend.LogicalWitness

namespace VampireHammer.Backend
open Lean Meta
open Internal

/-- Remove Boolean truth-equality wrappers only. Interpretation remains
checked by a separate proof transport; this helper never supplies a proof. -/
partial def higherOrderLogicalLiteral (expression : Expr) (negative : Bool := false) : MetaM Expr := do
  let expression ← whnfR expression
  if let some (_, left, right) := expression.eq? then
    if ← isProp left then
      for (side, body) in #[(left, right), (right, left)] do
        if ← isDefEq side (mkConst ``True) then
          return ← higherOrderLogicalLiteral body negative
        if ← isDefEq side (mkConst ``False) then
          return ← higherOrderLogicalLiteral body (!negative)
  if let some body ← notArgument? expression then
    return ← higherOrderLogicalLiteral body (!negative)
  pure (if negative then mkNot expression else expression)

/-- Read the existential predicate of `∃x, P x` or `¬∀x, P x`. -/
def higherOrderExistentialCondition (literal : Expr) : MetaM (Option (Expr × Expr)) := do
  let literal ← higherOrderLogicalLiteral literal
  if literal.isAppOfArity ``Exists 2 then
    let arguments := literal.getAppArgs
    return some (literal, arguments[1]!)
  let some universal ← notArgument? literal | return none
  let universal ← whnfR universal
  unless universal.isForall do return none
  withLocalDeclD universal.bindingName! universal.bindingDomain! fun argument => do
    let predicate ← mkLambdaFVars #[argument]
      (mkNot (universal.bindingBody!.instantiate1 argument))
    let existential ← mkAppM ``Exists #[predicate]
    pure (some (existential, predicate))

private def universalCondition (literal : Expr) : MetaM (Option Expr) := do
  let literal ← higherOrderLogicalLiteral literal
  let reduced ← whnfR literal
  if reduced.isForall then return some reduced
  let some existential ← notArgument? literal | return none
  unless existential.isAppOfArity ``Exists 2 do return none
  let arguments := existential.getAppArgs
  withLocalDeclD `quantified arguments[0]! fun argument => do
    some <$> mkForallFVars #[argument] (mkNot (mkApp arguments[1]! argument))

/-- Closed maximal applications headed by a local, outermost first. -/
private partial def fvarApplications (term : Expr) : Array Expr :=
  let here := if term.getAppFn.isFVar && !term.hasLooseBVars then #[term] else #[]
  here ++ match term with
    | .app .. => term.getAppArgs.flatMap fvarApplications
    | .lam _ domain body _ | .forallE _ domain body _ => fvarApplications domain ++ fvarApplications body
    | .mdata _ inner => fvarApplications inner
    | _ => #[]

/-- State the witness specification at the witness application displayed in
the child, e.g. `sK0 X1`, once it is checked to be definitionally the epsilon
witness. Boolean normalization may otherwise rewrite inside the predicate of
the unfolded witness, which no longer matches the folded child atom. -/
private def witnessAtom (proof predicate target : Expr) : MetaM Expr := do
  let witness ← mkAppM ``quantifierWitness #[predicate]
  let type ← inferType witness
  for candidate in fvarApplications target do
    if ← ((do isDefEq (← inferType candidate) type) <&&> isDefEq candidate witness) then
      if let some stated ← asExpectedType proof (mkApp predicate candidate).headBeta then
        return stated
  pure proof

/-- Preserve the other literals while eliminating a certified existential
proxy with its scoped epsilon witness. -/
def higherOrderSigma (input : RuleInput) (info : QuantifierWitnessInfo) : MetaM (Option Expr) := do
  unless input.sourceProof?.isNone && input.parents.size == 1 do return none
  let some parent := input.parents[0]? | return none
  -- Term dependencies are not checked by name: the witness is accepted
  -- only where the displayed application is definitionally the epsilon
  -- witness of the selected predicate (`witnessAtom`).
  unless parent.clauseForm && parent.parent.name == info.literal.parent &&
      (!info.dependencyTerms.isEmpty ||
        (witnessDependencyIndices? (parent.binders.map (·.name)) info.dependencies).isSome) &&
      input.symbols.contains info.symbol do return none
  let childNames := input.step.binders.map (·.name)
  let some positions := witnessBinderIndices? (parent.binders.map (·.name))
    childNames info.binderMapping? | return none
  let mappedBindings := parent.binders.zip positions |>.map fun (binder, index) =>
    (binder.name, MetadataTerm.variable childNames[index]!)
  let substitutions := #[{ parent := parent.parent.name, bindings := mappedBindings : ParentSubstitution }]
  withConfig (fun config => { config with zetaDelta := true }) <|
    underConclusionBinders input fun bindings _ => do
      let some scope ← instantiationScope input substitutions bindings | return none
      let some parents ← instantiateParentsIn input substitutions bindings scope | return none
      let some (proof, type) := parents[0]? | return none
      let some view ← resolutionClauseView proof type | return none
      unless !view.isAClause do return none
      let some selected := view.regular[info.literal.index]? | return none
      trace[vampire.replay] "sigma {input.step.name}: selected {selected}"
      let some (condition, predicate) ← higherOrderExistentialCondition selected | return none
      let some target := targetClauseLiterals? input bindings | return none
      -- A reused witness must be displayed applied to exactly the certified
      -- dependencies; an introduction fixes them when binding the symbol.
      let some symbol := input.symbols.get? info.symbol | return none
      let reuse? ← if info.introduce then pure none else do
        let raw := if info.dependencyTerms.isEmpty
          then info.dependencies.map MetadataTerm.variable else info.dependencyTerms
        let some dependencies ← materializeTermsIn input bindings scope raw
          | return none
        pure (some dependencies)
      for index in [:target.size] do
        if let some dependencies := reuse? then
          let displayed ← (fvarApplications target[index]!).anyM fun candidate => do
            let arguments := candidate.getAppArgs
            pure (candidate.getAppFn == symbol && arguments.size == dependencies.size) <&&>
              (arguments.zip dependencies).allM fun (argument, dependency) => isDefEq argument dependency
          unless displayed do continue
        let tail := target.eraseIdxIfInBounds index
        let some reordered ← VampireHammer.ClauseMeta.reorderAndNormalize proof
            view.regular.toList (selected :: tail.toList) | do
          trace[vampire.replay] "sigma {input.step.name}: context mismatch for candidate {index}"
          continue
        let transition ← withLocalDeclD `quantifierSource selected fun assumption => do
          let some existential ← higherOrderBooleanTransport assumption condition | return none
          let derivedProof ← mkAppM ``quantifierWitness_spec #[predicate, existential]
          let derivedProof ← witnessAtom derivedProof predicate target[index]!
          let some transported ← higherOrderBooleanTransport derivedProof target[index]! | return none
          some <$> mkLambdaFVars #[assumption] transported
        let some transition := transition | continue
        let result ← mkAppM ``higherOrderMapHead
          #[← mkListLit (mkSort .zero) tail.toList, transition, reordered]
        let some result ← VampireHammer.ClauseMeta.reorderAndNormalize result
            (target[index]! :: tail.toList) target.toList | continue
        return some result
      pure none

/-- Universal proxy removal instantiates the selected quantifier with the
newly printed child variables. Domains and the untouched context are checked. -/
def higherOrderPi (input : RuleInput) : MetaM (Option Expr) := do
  unless input.sourceProof?.isNone && input.parents.size == 1 do return none
  let some parent := input.parents[0]? | return none
  unless parent.clauseForm && parent.binders.all (fun binder =>
      input.step.binders.any (·.name == binder.name)) do return none
  let substitutions := #[{ parent := parent.parent.name, bindings := #[] : ParentSubstitution }]
  underConclusionBinders input fun bindings _ => do
    let fresh := bindings.filter fun binding => !parent.binders.any (·.name == binding.1)
    unless !fresh.isEmpty do return none
    let some parents ← instantiateParents input substitutions bindings | return none
    let some (proof, type) := parents[0]? | return none
    let some view ← resolutionClauseView proof type | return none
    unless !view.isAClause do return none
    let some target := targetClauseLiterals? input bindings | return none
    for selected in view.regular do
      let some condition ← universalCondition selected | continue
      trace[vampire.replay] "pi {input.step.name}: selected {selected}"
      for index in [:target.size] do
        let tail := target.eraseIdxIfInBounds index
        let some reordered ← VampireHammer.ClauseMeta.reorderAndNormalize proof
            view.regular.toList (selected :: tail.toList) | continue
        let transition ← withLocalDeclD `quantifierSource selected fun assumption => do
          let some universal ← higherOrderBooleanTransport assumption condition | return none
          let mut derivedProof := universal
          for (_, argument) in fresh do
            let type ← whnfR (← inferType derivedProof)
            unless ← (pure type.isForall <&&>
                (do isDefEq type.bindingDomain! (← inferType argument))) do return none
            derivedProof := mkApp derivedProof argument
          let some transported ← higherOrderBooleanTransport derivedProof target[index]! | return none
          some <$> mkLambdaFVars #[assumption] transported
        let some transition := transition | continue
        let result ← mkAppM ``higherOrderMapHead
          #[← mkListLit (mkSort .zero) tail.toList, transition, reordered]
        let some result ← VampireHammer.ClauseMeta.reorderAndNormalize result
            (target[index]! :: tail.toList) target.toList | continue
        return some result
    pure none

/-- `heuristic_instantiation` replaces a universal proxy (`∀`, or a negated
`∃`) in the selected literal by its predicate applied to the certified term.
The other literals are the parent's, under its type instantiation. -/
def higherOrderQuantifierInstance (input : RuleInput) (info : QuantifierInstanceInfo) :
    MetaM (Option Expr) := do
  unless input.sourceProof?.isNone && input.parents.size == 1 do return none
  let some parent := input.parents[0]? | return none
  unless parent.clauseForm && parent.parent.name == info.literal.parent do return none
  let substitutions := if info.substitutions.isEmpty then
      #[{ parent := parent.parent.name, bindings := #[] : ParentSubstitution }]
    else info.substitutions
  underConclusionBinders input fun bindings _ => do
    let some scope ← instantiationScope input substitutions bindings | return none
    let some parents ← instantiateParentsIn input substitutions bindings scope | return none
    let some (proof, type) := parents[0]? | return none
    let some view ← resolutionClauseView proof type | return none
    unless !view.isAClause do return none
    let some selected := view.regular[info.literal.index]? | return none
    let some terms ← materializeTermsIn input bindings scope #[info.term] | return none
    let some term := terms[0]? | return none
    let some condition ← universalCondition selected | return none
    let some target := targetClauseLiterals? input bindings | return none
    for index in [:target.size] do
      let tail := target.eraseIdxIfInBounds index
      let some reordered ← VampireHammer.ClauseMeta.reorderAndNormalize proof
          view.regular.toList (selected :: tail.toList) | continue
      let transition ← withLocalDeclD `quantifierSource selected fun assumption => do
        let some universal ← higherOrderBooleanTransport assumption condition | return none
        let quantified ← whnfR (← inferType universal)
        unless ← (pure quantified.isForall <&&>
            (do isDefEq quantified.bindingDomain! (← inferType term))) do
          return none
        let some transported ← higherOrderBooleanTransport (mkApp universal term) target[index]!
          | return none
        some <$> mkLambdaFVars #[assumption] transported
      let some transition := transition | continue
      let result ← mkAppM ``higherOrderMapHead
        #[← mkListLit (mkSort .zero) tail.toList, transition, reordered]
      let some result ← VampireHammer.ClauseMeta.reorderAndNormalize result
          (target[index]! :: tail.toList) target.toList | continue
      return some result
    pure none

end VampireHammer.Backend
