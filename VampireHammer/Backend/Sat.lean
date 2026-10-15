import VampireHammer.Backend.Common
import VampireHammer.Backend.EUF
import VampireHammer.Backend.SatCertificate
import Lean.Meta.Native
import VampLean

/-!
AVATAR SAT closure and the `sat_conversion` representation exit.

Small supplied SAT trails can be checked by proof-producing unit propagation.
Larger RUP trails are reflected through Lean's standard LRAT checker; trails
that cannot be converted are rederived by `bv_decide` from the checked
boundary parents. `sat_conversion` itself is an identity/transport handler,
not a `grind` fallback.
-/

namespace VampireHammer.Backend

open Lean Meta Elab Tactic
open Auto.Embedding.Lam
open VampireHammer.ClauseMeta
open Internal

/-- Bound reflection of Vampire's supplied SAT trail independently of the
small proof-producing replay budget. Zero disables LRAT reflection. -/
register_option vampire.satLratReplayLimit : Nat := {
  defValue := 4096
  descr := "SAT trail node budget for checked LRAT reflection (0 disables it)"
}

/-- Maximum SAT-trail node count attempted by checked unit-propagation replay.
A proportional literal/parent budget also prevents a few very wide nodes from
bypassing the limit. Larger trails use LRAT reflection, whose cost is nearly
constant (one native check); replay grows faster than linearly and was slower
than reflection at 125 nodes but faster at 75 in measured TPTP problems. -/
register_option vampire.satReplayLimit : Nat := {
  defValue := 96
  descr := "SAT replay node budget before falling back to bv_decide (0 disables replay)"
}

/-! ## AVATAR SAT closure

For a small trail, the parent hints are treated as untrusted RUP suggestions
and checked by proof-producing unit propagation. Larger trails use compact
LRAT reflection. If the supplied trail needs genuine RAT hints that Vampire
does not print, or exceeds both budgets, the checked boundary clauses are
translated to compact Boolean clauses and refuted with `bv_decide`. -/

private structure AvatarLiteral where
  atomIndex : Nat
  negated : Bool
deriving Inhabited

/-- Recognize one AVATAR literal and record the matching split proposition.
Only supplied split propositions enter this table. Ground first-order literals
may match a certified split definition by definitional equality. -/
private def avatarLiteral? (avatarSymbols : Array Expr) (literal : Expr) :
    MetaM (Option AvatarLiteral) := do
  if let some index := avatarSymbols.findIdx? (· == literal) then
    return some { atomIndex := index, negated := false }
  let atom? ← notArgument? literal
  if let some atom := atom? then
    if let some index := avatarSymbols.findIdx? (· == atom) then
      return some { atomIndex := index, negated := true }
  -- EUF conflict boundaries contain ground literals rather than split names.
  -- Accept an alias only when its certified local definition unfolds to the
  -- very same proposition. This is a definitional check, not a new theory axiom.
  withConfig (fun config => { config with zetaDelta := true }) do
    for (symbol, index) in avatarSymbols.zipIdx do
      if ← isDefEq literal symbol then return some { atomIndex := index, negated := false }
      if let some atom := atom? then
        if ← isDefEq atom symbol then return some { atomIndex := index, negated := true }
    pure none

private def booleanClause (literals : Array AvatarLiteral) (variables : Array Expr) : Expr :=
  literals.foldr (init := mkConst ``Bool.false) fun literal rest =>
    let atom := variables[literal.atomIndex]!
    let value := if literal.negated then mkApp (mkConst ``Bool.not) atom else atom
    mkAppN (mkConst ``Bool.or) #[value, rest]

private partial def withBooleanVariables (count index : Nat) (variables : Array Expr)
    (k : Array Expr → MetaM α) : MetaM α := do
  if index < count then
    let name := (`avatarBool).appendIndexAfter index
    withLocalDeclD name (mkConst ``Bool) fun booleanVariable =>
      withBooleanVariables count (index + 1) (variables.push booleanVariable) k
  else
    k variables

/-- A truth assignment carries an actual Lean proof of the signed atom. -/
private abbrev SatAssignments := Std.HashMap Nat (Bool × Expr)

private structure ReplayedSatClause where
  literals : Array Expr
  decoded : Array AvatarLiteral
  proof : Expr
deriving Inhabited

private def falseLiteralProof? (literal : AvatarLiteral) (assignments : SatAssignments) :
    MetaM (Option Expr) := do
  let some (value, proof) := assignments.get? literal.atomIndex | return none
  unless value == literal.negated do return none
  if literal.negated then some <$> mkAppM ``not_not_intro #[proof]
  else pure (some proof)

private def allFalseCertificate (literals : Array Expr) (decoded : Array AvatarLiteral)
    (assignments : SatAssignments) : MetaM Expr := do
  let mut tail := mkPropList []
  let mut certificate := mkConst ``VampireHammer.Clause.AllFalse.nil
  for index in (List.range literals.size).reverse do
    let some negative ← falseLiteralProof? decoded[index]! assignments
      | throwError "SAT replay attempted to erase an unassigned literal"
    certificate := mkAppN (mkConst ``VampireHammer.Clause.AllFalse.cons)
      #[literals[index]!, tail, negative, certificate]
    tail := mkPropList (literals.extract index literals.size).toList
  pure certificate

/-- Check reverse unit propagation using only the named antecedent clauses.
No SAT-search result or RAT label is trusted: every propagation applies a
small clause theorem to existing proof terms. -/
private def propagateSat (parents : Array ReplayedSatClause) (atomCount : Nat)
    (initial : SatAssignments) : MetaM (Option Expr) := do
  let mut assignments := initial
  for _ in [:atomCount + 1] do
    let mut progress := false
    for parent in parents do
      let mut satisfied := false
      let mut unknown : Array Nat := #[]
      for index in [:parent.decoded.size] do
        let literal := parent.decoded[index]!
        match assignments.get? literal.atomIndex with
        | some (value, _) =>
          if value != literal.negated then satisfied := true
        | none => unknown := unknown.push index
      if satisfied || unknown.size > 1 then continue
      if unknown.isEmpty then
        let literals := mkPropList parent.literals.toList
        let certificate ← allFalseCertificate parent.literals parent.decoded assignments
        return some (mkAppN (mkConst ``VampireHammer.Clause.AllFalse.notHolds)
          #[literals, certificate, parent.proof])
      let index := unknown[0]!
      let before := parent.literals.extract 0 index
      let after := parent.literals.extract (index + 1) parent.literals.size
      let beforeList := mkPropList before.toList
      let afterList := mkPropList after.toList
      let beforeFalse ← allFalseCertificate before (parent.decoded.extract 0 index) assignments
      let afterFalse ← allFalseCertificate after
        (parent.decoded.extract (index + 1) parent.decoded.size) assignments
      let proof := mkAppN (mkConst ``VampireHammer.Clause.unitOfFalse)
        #[beforeList, afterList, parent.literals[index]!, beforeFalse, afterFalse, parent.proof]
      let literal := parent.decoded[index]!
      assignments := assignments.insert literal.atomIndex (!literal.negated, proof)
      progress := true
    unless progress do return none
  pure none

private def proveSatRup (literals : Array Expr) (decoded : Array AvatarLiteral)
    (parents : Array ReplayedSatClause) (atomCount : Nat) : MetaM (Option Expr) := do
  let literalList := mkPropList literals.toList
  let target := mkApp (mkConst ``VampireHammer.Clause.Holds) literalList
  if literals.isEmpty then return ← propagateSat parents atomCount {}
  withLocalDeclD `satNegatedClause (mkNot target) fun negative => do
    let mut assignments : SatAssignments := {}
    let mut notTail := negative
    let mut contradiction? := none
    for index in [:literals.size] do
      let literal := decoded[index]!
      let tail := mkPropList (literals.extract (index + 1) literals.size).toList
      let notLiteral := mkAppN (mkConst ``VampireHammer.Clause.notHeadOfNotHolds)
        #[literals[index]!, tail, notTail]
      let proof ← if literal.negated then mkAppM ``Classical.byContradiction #[notLiteral]
        else pure notLiteral
      let value := literal.negated
      if let some (previous, previousProof) := assignments.get? literal.atomIndex then
        if value != previous then
          contradiction? := some (if value then mkApp previousProof proof else mkApp proof previousProof)
      assignments := assignments.insert literal.atomIndex (value, proof)
      notTail := mkAppN (mkConst ``VampireHammer.Clause.notTailOfNotHolds)
        #[literals[index]!, tail, notTail]
    let conflict? ← match contradiction? with
      | some proof => pure (some proof)
      | none => propagateSat parents atomCount assignments
    let some contradiction := conflict? | return none
    let body ← mkLambdaFVars #[negative] contradiction
    let proof ← mkAppOptM ``Classical.byContradiction #[some target, some body]
    asExpectedType proof target

/-- Replay a small supplied SAT trail when each derived clause has a checked
RUP proof. Genuine RAT steps and malformed hints simply decline this fast path. -/
private def avatarSatReplay (input : RuleInput) (atoms : Array Expr)
    (clauses : Array (Array AvatarLiteral)) (clauseProofs : Array Expr) :
    MetaM (Option Expr) := do
  let some (root, trail) := input.satProof? | return none
  let limit := vampire.satReplayLimit.get (← getOptions)
  if limit == 0 || trail.size > limit ||
      trail.foldl (fun total node => total + node.literals.size + node.parents.size) 0 > limit * 16 then
    return none
  let mut proved : Std.HashMap String ReplayedSatClause := {}
  for index in [:input.parents.size] do
    let some parent := input.parents[index]? | return none
    proved := proved.insert parent.parent.name {
      literals := clauses[index]!.map fun literal =>
        if literal.negated then mkNot atoms[literal.atomIndex]! else atoms[literal.atomIndex]!
      decoded := clauses[index]!, proof := clauseProofs[index]!
    }
  for node in trail do
    let mut decoded := #[]
    for literal in node.literals do
      let some literal ← avatarLiteral? atoms literal | return none
      decoded := decoded.push literal
    let mut parents := #[]
    for parent in node.parents do
      let some proof := proved.get? parent.name | return none
      parents := parents.push proof
    let targetList := mkPropList node.literals.toList
    let target := mkApp (mkConst ``VampireHammer.Clause.Holds) targetList
    let proof? ← if node.rule == "sat_conversion" && parents.size == 1 then
      let some reordered ← ClauseMeta.reorderAndNormalize parents[0]!.proof
        parents[0]!.literals.toList node.literals.toList | pure none
      asExpectedType reordered target
    else if node.rule == "rat" then
      proveSatRup node.literals decoded parents atoms.size
    else pure none
    let some proof := proof? | do
      trace[vampire.replay]
        "AVATAR SAT replay stopped at {node.name}: `{node.rule}` was not checkable by unit propagation"
      return none
    proved := proved.insert node.name { literals := node.literals, decoded, proof }
  let some final := proved.get? root | return none
  unless final.literals.isEmpty do return none
  trace[vampire.replay] "AVATAR SAT replay checked {trail.size} supplied nodes by unit propagation"
  asExpectedType final.proof (mkConst ``False)

/-- Convert one signed AVATAR clause with a single named theorem application.

Both conversions hold by construction: `sourceProof` has type `Holds aliases`
for the aliases `atoms`/`literals` determine (see `avatarSatByBVDecide`), which
is `literals`' signed list mapped to propositions, and `expected` is the
Boolean clause over `decide atom`, which `SignedLiteral.clause` of that list
reduces to. The kernel checks both when it checks the final proof; stating
`expected` directly avoids unifying them by reduction for every clause. -/
private def booleanClausePremise (sourceProof expected : Expr)
    (literals : Array AvatarLiteral) (atoms : Array Expr) :
    MetaM Expr := do
  let signed := literals.map fun literal =>
    mkApp2 (mkConst ``VampireHammer.Clause.SignedLiteral.mk)
      atoms[literal.atomIndex]!
      (if literal.negated then mkConst ``Bool.false else mkConst ``Bool.true)
  let signedList ← mkListLit (mkConst ``VampireHammer.Clause.SignedLiteral) signed.toList
  let bridge := mkApp (mkConst ``VampireHammer.Clause.SignedLiteral.toBoolean) signedList
  pure (mkExpectedPropHint (mkApp bridge sourceProof) expected)

/-- The balanced `SatCertificate.Assignment` whose lookup at `i` yields
`variables[i]`. A subtree's local index `j` is position `stride * j + offset`
of the whole assignment: its root is `j = 0`, and `Assignment.get` sends odd
local indices `2j+1` to the first child and even ones `2j+2` to the second. -/
private partial def assignmentTree (variables : Array Expr) (stride offset : Nat) : Expr :=
  if h : offset < variables.size then
    mkApp3 (mkConst ``SatCertificate.Assignment.node) variables[offset]
      (assignmentTree variables (2 * stride) (stride + offset))
      (assignmentTree variables (2 * stride) (2 * stride + offset))
  else mkConst ``SatCertificate.Assignment.leaf

/-- Use the standard LRAT checker on the original AVATAR CNF. The generated
Boolean theorem has only its clause hypotheses and fresh Boolean atoms; the
native check contains closed certificate data and no replay hypotheses. -/
private def avatarLratBooleanProof (input : RuleInput) (atoms : Array Expr)
    (clauses : Array (Array AvatarLiteral)) (booleanVariables booleanClauses : Array Expr)
    (theoremType : Expr) : MetaM (Option Expr) := do
  let some (root, trail) := input.satProof? | return none
  let limit := vampire.satLratReplayLimit.get (← getOptions)
  if limit == 0 || trail.size > limit ||
      trail.foldl (fun n step => n + step.literals.size + step.parents.size) 0 > limit * 32 then
    return none
  let boundary := (input.parents.zip clauses).map fun (parent, clause) =>
    (parent.parent.name, clause.map fun literal => (literal.atomIndex, !literal.negated))
  let mut steps : Array SatCertificate.RupStep := #[]
  for step in trail do
    let mut literals := #[]
    for literal in step.literals do
      let some decoded ← avatarLiteral? atoms literal | return none
      literals := literals.push (decoded.atomIndex, !decoded.negated)
    steps := steps.push ⟨step.name, literals, step.parents.map (·.name)⟩
  let some actions := SatCertificate.compile boundary steps root | do
    return none
  let data := boundary.toList.map (·.2.toList)
  let dataExpr := toExpr data
  -- The hints travel as one LRAT string literal, decoded by the standard
  -- (already compiled) parser. Embedding them as constructor terms instead
  -- made compiling the native check the dominant cost of this step.
  let certificate := mkStrLit (Std.Tactic.BVDecide.LRAT.lratProofToString actions)
  -- Reuse the heads and tails of this one reflected list. Re-reflecting
  -- every suffix would duplicate quadratic amounts of closed certificate
  -- data and make final proof abstraction expensive.
  let mut clauseExprs := #[]
  let mut tailExprs := #[]
  let mut cursor := dataExpr
  for _ in [:data.length] do
    clauseExprs := clauseExprs.push cursor.appFn!.appArg!
    cursor := cursor.appArg!
    tailExprs := tailExprs.push cursor
  let clauseArray ← mkAppM ``List.toArray #[dataExpr]
  let cnf ← mkAppM ``Std.Sat.CNF.mk #[clauseArray]
  let check := mkApp2 (mkConst ``Std.Tactic.BVDecide.Reflect.verifyCert) cnf certificate
  let .success checked ← nativeEqTrue `vampire_sat check | do
    return none
  let assign := mkApp (mkConst ``SatCertificate.Assignment.get) (assignmentTree booleanVariables 1 0)
  let result ← forallTelescope theoremType fun hypotheses _ => do
    unless hypotheses.size == booleanClauses.size do
      throwError "AVATAR LRAT theorem has unexpected premises"
    let mut satisfied ← mkEqRefl (mkConst ``Bool.true)
    for index in (List.range data.length).reverse do
      satisfied := mkAppN (mkConst ``SatCertificate.satCons) #[assign, clauseExprs[index]!,
        tailExprs[index]!, hypotheses[index]!, satisfied]
    let refutation := mkAppN (mkConst ``SatCertificate.refuteCert)
      #[dataExpr, certificate, checked, assign, satisfied]
    mkLambdaFVars hypotheses refutation
  pure (some result)

/-- Prove the AVATAR boundary clauses inconsistent with checked SAT reflection.

The Boolean theorem is built in a context containing only fresh Boolean
variables, so it cannot depend on first-order hypotheses or on Vampire's SAT
trail. `Replay` makes the final refutation cite the original pure-AVATAR
clauses behind `sat_conversion`. LRAT reflection uses that original CNF;
`bv_decide` remains the fallback if hint conversion or checking declines. The theorem is
instantiated with `decide splᵢ`; each checked clause parent is converted to a
Boolean clause by one named clause bridge. -/
def avatarSatByBVDecide (input : RuleInput) : MetaM (Option Expr) := do
  unless input.sourceProof?.isNone && !input.parents.isEmpty &&
      input.step.binders.isEmpty && input.parents.all (·.clauseForm) do
    return none
  let avatarSymbols := avatarAtoms input
  if avatarSymbols.isEmpty then return none
  let mut clauses : Array (Array AvatarLiteral) := #[]
  let mut clauseProofs : Array Expr := #[]
  for parent in input.parents do
    let parentType ← inferType parent.proof
    let some grounded ← groundClause parent.proof parentType | return none
    let mut clause := #[]
    for literal in grounded.literals do
      let some decoded ← avatarLiteral? avatarSymbols literal | return none
      clause := clause.push decoded
    let aliases := clause.map fun literal =>
      if literal.negated then mkNot avatarSymbols[literal.atomIndex]!
      else avatarSymbols[literal.atomIndex]!
    let expected ← holdsType aliases
    let some proof ← withConfig (fun config => { config with zetaDelta := true }) <|
        asExpectedType grounded.proof expected | return none
    clauseProofs := clauseProofs.push proof
    clauses := clauses.push clause
  let replay? ← try avatarSatReplay input avatarSymbols clauses clauseProofs catch error =>
    trace[vampire.replay] "AVATAR SAT replay declined: {error.toMessageData}"
    pure none
  if let some proof := replay? then return some proof
  trace[vampire.replay] "AVATAR SAT using Boolean refutation"
  withBooleanVariables avatarSymbols.size 0 #[] fun booleanVariables => do
    let booleanClauses ← clauses.mapM fun clause =>
      mkAppM ``Eq #[booleanClause clause booleanVariables, mkConst ``Bool.true]
    let mut theoremType := mkConst ``False
    for booleanClauseType in booleanClauses.reverse do
      theoremType ← mkArrow booleanClauseType theoremType
    let reflected? ← try
      avatarLratBooleanProof input avatarSymbols clauses
        booleanVariables booleanClauses theoremType
    catch _ =>
      pure none
    let theoremBody ← if let some proof := reflected? then pure proof else do
      let theoremProof ← mkFreshExprSyntheticOpaqueMVar theoremType
      let .mvar theoremGoalId := theoremProof | throwError "expected Boolean theorem goal"
      -- Remove every surrounding replay hypothesis from the Boolean theorem.
      let theoremGoal ← theoremGoalId.clearAllExcept
        (booleanVariables.map (·.fvarId!))
      let (remaining, _) ← Lean.Elab.runTactic theoremGoal (← `(tactic| bv_decide))
      unless remaining.isEmpty do throwError "Boolean SAT refutation left goals"
      instantiateMVars theoremProof
    let booleanTheorem ← mkLambdaFVars booleanVariables theoremBody
    let mut decidedAtoms := #[]
    for atom in avatarSymbols do
      let decidable ← mkAppM ``Classical.propDecidable #[atom]
      decidedAtoms := decidedAtoms.push
        (← mkAppOptM ``decide #[some atom, some decidable])
    let mut result := mkAppN booleanTheorem decidedAtoms
    let mut resultType ← whnf (← inferType result)
    for index in [:input.parents.size] do
      unless resultType.isForall do return none
      let expectedPremise := resultType.bindingDomain!
      let some clauseProof := clauseProofs[index]? | return none
      let some clause := clauses[index]? | return none
      let premise ← booleanClausePremise clauseProof expectedPremise clause avatarSymbols
      result := mkApp result premise
      resultType ← whnf (resultType.bindingBody!.instantiate1 premise)
    unless ← isDefEq resultType (mkConst ``False) do return none
    pure (some result)

/-- Prove a ground clause consequence by abstracting arbitrary first-order
atoms to Booleans. The SAT checker only sees clauses with checked Lean proofs;
the negated conclusion supplies additional unit hypotheses. -/
def propositionalConsequence (input : RuleInput) (parents : Array GroundClause)
    (target : Array Expr) : MetaM (Option Expr) := do
  let targetType ← holdsType target
  withLocalDeclD `notSatResult (mkNot targetType) fun negative => do
    let facts ← negatedClauseFacts target negative
    let mut clauses := parents
    for proof in facts do
      let proofType ← inferType proof
      let literal := (← notArgument? proofType).map mkNot |>.getD proofType
      let clauseProof ← injectLiteral #[literal] 0 proof
      clauses := clauses.push ⟨#[literal], clauseProof⟩
    let mut atoms : Array Expr := #[]
    let mut prepared := #[]
    for (clause, index) in clauses.zipIdx do
      for literal in clause.literals do
        let atom := (← notArgument? literal).getD literal
        unless atoms.contains atom do atoms := atoms.push atom
      let type ← holdsType clause.literals
      let some proof ← asExpectedType clause.proof type | return none
      prepared := prepared.push ({
        parent := { name := s!"satPremise{index}" }, binders := #[], existentialVariables := #[],
        componentBinders := #[], target := type, clauseForm := true,
        clauseLiterals? := some clause.literals, cnfCandidates := pure none,
        proof := proof } : ParentProof)
    if atoms.isEmpty then return ← eufConsequence parents target
    let symbols := atoms.zipIdx.foldl (fun map (atom, i) => map.insert s!"splSat{i}" atom)
      ({} : Std.HashMap String Expr)
    let localStep := { input.step with binders := #[], satProof? := none }
    let localInput : RuleInput := { input with
      target := mkConst ``False
      parents := prepared
      symbols := symbols
      sourceProof? := none
      satProof? := none
      step := localStep }
    -- Global subsumption usually certifies a propagation consequence. Try
    -- that cheap proof-producing check before invoking the Boolean solver.
    let mut rupParents : Array ReplayedSatClause := #[]
    for parent in prepared do
      let some literals := parent.clauseLiterals? | return none
      let some decoded := (← literals.mapM (avatarLiteral? atoms)).mapM id | return none
      rupParents := rupParents.push { literals, decoded, proof := parent.proof }
    let direct? ← proveSatRup #[] #[] rupParents atoms.size
    let proof? ← if let some proof := direct? then pure (some proof) else
      try avatarSatByBVDecide localInput catch error => do
        trace[vampire.replay] "propositional consequence declined: {error.toMessageData}"
        pure none
    let some conflict := proof? | return none
    let body ← mkLambdaFVars #[negative] conflict
    some <$> mkAppOptM ``Classical.byContradiction #[some targetType, some body]

/-- Replay an AVATAR `sat_conversion` node whose formula is unchanged while
crossing from Vampire's first-order proof into its propositional SAT layer. -/
def avatarIdentity (input : RuleInput) : MetaM (Option Expr) := do
  unless input.sourceProof?.isNone && input.parents.size == 1 do return none
  let some parent := input.parents[0]? | return none
  -- This fast path also covers the empty clause, definitionally `False`, if a
  -- Vampire version happens to print a direct empty `sat_conversion` node.
  if let some proof ← asExpectedType parent.proof input.target then
    return some proof
  if parent.clauseForm then
    let some (_, source) ← clauseView parent.proof (← inferType parent.proof)
      | return none
    let some target := input.clauseLiterals? | return none
    let some proof ← reorderAndNormalize parent.proof source.toList target.toList
      | return none
    pure (some proof)
  else
    asExpectedType parent.proof input.target

end VampireHammer.Backend
