import VampireHammer.Backend.Instantiation
import VampireHammer.Backend.Sat
import VampireHammer.Backend.PredicateElimination

namespace VampireHammer.Backend
open Lean Meta
open Internal

private partial def alignAtoms (literals : List Expr) (reference : Array Expr)
    (budget : IO.Ref Nat) (finish : MetaM (Option Expr)) : MetaM (Option Expr) := do
  match literals with
  | [] => finish
  | literal :: rest =>
    let atom := (← notArgument? literal).getD literal
    for candidate in reference do
      let candidate := (← notArgument? candidate).getD candidate
      if atom.getAppFn != candidate.getAppFn then continue
      let remaining ← budget.get
      if remaining == 0 then return none
      budget.set (remaining - 1)
      let saved ← saveState
      if ← isDefEq atom candidate then
        if let some proof ← alignAtoms rest reference budget finish then return some proof
      saved.restore
    alignAtoms rest reference budget finish

private partial def alignParents (input : RuleInput) (anchorName : String)
    (target : Array Expr) (budget : IO.Ref Nat) (index : Nat)
    (instances : Array OpenClause) (reference : Array Expr) : MetaM (Option Expr) := do
  if index >= input.parents.size then
    let some clauses ← closeClauseInstances instances | return none
    return ← propositionalConsequence input clauses target
  let some parent := input.parents[index]? | return none
  if parent.parent.name == anchorName then
    return ← alignParents input anchorName target budget (index + 1) instances reference
  let some opened ← openClauseParent parent | return none
  alignAtoms opened.clause.literals.toList reference budget do
    let literals ← opened.clause.literals.mapM instantiateMVars
    alignParents input anchorName target budget (index + 1) (instances.push opened) (reference ++ literals)

/-- Check Vampire's propositional abstraction against actual instantiated
parent clauses. Parent order is immaterial; all supplied premises participate. -/
def globalSubsumption (input : RuleInput) : MetaM (Option Expr) := do
  unless input.sourceProof?.isNone && !input.parents.isEmpty &&
      input.parents.all (·.clauseForm) do return none
  underConclusionBinders input fun bindings _ => do
    let substitutions := input.parents.map fun parent =>
      ({ parent := parent.parent.name, bindings := #[] } : ParentSubstitution)
    let some target := targetClauseLiterals? input bindings | return none
    if let some instantiated ← instantiateParents input substitutions bindings then
      if let some clauses := (← instantiated.mapM fun (proof, type) => groundClause proof type).mapM id then
        if let some proof ← propositionalConsequence input clauses target then return some proof
    -- Vampire alpha-normalizes clauses before its SAT abstraction. Recover
    -- renamed variables by matching atoms, then check the proposed instances.
    let budget ← IO.mkRef (4096 : Nat)
    for parent in input.parents do
      let saved ← saveState
      if let some anchor ← openClauseParent parent then
        if let some proof ← matchClauseLiterals target.toList anchor.clause.literals budget do
            alignParents input parent.parent.name target budget 0 #[anchor] anchor.clause.literals then
          return some proof
      saved.restore
    pure none

/-- Independently prove an AVATAR EUF conflict axiom with no proof parents. -/
def theoryTautologySatConflict (input : RuleInput) : MetaM (Option Expr) := do
  unless input.sourceProof?.isNone && input.parents.isEmpty do return none
  underConclusionBinders input fun bindings targetType => do
    let literals ← match targetClauseLiterals? input bindings with
      | some literals => pure literals
      | none => flattenClause targetType
    let some proof ← eufConsequence #[] literals | return none
    if storesClauseForm input then return some proof
    fromClauseForm proof targetType 0 (some literals)

end VampireHammer.Backend
