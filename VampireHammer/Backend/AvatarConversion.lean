import VampireHammer.Backend.Metadata
import VampireHammer.Backend.EUF

/-! Explicit, proof-producing transport of EUF literals to AVATAR SAT names.
The occurrence map is checked against the source and its named definitions;
SAT sorting and duplicate removal are handled only after that transport. -/
namespace VampireHammer.Backend
open Lean Meta
open VampireHammer.ClauseMeta
open Internal

private partial def transportOccurrences (source mapped : Array Expr)
    (arrows : Array Expr) (index : Nat) (proof : Expr) : MetaM Expr := do
  if index == source.size then
    return ← mkAppOptM ``False.elim #[some (← holdsType mapped), some proof]
  let head ← withLocalDeclD `sourceLiteral source[index]! fun h => do
    mkLambdaFVars #[h] (← injectLiteral mapped index (mkApp arrows[index]! h))
  let tail ← withLocalDeclD `sourceTail (← holdsType (source.drop (index + 1))) fun h => do
    mkLambdaFVars #[h] (← transportOccurrences source mapped arrows (index + 1) h)
  mkAppM ``Or.elim #[proof, head, tail]

/-- Check the exact parent/occurrence contract and use the supplied definition
proofs to replace every FO literal with its signed SAT symbol. -/
def avatarConversion (input : RuleInput) (mappings : Array AvatarMapping) :
    MetaM (Option Expr) := do
  unless input.sourceProof?.isNone && input.step.binders.isEmpty do return none
  let some origin := input.parents[0]? | return none
  unless origin.binders.isEmpty do return none
  let some clause ← groundClause origin.proof (← inferType origin.proof) | return none
  unless mappings.size == clause.literals.size do return none
  let some target := input.clauseLiterals? | return none
  let mut mapped := #[]
  let mut arrows := #[]
  let mut usedDefinitions : Std.HashSet String := {}
  -- The annotation's order is not trusted: source indices select occurrences.
  for index in [:clause.literals.size] do
    let occurrences := mappings.filter (·.source.index == index)
    let #[entry] := occurrences | return none
    unless entry.source.parent == origin.parent.name do return none
    let some split := input.symbols.get? entry.symbol | return none
    unless (avatarAtoms input).any (· == split) do return none
    let definitions := (input.parents.extract 1 input.parents.size).filter
      (·.parent.name == entry.definition)
    let #[definition] := definitions | return none
    unless definition.binders.isEmpty do return none
    let some definitionProof ← (if definition.clauseForm then
      fromClauseForm definition.proof definition.target 0 definition.clauseLiterals?
      else asExpectedType definition.proof definition.target) | return none
    let (.app (.app (.const ``Iff _) left) right) ← whnf (← inferType definitionProof)
      | return none
    let (component, definitionProof) ←
      if left == split then pure (right, definitionProof)
      else if right == split then pure (left, ← mkAppM ``Iff.symm #[definitionProof])
      else return none
    let signedComponent := if entry.positive then component else mkNot component
    let signedSplit := if entry.positive then split else mkNot split
    let signedDefinition ← if entry.positive then pure definitionProof
      else mkAppM ``not_congr #[definitionProof]
    let some equivalence ← literalEquivalent? clause.literals[index]! signedComponent
      | return none
    let arrow ← withLocalDeclD `sourceLiteral clause.literals[index]! fun h => do
      let componentProof ← mkAppM ``Iff.mp #[equivalence, h]
      mkLambdaFVars #[h] (← mkAppM ``Iff.mpr #[signedDefinition, componentProof])
    mapped := mapped.push signedSplit
    arrows := arrows.push arrow
    usedDefinitions := usedDefinitions.insert entry.definition
  unless input.parents.size == usedDefinitions.size + 1 do return none
  -- Check both inclusions: sorting/duplicate removal cannot add or lose atoms.
  let some containment ← containedWitness mapped.toList target.toList | return none
  unless (← containedWitness target.toList mapped.toList).isSome do return none
  let transported ← transportOccurrences clause.literals mapped arrows 0 clause.proof
  let some transported ← asExpectedType transported (← holdsType mapped) | return none
  let result ← mkAppM ``VampireHammer.Clause.containedHolds #[containment, transported]
  asExpectedType result (← holdsType target)

end VampireHammer.Backend
