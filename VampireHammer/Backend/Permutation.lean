import VampireHammer.Backend.Common

/-!
The explicit associativity/commutativity inference.

This is the handler that may permute regular literal occurrences. Ordinary
calculus handlers keep their natural order. The occurrence certificate and the
proof-producing permutation bridge are checked separately; AVATAR context uses
its independent set transport.
-/

namespace VampireHammer.Backend

open Lean Meta Elab Tactic
open Auto.Embedding.Lam
open VampireHammer.ClauseMeta
open Internal

/-- Check the positional part of a parser-side `permutation([sourceIndex,...])`
certificate.  Literal equality itself is checked by `reorderAndNormalize`:
besides a definitional match it may accept an equality printed with its two
sides reversed.  This first check still makes the occurrence mapping total
and one-to-one, including when a clause contains duplicates. -/
private def validClausePermutation (source target : Array Expr) (positions : Array Nat) :
    MetaM Bool := do
  if source.size != target.size then
    return false
  -- Older synthetic AC nodes can have an empty diagnostic list when the TPTP
  -- AST printer wrapped a literal differently while calculating the mapping.
  -- The proof-producing bridge below still checks the complete occurrence
  -- permutation and every literal equivalence, so accepting this omission
  -- cannot admit an unsound transformation.
  if positions.isEmpty then return true
  if positions.size != target.size then return false
  let mut used : Std.HashSet Nat := {}
  for sourceIndex in positions do
    if sourceIndex >= source.size || used.contains sourceIndex then
      return false
    used := used.insert sourceIndex
  return true

/-- Reconstruct the explicit `associativity_commutativity` bridge inserted by
parser-side preprocessing. This is deliberately the sole place where an
already-resolved clause is permuted: resolution and forward subsumption only
produce their natural tail-concatenation order. -/
def associativityCommutativity (input : RuleInput) (positions : Array Nat) :
    MetaM (Option Expr) := do
  unless input.sourceProof?.isNone && input.parents.size == 1 &&
      input.parents.all (·.clauseForm) do
    return none
  let some decoderLiterals := input.clauseLiterals? | return none
  let some parent := input.parents[0]? | return none
  let build (binders : Array Expr) : MetaM (Option Expr) := do
    let parentProof := mkAppN parent.proof binders
    let targetLiterals := instantiateDecodedLiterals decoderLiterals binders
    let parentType ← inferType parentProof
    let sourceView? ← aClauseView parentProof parentType
    match sourceView? with
    | none =>
      let some (_, sourceLiterals) ← clauseView parentProof parentType | return none
      unless ← validClausePermutation sourceLiterals targetLiterals positions do
        trace[vampire.replay] "AC {input.step.name}: malformed occurrence permutation {positions}"
        return none
      -- `positions` is checked above as Vampire's occurrence certificate. The
      -- proof-producing bridge additionally checks every literal equivalence.
      let some proof ← reorderAndNormalize parentProof sourceLiterals.toList targetLiterals.toList
        | trace[vampire.replay] "AC {input.step.name}: literals cannot be matched by order or equality symmetry"
          return none
      return some proof
    | some source =>
      let (targetRegular, targetAvatar) :=
        splitAClauseLiterals (avatarAtoms input) targetLiterals
      -- `positions` indexes the flattened regular-and-AVATAR spelling and
      -- therefore cannot validate the regular sub-list on its own. The
      -- proof-producing regular bridge below checks the exact occurrence
      -- permutation; the AVATAR bridge checks mutual membership containment.
      -- Their `mapParts` application keeps the A-clause boundary visible in
      -- the proof term instead of flattening it to one large disjunction.
      let makeRegularTransform (sourcePart targetPart : Array Expr) : MetaM (Option Expr) := do
        let sourceType ← holdsType sourcePart
        withLocalDeclD `sourceClause sourceType fun sourceProof => do
          let some targetProof ← reorderAndNormalize sourceProof
              sourcePart.toList targetPart.toList
            | return none
          pure <| some (← mkLambdaFVars #[sourceProof] targetProof)
      let makeAvatarTransform (sourcePart targetPart : Array Expr) : MetaM (Option Expr) := do
        let some sourceInTarget ← containedWitness sourcePart.toList targetPart.toList
          | return none
        let some _targetInSource ← containedWitness targetPart.toList sourcePart.toList
          | return none
        let sourceType ← holdsType sourcePart
        withLocalDeclD `sourceAvatar sourceType fun sourceProof => do
          let targetProof ← mkAppM ``VampireHammer.Clause.containedHolds
            #[sourceInTarget, sourceProof]
          pure <| some (← mkLambdaFVars #[sourceProof] targetProof)
      let some regularTransform ← makeRegularTransform source.regular targetRegular
        | trace[vampire.replay] "AC {input.step.name}: regular A-clause literals cannot be matched"
          return none
      let some avatarTransform ← makeAvatarTransform source.avatar targetAvatar
        | trace[vampire.replay] "AC {input.step.name}: AVATAR literal sets differ"
          return none
      let sourceRegularList := mkPropList source.regular.toList
      let targetRegularList := mkPropList targetRegular.toList
      let sourceAvatarList := mkPropList source.avatar.toList
      let targetAvatarList := mkPropList targetAvatar.toList
      pure <| some <| mkAppN (mkConst ``VampireHammer.Clause.AClause.mapParts)
        #[sourceRegularList, targetRegularList, sourceAvatarList, targetAvatarList,
          regularTransform, avatarTransform, parentProof]
  if input.step.binders.isEmpty then
    return ← build #[]
  Meta.forallTelescopeReducing input.target fun targetFVars _ => do
    unless targetFVars.size == input.step.binders.size &&
        parent.binders.size == targetFVars.size do
      return none
    let some body ← build targetFVars | return none
    pure (some (← mkLambdaFVars targetFVars body))

end VampireHammer.Backend
