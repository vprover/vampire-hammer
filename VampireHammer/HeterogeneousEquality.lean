import Auto.Tactic

/-! Proof-producing normalization of heterogeneous equality at equal types. -/

namespace VampireHammer.HeterogeneousEquality

open Lean Meta

private theorem sameTypeHEq {α : Sort u} (a b : α) : (HEq a b) = (a = b) :=
  propext ⟨eq_of_heq, heq_of_eq⟩

/-- Rewrite same-type HEq throughout a source proposition, including under
quantifiers and negation. Congruence constructs a proof of the entire rewrite;
transport the source proof along it so replay retains the original assumptions.
Different types remain heterogeneous. Never solve unknown type metavariables
just to make this conversion applicable. -/
def normalizeLemma (lemma : Auto.Lemma) : MetaM Auto.Lemma := do
  unless (lemma.type.find? (·.isConstOf ``HEq)).isSome do return lemma
  let context ← Simp.mkContext { maxSteps := 100000, zetaDelta := false, dsimp := false }
  let (result, _) ← Simp.main lemma.type context (methods := { post := fun expression => do
    let some (leftType, left, rightType, right) := expression.heq?
      | return .done { expr := expression }
    if leftType.hasMVar || rightType.hasMVar then return .done { expr := expression }
    unless ← withNewMCtxDepth <| isDefEq leftType rightType do
      return .done { expr := expression }
    let equality ← mkAppM ``sameTypeHEq #[left, right]
    return .done { expr := ← mkEq left right, proof? := some equality } })
  let proof ← match result.proof? with
    | none => pure lemma.proof
    | some equality => mkEqMP equality lemma.proof
  return { lemma with proof, type := result.expr }

end VampireHammer.HeterogeneousEquality
