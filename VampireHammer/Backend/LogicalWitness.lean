/-! Shared classical choice interpretation for typed THF terms and quantified
proxy reconstruction. This module is independent of inference dispatch. -/
namespace VampireHammer.Backend

noncomputable def quantifierWitness {α : Sort _} [Nonempty α] (predicate : α → Prop) : α :=
  Classical.epsilon predicate

theorem quantifierWitness_spec {α : Sort _} [Nonempty α] (predicate : α → Prop)
    (h : ∃ x, predicate x) : predicate (quantifierWitness predicate) :=
  Classical.epsilon_spec_aux _ predicate h

end VampireHammer.Backend
