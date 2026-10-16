import VampireHammer

/-!
Central squares imply central commutators, using only Lean and VampireHammer.
The group operations, group laws, and commutation predicate are defined here.
-/

namespace CentralSquaresExample

/-- A group, with its operations and both identity and inverse laws explicit. -/
class Group (G : Type u) extends Mul G, Inv G, OfNat G 1 where
  mul_assoc (a b c : G) : (a * b) * c = a * (b * c)
  one_mul (a : G) : 1 * a = a
  mul_one (a : G) : a * 1 = a
  inv_mul_cancel (a : G) : a⁻¹ * a = 1
  mul_inv_cancel (a : G) : a * a⁻¹ = 1

export Group (mul_assoc one_mul mul_one inv_mul_cancel mul_inv_cancel)

/-- Two elements commute when reversing their product leaves it unchanged. -/
def Commute {G : Type u} [Mul G] (a b : G) : Prop := a * b = b * a

variable {G : Type u} [Group G]

theorem mul_inv_cancel_left (a b : G) : a * (a⁻¹ * b) = b := by
  rw [← mul_assoc, mul_inv_cancel, one_mul]

/-- A product of two elements commuting with `c` also commutes with `c`. -/
theorem Commute.mul_left {a b c : G} (ha : Commute a c) (hb : Commute b c) :
    Commute (a * b) c := by
  change (a * b) * c = c * (a * b)
  change a * c = c * a at ha
  change b * c = c * b at hb
  rw [mul_assoc, hb, ← mul_assoc a c b, ha, mul_assoc]

theorem centralSquares_manual
    (h : ∀ x y : G, Commute (x * x) y) (a b c : G) :
    Commute (a * b * a⁻¹ * b⁻¹) c := by
  have factor : a * b * a⁻¹ * b⁻¹ =
      (a * a) * ((a⁻¹ * b) * (a⁻¹ * b)) * (b⁻¹ * b⁻¹) := by
    simp only [mul_assoc, mul_inv_cancel_left]
  rw [factor]
  exact ((h a c).mul_left (h (a⁻¹ * b) c)).mul_left (h b⁻¹ c)


theorem centralSquares
    (h : ∀ x y : G, Commute (x * x) y) (a b c : G) :
    Commute (a * b * a⁻¹ * b⁻¹) c := by
  vampire

#print axioms centralSquares_manual
#print axioms centralSquares

end CentralSquaresExample
