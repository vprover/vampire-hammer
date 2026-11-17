import VampireHammer
import Mathlib.Order.Defs.PartialOrder

namespace MinimalExamples

inductive Logic4 where
  | low
  | high
  | x
  | z
deriving DecidableEq

namespace Logic4

abbrev IsTrue (a : Logic4) : Prop := a = .high

def and (a : Logic4) (b : Logic4) : Logic4 :=
  match a, b with
    | .low, _ => .low
    | _, .low => .low
    | .high, b' => b'
    | a', .high => a'
    | _, _ => .x

def not (a : Logic4) : Logic4 :=
  match a with
    | .low => .high
    | .high => .low
    | _ => .x

def or (a : Logic4) (b : Logic4) : Logic4 :=
  match a, b with
    | .high, _ => .high
    | _, .high => .high
    | .low, b' => b'
    | a', .low => a'
    | _, _ => .x

def impl (a : Logic4) (b : Logic4) : Logic4 :=
  Logic4.or a.not b

def xor (a : Logic4) (b : Logic4) : Logic4 :=
  match a, b with
    | .high, .high => .low
    | .low, .low => .low
    | .high, .low => .high
    | .low, .high => .high
    | _, _ => .x

def xnor (a : Logic4) (b : Logic4) : Logic4 :=
  match a, b with
    | .high, .high => .high
    | .low, .low => .high
    | .high, .low => .low
    | .low, .high => .low
    | _, _ => .x

theorem xnor_eq_neg_xor (a : Logic4) (b : Logic4) : a.xnor b = (a.xor b).not := by
  vampire [xnor.eq_1, xnor.eq_2, xnor.eq_3, xnor.eq_4, xnor.eq_5,
    xor.eq_1, xor.eq_2, xor.eq_3, xor.eq_4, xor.eq_5,
    not.eq_1, not.eq_2, not.eq_3]

/-- Constructor distinctness does not by itself tell Vampire that these are all the values. -/
lemma eq_low_or_high_or_x_or_z (a : Logic4) :
    a = low ∨ a = high ∨ a = x ∨ a = z := by
  cases a <;> vampire

lemma double_neg_elim (a : Logic4) (h : a ≠ .z) : a.not.not = a := by
  vampire [h, eq_low_or_high_or_x_or_z, not.eq_1, not.eq_2, not.eq_3]

lemma de_morgan (a : Logic4) (b : Logic4) : (Logic4.and a b).not = (Logic4.or a.not b.not) := by
  vampire [and.eq_1, and.eq_2, and.eq_3, and.eq_4, and.eq_5,
    or.eq_1, or.eq_2, or.eq_3, or.eq_4, or.eq_5,
    not.eq_1, not.eq_2, not.eq_3, eq_low_or_high_or_x_or_z]

lemma de_morgen_rev (a : Logic4) (b : Logic4) : (Logic4.or a b).not = (Logic4.and a.not b.not) := by
  vampire [and.eq_1, and.eq_2, and.eq_3, and.eq_4, and.eq_5,
    or.eq_1, or.eq_2, or.eq_3, or.eq_4, or.eq_5,
    not.eq_1, not.eq_2, not.eq_3, eq_low_or_high_or_x_or_z]

instance : LE Logic4 where
  le a b := a = b ∨ a = low ∨ b = high

instance (a b : Logic4) : Decidable (a ≤ b) :=
  inferInstanceAs (Decidable (a = b ∨ a = low ∨ b = high))

instance : PartialOrder Logic4 where
  le_refl a := by vampire [*]
  le_trans a b c := by vampire [*]
  le_antisymm a b := by vampire [*]

instance (a b : Logic4) : Decidable (a < b) :=
  inferInstanceAs (Decidable (a ≤ b ∧ ¬ b ≤ a))

instance : Zero Logic4 := ⟨low⟩
instance : One Logic4 := ⟨high⟩

theorem zero_lt_x : (0 : Logic4) < x := by vampire
theorem zero_lt_z : (0 : Logic4) < z := by vampire
theorem x_lt_one : x < (1 : Logic4) := by vampire
theorem z_lt_one : z < (1 : Logic4) := by vampire

end Logic4

end MinimalExamples
