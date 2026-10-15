import VampireHammer

set_option vampire.executable "Tests/testdata/scripts/local-vampire.sh"
set_option vampire.disableAvatar false
set_option trace.vampire.replay false

-- SYN978+1: Vampire's ennf_transformation emits `<~>` (XOR), which the proof
-- decoder must accept.
set_option vampire.outputPath "artifacts/regression-syn978.p" in
theorem syn978 : ∀ (a b : Prop), a ∧ b → (a ↔ b) := by
  vampire [*]

-- SYN932+1, SYN933+1, SYN052+1: the sort only occurs as a vacuous binder, so
-- Vampire prints the proof as FOF with untyped quantifiers.
set_option vampire.outputPath "artifacts/regression-syn932.p" in
theorem syn932 : ∀ {α : Type} [Nonempty α] (c : Prop), (∃ (_ : α), c) ↔ c := by
  vampire [*]

set_option vampire.outputPath "artifacts/regression-syn933.p" in
theorem syn933 : ∀ {α : Type} [Nonempty α] (c : Prop), (∀ (_ : α), c) ↔ c := by
  vampire [*]

set_option vampire.outputPath "artifacts/regression-syn052.p" in
theorem syn052 : ∀ {α : Type} [Nonempty α] (p : Prop) (big_f : α → Prop),
    (∀ (X : α), p ↔ big_f X) → (p ↔ ∀ (X1 : α), big_f X1) := by
  vampire [*]

-- SYN970+1, SYN979+1: a ground CNF clause extracted from under universals
-- that other conjuncts use needs an inhabitant as witness.
set_option vampire.outputPath "artifacts/regression-syn970.p" in
theorem syn970 : ∀ {α : Type} [Nonempty α] (p r : α → Prop) (A B : α),
    ∃ (X : α) (Y : α), (p X → r Y) → p A → r B := by
  vampire [*]

set_option vampire.outputPath "artifacts/regression-syn979.p" in
theorem syn979 : ∀ {α : Type} [Nonempty α] (q : α → Prop) (p : α → α → Prop) (r s : α → Prop) (A B : α),
    ∃ (X : α) (Y : α), (q X → p X A) ∧ q A ∧ q B ∧ (r Y → p B Y) ∧ r A ∧ r B ∧ (s A → p X Y) ∧ s A → p A B := by
  vampire [*]

-- SYN385+1: `pure_predicate_removal` replaces a negative-only predicate by
-- `False` under a `¬∃ ∀` alternation, which `grind` cannot bridge.
set_option vampire.outputPath "artifacts/regression-syn385.p" in
theorem syn385 : ∀ {α : Type} [Nonempty α] (big_p big_q : α → Prop),
    ∃ (X : α), ∀ (Y : α), big_p X → big_q X ∨ big_p Y := by
  vampire [*]

-- SYN338+1: `ennf_transformation` prints `(a & b) & c`; the decoder must keep
-- that grouping for derived steps rather than right-associating it.
set_option vampire.outputPath "artifacts/regression-syn338.p" in
theorem syn338 : ∀ {α : Type} [Nonempty α] (big_f : α → α → Prop),
    ∃ (X : α), ∀ (Y : α), ∃ (Z : α), big_f X Y → big_f Z X → big_f Y Y := by
  vampire [*]

-- SYN318+1: `pure_predicate_removal` sets a positive-only `p` to `True`,
-- weakening `B` to `p → B` where `B` is itself a `∀`.
set_option vampire.outputPath "artifacts/regression-syn318.p" in
theorem syn318 : ∀ {α : Type} [Nonempty α] (big_f big_g : α → Prop) (p : Prop),
    ∃ (Y : α), (∀ (X : α), big_f X → big_f Y → big_g X) → p → ∀ (X : α), big_f X → big_g Y := by
  vampire [*]

-- SYN349+1: VampLean's `ennf_transformation` states `<~>` as `Xor'`, the
-- decoder as `¬(↔)`.
set_option vampire.outputPath "artifacts/regression-syn349.p" in
theorem syn349 : ∀ {α : Type} [Nonempty α] (big_f : α → α → Prop),
    ∃ (X1 : α), ∀ (X2 : α), ∃ (X3 : α), ∀ (X4 : α),
      (big_f X1 X4 ↔ big_f X2 X4) → (((big_f X1 X4 ↔ big_f X4 X3) ↔ big_f X3 X4) ↔ big_f X4 X2) := by
  vampire [*]

#print axioms syn349
