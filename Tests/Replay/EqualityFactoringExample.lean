import VampireHammer

-- set_option vampire.executable "Tests/testdata/scripts/mock-equality-factoring.sh"
-- set_option vampire.outputPath "artifacts/equality-factoring-example.p"
set_option trace.vampire.replay true
set_option vampire.executable "Tests/testdata/scripts/local-vampire.sh"
set_option vampire.disableAvatar true

/-- Equality factoring applies `Y ↦ X`, removes `f X = a`, and derives
`a ≠ b ∨ f X = b ∨ R X` by transitivity.
 theorem equalityFactoringExample {α : Type} (f : α → α) (d a b : α)
    (R : α → Prop)
    (S : α → α → Prop)
    (parent : ∀ x y, f x = a ∨ f y = b ∨ R y)
    (notSOrEq : ¬ S a b ∨ a = b) (hasS : S a b)
    (notFb : f d ≠ b) (notR : ¬ R d) : False := by
  vampire [parent, notSOrEq, hasS, notFb, notR]
-/


theorem asdf : ∀ {α : Type} [αNonempty : Nonempty α] (lives : α → Prop) (agatha : α) (killed : α → α → Prop) (butler charles : α)
    (hates richer : α → α → Prop) (pel55_1 : ∃ (X : α), lives X ∧ killed X agatha) (pel55_2_1 : lives agatha)
    (pel55_2_2 : lives butler) (pel55_2_3 : lives charles)
    (pel55_3 : ∀ (X : α), lives X → X = agatha ∨ X = butler ∨ X = charles)
    (pel55_4 : ∀ (X Y : α), killed X Y → hates X Y) (pel55_5 : ∀ (X Y : α), killed X Y → ¬richer X Y)
    (pel55_6 : ∀ (X : α), hates agatha X → ¬hates charles X) (pel55_7 : ∀ (X : α), X ≠ butler → hates agatha X)
    (pel55_8 : ∀ (X : α), ¬richer X agatha → hates butler X) (pel55_9 : ∀ (X : α), hates agatha X → hates butler X)
    (pel55_10 : ∀ (X : α), ∃ (Y : α), ¬hates X Y) (pel55_11 : agatha ≠ butler), killed agatha agatha := by
  vampire [*]
