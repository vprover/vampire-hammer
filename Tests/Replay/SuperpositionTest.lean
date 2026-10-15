import VampireHammer

set_option vampire.executable "Tests/testdata/scripts/local-vampire.sh"
set_option trace.vampire.replay true
set_option vampire.disableAvatar true

theorem pel55
    {Person : Type}
    (agatha butler charles : Person)
    (lives : Person → Prop)
    (killed hates richer : Person → Person → Prop)
    (pel55_1 : ∃ X, lives X ∧ killed X agatha)
    (pel55_2_1 : lives agatha)
    (pel55_2_2 : lives butler)
    (pel55_2_3 : lives charles)
    (pel55_3 : ∀ X, lives X → (X = agatha ∨ X = butler ∨ X = charles))
    (pel55_4 : ∀ X Y, killed X Y → hates X Y)
    (pel55_5 : ∀ X Y, killed X Y → ¬ richer X Y)
    (pel55_6 : ∀ X, hates agatha X → ¬ hates charles X)
    (pel55_7 : ∀ X, X ≠ butler → hates agatha X)
    (pel55_8 : ∀ X, ¬ richer X agatha → hates butler X)
    (pel55_9 : ∀ X, hates agatha X → hates butler X)
    (pel55_10 : ∀ X, ∃ Y, ¬ hates X Y)
    (pel55_11 : agatha ≠ butler) :
    killed agatha agatha := by
  vampire [pel55_1, pel55_2_1, pel55_2_2, pel55_2_3, pel55_3,
    pel55_4, pel55_5, pel55_6,pel55_7, pel55_8, pel55_9, pel55_10,pel55_11]
