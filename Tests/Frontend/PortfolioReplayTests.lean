import VampireHammer

-- All exported inputs are below 1 KiB. Portfolio workers run sequentially.
set_option vampire.executable "Tests/testdata/scripts/local-vampire.sh"
set_option vampire.timeLimit 5
set_option trace.vampire.replay true

set_option vampire.outputPath "artifacts/portfolio-resolution.p" in
theorem portfolio_resolution {α : Type} (a : α) (P : α → Prop)
    (h1 : ∀ x, x ≠ a ∨ P x) (h2 : ¬P a) : False := by
  vampire [h1, h2]

set_option vampire.outputPath "artifacts/portfolio-splitting.p" in
theorem portfolio_splitting {α : Type} (a : α) (P Q : α → α → Prop)
    (h1 : ∀ x y z, P x y ∨ Q y z) (h2 : ∀ x, ¬P x a) (h3 : ∀ z, ¬Q a z) : False := by
  vampire [h1, h2, h3]

set_option vampire.outputPath "artifacts/portfolio-equality.p" in
theorem portfolio_equality {α : Type} (a b : α) (f : α → α) (P W : α → Prop)
    (h1 : ∀ x, f x = a ∨ W x) (h2 : ∀ x, ¬W x) (h3 : ¬P (f b)) (h4 : P a) : False := by
  vampire [h1, h2, h3, h4]

set_option vampire.outputPath "artifacts/portfolio-skolem.p" in
theorem portfolio_skolem {α : Type} (a : α) (P : α → α → Prop)
    (h1 : ∀ x, ∃ y, P x y) (h2 : ∀ y, ¬P a y) : False := by
  vampire [h1, h2]

#print axioms portfolio_resolution
#print axioms portfolio_splitting
#print axioms portfolio_equality
#print axioms portfolio_skolem

set_option vampire.outputPath "artifacts/portfolio-avatar.p" in
theorem portfolio_avatar (P Q : Prop)
    (h1 : P ∨ Q) (h2 : P ∨ ¬Q) (h3 : ¬P ∨ Q) (h4 : ¬P ∨ ¬Q) : False := by
  vampire [h1, h2, h3, h4]

#print axioms portfolio_avatar
