import VampireHammer

set_option vampire.executable "Tests/testdata/scripts/local-vampire.sh"
set_option vampire.disableAvatar true
set_option vampire.outputPath "artifacts/binary-resolution.p"
set_option trace.vampire.replay true

/-- With AVATAR disabled, Vampire resolves the two quantified input clauses
to the reordered three-literal clause `C ∨ D x ∨ B x`.  It removes `C` by
forward subsumption, instantiates the remaining clause at `a`, and the backend
directly reconstructs both ordinary resolution steps. -/

theorem binaryResolutionExample {α : Type} (a : α) (A B D : α → Prop) (C : Prop)
   (h₁ : ∀ x, A x ∨ B x ∨ C) (h₂ : ∀ x, ¬ A x ∨ C ∨ D x ∨ ∀ y, D y) (h₃: ¬ C): B a ∨ D a:= by
  vampire [h₁, h₂, h₃]


#print binaryResolutionExample
