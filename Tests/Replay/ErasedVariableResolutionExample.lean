import VampireHammer

set_option vampire.executable "Tests/testdata/scripts/mock-erased-variable-resolution.sh"
set_option vampire.outputPath "artifacts/erased-variable-resolution.p"
set_option trace.vampire.replay true

/-- Resolution deletes the only literals containing `X0`; the child has no
`X0` binder and the certificate prints two empty identity substitutions.  The
backend must nevertheless instantiate both parent `∀ X0`s at one shared value
before applying the clause-resolution theorem. -/
theorem erasedVariableResolution {α : Type} [Nonempty α] (P : α → Prop) (Q : Prop)
    (hPositive : ∀ x, P x ∨ Q) (hNegative : ∀ x, ¬ P x) : Q := by
  vampire [hPositive, hNegative]

#print axioms erasedVariableResolution
