import VampireHammer

/-!
End-to-end tests for preprocessing nodes handled by `Backend_Preprocessing`.
The mock programs make these tests deterministic while still exercising the
normal parser, decoder, local proof DAG, and Lam2DAAF boundary.
-/

set_option vampire.executable "Tests/testdata/scripts/mock-vamplean-preprocessing.sh"
set_option vampire.outputPath "artifacts/vamplean-preprocessing.p"
set_option trace.vampire.replay true

/-- All three premises are used by the mock refutation. In sequence it removes
the first premise's double negation with `flattening`, removes `False` from
the second, converts the third premise to NNF, moves all three results through
`cnfify`, and resolves the resulting clauses. -/
theorem vampleanLogicalPreprocessing (A B R : Prop)
    (hFlatten : ¬¬A) (hRemove : B ∨ False)
    (hNnf : ¬ (A ∧ B)) : R := by
  vampire [hFlatten, hRemove, hNnf]

#print axioms vampleanLogicalPreprocessing

set_option vampire.executable "Tests/testdata/scripts/mock-vamplean-cnf-nonempty.sh"
set_option vampire.outputPath "artifacts/vamplean-cnf-nonempty.p"

/-- This CNF split uses VampLean's `cnf_prenex1`, whose reverse implication
needs a `Nonempty α` instance.  Replay builds that instance from lean-auto's
exported inhabitant `a` and discharges the witness through the verified
Lam2DAAF checker. -/
theorem vampleanCnfUsesExportedInhabitant {α : Type} (a : α)
    (P : α → Prop) (Q : Prop) (h : ∀ x, P x ∧ Q) : Q := by
  vampire [h]

#print axioms vampleanCnfUsesExportedInhabitant
