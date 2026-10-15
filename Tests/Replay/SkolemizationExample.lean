import VampireHammer

set_option vampire.executable "Tests/testdata/scripts/local-vampire.sh"
set_option vampire.disableAvatar true
set_option vampire.outputPath "artifacts/skolem-constant.p"
set_option trace.vampire.replay true

/-!
This example exercises lean-auto's smallest Skolemization before export:

* `hExists` supplies `∃ y, P y`;
* lean-auto introduces an existential atom of sort `α` and proves its
  Skolemized instance in the verified preprocessing checker;
* Vampire treats that atom as an ordinary constant in its TF0 problem;
* replay abstracts the atom from the completed local refutation and asks the
  checker to instantiate it with lean-auto's recorded Skolem term.

The arbitrary goal `R` prevents the refutation wrapper itself from supplying
an easier contradiction.  The two hypotheses are inconsistent only after the
existential witness has been selected.  The otherwise unused `a : α` supplies
the nonempty-domain evidence required when exporting the TFF sort.
-/
theorem simpleSkolemizationExample {α : Type} (_a : α) (P : α → Prop)
    (R : Prop) (hExists : ∃ y, P y) (hNegative : ∀ y, ¬ P y) : R := by
  vampire [hExists, hNegative]

#print simpleSkolemizationExample

/-!
The second theorem covers one preceding universal binder. Lean-auto's
existential atom therefore has sort `α → α`, corresponding to the function
`fun x => Classical.choose (hExists x)`. Mentioning `a` in the negative
premise gives resolution a concrete value at which to instantiate the
Skolemized universal formula. The printed proof term includes the verified
checker steps that connect this etom to the original existential premise.
-/
set_option vampire.outputPath "artifacts/skolem-function.p"

theorem unarySkolemFunctionExample {α : Type} (a : α) (P : α → α → Prop)
    (R : Prop) (hExists : ∀ x, ∃ y, P x y)
    (hNegative : ∀ y, ¬ P a y) : R := by
  vampire [hExists, hNegative]

#print unarySkolemFunctionExample
