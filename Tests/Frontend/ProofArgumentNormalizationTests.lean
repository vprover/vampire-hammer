import VampireHammer

open Lean Meta Elab Tactic

private def proofWrapper (n : Nat) (_ : n = n) : Nat := n
private opaque opaqueWrapper (n : Nat) (_ : n = n) : Nat

elab "check_proof_normalization" : tactic => withMainContext do
  let source ← Term.elabType (← `(∀ n (h : n = n), proofWrapper n h = n))
  let expected ← Term.elabType (← `(∀ n (_ : n = n), n = n))
  let normalized ← VampireHammer.SourceNormalization.normalizeProofArguments source
  let prepared ← VampireHammer.SourceNormalization.prepareForMonomorphization
    #[⟨⟨← mkFreshExprMVar source, source, .leaf "final boundary"⟩, #[]⟩]
  if (prepared[0]!.type.find? (·.isConstOf ``proofWrapper)).isSome then
    throwError "final monomorphization boundary retained a proof wrapper"
  unless ← isDefEq normalized expected do throwError "proof wrapper was not reduced"
  if (normalized.find? (·.isConstOf ``proofWrapper)).isSome then
    throwError "bound proof wrapper survived"
  let reflexive ← Term.elabType (← `(∀ (α : Type) (h : α = α) (a : α), cast h a = a))
  let reduced ← VampireHammer.SourceNormalization.normalizeProofArguments reflexive
  if (reduced.find? (·.isConstOf ``cast)).isSome then throwError "reflexive cast survived"
  let genuine ← Term.elabType (← `(∀ (α β : Type) (h : α = β) (a : α), cast h a = cast h a))
  let retained ← VampireHammer.SourceNormalization.normalizeProofArguments genuine
  unless ← isDefEq retained genuine do throwError "genuine transport changed meaning"
  forallTelescope retained fun variables body => do
    unless body.containsFVar variables[2]!.fvarId! do
      throwError "genuine transport lost its equality proof"
  let opaqueType ← Term.elabType (← `(∀ n (h : n = n), opaqueWrapper n h = n))
  let retained ← VampireHammer.SourceNormalization.normalizeProofArguments opaqueType
  unless (retained.find? (·.isConstOf ``opaqueWrapper)).isSome do throwError "opaque proof argument erased"
  let proof ← Term.elabTerm (← `(fun n (h : n = n) => (rfl : proofWrapper n h = n))) (some source)
  let proof ← instantiateMVars proof
  let checked := mkApp2 (mkConst ``id [.zero]) normalized proof
  unless ← Auto.Meta.isTypeCorrectCore checked do throwError "normalized fact rejected by kernel"

example : True := by
  check_proof_normalization
  trivial

set_option vampire.attributeLemmas false
set_option vampire.outputPath "artifacts/proof-argument-normalization.p" in
theorem proof_argument_resolution (P : Nat → Prop) (n : Nat)
    (h : ∀ n (p : n = n), P (proofWrapper n p)) : P n := by
  vampire [h]

#print axioms proof_argument_resolution
