import VampireHammer

set_option vampire.executable "Tests/testdata/scripts/local-vampire.sh"

structure TransferRecord (P Q : Nat → Prop) where
  operation : Nat → Nat
  transfer : ∀ n, P n → Q (operation n)

structure ExtendedTransferRecord (P Q R : Nat → Prop) extends TransferRecord P Q where
  next : ∀ n, Q n → R n

-- Both laws are taken from this value, including its inherited transfer field.
set_option vampire.outputPath "artifacts/ordinary-record-laws.p" in
theorem ordinary_record_laws (P Q R : Nat → Prop)
    (record : ExtendedTransferRecord P Q R) (n : Nat) (p : P n) :
    R (record.operation n) := by
  vampire [p]

structure PropositionRecord (P : Prop) : Prop where
  evidence : P

-- Ordinary proof hypotheses respect explicit premise selection. Classes in
-- Prop retain their separate existing class-law behavior.
example (P : Prop) (record : PropositionRecord P) : True := by
  fail_if_success have : P := by vampire []
  trivial

-- Operation fields and proposition values are data, not proofs of those values.
structure PredicateRecord where
  predicate : Prop

example (record : PredicateRecord) : True := by
  fail_if_success have : record.predicate := by vampire []
  trivial

private opaque acceptsDependentRecord : ((n : Nat) → Fin (n + 1)) → Prop := fun _ => True

structure UnsupportedRecord : Type where
  law : acceptsDependentRecord (fun n => ⟨0, Nat.zero_lt_succ n⟩)

-- The new provenance remains optional; an unsupported record field must not
-- discard the usable record laws or prevent an unrelated first-order proof.
set_option vampire.outputPath "artifacts/optional-record-law.p" in
theorem optional_record_law (P Q : Nat → Prop) (unsupported : UnsupportedRecord)
    (record : TransferRecord P Q) (n : Nat) (p : P n) : Q (record.operation n) := by
  vampire [p]

-- An explicit hint outside the translatable fragment is omitted rather than
-- failing the call; the remaining facts still give a checked proof.
set_option vampire.directProof false in
example (unsupported : UnsupportedRecord) (P : Prop) (p : P) (np : ¬P) : False := by
  vampire [p, np, unsupported.law]

#print axioms ordinary_record_laws
#print axioms optional_record_law
