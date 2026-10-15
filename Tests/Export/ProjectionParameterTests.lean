import VampireHammer.SourceNormalization

open Lean Meta Elab Tactic

/-! Primitive projections already carry their structure's exact parameters,
including class instances that need not be available to instance search. -/

private structure StoredOperation (α : Type u) [Mul α] where
  value : α

private structure StoredDependent (α : Type u) [Mul α] (family : α → Type v) where
  value : α
  dependent : family value

private structure StoredZero (α : Type u) [Zero α] where
  value : α
  property : value = 0

private def checkProjection (name : Name) (index : Nat) (value : Expr) : MetaM Unit := do
  let source := Expr.proj name index value
  let normalized ← VampireHammer.SourceNormalization.normalizeSyntax source
  if (normalized.find? (·.isProj)).isSome then
    throwError "primitive projection survived normalization"
  unless ← isDefEq source normalized do
    throwError "projection normalization changed its meaning"
  let proof ← mkEqRefl source
  let type ← VampireHammer.SourceNormalization.normalizeSyntax (← inferType proof)
  let checked ← instantiateMVars (mkApp2 (mkConst ``id [.zero]) type proof)
  match Kernel.check (← getEnv) (← getLCtx) checked with
  | .ok _ => pure ()
  | .error _ => throwError "kernel rejected the normalized projection"

elab "check_stored_projection " value:term : tactic => withMainContext do
  let value ← Term.elabTerm value none
  let type ← whnf (← inferType value)
  let name := type.getAppFn.constName!
  checkProjection name 0 value
  if name == ``StoredDependent then checkProjection name 1 value
  if name == ``StoredZero then checkProjection name 1 value
  -- Recover parameters in the context of a quantified structure variable too.
  let quantified ← withLocalDeclD `record type fun record => do
    mkForallFVars #[record] (← mkEq (.proj name 0 record) (.proj name 0 record))
  let normalized ← VampireHammer.SourceNormalization.normalizeSyntax quantified
  if (normalized.find? (·.isProj)).isSome then
    throwError "primitive projection survived under a binder"
  unless ← isDefEq quantified normalized do
    throwError "quantified projection changed its meaning"

-- op is an ordinary parameter, deliberately unavailable to instance search.
example (α : Type u) (op : Mul α) (record : @StoredOperation α op) : True := by
  check_stored_projection record
  trivial

example (α : Type u) (op : Mul α) (family : α → Type v)
    (record : @StoredDependent α op family) : True := by
  check_stored_projection record
  trivial

-- Instance search must not replace the instance stored in a dependent type
-- with a different instance that happens to be available in the context.
example (α : Type u) (first second : Zero α) (record : @StoredZero α first) : True := by
  letI : Zero α := second
  check_stored_projection record
  trivial
