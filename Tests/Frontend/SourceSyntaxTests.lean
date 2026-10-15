import VampireHammer

open Lean Meta Elab Tactic

private def checkNormalization (source expected : Expr) : MetaM Unit := do
  let normalized ← VampireHammer.SourceNormalization.normalizeSyntax source
  if (normalized.find? fun expression => expression.isProj || expression.isLet).isSome then
    throwError "primitive projection or let survived: {normalized}"
  unless ← isDefEq normalized expected do
    throwError "normalization changed the meaning: {normalized}"
  let proof ← mkEqRefl source
  let originalType ← inferType proof
  let normalizedType ← VampireHammer.SourceNormalization.normalizeSyntax originalType
  -- Check the unchanged proof against its normalized type in the kernel.
  let identity := mkApp2 (mkConst ``id [.zero]) normalizedType proof
  unless ← Auto.Meta.isTypeCorrectCore identity do
    throwError "the kernel rejected the normalized fact"
  -- Saturation can reintroduce this syntax through substitutions, after the
  -- frontend has normalized its original inputs. Exercise lean-auto's own
  -- traversal boundary on the raw type as well.
  Auto.Monomorphization.monomorphize
    #[⟨⟨proof, originalType, .leaf "raw syntax regression"⟩, #[]⟩] #[] fun state => do
      if state.facts.isEmpty then throwError "monomorphization discarded the source fact"

elab "check_primitive_source " pair:term : tactic => withMainContext do
  let pair ← Term.elabTerm pair none
  let pair ← instantiateMVars pair
  let raw := Expr.proj ``Prod 0 pair
  let expected ← mkAppM ``Prod.fst #[pair]
  checkNormalization raw expected
  let value := Expr.letE `pair (← inferType pair) pair
    (.proj ``Prod 0 (.bvar 0)) false
  checkNormalization value expected
  let function := Expr.letE `projector (← inferType (← mkLambdaFVars #[] expected))
    expected (.bvar 0) false
  checkNormalization function expected
  let annotated := mkMData {} (mkMData {} raw)
  let normalized ← VampireHammer.SourceNormalization.normalizeSyntax annotated
  if (normalized.find? (·.isMData)).isSome then
    throwError "nested metadata survived normalization"
  checkNormalization annotated expected
  -- Projection parameters must be inferred in the bound variable's context.
  let quantified ← forallTelescope (← inferType (← mkConstWithFreshMVarLevels ``Prod.fst))
    fun xs _ => do
      let pairVariable := xs.back!
      mkForallFVars xs (← mkEq (.proj ``Prod 0 pairVariable) (.proj ``Prod 0 pairVariable))
  let normalized ← VampireHammer.SourceNormalization.normalizeSyntax quantified
  if (normalized.find? fun expression => expression.isProj || expression.isLet).isSome then
    throwError "projection survived under a binder"

example (pair : Nat × Nat) : True := by
  check_primitive_source pair
  trivial

set_option vampire.executable "Tests/testdata/scripts/local-vampire.sh"

private def atFirst (predicate : Nat → Prop) (pair : Nat × Nat) : Prop :=
  let function := fun value => predicate value
  function pair.1

-- Unfolding a higher-order head introduces a let and a projection. The
-- resulting proof must still travel through Vampire and kernel replay.
set_option vampire.outputPath "artifacts/source-syntax.p" in
theorem source_syntax_replay (predicate : Nat → Prop) (pair : Nat × Nat)
    (hypothesis : predicate pair.1) : atFirst predicate pair := by
  vampire [hypothesis]

#print axioms source_syntax_replay
