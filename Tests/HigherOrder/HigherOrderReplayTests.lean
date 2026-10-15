import VampireHammer
import VampireHammer.THF

/-! End-to-end replay of the certificate-emitting Vampire build's real outputs
(`*.vampire.tstp`), plus synthetic suffixes (`*.mock.tstp`) for certificates
no real proof has exercised yet; see docs/VAMPIRE_HO_CERTIFICATES.md. Parsing, typed decoding, the local
proof DAG, scoped witnesses, and the completed Lean theorem are all exercised. -/
open Lean Meta Elab Tactic
open Auto.Embedding.Lam
open VampireHammer

set_option trace.vampire.replay true

private def lookupLocal (name : String) : MetaM Expr := do
  for declaration in ← getLCtx do
    if declaration.userName.toString == name then return declaration.toExpr
  throwError "missing local {name}"

private def replayFixture (file : String) (problem : TFF.Problem)
    (sorts symbols facts : Array Expr) : TacticM Unit := withMainContext do
  let .ok ast ← parseVampireTSTP "" file
    | throwError "fixture parser failed"
  let .ok decoded := Replay.decodeSteps problem ast
    | throwError "fixture decoder failed"
  let levels := ({} : Std.HashMap Nat Level).insert 0 (.succ .zero)
  let result ← Replay.Internal.buildLocalProof problem decoded {} levels
  let usedSorts ← result.sorts.mapM fun
    | .atom index => pure sorts[index]!
    | _ => throwError "unexpected sort"
  let usedSymbols ← result.symbols.mapM fun
    | .atom index => pure symbols[index]!
    | _ => throwError "unexpected symbol"
  let inhabitants ← result.inhabitantSorts.mapM fun
    | .atom index => do mkAppM ``Classical.choice #[← synthInstance (← mkAppM ``Nonempty #[sorts[index]!])]
    | _ => throwError "unexpected inhabitant"
  let proof := mkAppN result.proof
    (usedSorts ++ usedSymbols ++ inhabitants ++ result.factIndices.map (facts[·]!))
  unless ← isTypeCorrect proof do throwError "ill-typed replay theorem"
  (← getMainGoal).assign proof

private def lambdaProblem : TFF.Problem := Id.run do
  let i := LamSort.atom 0
  let fn := LamSort.func i i
  let prop := LamSort.base .prop
  let all := LamTerm.mkForallEF fn
    (.app i (.atom 2) (.app i (.bvar 0) (.atom 0)))
  let neg := LamTerm.mkNot (.app i (.atom 2) (.atom 1))
  return {
    higherOrder := true
    text := ""
    sorts := #[("i", i)]
    symbols := #[("a", .atom 0, i), ("b", .atom 1, i), ("p", .atom 2, .func i prop)]
    facts := #[("all", all), ("neg", neg)] }

theorem mocked_higher_order_superposition (i : Type) (a b : i) (p : i → Prop)
    (all : ∀ F : i → i, p (F a)) (neg : ¬p b) : False := by
  haveI : Nonempty i := ⟨a⟩
  run_tac do
    replayFixture "Tests/testdata/higher-order/lambda.vampire.tstp" lambdaProblem
      #[← lookupLocal "i"] #[← lookupLocal "a", ← lookupLocal "b", ← lookupLocal "p"]
      #[← lookupLocal "all", ← lookupLocal "neg"]

private def extProblem : TFF.Problem := Id.run do
  let i := LamSort.atom 0
  let fn := LamSort.func i i
  let pointwise := LamTerm.mkForallEF i
    (.mkEq i (.app i (.atom 0) (.bvar 0)) (.app i (.atom 1) (.bvar 0)))
  let neg := LamTerm.mkNot (.mkEq fn (.atom 0) (.atom 1))
  return {
    higherOrder := true
    text := ""
    sorts := #[("i", i)]
    symbols := #[("f", .atom 0, fn), ("g", .atom 1, fn)]
    facts := #[("pointwise", pointwise), ("neg", neg)] }

theorem mocked_negative_extensionality (i : Type) (f g : i → i)
    (pointwise : ∀ x, f x = g x) (neg : f ≠ g) : False := by
  -- The boundary needs a domain element only if a rule uses it. Here f≠g
  -- implies one exists; supplying an arbitrary element keeps the test simple.
  classical
  by_cases inhabited : Nonempty i
  · letI := inhabited
    run_tac do
      replayFixture "Tests/testdata/higher-order/ext.vampire.tstp" extProblem
        #[← lookupLocal "i"] #[← lookupLocal "f", ← lookupLocal "g"]
        #[← lookupLocal "pointwise", ← lookupLocal "neg"]
  · exact neg (funext fun x => False.elim (inhabited ⟨x⟩))

#print axioms mocked_higher_order_superposition
#print axioms mocked_negative_extensionality

private def extDependenciesProblem : TFF.Problem := Id.run do
  let i := LamSort.atom 0
  let fn := LamSort.func i i
  let fX := LamTerm.app i (.atom 0) (.bvar 0)
  let gX := LamTerm.app i (.atom 1) (.bvar 0)
  let pointwise := LamTerm.mkForallEF i (.mkForallEF i
    (.mkEq i (.app i (.app i (.atom 0) (.bvar 1)) (.bvar 0))
      (.app i (.app i (.atom 1) (.bvar 1)) (.bvar 0))))
  let neg := LamTerm.mkForallEF i (.mkNot (.mkEq fn fX gX))
  return {
    higherOrder := true
    text := ""
    sorts := #[("i", i)]
    symbols := #[("f", .atom 0, .func i fn), ("g", .atom 1, .func i fn)]
    facts := #[("pointwise", pointwise), ("neg", neg)] }

theorem mocked_extensionality_dependencies (i : Type) (a : i) (f g : i → i → i)
    (pointwise : ∀ x y, f x y = g x y) (neg : ∀ x, f x ≠ g x) : False := by
  haveI : Nonempty i := ⟨a⟩
  run_tac do
    replayFixture "Tests/testdata/higher-order/ext-dependencies.vampire.tstp" extDependenciesProblem
      #[← lookupLocal "i"] #[← lookupLocal "f", ← lookupLocal "g"]
      #[← lookupLocal "pointwise", ← lookupLocal "neg"]

private def rejectsFixture (file : String) (problem : TFF.Problem)
    (before after : String) : MetaM Unit := do
  let text ← IO.FS.readFile file
  unless text.contains before do throwError "mutation not present in fixture"
  let path := "artifacts/higher-order-invalid.tstp"
  IO.FS.writeFile path (text.replace before after)
  let .ok ast ← parseVampireTSTP "" path
    | throwError "mutation should remain syntactically valid"
  if let .error _ := Replay.decodeSteps problem ast then return
  let .ok decoded := Replay.decodeSteps problem ast | throwError "unexpected decoder result"
  let accepted ← withNewMCtxDepth do
    try
      discard <| Replay.Internal.buildLocalProof problem decoded {}
        (({} : Std.HashMap Nat Level).insert 0 (.succ .zero))
      pure true
    catch _ => pure false
  if accepted then throwError "accepted invalid higher-order certificate"

example : True := by
  run_tac do
    rejectsFixture "Tests/testdata/higher-order/ext.vampire.tstp" extProblem
      "extensionality_witness(literal(f4,0),sK0,[])"
      "extensionality_witness(literal(f4,1),sK0,[])"
    rejectsFixture "Tests/testdata/higher-order/ext-dependencies.vampire.tstp" extDependenciesProblem
      "sK0,[X0]" "sK0,[]"
    rejectsFixture "Tests/testdata/higher-order/lambda.vampire.tstp" lambdaProblem
      "^[Y0 : i]: (b)" "^[Y0 : $o]: (b)"
  trivial

#print axioms mocked_extensionality_dependencies

private def witnessSubsetProblem : TFF.Problem := Id.run do
  let i := LamSort.atom 0
  let fn := LamSort.func i i
  let ternary := LamSort.func i (.func i fn)
  let pointwise := LamTerm.mkForallEF i (.mkForallEF i (.mkForallEF i
    (.mkEq i (.app i (.app i (.app i (.atom 0) (.bvar 2)) (.bvar 1)) (.bvar 0))
      (.app i (.app i (.app i (.atom 1) (.bvar 2)) (.bvar 1)) (.bvar 0)))))
  let neg := LamTerm.mkForallEF i (.mkForallEF i (.mkForallEF i
    (.mkOr (.app i (.atom 2) (.bvar 0))
      (.mkNot (.mkEq fn (.app i (.app i (.atom 0) (.bvar 2)) (.bvar 1))
        (.app i (.app i (.atom 1) (.bvar 2)) (.bvar 1)))))))
  return {
    higherOrder := true
    text := ""
    sorts := #[("i", i)]
    symbols := #[("f", .atom 0, ternary), ("g", .atom 1, ternary),
      ("side", .atom 2, .func i (.base .prop))]
    facts := #[("pointwise", pointwise), ("neg", neg),
      ("neg_side", .mkForallEF i (.mkNot (.app i (.atom 2) (.bvar 0))))] }

theorem mocked_witness_dependency_subset (i : Type) (a : i) (f g : i → i → i → i)
    (side : i → Prop) (pointwise : ∀ x y t, f x y t = g x y t)
    (neg : ∀ x y z, side z ∨ f x y ≠ g x y) (neg_side : ∀ z, ¬side z) : False := by
  haveI : Nonempty i := ⟨a⟩
  run_tac do
    replayFixture "Tests/testdata/higher-order/witness-subset.vampire.tstp" witnessSubsetProblem
      #[← lookupLocal "i"] #[← lookupLocal "f", ← lookupLocal "g", ← lookupLocal "side"]
      #[← lookupLocal "pointwise", ← lookupLocal "neg", ← lookupLocal "neg_side"]

example : True := by
  run_tac do
    for invalid in #["[X0]", "[X1,X1]", "[X1,Missing]", "[X0,X1]"] do
      rejectsFixture "Tests/testdata/higher-order/witness-subset.vampire.tstp" witnessSubsetProblem
        "sK0,[X1,X0]" ("sK0," ++ invalid)
  trivial

#print axioms mocked_witness_dependency_subset

theorem mocked_witness_reordered_real_proof (i : Type) (a : i) (f g : i → i → i → i)
    (side : i → Prop) (pointwise : ∀ x y t, f x y t = g x y t)
    (neg : ∀ x y z, side z ∨ f x y ≠ g x y) (neg_side : ∀ z, ¬side z) : False := by
  haveI : Nonempty i := ⟨a⟩
  run_tac do
    replayFixture "Tests/testdata/higher-order/witness-reordered.mock.tstp" witnessSubsetProblem
      #[← lookupLocal "i"] #[← lookupLocal "f", ← lookupLocal "g", ← lookupLocal "side"]
      #[← lookupLocal "pointwise", ← lookupLocal "neg", ← lookupLocal "neg_side"]

#print axioms mocked_witness_reordered_real_proof

private def quantifierSubsetProblem : TFF.Problem := Id.run do
  let i := LamSort.atom 0
  let prop := LamSort.base .prop
  let applied (x y t : Nat) := LamTerm.app i
    (.app i (.app i (.atom 0) (.bvar x)) (.bvar y)) (.bvar t)
  let existential := LamTerm.mkExistEF i (applied 3 2 0)
  let ex := LamTerm.mkForallEF i (.mkForallEF i (.mkForallEF i
    (.mkOr (.app i (.atom 1) (.bvar 0)) (.mkEq prop existential (.base .trueE)))))
  return {
    higherOrder := true
    text := ""
    sorts := #[("i", i)]
    symbols := #[("p", .atom 0, .func i (.func i (.func i prop))),
      ("side", .atom 1, .func i prop)]
    facts := #[("ex", ex),
      ("neg", .mkForallEF i (.mkForallEF i (.mkForallEF i (.mkNot (applied 2 1 0))))),
      ("neg_side", .mkForallEF i (.mkNot (.app i (.atom 1) (.bvar 0))))] }

theorem mocked_quantifier_dependency_subset (i : Type) (a : i) (p : i → i → i → Prop)
    (side : i → Prop) (ex : ∀ x y z, side z ∨ ((∃ t, p x y t) = True))
    (neg : ∀ x y t, ¬p x y t) (neg_side : ∀ z, ¬side z) : False := by
  haveI : Nonempty i := ⟨a⟩
  run_tac do
    replayFixture "Tests/testdata/higher-order/quantifier-subset.vampire.tstp" quantifierSubsetProblem
      #[← lookupLocal "i"] #[← lookupLocal "p", ← lookupLocal "side"]
      #[← lookupLocal "ex", ← lookupLocal "neg", ← lookupLocal "neg_side"]

example : True := by
  run_tac do
    for invalid in #["[X3]", "[X3,X3]", "[X3,Missing]", "[X2,X3]"] do
      rejectsFixture "Tests/testdata/higher-order/quantifier-subset.vampire.tstp" quantifierSubsetProblem
        "sK0,[X3,X2]" ("sK0," ++ invalid)
  trivial

#print axioms mocked_quantifier_dependency_subset

theorem mocked_quantifier_reordered_real_proof (i : Type) (a : i) (p : i → i → i → Prop)
    (side : i → Prop) (ex : ∀ x y z, side z ∨ ((∃ t, p x y t) = True))
    (neg : ∀ x y t, ¬p x y t) (neg_side : ∀ z, ¬side z) : False := by
  haveI : Nonempty i := ⟨a⟩
  run_tac do
    replayFixture "Tests/testdata/higher-order/quantifier-reordered.mock.tstp" quantifierSubsetProblem
      #[← lookupLocal "i"] #[← lookupLocal "p", ← lookupLocal "side"]
      #[← lookupLocal "ex", ← lookupLocal "neg", ← lookupLocal "neg_side"]

#print axioms mocked_quantifier_reordered_real_proof

theorem mocked_witness_renamed_scope (i : Type) (a : i) (f g : i → i → i → i)
    (side : i → Prop) (pointwise : ∀ x y t, f x y t = g x y t)
    (neg : ∀ x y z, side z ∨ f x y ≠ g x y) (neg_side : ∀ z, ¬side z) : False := by
  haveI : Nonempty i := ⟨a⟩
  run_tac do
    replayFixture "Tests/testdata/higher-order/witness-renamed.mock.tstp" witnessSubsetProblem
      #[← lookupLocal "i"] #[← lookupLocal "f", ← lookupLocal "g", ← lookupLocal "side"]
      #[← lookupLocal "pointwise", ← lookupLocal "neg", ← lookupLocal "neg_side"]

theorem mocked_quantifier_renamed_scope (i : Type) (a : i) (p : i → i → i → Prop)
    (side : i → Prop) (ex : ∀ x y z, side z ∨ ((∃ t, p x y t) = True))
    (neg : ∀ x y t, ¬p x y t) (neg_side : ∀ z, ¬side z) : False := by
  haveI : Nonempty i := ⟨a⟩
  run_tac do
    replayFixture "Tests/testdata/higher-order/quantifier-renamed.mock.tstp" quantifierSubsetProblem
      #[← lookupLocal "i"] #[← lookupLocal "p", ← lookupLocal "side"]
      #[← lookupLocal "ex", ← lookupLocal "neg", ← lookupLocal "neg_side"]

example : True := by
  run_tac do
    for (file, problem) in #[
        ("Tests/testdata/higher-order/witness-renamed.mock.tstp", witnessSubsetProblem),
        ("Tests/testdata/higher-order/quantifier-renamed.mock.tstp", quantifierSubsetProblem)] do
      for invalid in #["[b(X0,A),b(X1,B)]", "[b(X0,A),b(X1,B),b(X2,B)]",
          "[b(X0,A),b(X0,B),b(X2,C)]", "[b(X0,A),b(X1,B),b(X2,Missing)]",
          "[b(Missing,A),b(X1,B),b(X2,C)]", "[b(X0,lowercase),b(X1,B),b(X2,C)]",
          "[b(X0,B),b(X1,A),b(X2,C)]"] do
        rejectsFixture file problem "[b(X0,A),b(X1,B),b(X2,C)]" invalid
      rejectsFixture file problem ",binder_mapping([b(X0,A),b(X1,B),b(X2,C)])" ""
      rejectsFixture file problem ",binder_mapping([b(X0,A),b(X1,B),b(X2,C)])"
        ",binder_mapping([b(X0,A),b(X1,B),b(X2,C)]),binder_mapping([])"
  trivial

#print axioms mocked_witness_renamed_scope
#print axioms mocked_quantifier_renamed_scope

private def lambdaRewriteProblem : TFF.Problem := Id.run do
  let i := LamSort.atom 0
  let fn := LamSort.func i i
  let prop := LamSort.base .prop
  let body (index : Nat) := LamTerm.lam i
    (.app i (.atom 0) (.app i (.atom index) (.bvar 0)))
  let pos := LamTerm.app fn (.atom 3) (body 1)
  let neg := LamTerm.mkNot (.app fn (.atom 3) (body 2))
  return {
    higherOrder := true
    text := ""
    sorts := #[("i", i)]
    symbols := #[("f", .atom 0, fn), ("g", .atom 1, fn),
      ("h", .atom 2, fn), ("q", .atom 3, .func fn prop)]
    facts := #[("eq", .mkEq fn (.atom 1) (.atom 2)), ("pos", pos), ("neg", neg)] }

theorem mocked_rewriting_under_lambda (i : Type) (a : i) (f g h : i → i)
    (q : (i → i) → Prop) (eq : g = h)
    (pos : q (fun x => f (g x))) (neg : ¬q (fun x => f (h x))) : False := by
  haveI : Nonempty i := ⟨a⟩
  run_tac do
    replayFixture "Tests/testdata/higher-order/lambda-rewrite.vampire.tstp" lambdaRewriteProblem
      #[← lookupLocal "i"]
      #[← lookupLocal "f", ← lookupLocal "g", ← lookupLocal "h", ← lookupLocal "q"]
      #[← lookupLocal "eq", ← lookupLocal "pos", ← lookupLocal "neg"]

example : True := by
  run_tac do
    rejectsFixture "Tests/testdata/higher-order/lambda-rewrite.vampire.tstp" lambdaRewriteProblem
      "($true = ((q @ (^[Y0 : i]: (f @ (h @ Y0)))))))"
      "($true = ((q @ (^[Y0 : i]: (f @ (f @ Y0)))))))"
  trivial

#print axioms mocked_rewriting_under_lambda

theorem mocked_residual_function_constraint (i : Type) (a : i) (f g h : i → i)
    (q : (i → i) → Prop) (eq : g = h)
    (pos : q (fun x => f (g x))) (neg : ¬q (fun x => f (h x))) : False := by
  haveI : Nonempty i := ⟨a⟩
  run_tac do
    replayFixture "Tests/testdata/higher-order/lambda-constraint.mock.tstp" lambdaRewriteProblem
      #[← lookupLocal "i"]
      #[← lookupLocal "f", ← lookupLocal "g", ← lookupLocal "h", ← lookupLocal "q"]
      #[← lookupLocal "eq", ← lookupLocal "pos", ← lookupLocal "neg"]

#print axioms mocked_residual_function_constraint

theorem mocked_lambda_instantiation (i : Type) (a b : i) (p : i → Prop)
    (all : ∀ F : i → i, p (F a)) (neg : ¬p b) : False := by
  haveI : Nonempty i := ⟨a⟩
  run_tac do
    replayFixture "Tests/testdata/higher-order/lambda-instantiation.mock.tstp" lambdaProblem
      #[← lookupLocal "i"] #[← lookupLocal "a", ← lookupLocal "b", ← lookupLocal "p"]
      #[← lookupLocal "all", ← lookupLocal "neg"]

#print axioms mocked_lambda_instantiation

private def booleanProblem : TFF.Problem := Id.run do
  let prop := LamSort.base .prop
  let fn := LamSort.func prop prop
  let identity := LamTerm.lam prop (.bvar 0)
  let pos := LamTerm.app fn (.atom 0) (.lam prop (.mkAnd (.bvar 0) (.base .trueE)))
  let neg := LamTerm.mkNot (.app fn (.atom 0) identity)
  return {
    higherOrder := true
    text := ""
    sorts := #[]
    symbols := #[("r", .atom 0, .func fn prop)]
    facts := #[("pos", pos), ("neg", neg)] }

theorem replayed_boolean_simplification (r : (Prop → Prop) → Prop)
    (pos : r (fun B => B ∧ True)) (neg : ¬r (fun B => B)) : False := by
  run_tac do
    replayFixture "Tests/testdata/higher-order/boolean.vampire.tstp" booleanProblem
      #[] #[← lookupLocal "r"] #[← lookupLocal "pos", ← lookupLocal "neg"]

#print axioms replayed_boolean_simplification

private def booleanClauseProblem : TFF.Problem := Id.run do
  let prop := LamSort.base .prop
  let fn := LamSort.func prop prop
  let identity := LamTerm.lam prop (.bvar 0)
  let p := LamTerm.app fn (.atom 0) identity
  let q := LamTerm.app fn (.atom 1) identity
  let a := LamTerm.atom 2
  return {
    higherOrder := true
    text := ""
    sorts := #[]
    symbols := #[("p", .atom 0, .func fn prop), ("q", .atom 1, .func fn prop), ("a", .atom 2, prop)]
    facts := #[("pos", .mkOr a (.mkEq prop (.mkAnd p q) (.base .trueE))),
      ("neg_a", .mkNot a), ("neg_p", .mkNot p)] }

theorem replayed_boolean_clausification (p q : (Prop → Prop) → Prop) (a : Prop)
    (pos : a ∨ ((p id ∧ q id) = True)) (neg_a : ¬a) (neg_p : ¬p id) : False := by
  run_tac do
    replayFixture "Tests/testdata/higher-order/boolean-clause.vampire.tstp" booleanClauseProblem
      #[] #[← lookupLocal "p", ← lookupLocal "q", ← lookupLocal "a"]
      #[← lookupLocal "pos", ← lookupLocal "neg_a", ← lookupLocal "neg_p"]

#print axioms replayed_boolean_clausification

theorem mocked_boolean_cases (p q : (Prop → Prop) → Prop) (a : Prop)
    (pos : a ∨ ((p id ∧ q id) = True)) (neg_a : ¬a) (neg_p : ¬p id) : False := by
  run_tac do
    replayFixture "Tests/testdata/higher-order/boolean-cases.mock.tstp" booleanClauseProblem
      #[] #[← lookupLocal "p", ← lookupLocal "q", ← lookupLocal "a"]
      #[← lookupLocal "pos", ← lookupLocal "neg_a", ← lookupLocal "neg_p"]

#print axioms mocked_boolean_cases

theorem mocked_boolean_projection (p q : (Prop → Prop) → Prop) (a : Prop)
    (pos : a ∨ ((p id ∧ q id) = True)) (neg_a : ¬a) (neg_p : ¬p id) : False := by
  run_tac do
    replayFixture "Tests/testdata/higher-order/boolean-projection.vampire.tstp" booleanClauseProblem
      #[] #[← lookupLocal "p", ← lookupLocal "q", ← lookupLocal "a"]
      #[← lookupLocal "pos", ← lookupLocal "neg_a", ← lookupLocal "neg_p"]

#print axioms mocked_boolean_projection

private def flexFlexProblem : TFF.Problem := Id.run do
  let i := LamSort.atom 0
  let fn := LamSort.func i i
  let disequality := LamTerm.mkNot (.mkEq i
    (.app i (.bvar 1) (.atom 0)) (.app i (.bvar 0) (.atom 1)))
  return {
    higherOrder := true
    text := ""
    sorts := #[("i", i)]
    symbols := #[("a", .atom 0, i), ("b", .atom 1, i)]
    facts := #[("all", .mkForallEF fn (.mkForallEF fn disequality))] }

theorem mocked_flex_flex (i : Type) (a b : i)
    (all : ∀ F G : i → i, F a ≠ G b) : False := by
  haveI : Nonempty i := ⟨a⟩
  run_tac do
    replayFixture "Tests/testdata/higher-order/flex-flex.vampire.tstp" flexFlexProblem
      #[← lookupLocal "i"] #[← lookupLocal "a", ← lookupLocal "b"] #[← lookupLocal "all"]

#print axioms mocked_flex_flex

private def quantifiedProblem : TFF.Problem := Id.run do
  let i := LamSort.atom 0
  let fn := LamSort.func i i
  let prop := LamSort.base .prop
  let applied := LamTerm.app fn (.atom 1) (.bvar 0)
  return {
    higherOrder := true
    text := ""
    sorts := #[("i", i)]
    symbols := #[("a", .atom 0, i), ("p", .atom 1, .func fn prop)]
    facts := #[("ex", .mkEq prop (.mkExistEF fn applied) (.base .trueE)),
      ("neg", .mkForallEF fn (.mkNot applied))] }

theorem mocked_quantified_proxies (i : Type) (a : i) (p : (i → i) → Prop)
    (ex : (∃ F, p F) = True) (neg : ∀ F, ¬p F) : False := by
  haveI : Nonempty i := ⟨a⟩
  run_tac do
    replayFixture "Tests/testdata/higher-order/quantified.vampire.tstp" quantifiedProblem
      #[← lookupLocal "i"] #[← lookupLocal "a", ← lookupLocal "p"]
      #[← lookupLocal "ex", ← lookupLocal "neg"]

#print axioms mocked_quantified_proxies

private def quantifiedDependenciesProblem : TFF.Problem := Id.run do
  let i := LamSort.atom 0
  let fn := LamSort.func i i
  let prop := LamSort.base .prop
  let p := LamTerm.app fn (.app i (.atom 1) (.bvar 1)) (.bvar 0)
  let existential := LamTerm.mkExistEF fn p
  let side := LamTerm.app i (.atom 2) (.bvar 0)
  return {
    higherOrder := true
    text := ""
    sorts := #[("i", i)]
    symbols := #[("a", .atom 0, i), ("p", .atom 1, .func i (.func fn prop)),
      ("side", .atom 2, .func i prop)]
    facts := #[("ex", .mkForallEF i (.mkOr side (.mkEq prop existential (.base .trueE)))),
      ("neg", .mkForallEF i (.mkForallEF fn (.mkNot p))),
      ("neg_side", .mkForallEF i (.mkNot side))] }

theorem mocked_quantifier_dependencies (i : Type) (a : i) (p : i → (i → i) → Prop)
    (side : i → Prop) (ex : ∀ x, side x ∨ ((∃ F, p x F) = True))
    (neg : ∀ x F, ¬p x F) (neg_side : ∀ x, ¬side x) : False := by
  haveI : Nonempty i := ⟨a⟩
  run_tac do
    replayFixture "Tests/testdata/higher-order/quantified-dependencies.vampire.tstp" quantifiedDependenciesProblem
      #[← lookupLocal "i"] #[← lookupLocal "a", ← lookupLocal "p", ← lookupLocal "side"]
      #[← lookupLocal "ex", ← lookupLocal "neg", ← lookupLocal "neg_side"]

example : True := by
  run_tac do
    rejectsFixture "Tests/testdata/higher-order/quantified.vampire.tstp" quantifiedProblem
      "quantifier_witness(literal(f11,0),sK0,[])" "quantifier_witness(literal(f11,1),sK0,[])"
    rejectsFixture "Tests/testdata/higher-order/quantified-dependencies.vampire.tstp" quantifiedDependenciesProblem
      "sK0,[X1]" "sK0,[]"
  trivial

#print axioms mocked_quantifier_dependencies

/- Synthetic suffixes of the real proof above. `witness-reuse` reuses `sK0`
with the term dependency `a`, as Vampire prints a witness taken from its
Skolem index; `witness-term` introduces `sK0` with that term dependency.
`heuristic-instantiation` instantiates universal proxies with
`quantifier_instance`. Their conclusions stay valid under a wrong certificate,
so only the introduction is checked for rejection here. -/
theorem witness_reuse_term_dependency (i : Type) (a : i) (p : i → (i → i) → Prop)
    (side : i → Prop) (ex : ∀ x, side x ∨ ((∃ f, p x f) = True))
    (neg : ∀ x f, ¬p x f) (neg_side : ∀ x, ¬side x) : False := by
  haveI : Nonempty i := ⟨a⟩
  run_tac do
    replayFixture "Tests/testdata/higher-order/witness-reuse.mock.tstp" quantifiedDependenciesProblem
      #[← lookupLocal "i"] #[← lookupLocal "a", ← lookupLocal "p", ← lookupLocal "side"]
      #[← lookupLocal "ex", ← lookupLocal "neg", ← lookupLocal "neg_side"]

theorem witness_introduced_term_dependency (i : Type) (a : i) (p : i → (i → i) → Prop)
    (side : i → Prop) (ex : ∀ x, side x ∨ ((∃ f, p x f) = True))
    (neg : ∀ x f, ¬p x f) (neg_side : ∀ x, ¬side x) : False := by
  haveI : Nonempty i := ⟨a⟩
  run_tac do
    replayFixture "Tests/testdata/higher-order/witness-term.mock.tstp" quantifiedDependenciesProblem
      #[← lookupLocal "i"] #[← lookupLocal "a", ← lookupLocal "p", ← lookupLocal "side"]
      #[← lookupLocal "ex", ← lookupLocal "neg", ← lookupLocal "neg_side"]

theorem heuristic_quantifier_instance (i : Type) (a : i) (p : i → (i → i) → Prop)
    (side : i → Prop) (ex : ∀ x, side x ∨ ((∃ f, p x f) = True))
    (neg : ∀ x f, ¬p x f) (neg_side : ∀ x, ¬side x) : False := by
  haveI : Nonempty i := ⟨a⟩
  run_tac do
    replayFixture "Tests/testdata/higher-order/heuristic-instantiation.mock.tstp" quantifiedDependenciesProblem
      #[← lookupLocal "i"] #[← lookupLocal "a", ← lookupLocal "p", ← lookupLocal "side"]
      #[← lookupLocal "ex", ← lookupLocal "neg", ← lookupLocal "neg_side"]

example : True := by
  run_tac do
    rejectsFixture "Tests/testdata/higher-order/witness-term.mock.tstp" quantifiedDependenciesProblem
      "sK0,[$thf(a)]" "sK0,[]"
  trivial

#print axioms witness_reuse_term_dependency
#print axioms witness_introduced_term_dependency
#print axioms heuristic_quantifier_instance

private def leibnizProblem : TFF.Problem := Id.run do
  let i := LamSort.atom 0
  let pred := LamSort.func i (.base .prop)
  let pos := LamTerm.app i (.bvar 0) (.atom 0)
  let neg := LamTerm.mkNot (.app i (.bvar 0) (.atom 1))
  return {
    higherOrder := true
    text := ""
    sorts := #[("i", i)]
    symbols := #[("a", .atom 0, i), ("b", .atom 1, i)]
    facts := #[("all", .mkForallEF pred (.mkOr pos neg)),
      ("neg", .mkNot (.mkEq i (.atom 0) (.atom 1)))] }

theorem mocked_leibniz_elimination (i : Type) (a b : i)
    (all : ∀ P : i → Prop, P a ∨ ¬P b) (neg : a ≠ b) : False := by
  haveI : Nonempty i := ⟨a⟩
  run_tac do
    replayFixture "Tests/testdata/higher-order/leibniz.vampire.tstp" leibnizProblem
      #[← lookupLocal "i"] #[← lookupLocal "a", ← lookupLocal "b"]
      #[← lookupLocal "all", ← lookupLocal "neg"]

#print axioms mocked_leibniz_elimination

theorem mocked_hilbert_choice (i : Type) (a : i) (p : (i → i) → Prop)
    (ex : (∃ F, p F) = True) (neg : ∀ F, ¬p F) : False := by
  haveI : Nonempty i := ⟨a⟩
  run_tac do
    replayFixture "Tests/testdata/higher-order/choice.mock.tstp" quantifiedProblem
      #[← lookupLocal "i"] #[← lookupLocal "a", ← lookupLocal "p"]
      #[← lookupLocal "ex", ← lookupLocal "neg"]

#print axioms mocked_hilbert_choice

theorem mocked_functional_extensionality_axiom (i : Type) (a : i) (f g : i → i)
    (pointwise : ∀ x, f x = g x) (neg : f ≠ g) : False := by
  haveI : Nonempty i := ⟨a⟩
  run_tac do
    replayFixture "Tests/testdata/higher-order/extensionality-axiom.mock.tstp" extProblem
      #[← lookupLocal "i"] #[← lookupLocal "f", ← lookupLocal "g"]
      #[← lookupLocal "pointwise", ← lookupLocal "neg"]

#print axioms mocked_functional_extensionality_axiom

private def occurrenceProblem : TFF.Problem := Id.run do
  let i := LamSort.atom 0
  let fn := LamSort.func i i
  let prop := LamSort.base .prop
  let eta (index : Nat) := LamTerm.lam i (.app i (.atom index) (.bvar 0))
  let application (index : Nat) := LamTerm.app fn (.app fn (.atom 2) (eta index)) (eta index)
  return {
    higherOrder := true
    text := ""
    sorts := #[("i", i)]
    symbols := #[("g", .atom 0, fn), ("h", .atom 1, fn), ("q", .atom 2, .func fn (.func fn prop))]
    facts := #[("eq", .mkEq fn (.atom 0) (.atom 1)),
      ("pos", application 0), ("neg", .mkNot (application 1))] }

theorem mocked_single_occurrence_rewriting (i : Type) (a : i) (g h : i → i)
    (q : (i → i) → (i → i) → Prop) (eq : g = h)
    (pos : q (fun x => g x) (fun x => g x)) (neg : ¬q (fun x => h x) (fun x => h x)) : False := by
  haveI : Nonempty i := ⟨a⟩
  run_tac do
    replayFixture "Tests/testdata/higher-order/occurrence.vampire.tstp" occurrenceProblem
      #[← lookupLocal "i"] #[← lookupLocal "g", ← lookupLocal "h", ← lookupLocal "q"]
      #[← lookupLocal "eq", ← lookupLocal "pos", ← lookupLocal "neg"]

#print axioms mocked_single_occurrence_rewriting

example : True := by
  run_tac do
    rejectsFixture "Tests/testdata/higher-order/choice.mock.tstp" quantifiedProblem
      "c:(((i > i) > $o) > (i > i))" "c:(((i > i) > $o) > i)"
    rejectsFixture "Tests/testdata/higher-order/choice.mock.tstp" quantifiedProblem
      "(p @ F) = $false | (p @ (c @ p)) = $true"
      "(p @ F) = $true | (p @ (c @ p)) = $false"
    rejectsFixture "Tests/testdata/higher-order/extensionality-axiom.mock.tstp" extProblem
      "(F = G)" "(F != G)"
  trivial
