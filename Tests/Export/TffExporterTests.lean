import VampireHammer

open Auto.Embedding.Lam VampireHammer

private def assertContains (text expected : String) : IO Unit := do
  unless (text.splitOn expected).length > 1 do
    throw <| IO.userError s!"Missing {expected} in:\n{text}"

private def expectError (result : Except String TFF.Problem) (message : String) : IO Unit := do
  match result with
  | .ok _ => throw <| IO.userError s!"Expected rejection: {message}"
  | .error actual => assertContains actual message

/- Exercise binding, typing and fragment boundaries independently of auto's
preprocessing (which can otherwise simplify these cases away). -/
#eval show IO Unit from do
  let a := LamSort.atom 0
  let b := LamSort.atom 1
  let prop := LamSort.base .prop
  let rTy := LamSort.func a (.func b prop)
  let rxy := LamTerm.app b (.app a (.atom 0) (.bvar 1)) (.bvar 0)
  let fact := LamTerm.mkForallEF a (LamTerm.mkExistEF b rxy)
  let result ← IO.ofExcept <| TFF.exportProblem #[rTy] #[] #[a, b] #[fact]
  assertContains result.text "t_a0: ((s_a0 * s_a1) > $o)"
  assertContains result.text "(! [X0: s_a0] : (? [X1: s_a1] : t_a0(X0, X1)))"
  unless result.facts == #[("fact0", fact)] && result.symbols.size == 1 do
    throw <| IO.userError "Source IDs were not preserved"

  -- Eta expansion under an existing binder must shift the captured variable.
  let eta := LamTerm.mkForallEF a
    (LamTerm.mkExistE b (.app a (.atom 0) (.bvar 0)))
  let etaResult ← IO.ofExcept <| TFF.exportProblem #[rTy] #[] #[a, b] #[eta]
  assertContains etaResult.text "t_a0(X0, X1)"

  let eq := LamTerm.mkEq a (.atom 0) (.etom 0)
  let equality ← IO.ofExcept <| TFF.exportProblem #[a] #[a] #[a] #[eq]
  assertContains equality.text "(t_a0 = t_e0)"
  assertContains equality.text "t_e0: s_a0"

  let iff := LamTerm.mkEq prop (.atom 0) (.atom 1)
  let equivalence ← IO.ofExcept <| TFF.exportProblem #[prop, prop] #[] #[] #[iff]
  assertContains equivalence.text "(t_a0 <=> t_a1)"

  -- Natural numbers deliberately use an ordinary TF0 sort and ordinary
  -- function symbols.  The exporter adds no arithmetic theory of its own;
  -- algebraic laws come only from the `Std` law instances collected for the
  -- source operations.
  let nat := LamSort.base .nat
  let natAdd (left right : LamTerm) :=
    LamTerm.app nat (LamTerm.app nat (.base .nadd) left) right
  let natFact := LamTerm.mkEq nat (natAdd (.bvar 0) (.base (.natVal 1)))
    (natAdd (.base (.natVal 1)) (.bvar 0))
  let natural ← IO.ofExcept <| TFF.exportProblem #[] #[] #[]
    #[LamTerm.mkForallEF nat natFact]
  assertContains natural.text "tff(type_s_nat, type, s_nat: $tType)."
  assertContains natural.text "nat_add: ((s_nat * s_nat) > s_nat)"
  assertContains natural.text "nat_1: s_nat"

  expectError (TFF.exportProblem #[rTy] #[] #[a] #[fact]) "no known inhabitation"
  expectError (TFF.exportProblem #[.func (.func a a) prop] #[] #[a] #[.atom 0])
    "unsupported domain"
  expectError (TFF.exportProblem #[rTy] #[] #[a, b] #[.atom 0]) "fully applied"
  expectError (TFF.exportProblem #[] #[] #[] #[LamTerm.mkForallEF prop (.bvar 0)])
    "unsupported domain"
  expectError (TFF.exportProblem #[a, b] #[] #[a, b]
    #[LamTerm.mkEq a (.atom 0) (.atom 1)]) "result type mismatch"
  expectError (TFF.exportProblem #[] #[] #[a]
    #[LamTerm.mkEq a (.bvar 0) (.bvar 0)]) "unbound variable"
  expectError (TFF.exportProblem #[] #[] #[a]
    #[LamTerm.mkForallEF (.func a a) (.base (.pcst .trueE))]) "unsupported domain"
  -- Errors the object encoding can avoid are marked for its retry; ordinary
  -- malformed input is not.
  expectError (TFF.exportProblem #[rTy] #[] #[a] #[fact]) TFF.objectEncodingSuffix
  expectError (TFF.exportProblem #[] #[] #[a]
    #[LamTerm.mkForallEF (.func a a) (.base (.pcst .trueE))]) TFF.objectEncodingSuffix
  match TFF.exportProblem #[a, b] #[] #[a, b] #[LamTerm.mkEq a (.atom 0) (.atom 1)] with
  | .error message =>
    if (message.splitOn TFF.objectEncodingSuffix).length > 1 then
      throw <| IO.userError s!"type error marked for the object encoding: {message}"
  | .ok _ => throw <| IO.userError "type error was accepted"
  IO.println "TF0 exporter checks passed"

-- Two inhabited sorts, a function crossing sorts, and equality.
set_option vampire.outputPath "artifacts/multisort.p" in
example {α β : Type} [Nonempty β] (a a' : α) (f : α → β) (P : β → Prop)
    (h : f a = f a') (hp : P (f a)) : P (f a') := by
  vampire_export [h, hp]
  exact h ▸ hp

-- Shadowed variables and quantifiers survive the end-to-end pipeline.
set_option vampire.outputPath "artifacts/quantifiers.p" in
example {α β : Type} [Nonempty α] [Nonempty β] (R : α → β → Prop)
    (h : ∀ x, ∃ y, R x y) : ∀ x, ∃ y, R x y := by
  vampire_export [h]
  exact h

-- An export failure must restore the original goal, just like successful export.
set_option vampire.mockScript "Tests/scripts/does-not-exist.sh" in
example (p : Prop) (h : p) : p := by
  fail_if_success vampire_export [h]
  exact h
