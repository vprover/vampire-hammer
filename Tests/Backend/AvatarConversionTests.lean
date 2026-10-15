import VampireHammer

open Lean Meta Elab Tactic VampireHammer.Backend VampireHammer.Backend.Internal
open VampireHammer.Clause

syntax "replay_avatar_map " str " using " "[" term,* "]" : tactic
elab_rules : tactic
  | `(tactic| replay_avatar_map $variant:str using [$terms:term,*]) => withMainContext do
    let goal ← getMainGoal
    let target ← goal.getType
    let some targetView ← resolutionClauseView (mkConst ``True.intro) target
      | throwError "expected clause target"
    let parents ← terms.getElems.zipIdx |>.mapM fun (term, i) => do
      let proof ← Term.elabTerm term none
      let type ← inferType proof
      let view? ← resolutionClauseView proof type
      let rawTarget := if i > 0 then
        (view?.bind fun view => view.regular[0]?).getD type else type
      pure ({
        parent := { name := s!"p{i}" }, binders := #[], existentialVariables := #[],
        componentBinders := #[], target := rawTarget, clauseForm := view?.isSome,
        clauseLiterals? := view?.map (·.regular), cnfCandidates := pure none,
        proof := proof } : ParentProof)
    let mut symbols : Std.HashMap String Expr := {}
    for decl in ← getLCtx do
      if decl.userName.toString.startsWith "spl" then
        symbols := symbols.insert decl.userName.toString decl.toExpr
    let mapping (index : Nat) (sign symbol definition : String) : MetadataTerm :=
      .application "map" #[.application "literal" #[.atom "p0", .number (toString index)],
        .application sign #[.atom symbol], .atom definition]
    let mut entries := #[mapping 0 "negative" "splA" "p1",
      mapping 1 "positive" "splB" "p2", mapping 2 "negative" "splA" "p1"]
    match variant.getString with
    | "polarity" => entries := entries.set! 0 (mapping 0 "positive" "splA" "p1")
    | "definition" => entries := entries.set! 0 (mapping 0 "negative" "splA" "p2")
    | "missing-parent" => entries := entries.set! 0 (mapping 0 "negative" "splA" "absent")
    | "duplicate-index" => entries := entries.set! 2 (mapping 0 "negative" "splA" "p1")
    | "out-of-range" => entries := entries.set! 2 (mapping 3 "negative" "splA" "p1")
    | "missing-index" => entries := entries.extract 0 2
    | _ => pure ()
    let mut info := #[MetadataTerm.application "avatar_map" #[.list entries.reverse]]
    if variant.getString == "malformed" then
      info := #[.application "avatar_map" #[.atom "bad"]]
    if variant.getString == "duplicate-annotation" then info := info ++ info
    let inference : Inference := {
      rule := "sat_conversion", info := info, parents := parents.map (·.parent) }
    let input : RuleInput := {
      step := {
        name := "conversion", formula := .base .falseE, binders := #[],
        parents := parents.map (·.parent), sourceFact? := none,
        inference? := some inference, clauseLiterals? := some #[] },
      target := target, clauseLiterals? := some targetView.regular, parents := parents,
      sourceProof? := none, sourceFVars := #[], symbols := symbols }
    let some (handler, proof) ← dispatch input inference | throwError "conversion rejected"
    unless handler == "AVATAR conversion" do throwError "wrong handler"
    unless ← isTypeCorrect proof do throwError "ill-typed conversion"
    unless ← isDefEq (← inferType proof) target do throwError "wrong target"
    goal.assign proof

-- Occurrence order differs from both SAT and annotation order; a duplicate
-- source occurrence is removed. Definition orientation and storage may differ.
example (P Q splA splB : Prop) (h : Holds [¬P, Q, ¬P])
    (da : Holds [splA ↔ P]) (db : Q ↔ splB) : Holds [splB, ¬splA] := by
  replay_avatar_map "valid" using [h, da, db]

example {α : Type} (a b : α) (Q splA splB : Prop)
    (h : Holds [b ≠ a, Q, b ≠ a])
    (da : Holds [splA ↔ a = b]) (db : splB ↔ Q) : Holds [splB, ¬splA] := by
  replay_avatar_map "valid" using [h, da, db]

-- Each failure has an ambient proof of the desired conclusion. The handler
-- must still reject bad certificates rather than use ambient facts.
example (P Q splA splB : Prop) (h : Holds [¬P, Q, ¬P])
    (da : Holds [splA ↔ P]) (db : Holds [splB ↔ Q])
    (valid : Holds [splB, ¬splA]) : Holds [splB, ¬splA] := by
  fail_if_success replay_avatar_map "polarity" using [h, da, db]
  fail_if_success replay_avatar_map "definition" using [h, da, db]
  fail_if_success replay_avatar_map "missing-parent" using [h, da, db]
  fail_if_success replay_avatar_map "duplicate-index" using [h, da, db]
  fail_if_success replay_avatar_map "out-of-range" using [h, da, db]
  fail_if_success replay_avatar_map "missing-index" using [h, da, db]
  fail_if_success replay_avatar_map "malformed" using [h, da, db]
  fail_if_success replay_avatar_map "duplicate-annotation" using [h, da, db]
  fail_if_success replay_avatar_map "valid" using [h, da]
  fail_if_success replay_avatar_map "valid" using [h, da, db, da]
  exact valid

example (P Q splA splB : Prop) (h : Holds [¬P, Q, ¬P])
    (da : Holds [splA ↔ P]) (db : Holds [splB ↔ Q])
    (valid : Holds [splB]) : Holds [splB] := by
  fail_if_success replay_avatar_map "valid" using [h, da, db]
  exact valid

example (P Q splA splB splC : Prop) (h : Holds [¬P, Q, ¬P])
    (da : Holds [splA ↔ P]) (db : Holds [splB ↔ Q])
    (valid : Holds [splB, ¬splA, splC]) : Holds [splB, ¬splA, splC] := by
  fail_if_success replay_avatar_map "valid" using [h, da, db]
  exact valid
