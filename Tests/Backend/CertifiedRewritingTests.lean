import VampireHammer.Backend.CertifiedRewriting
import VampireHammer.Backend.Metadata

open Lean Meta Elab Tactic VampireHammer.Backend VampireHammer.Backend.Internal
open VampireHammer.Clause

syntax "replay_rewrite " str " using " "[" term,* "]" " equality " num
  " at " "[" num,* "]" " from " "(" term ")" " to " "(" term ")" " guards " "[" term,* "]"
  (" occurrence " num)? : tactic

private def runRewrite (rule : TSyntax `str) (parentTerms : Array (TSyntax `term))
    (eq : TSyntax `num) (positions : Array (TSyntax `num)) (lhs rhs : TSyntax `term)
    (guardTerms : Array (TSyntax `term)) (occurrence? : Option Nat) : TacticM Unit :=
    withMainContext do
      let goal ← getMainGoal
      let target ← goal.getType
      let some targetView ← resolutionClauseView (.mvar goal) target
        | throwError "expected clause goal"
      let parents ← parentTerms.zipIdx |>.mapM fun (term, index) => do
        let proof ← Term.elabTerm term none
        let type ← inferType proof
        let some view ← resolutionClauseView proof type | throwError "expected clause parent"
        pure ({
          parent := { name := s!"p{index}" }, binders := #[],
          existentialVariables := #[], componentBinders := #[], target := type,
          clauseForm := true, clauseLiterals? := some (view.regular ++ view.avatar),
          cnfCandidates := pure none, proof } : ParentProof)
      let lhs ← Term.elabTerm lhs none
      let rhs ← Term.elabTerm rhs none
      let mut symbols := ({} : Std.HashMap String Expr).insert "rw_from" lhs |>.insert "rw_to" rhs
      for declaration in ← getLCtx do
        if declaration.userName.toString.startsWith "spl" then
          symbols := symbols.insert declaration.userName.toString declaration.toExpr
      let mut constraintMetadata := #[]
      for (term, i) in guardTerms.zipIdx do
        let diseq ← Term.elabTerm term (some (mkSort levelZero))
        let some equation ← notArgument? diseq | throwError "expected disequality"
        let some (_, left, right) := equation.eq? | throwError "expected disequality"
        symbols := symbols.insert s!"cL{i}" left |>.insert s!"cR{i}" right
        constraintMetadata := constraintMetadata.push (.application "disequality"
          #[.atom "sort", .atom s!"cL{i}", .atom s!"cR{i}"])
      let substitutions := parents.map fun parent =>
        ({ parent := parent.parent.name, bindings := #[] } : ParentSubstitution)
      let literals := positions.map fun position =>
        ({ parent := "p0", index := position.getNat } : LiteralRef)
      let eqParent := if rule.getString == "inner_rewriting" then "p0" else "p1"
      let info : CertifiedRewriteInfo := {
        substitutions, rewrittenLiterals := literals,
        «equality» := { parent := eqParent, index := eq.getNat },
        fromTerm := .atom "rw_from", toTerm := .atom "rw_to", constraints := constraintMetadata,
        occurrence? }
      let input : RuleInput := {
        step := {
          name := "test", formula := .base .falseE, binders := #[],
          parents := parents.map (·.parent), sourceFact? := none,
          inference? := some { rule := rule.getString, parents := parents.map (·.parent), info := #[] },
          clauseLiterals? := some #[] }, target,
        clauseLiterals? := some (targetView.regular ++ targetView.avatar), parents,
        sourceProof? := none, sourceFVars := #[], symbols }
      let some proof ← certifiedRewriting input info | throwError "rewrite certificate declined"
      unless ← isTypeCorrect proof do throwError "ill-typed rewrite proof"
      unless ← isDefEq (← inferType proof) target do throwError "wrong rewrite result"
      goal.assign proof

elab_rules : tactic
  | `(tactic| replay_rewrite $rule:str using [$parentTerms:term,*] equality $eq:num
      at [$positions:num,*] from ($lhs:term) to ($rhs:term) guards [$guardTerms:term,*]) =>
    runRewrite rule parentTerms.getElems eq positions.getElems lhs rhs guardTerms.getElems none
  | `(tactic| replay_rewrite $rule:str using [$parentTerms:term,*] equality $eq:num
      at [$positions:num,*] from ($lhs:term) to ($rhs:term) guards [$guardTerms:term,*] occurrence $selected:num) =>
    runRewrite rule parentTerms.getElems eq positions.getElems lhs rhs guardTerms.getElems (some selected.getNat)

example {α : Type} (a b : α) (f : α → α) (P Q : α → Prop)
    (main : Holds [P (f a), Q (f a)]) (side : Holds [f a = b]) : Holds [P b, Q (f a)] := by
  replay_rewrite "backward_demodulation" using [main, side] equality 0 at [0] from (f a) to (b) guards []

example {α : Type} (a b : α) (f : α → α) (P Q : α → Prop)
    (main : Holds [P (f a), Q (f a)]) (side : Holds [f a = b]) : Holds [P b, Q b] := by
  fail_if_success replay_rewrite "backward_demodulation" using [main, side] equality 0 at [0] from (f a) to (b) guards []
  replay_rewrite "constrained_superposition" using [main, side] equality 0 at [0] from (f a) to (b) guards []

example {α : Type} (a b : α) (f : α → α) (P : α → Prop) (R : Prop)
    (main : Holds [P (f a), R]) (side : Holds [R, b = f a]) : Holds [P b, R] := by
  replay_rewrite "forward_subsumption_demodulation" using [main, side] equality 1 at [0] from (f a) to (b) guards []

example {α : Type} (a b : α) (f : α → α) (P : α → Prop) (R : Prop)
    (main : Holds [P (f a)]) (side : Holds [R, f a = b]) : Holds [P b, R] := by
  fail_if_success replay_rewrite "forward_subsumption_demodulation" using [main, side] equality 1 at [0] from (f a) to (b) guards []
  replay_rewrite "constrained_superposition" using [main, side] equality 1 at [0] from (f a) to (b) guards []

example {α : Type} (a b : α) (f : α → α) (P Q : α → Prop)
    (main : Holds [b ≠ f a, P (f a), Q (f a)]) : Holds [b ≠ f a, P b, Q b] := by
  replay_rewrite "inner_rewriting" using [main] equality 0 at [1, 2] from (f a) to (b) guards []

example {α : Type} (a b : α) (f : α → α) (P Q : α → Prop)
    (main : Holds [f a ≠ b, P (f a), Q (f a)]) : Holds [f a ≠ b, P (f a), Q b] := by
  replay_rewrite "inner_rewriting" using [main] equality 0 at [2] from (f a) to (b) guards []

example {α : Type} (a b c : α) (f : α → α) (P : α → Prop) (R : Prop)
    (main : Holds [P (f a)]) (side : Holds [R, b = c]) : Holds [P c, R, f a ≠ b] := by
  fail_if_success replay_rewrite "constrained_superposition" using [main, side] equality 1 at [0] from (f a) to (c) guards []
  replay_rewrite "constrained_superposition" using [main, side] equality 1 at [0] from (f a) to (c) guards [f a ≠ b]

example {α : Type} (a b c : α) (f : α → α) (P : α → Prop)
    (main : Holds [P (f (f a))]) (side : Holds [f b = f c]) : Holds [P (f c), b ≠ f a] := by
  replay_rewrite "constrained_superposition" using [main, side] equality 0 at [0] from (f (f a)) to (f c) guards [b ≠ f a]

example {α : Type} (a b : α) (f : α → α) (P : α → Prop) (splA splB : Prop)
    (main : AClause.Holds [P (f a)] [splA]) (side : AClause.Holds [f a = b] [splB]) :
    AClause.Holds [P b] [splA, splB] := by
  replay_rewrite "backward_demodulation" using [main, side] equality 0 at [0] from (f a) to (b) guards []

-- The rewritten literal leads the natural superposition conclusion. Check
-- both simultaneous superposition and the setting that rewrites only it.
example {α : Type} (a b : α) (f : α → α) (P Q : α → Prop)
    (main : Holds [Q (f a), P (f a)]) (side : Holds [f a = b]) : Holds [P b, Q b] := by
  replay_rewrite "constrained_superposition" using [main, side] equality 0 at [1] from (f a) to (b) guards []

example {α : Type} (a b : α) (f : α → α) (P Q : α → Prop)
    (main : Holds [Q (f a), P (f a)]) (side : Holds [f a = b]) : Holds [P b, Q (f a)] := by
  replay_rewrite "constrained_superposition" using [main, side] equality 0 at [1] from (f a) to (b) guards []

example {α : Type} (a b c : α) (f : α → α) (P : α → Prop) (splA splB : Prop)
    (main : AClause.Holds [P (f a)] [splA]) (side : AClause.Holds [b = c] [splB]) :
    AClause.Holds [P c, f a ≠ b] [splA, splB] := by
  replay_rewrite "constrained_superposition" using [main, side] equality 0 at [0] from (f a) to (c) guards [f a ≠ b]

example {α : Type} (a b : α) (f : α → α) (P : α → Prop) (splA : Prop)
    (main : AClause.Holds [f a ≠ b, P (f a)] [splA]) : AClause.Holds [f a ≠ b, P b] [splA] := by
  replay_rewrite "inner_rewriting" using [main] equality 0 at [1] from (f a) to (b) guards []

#eval show IO Unit from do
  let cert : Inference := {
    rule := "inner_rewriting", parents := #[{ name := "p0" }],
    info := #[.application "unifier" #[.list #[.application "subs" #[.atom "p0", .list #[]]]],
      .application "rewritten_literals" #[.list #[
        .application "literal" #[.atom "p0", .number "1"],
        .application "literal" #[.atom "p0", .number "2"]]],
      .application "rewrite" #[.list #[
        .application "equality" #[.application "literal" #[.atom "p0", .number "0"]],
        .application "from" #[.atom "a"], .application "to" #[.atom "b"]]]] }
  let some decoded := cert.certifiedRewrite?
    | throw <| IO.userError "failed to decode plural rewritten positions"
  unless decoded.rewrittenLiterals.size == 2 && decoded.equality.index == 0 do
    throw <| IO.userError "incorrect selected occurrences"
  unless ({ cert with info := cert.info.pop }).certifiedRewrite?.isNone do
    throw <| IO.userError "accepted a certificate without its rewrite direction"
  let rewriteFields := #[
    MetadataTerm.application "equality" #[.application "literal" #[.atom "p0", .number "0"]],
    .application "from" #[.atom "a"], .application "to" #[.atom "b"]]
  let withOccurrences := fun fields => { cert with
    info := cert.info.pop.push (.application "rewrite" #[.list (rewriteFields ++ fields)]) }
  let selected := withOccurrences #[.application "occurrence" #[.number "0"]]
  unless selected.certifiedRewrite?.any (·.occurrence? == some 0) do
    throw <| IO.userError "failed to decode zero-based occurrence"
  for fields in #[
      #[.application "occurrence" #[.number "-1"]],
      #[.application "occurrence" #[.atom "zero"]],
      #[.atom "occurrence"],
      #[.application "occurrence" #[.number "0"],
        .application "occurrence" #[.number "1"]]] do
    unless (withOccurrences fields).certifiedRewrite?.isNone do
      throw <| IO.userError "accepted malformed occurrence metadata"
  let booleanCase := fun fields => ({
    rule := "cases_simplifying"
    parents := #[{ name := "p0" }]
    info := #[.application "boolean_case" (#[
      .application "literal" #[.atom "p0", .number "0"], .atom "p", .atom "true"] ++ fields)]
    } : Inference)
  unless (booleanCase #[]).booleanCase?.any (·.occurrence?.isNone) do
    throw <| IO.userError "failed to decode legacy Boolean case"
  unless (booleanCase #[.application "occurrence" #[.number "1"]]).booleanCase?.any
      (·.occurrence? == some 1) do
    throw <| IO.userError "failed to decode Boolean occurrence selector"
  for fields in #[#[.application "occurrence" #[.number "-1"]],
      #[.application "occurrence" #[.atom "first"]],
      #[.application "occurrence" #[.number "0"], .application "occurrence" #[.number "1"]]] do
    unless (booleanCase fields).booleanCase?.isNone do
      throw <| IO.userError "accepted malformed Boolean occurrence metadata"

-- Backward subsumption demodulation shares the certified non-unit side rule.
example {α : Type} (a b : α) (f : α → α) (P : α → Prop) (R : Prop)
    (main : Holds [P (f a), R]) (side : Holds [R, b = f a]) : Holds [P b, R] := by
  replay_rewrite "backward_subsumption_demodulation" using [main, side] equality 1 at [0] from (f a) to (b) guards []

example {α : Type} (a b : α) (f : α → α) (P : α → Prop) (R : Prop)
    (main : Holds [P (f a)]) (side : Holds [R, f a = b]) (valid : Holds [P b]) : Holds [P b] := by
  fail_if_success replay_rewrite "backward_subsumption_demodulation" using [main, side] equality 1 at [0] from (f a) to (b) guards []
  exact valid

example {α : Type} (a b : α) (f : α → α) (P : α → Prop) (R splA splB : Prop)
    (main : AClause.Holds [P (f a), R] [splA])
    (side : AClause.Holds [f a = b, R] [splB]) : AClause.Holds [P b, R] [splA, splB] := by
  replay_rewrite "backward_subsumption_demodulation" using [main, side] equality 0 at [0] from (f a) to (b) guards []

-- A single matching occurrence changes, even when the literal repeats it.
theorem certified_single_occurrence {α : Type} (a b : α) (P : α → α → Prop)
    (main : Holds [P a a]) (side : Holds [a = b]) : Holds [P b a] := by
  replay_rewrite "backward_demodulation" using [main, side] equality 0 at [0]
    from (a) to (b) guards [] occurrence 0

theorem certified_second_occurrence {α : Type} (a b : α) (P : α → α → Prop)
    (main : Holds [P a a]) (side : Holds [a = b]) : Holds [P a b] := by
  fail_if_success replay_rewrite "backward_demodulation" using [main, side] equality 0 at [0]
    from (a) to (b) guards [] occurrence 0
  replay_rewrite "backward_demodulation" using [main, side] equality 0 at [0]
    from (a) to (b) guards [] occurrence 1

example {α : Type} (a b : α) (P : α → α → Prop)
    (main : Holds [P a a]) (side : Holds [a = b]) (valid : Holds [P b b]) : Holds [P b b] := by
  fail_if_success replay_rewrite "backward_demodulation" using [main, side] equality 0 at [0]
    from (a) to (b) guards [] occurrence 0
  fail_if_success replay_rewrite "backward_demodulation" using [main, side] equality 0 at [0]
    from (a) to (b) guards [] occurrence 2
  exact valid

theorem certified_occurrence_under_lambda (f g : Nat → Nat) (P : (Nat → Nat) → Prop)
    (main : Holds [P (fun x => f (f x))]) (side : Holds [f = g]) :
    Holds [P (fun x => f (g x))] := by
  replay_rewrite "definition_unfolding" using [main, side] equality 0 at [0]
    from (f) to (g) guards [] occurrence 1

theorem certified_alpha_renamed_rewrite (f g : Nat → Nat) (P : (Nat → Nat) → Prop)
    (main : Holds [P (fun printedBinder => f printedBinder)]) (side : Holds [f = g]) :
    Holds [P g] := by
  replay_rewrite "definition_unfolding" using [main, side] equality 0 at [0]
    from (fun certificateBinder => f certificateBinder) to (g) guards [] occurrence 0

theorem certified_occurrence_with_constraints {α : Type} (a b c : α) (P : α → α → Prop)
    (main : Holds [P a a]) (side : Holds [b = c]) : Holds [P a c, a ≠ b] := by
  replay_rewrite "constrained_superposition" using [main, side] equality 0 at [0]
    from (a) to (c) guards [a ≠ b] occurrence 1

#print axioms certified_occurrence_under_lambda
#print axioms certified_single_occurrence
