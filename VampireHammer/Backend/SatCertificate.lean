import Lean.Meta.Tactic.BVDecide.LRAT
import Std.Tactic.BVDecide.LRAT
import Std.Tactic.BVDecide.Reflect

/-! Checked reflection for AVATAR's original CNF, without Boolean bit-blasting.
The hint compiler is untrusted: `LRAT.check` independently checks its output. -/

namespace VampireHammer.SatCertificate

open Std.Sat Std.Tactic.BVDecide

abbrev Literal := Nat × Bool

structure RupStep where
  name : String
  literals : Array Literal
  parents : Array String

private def orderedHints (target : Array Literal)
    (parents : Array (Nat × Array Literal)) : Option (Array Nat) := Id.run do
  let mut assigned : Std.HashMap Nat Bool := {}
  for (atom, positive) in target do
    if let some previous := assigned.get? atom then
      if previous == positive then return none -- tautological target
    assigned := assigned.insert atom (!positive)
  let mut hints := #[]
  -- Every successful pass assigns at least one previously unassigned atom.
  let bound := parents.foldl (fun n parent => n + parent.2.size) 1
  for _ in [:bound] do
    let mut progress := false
    for (id, clause) in parents do
      let mut satisfied := false
      let mut unknown : Array Literal := #[]
      for (atom, positive) in clause do
        match assigned.get? atom with
        | some value => if value == positive then satisfied := true
        | none => if !unknown.contains (atom, positive) then
            unknown := unknown.push (atom, positive)
      if satisfied || unknown.size > 1 then continue
      hints := hints.push id
      if unknown.isEmpty then return some hints
      assigned := assigned.insert unknown[0]!.1 unknown[0]!.2
      progress := true
    unless progress do return none
  return none

/-- Generate LRAT RUP actions from possibly unordered named antecedents.
Variables are shifted by one to match `CNF.convertLRAT`. Initial clauses are
numbered from one, in exactly the supplied boundary order. -/
def compile (boundary : Array (String × Array Literal)) (trail : Array RupStep)
    (root : String) : Option (Array LRAT.IntAction) := Id.run do
  let mut known : Std.HashMap String (Nat × Array Literal) := {}
  for index in [:boundary.size] do
    let clause := boundary[index]!.2
    -- The standard CNF converter drops tautological initial clauses.
    -- Decline them rather than risk shifting subsequent clause identifiers.
    if clause.any (fun lit => clause.contains (lit.1, !lit.2)) then return none
    known := known.insert boundary[index]!.1 (index + 1, clause)
  let mut next := boundary.size + 1
  let mut actions := #[]
  for step in trail do
    let mut parents := #[]
    for name in step.parents do
      let some parent := known.get? name | return none
      parents := parents.push parent
    let some hints := orderedHints step.literals parents | return none
    if step.literals.isEmpty then
      if step.name != root then return none
      return some (actions.push (.addEmpty next hints))
    let ints := step.literals.map fun (atom, positive) =>
      let signedIndex := Int.ofNat (atom + 1)
      if positive then signedIndex else -signedIndex
    actions := actions.push (.addRup next ints hints)
    known := known.insert step.name (next, step.literals)
    next := next + 1
  return none

/-- A Boolean assignment stored as a balanced tree: index `0` is the root,
odd indices `2j+1` continue at `j` in the first child and even ones `2j+2` at
`j` in the second. The kernel reduces `get` in logarithmically many steps by
structural recursion on the tree, whereas a list lookup walks the whole
prefix for every literal. Absent positions are `false`. -/
inductive Assignment where
  | leaf
  | node (value : Bool) (odd even : Assignment)

def Assignment.get : Assignment → Nat → Bool
  | .leaf, _ => false
  | .node value odd even, index =>
    -- `cond` and `Nat.beq` reduce directly on literals in the kernel,
    -- without unfolding `Decidable` instances as an `if` would.
    cond (Nat.beq index 0) value
      (cond (Nat.beq (index % 2) 1) (odd.get (index / 2)) (even.get (index / 2 - 1)))

def clauseValue (assign : Nat → Bool) (clause : List Literal) : Bool :=
  clause.foldr (fun lit rest => cond lit.2 (assign lit.1) (!assign lit.1) || rest) false

theorem clauseValue_eq_eval (assign : Nat → Bool) (clause : List Literal) :
    clauseValue assign clause = CNF.Clause.eval assign clause := by
  induction clause with
  | nil => rfl
  | cons lit tail ih =>
    rcases lit with ⟨atom, positive⟩
    simp only [clauseValue, List.foldr_cons, CNF.Clause.eval_cons] at ih ⊢
    rw [ih]
    cases positive <;> cases assign atom <;> rfl

theorem satCons (assign : Nat → Bool) (clause : List Literal) (tail : List (List Literal))
    (head : clauseValue assign clause = true)
    (rest : tail.all (CNF.Clause.eval assign) = true) :
    (clause :: tail).all (CNF.Clause.eval assign) = true := by
  rw [List.all_cons, ← clauseValue_eq_eval, head, rest]
  rfl

theorem refute (clauses : List (List Literal)) (actions : Array LRAT.IntAction)
    (checked : LRAT.check actions ⟨clauses.toArray⟩ = true) (assign : Nat → Bool)
    (satisfied : clauses.all (CNF.Clause.eval assign) = true) : False := by
  have unsat := LRAT.check_sound actions ⟨clauses.toArray⟩ checked assign
  have sat : (CNF.mk clauses.toArray).eval assign = true := by
    simpa only [CNF.eval, List.all_toArray] using satisfied
  rw [sat] at unsat
  contradiction

/-- `refute` with the LRAT actions given as their textual serialization. The
native check then only embeds one string literal for the hints, which the
compiler handles far faster than the equivalent constructor terms; the
already-compiled standard parser decodes it. -/
theorem refuteCert (clauses : List (List Literal)) (certificate : String)
    (checked : Reflect.verifyCert ⟨clauses.toArray⟩ certificate = true) (assign : Nat → Bool)
    (satisfied : clauses.all (CNF.Clause.eval assign) = true) : False := by
  have unsat := Reflect.verifyCert_correct ⟨clauses.toArray⟩ certificate checked assign
  have sat : (CNF.mk clauses.toArray).eval assign = true := by
    simpa only [CNF.eval, List.all_toArray] using satisfied
  rw [sat] at unsat
  contradiction

end VampireHammer.SatCertificate
