import VampireHammer.Replay.Term
import Auto.Tactic

/-!
Translate decoded LamTerms into the local Lean signature and retain both formula and clause
views of replayed nodes.
-/

namespace VampireHammer.Replay.Internal

open Lean Meta Elab Tactic
open Auto.Embedding.Lam
open VampireHammer.Backend

/-- Lean expressions translated from one decoded proof step. `formula` keeps
the original TPTP connective shape for preprocessing and `grind`; the optional
literal array is the independent post-CNF clause view. -/
structure TranslatedStep where
  formula : Expr
  clauseLiterals? : Option (Array Expr)

structure StepProof where
  /-- Original parsed information, retained for a child's binder metadata. -/
  step : Step
  /-- The original TPTP formula, retained for the CNF conversion and for a
  fallback rule that temporarily leaves clause representation. -/
  target : Expr
  /-- Whether this node has entered the clause-form part of the proof. -/
  clauseForm : Bool
  /-- Clause literals in the original leading-binder context, if this is a
  post-CNF node. Keeping them with the proof lets a later fallback recover the
  raw `Or` formula without losing the decoded clause ordering. -/
  clauseLiterals? : Option (Array Expr)
  /-- The proof expression keyed by `step.name` in the replay DAG. -/
  proof : Expr

/-- Interpret a `LamTerm` using the readable type and term variables of the
local reconstruction signature. This is lean-auto's ordinary Lam-to-Expr
interpreter with a valuation owned by this module; it does not enter
`Lam2DAAF` or refer to the original Lean problem. -/
def translateLocal (typeAtoms termAtoms etoms : Std.HashMap Nat Expr)
    (term : LamTerm) : MetaM Expr :=
  Auto.Lam2D.interpLamTermAsUnlifted typeAtoms termAtoms etoms 0 term

/-- Translate both decoder views of a step while its variables are still
lean-auto `LamTerm` variables. The clause literals deliberately retain their
de Bruijn variables; `Backend` replaces them with the fresh local binders
opened for the current inference before it creates `Holds [Prop]`. -/
def translateStep (typeAtoms termAtoms etoms : Std.HashMap Nat Expr)
    (step : Step) : MetaM TranslatedStep := do
  let formula ← translateLocal typeAtoms termAtoms etoms step.formula
  let clauseLiterals? ← match step.clauseLiterals? with
    | none => pure none
    | some literals => some <$> literals.mapM (translateLocal typeAtoms termAtoms etoms)
  pure ⟨formula, clauseLiterals?⟩

end VampireHammer.Replay.Internal
