import VampireHammer.Replay.Steps

/-!
Introduce the isolated first-order signature and source facts, then close the refutation over
only the boundary parameters it uses.
-/

namespace VampireHammer.Replay.Internal

open Lean Meta Elab Tactic
open Auto.Embedding.Lam
open Tptp.Data
open VampireHammer.Backend

/-- Introduce local type variables for the genuinely uninterpreted TF0 sorts.

`Nat` and `Int` are exported with TF0 sort names so that Vampire can use them,
but they are not parameters of the readable local theorem: lean-auto already
gives their base sorts the concrete Lean interpretations `Nat` and `Int`.
Keeping that distinction here is what lets the finite first-order arithmetic
theory use closed theorems such as `Nat.zero_add`. -/
private partial def withLocalSorts (sorts : Array (String × LamSort))
    (propositionAtoms : Std.HashSet Nat) (sortLevels : Std.HashMap Nat Level) (index : Nat)
    (typeAtoms : Std.HashMap Nat Expr) (sortFVars : Array Expr)
    (k : Std.HashMap Nat Expr → Array Expr → MetaM α) : MetaM α := do
  if h : index < sorts.size then
    let (name, sort) := sorts[index]
    match sort with
    | .atom atom =>
      -- A source domain may be Sort u, including Prop. Assuming a successor
      -- universe here prevents instantiating the completed theorem at Sort u.
      -- Preserve known source levels; standalone callers get a general fresh
      -- level rather than an implicit Type-only restriction.
      let level ← match sortLevels[atom]? with
        | some level => pure level
        | none => if propositionAtoms.contains atom then pure Level.zero else mkFreshLevelMVar
      withLocalDecl (Name.mkSimple name) .default (.sort level) fun typeFVar =>
        withLocalSorts sorts propositionAtoms sortLevels (index + 1) (typeAtoms.insert atom typeFVar)
          (sortFVars.push typeFVar) k
    | .base .nat | .base .int | .base .bool | .base .string | .base (.bv _) =>
      withLocalSorts sorts propositionAtoms sortLevels (index + 1) typeAtoms sortFVars k
    | _ =>
      throwError "local replay expected `{name}` to denote an atomic or supported scalar sort"
  else
    k typeAtoms sortFVars

/-- Give every local TPTP sort a concrete inhabitant and install the resulting
`Nonempty` proposition as a local typeclass instance.

TPTP sorts are nonempty.  lean-auto records a witness for every exported
sort, and that witness is supplied only at the final Lam2DAAF boundary.  The
readable local reconstruction still needs the same assumption because some
VampLean theorems (for example `cnf_prenex1` and `forall_false_iff`) use
`Classical.choice` on a `Nonempty` instance.

The callback receives both the witness variables and the instance variables.
The latter are later abstracted and immediately applied to `Nonempty.intro`
values, so the completed local theorem exposes only ordinary element
parameters, exactly in the format expected by `Lam2DAAF.withAll`. -/
private partial def withLocalInhabitants (sorts : Array Expr) (index : Nat)
    (witnesses instances instanceValues : Array Expr)
    (k : Array Expr → Array Expr → Array Expr → MetaM α) : MetaM α := do
  if h : index < sorts.size then
    let sort := sorts[index]
    let witnessName := (`vampireInhabitant).appendIndexAfter index
    withLocalDecl witnessName .default sort fun witness => do
      let nonemptyType ← mkAppM ``Nonempty #[sort]
      let instanceValue ← mkAppM ``Nonempty.intro #[witness]
      let instanceName := (`vampireNonempty).appendIndexAfter index
      withLocalDecl instanceName .instImplicit nonemptyType fun instanceFVar =>
        withLocalInhabitants sorts (index + 1)
          (witnesses.push witness) (instances.push instanceFVar)
          (instanceValues.push instanceValue) k
  else
    k witnesses instances instanceValues

/-- Introduce every exported function and predicate as a local variable with
its TPTP name. The two atom maps are used only by the local `LamTerm`
interpreter; `symbols` is the name-based table consumed by rule metadata such
as a resolution unifier. -/
private partial def withLocalSymbols
    (entries : Array (String × LamTerm × LamSort)) (index : Nat)
    (typeAtoms termAtoms etoms : Std.HashMap Nat Expr)
    (symbols : Std.HashMap String Expr) (symbolFVars : Array Expr)
    (k : Std.HashMap Nat Expr → Std.HashMap Nat Expr → Std.HashMap String Expr →
      Array Expr → MetaM α) : MetaM α := do
  if h : index < entries.size then
    let (name, term, sort) := entries[index]
    match term with
    | .atom atom =>
      let type ← Auto.Lam2D.interpLamSortAsUnlifted typeAtoms sort
      withLocalDecl (Name.mkSimple name) .default type fun symbolFVar =>
        withLocalSymbols entries (index + 1) typeAtoms
          (termAtoms.insert atom symbolFVar) etoms (symbols.insert name symbolFVar)
          (symbolFVars.push symbolFVar) k
    | .etom etom =>
      let type ← Auto.Lam2D.interpLamSortAsUnlifted typeAtoms sort
      withLocalDecl (Name.mkSimple name) .default type fun symbolFVar =>
        withLocalSymbols entries (index + 1) typeAtoms termAtoms
          (etoms.insert etom symbolFVar) (symbols.insert name symbolFVar)
          (symbolFVars.push symbolFVar) k
    | .base (.ncst _) | .base (.icst _) | .base (.ite _) | .base (.bcst _) |
        .base (.scst _) | .base (.bvcst _) =>
      -- Interpreted heads have no proof-local fvar. The exported TPTP name is
      -- still entered in `symbols` because reconstruction annotations (for
      -- example unifiers) use those names, while formulas translate to the
      -- actual Lean arithmetic operation or conditional through lean-auto.
      let value ← translateLocal typeAtoms termAtoms etoms term
      withLocalSymbols entries (index + 1) typeAtoms termAtoms etoms
        (symbols.insert name value) symbolFVars k
    | _ => throwError "local replay expected `{name}` to denote a lean-auto atom, scalar operation or conditional"
  else
    k termAtoms etoms symbols symbolFVars

/-- Introduce the exported input formulas as local hypotheses named `factN`.
These hypotheses are the leaves of the local proof DAG. They are replaced by
the actual lean-auto proofs only after the final refutation is complete. -/
private partial def withLocalFacts (facts : Array (String × LamTerm)) (index : Nat)
    (typeAtoms termAtoms etoms : Std.HashMap Nat Expr)
    (sourceProofs : Std.HashMap String Expr) (sourceFVars : Array Expr)
    (k : Std.HashMap String Expr → Array Expr → MetaM α) : MetaM α := do
  if h : index < facts.size then
    let (name, formula) := facts[index]
    let type ← translateLocal typeAtoms termAtoms etoms formula
    unless ← isProp type do
      throwError "local replay source `{name}` is not a proposition"
    withLocalDecl (Name.mkSimple name) .default type fun proof =>
      withLocalFacts facts (index + 1) typeAtoms termAtoms etoms
        (sourceProofs.insert name proof) (sourceFVars.push proof) k
  else
    k sourceProofs sourceFVars

/-- The checked theorem and the exact boundary parameters it actually uses.
Indices refer to the replay problem's source facts; signature entries retain
their original lean-auto identities and order. -/
structure LocalProof where
  proof : Expr
  sorts : Array LamSort
  symbols : Array LamTerm
  inhabitantSorts : Array LamSort
  factIndices : Array Nat

/-- Collect dependencies once, including the types of used local variables.
The candidates are in declaration order, so one reverse pass closes the set. -/
private def usedBoundaryFVars (proof : Expr) (candidates : Array Expr) : MetaM FVarIdSet := do
  let mut state := Lean.collectFVars {} proof
  for candidate in candidates.reverse do
    if state.fvarSet.contains candidate.fvarId! then
      state := Lean.collectFVars state (← instantiateMVars (← inferType candidate))
  pure state.fvarSet

private def usedIndices (variables : Array Expr) (used : FVarIdSet) : Array Nat :=
  variables.zipIdx |>.filterMap fun (entry, index) =>
    if used.contains entry.fvarId! then some index else none

/-- Reconstruct the complete Vampire proof in an isolated, readable local
first-order signature.

The returned expression is closed over its used local variables and has the shape
`∀ used sorts, ∀ used symbols, ∀ used sort witnesses, used facts → False`. Each
derived DAG node was first proved as its own parent-to-child lemma by
`Backend.reconstruct`. No lean-auto atom or source proof has crossed
`Lam2DAAF` yet. -/
def buildLocalProof (problem : TFF.Problem) (decoded : DecodedProof)
    (propositionAtoms : Std.HashSet Nat := {})
    (sortLevels : Std.HashMap Nat Level := {}) : MetaM LocalProof :=
  Meta.withLCtx {} {} do
    let steps := decoded.steps
    withLocalSorts problem.sorts propositionAtoms sortLevels 0 {} #[] fun typeAtoms sortFVars =>
      withLocalSymbols problem.symbols 0 typeAtoms {} {} {} #[] fun termAtoms etoms symbols symbolFVars => do
        withLocalInhabitants sortFVars 0 #[] #[] #[]
            fun inhabitantFVars instanceFVars instanceValues => do
          withLocalFacts problem.facts 0 typeAtoms termAtoms etoms {} #[] fun sourceProofs sourceFVars => do
            let sourceIds := sourceFVars.map (·.fvarId!)
            let result ← replaySteps steps decoded.derivedSymbols decoded.polarityFlips
              sourceIds sourceProofs
              typeAtoms termAtoms etoms symbols inhabitantFVars
            let result ← instantiateMVars result
            -- Eliminate the proof-local typeclass assumptions by applying
            -- them to `Nonempty.intro inhabitant`.  Only the inhabitants are
            -- exposed as theorem parameters.
            let candidates := sortFVars ++ symbolFVars ++ inhabitantFVars ++ sourceFVars
            let instanceUsed ← usedBoundaryFVars result
              (sortFVars ++ symbolFVars ++ inhabitantFVars ++ instanceFVars ++ sourceFVars)
            let instanceIndices := usedIndices instanceFVars instanceUsed
            let result ← mkLambdaFVars (instanceIndices.map (instanceFVars[·]!)) result
            let result := mkAppN result (instanceIndices.map (instanceValues[·]!))
            let used ← usedBoundaryFVars result candidates
            let sortIndices := usedIndices sortFVars used
            let symbolIndices := usedIndices symbolFVars used
            let inhabitantIndices := usedIndices inhabitantFVars used
            let factIndices := usedIndices sourceFVars used
            let binders := candidates.filter (used.contains ·.fvarId!)
            let proof ← mkLambdaFVars binders result
            let localSorts := problem.sorts.filterMap fun (_, sort) =>
              if sort.isAtom then some sort else none
            let localSymbols := problem.symbols.filterMap fun
              | (_, term@(.atom _), _) | (_, term@(.etom _), _) => some term
              | _ => none
            -- A successful replay proof can contain tens of thousands of
            -- nested local lemmas.  Delaborating the whole expression for a
            -- trace is both unhelpful and can exhaust Lean's interpreter
            -- stack before the checked proof reaches `Lam2DAAF` (ALG402 is
            -- one such case).  The per-step trace above records the useful
            -- reconstruction detail, so retain only a bounded completion
            -- message here.
            trace[vampire.replay] "completed local Vampire proof from {steps.size} decoded step(s)"
            pure ⟨proof, sortIndices.map (localSorts[·]!),
              symbolIndices.map (localSymbols[·]!), inhabitantIndices.map (localSorts[·]!),
              factIndices⟩

end VampireHammer.Replay.Internal
