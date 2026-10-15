import VampireHammer.Replay.Decode.Formula
import VampireHammer.Replay.Decode.HigherOrder
import VampireHammer.Replay.Decode.Binders
import VampireHammer.Replay.Decode.Symbols
import VampireHammer.Replay.Decode.Graph

/-!
Decode proof nodes, attach their clause views, collect SAT trails, and order the DAG after
symbol discovery.
-/

namespace VampireHammer.Replay

open Lean Meta Elab Tactic
open Auto.Embedding.Lam
open Tptp.Data
open VampireHammer.Backend
open VampireHammer.Replay.Internal
open Decode.Internal

/-- Decode one logical THF, TFF, CNF, or quantifier-free FOF item from
Vampire's output.

Type declarations and unsupported TPTP dialects are intentionally skipped by
returning `none`; a malformed supported logical proof formula returns an error.
Keeping the raw inference metadata alongside the `LamTerm` makes later rule
handlers independent of the C parser's AST. -/
private def step? (input : TptpInput) : DecodeM (Option Step) := do
  match input with
  | .annotatedFormula (.thfAnnotated (.mk tptpName _ (.thfLogicFormula formula) annotations)) =>
    let name ← nameToString tptpName
    inStep name do
      let parsed ← THF.Syntax.term formula
      let outer ← higherOrderOuterBinders parsed
      let nested ← if outer.isEmpty then higherOrderNestedBinders parsed else pure none
      let decodedFormula ← decodeHigherOrderTerm parsed
      unless decodedFormula.sort == .base .prop do fail "THF proof formula is not a proposition"
      let (parents, sourceFact?, inference?) := annotation annotations
      let componentBinders ← if inference?.bind Inference.avatarDefinition? |>.isSome then
        higherOrderComponentBinders parsed
      else pure #[]
      let decodedFormula := if sourceFact?.isSome then normalizeSourceOr decodedFormula else decodedFormula
      let (decodedFormula, binders) ← if outer.isEmpty then
        normalizeNestedAClause decodedFormula nested
      else pure (decodedFormula, outer)
      pure <| some {
        name, binders, componentBinders, parents, sourceFact?, inference?
        formula := decodedFormula.term
        existentialVariables := higherOrderExistentialVariables parsed
        clauseLiterals? := none }
  | .annotatedFormula (.tffAnnotated (.mk tptpName _ (.tffLogicFormula formula) annotations)) =>
    let name ← nameToString tptpName
    inStep name do
      let outer ← outerBinders formula
      let nested ← if outer.isEmpty then nestedDisjunctBinders formula else pure none
      let decodedFormula ← decodeLogic formula
      unless decodedFormula.sort == .base .prop do
        fail "TFF proof formula is not a proposition"
      let (parents, sourceFact?, inference?) := annotation annotations
      let componentBinders ← if inference?.bind Inference.avatarDefinition? |>.isSome then
        avatarDefinitionComponentBinders formula
      else
        pure #[]
      let decodedFormula := if sourceFact?.isSome then normalizeSourceOr decodedFormula else decodedFormula
      let (decodedFormula, binders) ← if outer.isEmpty then
        normalizeNestedAClause decodedFormula nested
      else
        pure (decodedFormula, outer)
      pure <| some {
        name, binders, componentBinders, parents, sourceFact?, inference?
        formula := decodedFormula.term
        existentialVariables := existentialVariablesLogic formula
        clauseLiterals? := none
      }
  | .annotatedFormula (.fofAnnotated (.mk tptpName _ (.fofLogicFormula formula) annotations)) =>
    let name ← nameToString tptpName
    inStep name do
      let decodedFormula ← decodeFofLogic formula
      unless decodedFormula.sort == .base .prop do
        fail "FOF proof formula is not a proposition"
      let (parents, sourceFact?, inference?) := annotation annotations
      let decodedFormula := if sourceFact?.isSome then normalizeSourceOr decodedFormula else decodedFormula
      pure <| some {
        name, parents, sourceFact?, inference?
        formula := decodedFormula.term
        binders := #[]
        existentialVariables := #[]
        clauseLiterals? := none
      }
  | .annotatedFormula (.cnfAnnotated (.mk tptpName _ formula annotations)) =>
    let name ← nameToString tptpName
    inStep name do
      let decodedFormula ← decodeCnfFormula formula
      unless decodedFormula.sort == .base .prop do
        fail "CNF proof formula is not a proposition"
      let (parents, sourceFact?, inference?) := annotation annotations
      pure <| some {
        name, parents, sourceFact?, inference?
        formula := decodedFormula.term
        binders := #[]
        existentialVariables := #[]
        clauseLiterals? := none
      }
  | _ => pure none

/-- Mark the sequential CNF suffix and retain its literals before `LamTerm`s
are translated into local Lean expressions. -/
private def decodeClausePhase (steps : Array Step) : Array Step :=
  let (_, marked) := steps.foldl (fun (inClause, result) step =>
    let startsClause := step.inference?.any (·.rule == "cnf_transformation")
    let inClause := inClause || startsClause
    let clauseLiterals? := if inClause then
      (stripLeadingForalls step.binders.size step.formula).map fun body =>
        -- TPTP's `$false` contributes no literal, including in Vampire's
        -- occasional `$false | L` spelling. This agrees with `Clause.Tree`,
        -- where a false leaf is the empty clause and the remaining disjuncts
        -- retain their order.
        (flattenOr body).filter (· != .base .falseE) |>.toArray
    else none
    (inClause, result.push { step with clauseLiterals? := clauseLiterals? })) (false, #[])
  marked

/-! ## Collapsing Vampire's internal SAT trail

The only proof-DAG propositions needed downstream are the clauses at the
`sat_conversion` boundary. We replace the final `avatar_sat_refutation` node's
SAT parent by those boundary nodes and remove the intervening nodes from the
main replay DAG. A compact copy of the SAT sub-DAG remains attached as an
untrusted hint: the backend checks small RUP trails directly and otherwise
refutes the boundary clauses with `bv_decide`.

Doing this after formula decoding but before Lean-expression translation keeps
the transformation small: it operates solely on `Step` names and parent edges.
-/

/-- Walk backwards from a SAT-refutation parent to checked boundary clauses.
Annotated conversions remain as boundaries; ordinary conversions expose their
first-order source clauses. The returned set identifies the internal
SAT nodes removed from the main DAG; the array contains the checked clauses from
which Vampire entered its SAT solver.

`pending` is a list because prepending parent names gives a simple worklist.
`seen` protects malformed or unexpectedly shared proof graphs from looping. -/
private partial def collectAvatarSatBoundary
    (stepsByName : Std.HashMap String Step) (pending : List String)
    (seen internal : Std.HashSet String) (boundary : Array ParentRef) :
    Std.HashSet String × Array ParentRef :=
  match pending with
  | [] => (internal, boundary)
  | name :: rest =>
    if seen.contains name then
      collectAvatarSatBoundary stepsByName rest seen internal boundary
    else
      let seen := seen.insert name
      match stepsByName.get? name with
      | none => collectAvatarSatBoundary stepsByName rest seen internal boundary
      | some step =>
        if step.inference?.any (fun inference => inference.rule == "sat_conversion") then
          if step.inference?.any (·.hasAvatarMap) then
            -- Explicit EUF conversions have definition parents. Reconstruct
            -- the conversion itself and use its SAT clause as the boundary.
            collectAvatarSatBoundary stepsByName rest seen internal
              (boundary.push { name })
          else
            -- Ordinary conversions change representation only. Their parents
            -- are the boundary; do not traverse their FO derivations.
            collectAvatarSatBoundary stepsByName rest seen (internal.insert name)
              (boundary ++ step.parents)
        else
          let parentNames := step.parents.toList.map (·.name)
          collectAvatarSatBoundary stepsByName (parentNames ++ rest) seen
            (internal.insert name) boundary

/-- Collapse the AVATAR SAT sub-DAG to one final node whose parents are the
checked conversion boundaries. If the expected boundary
cannot be found, retain the original proof unchanged so diagnostics still
refer to Vampire's real graph. -/
private def collapseAvatarSatTrail (steps : Array Step) : Array Step :=
  let stepsByName := steps.foldl (fun result step => result.insert step.name step) {}
  match steps.find? fun step =>
      step.inference?.any (fun inference => inference.rule == "avatar_sat_refutation") with
  | none => steps
  | some finalStep =>
    let pending := finalStep.parents.toList.map (·.name)
    let (internal, boundary) := collectAvatarSatBoundary stepsByName pending {} {} #[]
    if boundary.isEmpty then
      steps
    else
      let trail : Array SatProofStep := steps.filterMap fun step =>
        if internal.contains step.name then
          some ⟨step.name, step.formula, step.parents,
            (step.inference?.map (·.rule)).getD ""⟩
        else none
      let satProof? : Option SatProof := finalStep.parents[0]?.map fun root =>
        { root := root.name, steps := trail }
      steps.filterMap fun step =>
        if internal.contains step.name then
          none
        else if step.name == finalStep.name then
          let inference? := step.inference?.map fun inference =>
            { inference with parents := boundary }
          some { step with parents := boundary, inference? := inference?, satProof? := satProof? }
        else
          some step

/-- Split a clause literal into its polarity and atom. -/
private def literalPolarity : LamTerm → Bool × LamTerm
  | .app _ (.base .not) atom => (false, atom)
  | atom => (true, atom)

/-- The head symbol of an applied atom. -/
private def lamHead : LamTerm → LamTerm
  | .app _ fn _ => lamHead fn
  | term => term

/-- Read the flipped predicates off the `consistent_polarity_flipping` nodes.
Vampire complements exactly the literals of flipped predicates and keeps their
atoms, so no certificate is needed. Literals are paired by atom, since the
printed clauses may be in different orders. Whether the
resulting interpretation is consistent is checked by the replayed proofs. -/
private def decodePolarityFlips (steps : Array Step) : Except String PolarityFlips := do
  let byName := steps.foldl (fun result step => result.insert step.name step)
    ({} : Std.HashMap String Step)
  let mut flips : PolarityFlips := {}
  for step in steps do
    unless step.inference?.any (·.rule == "consistent_polarity_flipping") do continue
    if flips.boundary?.isNone then flips := { flips with boundary? := some step.name }
    let #[parentRef] := step.parents
      | throw s!"polarity flipping `{step.name}` does not have exactly one parent"
    let some parent := byName.get? parentRef.name
      | throw s!"polarity flipping `{step.name}` refers to unknown parent `{parentRef.name}`"
    let (some before, some after) := (parent.clauseLiterals?, step.clauseLiterals?)
      | throw s!"polarity flipping `{step.name}` or its parent is not a decoded clause"
    unless before.size == after.size && parent.binders.size == step.binders.size do
      throw s!"polarity flipping `{step.name}` changes the clause shape"
    -- Pair literals by atom rather than position: literal selection may
    -- reorder either printed clause.
    let mut unpaired := before.toList
    for flipped in after do
      let (flippedSign, flippedAtom) := literalPolarity flipped
      let some index := unpaired.findIdx? fun original => (literalPolarity original).2 == flippedAtom
        | throw s!"polarity flipping `{step.name}` changes a literal's atom"
      let (originalSign, originalAtom) := literalPolarity unpaired[index]!
      unpaired := unpaired.eraseIdx index
      if originalSign != flippedSign then
        let head := lamHead originalAtom
        unless flips.heads.contains head do
          flips := { flips with heads := flips.heads.push head }
  pure flips

/-- Complement every literal of the predicate `head` in `term`: `h t̄` becomes
`¬h t̄` and `¬h t̄` becomes `h t̄`. -/
private partial def complementHead (head : LamTerm) : LamTerm → LamTerm
  | .app _ (.base .not) atom =>
    if lamHead atom == head then atom else .app (.base .prop) (.base .not) (complementHead head atom)
  | term@(.app sort fn arg) =>
    if lamHead term == head then .app (.base .prop) (.base .not) term
    else .app sort (complementHead head fn) (complementHead head arg)
  | .lam sort body => .lam sort (complementHead head body)
  | term => term

/-- Replay rebinds a flipped predicate by a `let`, which needs a symbol of the
problem. Vampire also flips predicates that lean-auto interprets, such as
`nat_le`; those flips are undone instead. Vampire flips during preprocessing,
so the unflipped steps are exactly the parents of the flipping steps and their
ancestors; every other step (including fresh AVATAR definitions, which have no
parents) gets the literals of those predicates complemented back. Complementing
one predicate uniformly is a renaming, so every inference stays valid, and the
flipping steps become identities. -/
private def undoInterpretedFlips (steps : Array Step) (flips : PolarityFlips) :
    Array Step × PolarityFlips := Id.run do
  let interpreted := flips.heads.filter fun head => !(head matches .atom _ | .etom _)
  if interpreted.isEmpty then return (steps, flips)
  let complement := fun term => interpreted.foldl (fun term head => complementHead head term) term
  let byName := steps.foldl (fun result step => result.insert step.name step)
    ({} : Std.HashMap String Step)
  -- Ancestors of the flipping steps, parents included.
  let mut unflipped : Std.HashSet String := {}
  let mut pending : List String := steps.toList.flatMap fun step =>
    if step.inference?.any (·.rule == "consistent_polarity_flipping") then
      step.parents.toList.map (·.name) else []
  while !pending.isEmpty do
    let name :: rest := pending | break
    pending := rest
    if unflipped.contains name then continue
    unflipped := unflipped.insert name
    if let some step := byName.get? name then
      pending := step.parents.toList.map (·.name) ++ pending
  let result := steps.map fun step =>
    if unflipped.contains step.name then step else { step with
      formula := complement step.formula
      clauseLiterals? := step.clauseLiterals?.map (·.map complement) }
  let heads := flips.heads.filter (!interpreted.contains ·)
  return (result, { flips with heads })

/-- Decode every supported logical formula in a parsed Vampire proof.

Input symbols recover the exact `LamTerm` recorded by the exporter. Fresh
Skolem and AVATAR declarations receive proof-local synthetic terms, returned
separately so replay can interpret them as Lean lets rather than original
problem atoms. -/
def decodeSteps (problem : TFF.Problem) (proof : TptpFile) : Except String DecodedProof := do
  let derivedSymbols ← decodeDerivedSymbols problem proof
  let .mk inputs := proof
  -- The clause phase is the suffix starting at the first `cnf_transformation`
  -- (see `decodeClausePhase`); every earlier formula step uses Lean's
  -- right-associated reading of disjunction chains.
  let mut inClause := false
  let mut decoded := #[]
  let context : Decode.Internal.Context := { problem, derivedSymbols }
  let mut names : Std.HashSet String := {}
  for input in inputs do
    let inference? := inputInference? input
    inClause := inClause || inference?.any (·.rule == "cnf_transformation")
    let flattenConjunctions := inference?.isNone
    if let some step ← (step? input).run
        { context with rightChains := !inClause, flattenConjunctions } then
      -- Validate before SAT-trail collapsing can remove internal nodes.
      if names.contains step.name then throw s!"duplicate Vampire proof step `{step.name}`"
      names := names.insert step.name
      decoded := decoded.push step
  let steps ← parentsFirst (collapseAvatarSatTrail decoded)
  let steps := decodeClausePhase steps
  let (steps, polarityFlips) := undoInterpretedFlips steps (← decodePolarityFlips steps)
  pure { steps, derivedSymbols, polarityFlips }

end VampireHammer.Replay
