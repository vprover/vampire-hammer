import VampireHammer.Backend.Types
import VampireHammer.Backend.HigherOrderTerm

/-!
Open conclusion binders and apply Vampire's parent substitutions.

All calculus handlers share this path, including variable-to-variable bindings
and variables erased from the child. Internal helpers infer sorts and use a
proof-local inhabitant when a certificate leaves an irrelevant variable free.
No rule-specific proof construction occurs here.
-/

namespace VampireHammer.Backend.Internal

open Lean Meta Elab Tactic
open Auto.Embedding.Lam

/-- A resolution substitution after its raw TPTP terms have been interpreted
in the local reconstruction signature. -/
private structure MaterializedInstantiation where
  /-- Binder names paired with actual Lean arguments of the correct sort. -/
  bindings : Array (String × Expr)

/-- Interpret a raw unifier term in the local first-order signature.

An atom such as `t_a1` is looked up in `RuleInput.symbols`. A variable such as
`Y0` is looked up among the binders just opened from the resolvent. Applications
are constructed recursively; each argument's type is checked against the
function's domain, so an ill-typed certificate is declined here rather than
rejected later by the kernel. No part of the unifier
needs to cross `Lam2DAAF`; the completed local proof is imported only after the
whole DAG has been reconstructed. -/
private partial def materializeTerm (term : MetadataTerm)
    (symbols : Std.HashMap String Expr) (targetBindings : Array (String × Expr)) :
    MetaM (Option Expr) := do
  match term with
  | .higherOrder (.ok term) => materializeHigherOrderTerm term symbols targetBindings
  | .atom name => pure (symbols.get? name)
  | .variable name =>
    pure (targetBindings.find? (fun binding => binding.1 == name) |>.map Prod.snd)
  | .application name arguments =>
    let some function := symbols.get? name
      | return none
    let mut applied := function
    let mut type ← inferType function
    for argument in arguments do
      let some argument ← materializeTerm argument symbols targetBindings
        | return none
      type ← whnf type
      let .forallE _ domain body _ := type | return none
      unless ← isDefEq domain (← inferType argument) do return none
      applied := mkApp applied argument
      type := body.instantiate1 argument
    pure (some applied)
  | _ => pure none

/-- Collect the variable spellings used in the right-hand side of one printed
Vampire substitution term.

This deliberately ignores the left-hand-side binder of `b(X, term)`: only
variables occurring *inside* `term` need a Lean value when the substitution is
materialized.  A name may occur more than once; callers use it only as a
lookup key, so preserving duplicates would add no information. -/
private partial def substitutionTermVariables : MetadataTerm → Array String
  | .higherOrder (.ok term) => term.freeVariables
  | .variable name => #[name]
  | .application _ arguments => arguments.foldl
      (fun result argument => result ++ substitutionTermVariables argument) #[]
  | .list entries | .tuple entries => entries.foldl
      (fun result entry => result ++ substitutionTermVariables entry) #[]
  | .annotated head tail => substitutionTermVariables head ++ substitutionTermVariables tail
  | _ => #[]

/-- Infer sorts for variables in the unifier's right-hand-side namespace.

Vampire may use a fresh MGU variable such as `X3` without listing it among a
parent's or the conclusion's quantifiers.  It has no independent Lean binder,
but its surrounding first-order term fixes its sort.  This walk follows the
types of the exported function symbols and records that expected sort.  A
repeated variable spelling must always receive definitionally equal sorts.

Conclusion binders take precedence. Parent binder names belong to separate
namespaces: in `left[X1 ↦ X0], right[X0 ↦ f(X0)]`, the RHS `X0` can have
the argument sort of `f`, while the right parent's `X0` has its result sort.
Infer every other RHS variable from its typed position rather than treating
a matching parent-local spelling as a type constraint. TFF
function types are non-dependent, so after inspecting an argument domain we
can simply continue with the function's codomain. -/
private partial def inferUnifierVariableDomains (term : MetadataTerm) (expected : Expr)
    (symbols : Std.HashMap String Expr) (targetBindings : Array (String × Expr))
    (inferred : Std.HashMap String Expr) :
    MetaM (Option (Std.HashMap String Expr)) := do
  match term with
  | .higherOrder (.ok term) =>
    inferHigherOrderVariableDomains term expected symbols targetBindings inferred
  | .variable name =>
    if let some (_, value) := targetBindings.find? (fun binding => binding.1 == name) then
      unless ← isDefEq (← inferType value) expected do return none
      return some inferred
    if let some domain := inferred.get? name then
      unless ← isDefEq domain expected do return none
      return some inferred
    pure (some (inferred.insert name expected))
  | .atom name =>
    let some value := symbols.get? name | return none
    unless ← isDefEq (← inferType value) expected do return none
    pure (some inferred)
  | .application name arguments =>
    let some function := symbols.get? name | return none
    let mut functionType ← inferType function
    let mut inferred := inferred
    for argument in arguments do
      functionType ← whnf functionType
      unless functionType.isForall do return none
      let some next ← inferUnifierVariableDomains argument functionType.bindingDomain!
        symbols targetBindings inferred
        | return none
      inferred := next
      -- TFF signatures do not have dependent argument types.  Keeping the
      -- body without substituting the raw argument is therefore sufficient
      -- and avoids materializing an auxiliary variable before it has a value.
      functionType := functionType.bindingBody!
    functionType ← whnf functionType
    unless ← isDefEq functionType expected do return none
    pure (some inferred)
  | _ => pure none

/-- Return the Lean domains of a parent's leading first-order binders.

The decoded `FormulaBinder` stores the TPTP sort for diagnostics and decoding,
but an omitted calculus variable needs the actual local Lean sort in order to
choose a harmless representative. TF0 sorts are non-dependent, so walking the
parent's leading `∀` telescope is sufficient here. -/
private def parentBinderDomains (parent : ParentProof) : MetaM (Option (Array Expr)) := do
  let mut type := parent.target
  let mut domains := #[]
  for _ in parent.binders do
    type ← whnf type
    unless type.isForall do return none
    domains := domains.push type.bindingDomain!
    type := type.bindingBody!
  pure (some domains)

/-- Find the witness for a local TPTP sort introduced by `Replay`.

TPTP sorts are nonempty. Replay therefore creates one
`vampireInhabitantᵢ : sort` local for every sort before it starts rebuilding
the proof DAG. A calculus unifier may leave a variable unmapped when every
occurrence belongs to a literal or redex removed by that inference. Such a
variable is absent from the conclusion telescope, yet any value of its
nonempty sort is valid. This helper deliberately uses only Replay's explicit
inhabitant locals (`candidates`), never an arbitrary proof or source hypothesis
from the surrounding theorem. -/
private partial def localTptpInhabitant? (candidates : Array Expr) (domain : Expr) :
    MetaM (Option Expr) := do
  let domain ← whnf (← instantiateMVars domain)
  if domain == mkSort .zero then return some (mkConst ``True)
  if domain == mkConst ``Nat then return some (mkNatLit 0)
  if domain == mkConst ``Int then return some (mkApp (mkConst ``Int.ofNat) (mkNatLit 0))
  if let .forallE name argument body _ := domain then
    unless body.hasLooseBVars do
      return ← withLocalDeclD name argument fun boundValue => do
        let some value ← localTptpInhabitant? candidates body | return none
        some <$> mkLambdaFVars #[boundValue] value
  for candidate in candidates do
    if ← isDefEq (← inferType candidate) domain then
      return some candidate
  pure none

/-- Replay's sort inhabitants: `RuleInput.inhabitants` when Replay supplied
them, otherwise the `vampireInhabitant*` locals of the current context (used by
handlers invoked outside Replay, e.g. in tests). Computed once per inference. -/
private def inhabitantCandidates (input : RuleInput) : MetaM (Array Expr) := do
  if !input.inhabitants.isEmpty then return input.inhabitants
  return (← getLCtx).foldl (init := #[]) fun candidates declaration =>
    if declaration.userName.toString.startsWith "vampireInhabitant" then
      candidates.push declaration.toExpr
    else candidates

/-- Complete a parent substitution while retaining variables erased by an
inference.

Every post-CNF calculus rule first applies the substitutions printed by
Vampire to its parent clauses.  Usually every parent binder is either named
in that substitution or survives as a binder of the conclusion.  A variable
which occurs only in a deleted literal (resolution/factoring) or only inside
a rewritten redex (superposition/demodulation) is the exception: it has no
name in the conclusion but Lean still needs an argument to apply the parent's
universally quantified theorem.

`shared` is the temporary environment for precisely those hidden variables.
It is shared by all parents of one inference, because a printed substitution
term in one parent may refer to a variable which was omitted from another
parent's substitution.  The final rule-specific literal check still verifies
the instantiated clauses and conclusion; the inhabitant fallback merely makes
the otherwise invisible quantifier application expressible in Lean. -/
private def completeInstantiation (parent : ParentProof) (domains : Array Expr)
    (instantiation : ParentSubstitution) (symbols : Std.HashMap String Expr)
    (targetBindings : Array (String × Expr)) (shared : Std.HashMap String Expr)
    (inhabitants : Array Expr) :
    MetaM (Option (MaterializedInstantiation × Std.HashMap String Expr)) := do
  unless instantiation.parent == parent.parent.name do return none
  unless instantiation.bindings.all fun binding =>
      parent.binders.any fun binder => binder.name == binding.1 do
    return none
  unless domains.size == parent.binders.size do return none
  let mut bindings := #[]
  let mut shared := shared
  for index in [:parent.binders.size] do
    let some binder := parent.binders[index]? | return none
    let some domain := domains[index]? | return none
    if let some (_, rawValue) := instantiation.bindings.find?
        (fun binding => binding.1 == binder.name) then
      -- Explicit terms can mention a variable that was erased from a sibling
      -- parent.  Make both the conclusion telescope and the shared
      -- intermediate variables visible to the TPTP-term decoder.
      let availableBindings := targetBindings ++ shared.toArray
      let some value ← materializeTerm rawValue symbols availableBindings | return none
      bindings := bindings.push (binder.name, value)
    else if let some (_, targetValue) := targetBindings.find?
        (fun target => target.1 == binder.name) then
      bindings := bindings.push (binder.name, targetValue)
    else if let some value := shared.get? binder.name then
      unless ← isDefEq (← inferType value) domain do return none
      bindings := bindings.push (binder.name, value)
    else
      let some inhabitant ← localTptpInhabitant? inhabitants domain | return none
      trace[vampire.replay] "parent instantiation: assigned erased variable `{binder.name}` Replay's sort inhabitant"
      shared := shared.insert binder.name inhabitant
      bindings := bindings.push (binder.name, inhabitant)
  pure (some ({ bindings }, shared))

/-- Pre-allocate the variables that disappear from a parent before applying
any parent substitution.

Parent order in a Vampire proof is not an evaluation order for unifier terms.
For example, the first parent may omit `X0` while the second contains
`X0 ↦ f(X0)`.  If the first parent is instantiated only after the second one,
the term on the second parent would have no Lean value for its inner `X0`.
This pass assigns each omitted variable first.  When another parent provides a
closed hint for it we use that hint; otherwise we use Replay's canonical
inhabitant of the TPTP sort. -/
private def seedErasedInstantiationVariables (parents : Array ParentProof)
    (parentDomains : Array (Array Expr))
    (substitutions : Array ParentSubstitution) (symbols : Std.HashMap String Expr)
    (targetBindings : Array (String × Expr)) (inhabitants : Array Expr) :
    MetaM (Option (Std.HashMap String Expr)) := do
  unless parents.size == substitutions.size && parents.size == parentDomains.size do return none
  let mut shared : Std.HashMap String Expr := {}
  -- Infer the sorts of RHS MGU variables before allocating their
  -- canonical values.  In `f47`, for example, `X3` occurs only in terms such
  -- as `t_a1(X2, t_a1(X0, X3))`; it is neither a parent nor a conclusion
  -- binder, but the argument types of `t_a1` certify that it has sort `s_a0`.
  let mut rhsDomains : Std.HashMap String Expr := {}
  for ((parent, substitution), domains) in (parents.zip substitutions).zip parentDomains do
    unless substitution.parent == parent.parent.name do return none
    unless domains.size == parent.binders.size do return none
    for (binderName, rawValue) in substitution.bindings do
      let some index := parent.binders.findIdx? (fun binder => binder.name == binderName)
        | return none
      let some expected := domains[index]? | return none
      let some inferred ← inferUnifierVariableDomains rawValue expected symbols
        targetBindings rhsDomains
        | return none
      rhsDomains := inferred

  -- A variable can occur only in a substitution right-hand side.  For
  -- example, `f102` has `f23[X1 ↦ X2]`, where that `X2` is erased by the
  -- following rewrite and does not occur in the conclusion binders.  It is
  -- nevertheless required to instantiate the parent theorem in Lean.  Since
  -- the final rewrite check proves that the value is erased, any inhabitant of
  -- its first-order sort is sound.  Seed it before processing parent order so
  -- every parent sees the same representative.
  for substitution in substitutions do
    for (_, rawValue) in substitution.bindings do
      for variableName in substitutionTermVariables rawValue do
        if targetBindings.any (fun binding => binding.1 == variableName) ||
            (shared.get? variableName).isSome then
          continue
        let some domain := rhsDomains.get? variableName | return none
        let some inhabitant ← localTptpInhabitant? inhabitants domain | return none
        trace[vampire.replay] "parent instantiation: pre-allocated erased mgu variable `{variableName}` with Replay's sort inhabitant"
        shared := shared.insert variableName inhabitant
  for ((parent, own), domains) in (parents.zip substitutions).zip parentDomains do
    unless own.parent == parent.parent.name do return none
    unless domains.size == parent.binders.size do return none
    for index in [:parent.binders.size] do
      let some binder := parent.binders[index]? | return none
      let some domain := domains[index]? | return none
      -- An explicit parent binding or conclusion binder already provides this
      -- variable's value.  Only the omitted case needs the shared map.
      if own.bindings.any (fun binding => binding.1 == binder.name) ||
          targetBindings.any (fun binding => binding.1 == binder.name) then
        continue
      if let some existing := shared.get? binder.name then
        unless ← isDefEq (← inferType existing) domain do return none
        continue
      let mut hinted : Option Expr := none
      for other in substitutions do
        if other.parent != own.parent && hinted.isNone then
          if let some (_, rawValue) := other.bindings.find?
              (fun binding => binding.1 == binder.name) then
            let availableBindings := targetBindings ++ shared.toArray
            if let some value ← materializeTerm rawValue symbols availableBindings then
              if ← isDefEq (← inferType value) domain then
                hinted := some value
      let value ← match hinted with
        | some value => pure value
        | none =>
          let some inhabitant ← localTptpInhabitant? inhabitants domain | return none
          trace[vampire.replay] "parent instantiation: pre-allocated erased variable `{binder.name}` with Replay's sort inhabitant"
          pure inhabitant
      shared := shared.insert binder.name value
  pure (some shared)

/-- Apply a fully materialized Vampire substitution to a parent proof.

The TPTP parser keeps the names of the outer `∀` binders, so the backend can
check that the substitution has not been reordered or truncated before
constructing the actual Lean applications. -/
private def instantiateForalls (proof : Expr) (binders : Array FormulaBinder)
    (instantiation : MaterializedInstantiation) : MetaM (Option (Expr × Expr)) := do
  if binders.size != instantiation.bindings.size then
    trace[vampire.replay] "instantiation declined: {binders.size} leading binders but {instantiation.bindings.size} bindings"
    return none
  let mut proof := proof
  let mut type ← inferType proof
  if binders.isEmpty then
    return some (proof, type)
  type ← whnf type
  let mut index := 0
  for (binder, binding) in binders.zip instantiation.bindings do
    if binder.name != binding.1 || !type.isForall then
      return none
    let argument := binding.2
    if !(← isDefEq type.bindingDomain! (← inferType argument)) then
      trace[vampire.replay] "instantiation declined: type mismatch for `{binder.name}`"
      return none
    proof := mkApp proof argument
    type := type.bindingBody!.instantiate1 argument
    -- Keep the final body syntactically as `Holds ...` when a previous replay
    -- step produced a clause proof. Only another leading binder needs WHNF.
    if index + 1 < binders.size then
      type ← whnf type
    index := index + 1
  pure (some (proof, type))

/-- Open exactly the leading universal binders printed on a derived TPTP step.

Rule handlers work on the body where Vampire's substitutions and literal
positions are meaningful. This helper restores the binders around a successful
body proof, so factoring, resolution, and superposition do not each implement
their own telescope traversal. -/
def underConclusionBinders (input : RuleInput)
    (build : Array (String × Expr) → Expr → MetaM (Option Expr)) : MetaM (Option Expr) := do
  /- `forallTelescopeReducing` is intentionally *not* used here. Lean unfolds
  `¬ P` to `P → False`, and that utility consequently opens the negated
  literal as one more telescope binder after it has opened all TPTP `∀`s.
  Rule certificates name only the explicit leading TPTP binders, so doing that
  makes a unit negative clause appear to have one binder too many. Walk the
  recorded number of binders ourselves and leave the remaining clause body
  opaque, even when its outermost literal is a negation. -/
  let rec openBinders (remaining : List FormulaBinder) (target : Expr)
      (bindings : Array (String × Expr)) (fvars : Array Expr) :
      MetaM (Option Expr) := do
    match remaining with
    | [] =>
      let some bodyProof ← build bindings target | return none
      some <$> mkLambdaFVars fvars bodyProof
    | binder :: remaining =>
      let target ← whnf target
      unless target.isForall do return none
      withLocalDeclD (Name.mkSimple binder.name) target.bindingDomain! fun fvar => do
        let body := target.bindingBody!.instantiate1 fvar
        openBinders remaining body (bindings.push (binder.name, fvar)) (fvars.push fvar)
  trace[vampire.replay] "opening {input.step.binders.size} TPTP conclusion binder(s): {String.intercalate "," (input.step.binders.map FormulaBinder.name).toList}"
  openBinders input.step.binders.toList input.target #[] #[]

/-- The values shared by all parents of one inference: the erased variables
seeded by `seedErasedInstantiationVariables`, each parent's binder domains, and
Replay's sort inhabitants. Handlers that both instantiate parents and
materialize certificate terms compute it once with `instantiationScope`. -/
structure InstantiationScope where
  shared : Std.HashMap String Expr
  parentDomains : Array (Array Expr)
  inhabitants : Array Expr

/-- Seed the erased variables of one inference under the opened conclusion
binders. -/
def instantiationScope (input : RuleInput) (substitutions : Array ParentSubstitution)
    (targetBindings : Array (String × Expr)) : MetaM (Option InstantiationScope) := do
  unless substitutions.size == input.parents.size do return none
  let mut parentDomains := #[]
  for parent in input.parents do
    let some domains ← parentBinderDomains parent | return none
    parentDomains := parentDomains.push domains
  let inhabitants ← inhabitantCandidates input
  let some shared ← seedErasedInstantiationVariables input.parents parentDomains substitutions
    input.symbols targetBindings inhabitants | return none
  pure (some { shared, parentDomains, inhabitants })

/-- Materialize and apply all parent substitutions in their reported parent
order within `scope`. -/
def instantiateParentsIn (input : RuleInput) (substitutions : Array ParentSubstitution)
    (targetBindings : Array (String × Expr)) (scope : InstantiationScope) :
    MetaM (Option (Array (Expr × Expr))) := do
  unless substitutions.size == input.parents.size &&
      scope.parentDomains.size == input.parents.size do return none
  let mut instantiated := #[]
  let mut shared := scope.shared
  for ((parent, substitution), domains) in
      (input.parents.zip substitutions).zip scope.parentDomains do
    let some (completed, nextShared) ← completeInstantiation parent domains substitution
      input.symbols targetBindings shared scope.inhabitants
      | return none
    shared := nextShared
    let some parentProof ← instantiateForalls parent.proof parent.binders completed
      | return none
    instantiated := instantiated.push parentProof
  pure (some instantiated)

/-- Materialize conclusion-namespace rewrite terms, including erased MGU
variables allocated by the same typed instantiation pass as its parents. -/
def materializeTermsIn (input : RuleInput) (targetBindings : Array (String × Expr))
    (scope : InstantiationScope) (terms : Array MetadataTerm) : MetaM (Option (Array Expr)) := do
  let available := targetBindings ++ scope.shared.toArray
  let mut result := #[]
  for term in terms do
    let some value ← materializeTerm term input.symbols available | return none
    result := result.push value
  pure (some result)

/-- Materialize and apply all parent substitutions in their reported parent
order. Every clause inference performs this grounding before it inspects its
literals. `seedErasedInstantiationVariables` makes this common path work for
variables removed by any calculus inference, rather than treating that issue
as a superposition-only special case. -/
def instantiateParents (input : RuleInput)
    (substitutions : Array ParentSubstitution)
    (targetBindings : Array (String × Expr)) : MetaM (Option (Array (Expr × Expr))) := do
  let some scope ← instantiationScope input substitutions targetBindings | return none
  instantiateParentsIn input substitutions targetBindings scope

/-- Materialize one certificate term against explicit name bindings. -/
def materializeMetadataTerm (term : MetadataTerm) (symbols : Std.HashMap String Expr)
    (bindings : Array (String × Expr)) : MetaM (Option Expr) :=
  materializeTerm term symbols bindings

/-- Materialize conclusion-namespace rewrite terms in a fresh scope. -/
def materializeInferenceTerms (input : RuleInput) (substitutions : Array ParentSubstitution)
    (targetBindings : Array (String × Expr)) (terms : Array MetadataTerm) :
    MetaM (Option (Array Expr)) := do
  let some scope ← instantiationScope input substitutions targetBindings | return none
  materializeTermsIn input targetBindings scope terms

/-- Put parent-local substitution records in proof-parent order while consuming
each record exactly once.

Most inference annotations can be paired by a parent name alone.  Self
inferences are the important exception: a certificate for
`superposition(...,[f102,f102])` legitimately contains two
`subs(f102, ...)` records, one for each occurrence.  Reusing the first record
for both parents silently changes the inference.  This stable matching keeps
Vampire's annotation order as the occurrence order for duplicate names while
still accepting an annotation order that differs from the proof-parent order
for distinct names. -/
def orderParentSubstitutions (parents : Array ParentProof)
    (records : Array ParentSubstitution) : Option (Array ParentSubstitution) := do
  guard (parents.size == records.size)
  let mut used : Array Nat := #[]
  let mut ordered := #[]
  for parent in parents do
    let some (record, index) := records.zipIdx.find? fun (record, index) =>
      record.parent == parent.parent.name && !used.contains index
      | none
    ordered := ordered.push record
    used := used.push index
  some ordered

end VampireHammer.Backend.Internal
