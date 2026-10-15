import VampireHammer.Replay.Decode.Context
import VampireHammer.Replay.Decode.HigherOrder
import VampireHammer.Backend.Metadata

/-!
Source annotations and proof-local symbol declarations. Fresh symbols are typed before logical
proof nodes are decoded.
-/

namespace VampireHammer.Replay.Decode.Internal

open Lean Meta Elab Tactic
open Auto.Embedding.Lam
open Tptp.Data
open VampireHammer.Backend
open VampireHammer.Replay.Internal

/-- Extract the exported fact identifier from a `file(..., factN)` source
annotation.  This is the key used to retrieve lean-auto's existing proof. -/
private def sourceFact : Source → Option String
  | .externalSource (.fileSource (.mk _ (.name entryName))) => nameToString entryName |>.toOption
  | _ => none

/-- Split a TPTP annotation into either source-fact information or an inferred
DAG edge with rule metadata.  The parser itself remains generic; this is the
single point where replay interprets its annotations. -/
def annotation (annotations : Annotations) :
    Array ParentRef × Option String × Option Inference :=
  match annotations with
  | .sourceOptionalInfo (.dagSource (.inferenceRecord (.mk rule info parentList))) _ =>
    let inference := Inference.ofTptp rule info parentList
    (inference.parents, none, some inference)
  | .sourceOptionalInfo (.internalSource (.mk (.mk introType) info marker)) _ =>
    match word introType with
    | .ok "definition" =>
      let inference := Inference.ofDefinition info marker
      if inference.avatarDefinition?.isSome || inference.predicateDefinition?.isSome then
        (#[], none, some inference)
      else (#[], none, none)
    | .ok "theory" => (#[], none, Inference.ofTheory? info)
    | _ => (#[], none, none)
  | .sourceOptionalInfo source _ => (#[], sourceFact source, none)
  | .nothing => (#[], none, none)

/-! ## Proof-local symbol declarations

The TF0 input contains only symbols originating in lean-auto.  Vampire can add
new declarations to its proof, most notably `sK0 : α → β` for a Skolem
function.  Formulas containing such a symbol cannot be decoded until its TFF
type is known.  The following deliberately small type decoder reads only the
monomorphic first-order declaration fragment produced by this project and by
Vampire for those fresh symbols. -/

private def typeConstantName : TypeConstant → Except String String
  | .mk (.mk name) => word name

private def untypedAtomName : UntypedAtom → Option String
  | .constant value => (constant value).toOption
  | .systemConstant _ => none

private partial def decodeAtomicSort : TffAtomicType → DecodeM LamSort
  | .typeConstant name => do
    lookupSort (← typeConstantName name)
  | .definedType (.mk (.mk (.mk name))) =>
    match name with
    | "o" | "$o" => pure (.base .prop)
    | _ => fail s!"unsupported defined TFF type `${name}` on a proof-local symbol"
  | .tffAtomicType sort => decodeAtomicSort sort
  | _ => fail "unsupported polymorphic or tuple-valued proof-local symbol type"

mutual

private partial def decodeXprodSorts : TffXprodType → DecodeM (List LamSort)
  | .tffUnitaryTypeTffAtomicType first last => do
    pure ((← decodeUnitarySorts first) ++ [← decodeAtomicSort last])
  | .tffXprodTypeTffAtomicType first last => do
    pure ((← decodeXprodSorts first) ++ [← decodeAtomicSort last])

private partial def decodeUnitarySorts : TffUnitaryType → DecodeM (List LamSort)
  | .tffAtomicType sort => do
    pure [← decodeAtomicSort sort]
  | .tffXprodType product => decodeXprodSorts product

end

private partial def decodeNonAtomicSort : TffNonAtomicType → DecodeM LamSort
  | .tffMappingType (.mk arguments result) => do
    let arguments ← decodeUnitarySorts arguments
    let result ← decodeAtomicSort result
    pure <| arguments.foldr LamSort.func result
  | .tffNonAtomicType type => decodeNonAtomicSort type
  | .tf1QuantifiedType _ => fail "polymorphic proof-local symbols are unsupported"

private def decodeTopLevelSort : TffTopLevelType → DecodeM LamSort
  | .tffAtomicType sort => decodeAtomicSort sort
  | .tffNonAtomicType sort => decodeNonAtomicSort sort

private partial def symbolDeclaration? : TffAtomTyping → Option (String × TffTopLevelType)
  | .untypedAtomTffTopLevelType atom type => do
    pure (← untypedAtomName atom, type)
  | .tffAtomTyping declaration => symbolDeclaration? declaration

/-- Read a raw inference annotation without decoding its formula.  This first
pass is what lets us discover `new_symbols(skolem, [...])` before a later pass
encounters the symbol in a formula. -/
def inputInference? : TptpInput → Option Inference
  | .annotatedFormula (.thfAnnotated (.mk _ _ _ annotations)) =>
    let (_, _, inference?) := annotation annotations
    inference?
  | .annotatedFormula (.tffAnnotated (.mk _ _ _ annotations)) =>
    let (_, _, inference?) := annotation annotations
    inference?
  | .annotatedFormula (.fofAnnotated (.mk _ _ _ annotations)) =>
    let (_, _, inference?) := annotation annotations
    inference?
  | .annotatedFormula (.cnfAnnotated (.mk _ _ _ annotations)) =>
    let (_, _, inference?) := annotation annotations
    inference?
  | _ => none

/-- Collect and type-check every proof-local symbol declared by Vampire.

Synthetic `etom` IDs are allocated above the IDs already used by the exported
problem.  They are merely stable names for the context-free `LamTerm` phase;
local replay replaces them with checked let-bound Lean expressions. Skolem
symbols and predicates with arguments obtain their sort from a TFF
declaration. Vampire can omit declarations for nullary formula-naming
predicates, which have sort `prop`, just like AVATAR component symbols.
Both kinds of definition must be certified by `new_symbols(definition, [...])`.
The formula decoder still checks every application against the assigned sort,
so this convention cannot silently accept an undeclared predicate with arguments. -/
def decodeDerivedSymbols (problem : TFF.Problem) (proof : TptpFile) :
    Except String (Array DerivedSymbol) := do
  let .mk inputs := proof
  let mut requiredSkolems : Array String := #[]
  let mut differenceWitnesses : Array String := #[]
  let mut quantifierWitnesses : Array String := #[]
  let mut choiceOperators : Array String := #[]
  let mut differenceOperators : Array String := #[]
  let mut avatarDefinitions : Array String := #[]
  let mut predicateDefinitions : Array String := #[]
  for input in inputs do
    if let some inference := inputInference? input then
      if let some info := inference.functionalExtensionality? then
        if info.introduce then
          if differenceOperators.contains info.symbol then
            throw s!"duplicate difference operator `{info.symbol}`"
          differenceOperators := differenceOperators.push info.symbol
      if let some info := inference.choiceAxiom? then
        if info.introduce then
          if choiceOperators.contains info.symbol then
            throw s!"duplicate choice operator `{info.symbol}`"
          choiceOperators := choiceOperators.push info.symbol
      if let some info := inference.quantifierWitness? then
        if info.introduce then
          if quantifierWitnesses.contains info.symbol then
            throw s!"duplicate quantifier witness `{info.symbol}`"
          quantifierWitnesses := quantifierWitnesses.push info.symbol
      if let some info := inference.negativeExtensionality? then
        if differenceWitnesses.contains info.symbol || requiredSkolems.contains info.symbol then
          throw s!"duplicate difference witness `{info.symbol}`"
        differenceWitnesses := differenceWitnesses.push info.symbol
      if let some info := inference.skolemization? then
        for binding in info.bindings do
          unless requiredSkolems.contains binding.symbol do
            requiredSkolems := requiredSkolems.push binding.symbol
      if let some info := inference.predicateDefinition? then
        unless predicateDefinitions.contains info.symbol do
          predicateDefinitions := predicateDefinitions.push info.symbol
      if let some info := inference.avatarDefinition? then
        unless avatarDefinitions.contains info.symbol do
          avatarDefinitions := avatarDefinitions.push info.symbol
  let mut nextEtom := problem.symbols.foldl (init := 0) fun next entry =>
    match entry.2.1 with
    | .etom index => max next (index + 1)
    | _ => next
  for name in differenceWitnesses do
    if requiredSkolems.contains name || predicateDefinitions.contains name || avatarDefinitions.contains name || quantifierWitnesses.contains name then
      throw s!"difference witness `{name}` has conflicting symbol introductions"
  for name in quantifierWitnesses do
    if requiredSkolems.contains name || predicateDefinitions.contains name || avatarDefinitions.contains name then
      throw s!"quantifier witness `{name}` has conflicting symbol introductions"
  for name in choiceOperators do
    if requiredSkolems.contains name || differenceWitnesses.contains name || quantifierWitnesses.contains name ||
        predicateDefinitions.contains name || avatarDefinitions.contains name then
      throw s!"choice operator `{name}` has conflicting symbol introductions"
  for name in differenceOperators do
    if requiredSkolems.contains name || differenceWitnesses.contains name || quantifierWitnesses.contains name ||
        choiceOperators.contains name || predicateDefinitions.contains name || avatarDefinitions.contains name then
      throw s!"difference operator `{name}` has conflicting symbol introductions"
  let mut derived := #[]
  let context : Context := { problem }
  for input in inputs do
    match input with
    | .annotatedFormula (.thfAnnotated (.mk _ _ (.thfAtomTyping declaration) _)) =>
      let rec declared : ThfAtomTyping → Option (String × ThfTopLevelType)
        | .untypedAtomThfTopLevelType atom type => do pure (← untypedAtomName atom, type)
        | .thfAtomTyping inner => declared inner
      if let some (name, type) := declared declaration then
        let kind? : Option DerivedSymbolKind :=
          if differenceOperators.contains name then some .differenceOperator
          else if choiceOperators.contains name then some .choiceOperator
          else if quantifierWitnesses.contains name then some .quantifierWitness
          else if differenceWitnesses.contains name then some .differenceWitness
          else if requiredSkolems.contains name then some .skolem
          else if predicateDefinitions.contains name then some .predicateDefinition
          else none
        if let some kind := kind? then
          if problem.symbols.any (fun entry => entry.1 == name) then
            throw s!"Vampire declared `{name}` as both an input and a fresh proof-local symbol"
          unless derived.any (·.name == name) do
            let parsedSort ← THF.Syntax.sort type
            let sort ← (decodeHigherOrderSort parsedSort).run context
            derived := derived.push { name, term := .etom nextEtom, sort, kind }
            nextEtom := nextEtom + 1
    | .annotatedFormula (.tffAnnotated (.mk _ _ (.tffAtomTyping declaration) _)) =>
      if let some (name, type) := symbolDeclaration? declaration then
        let kind? : Option DerivedSymbolKind :=
          if differenceOperators.contains name then some .differenceOperator
          else if choiceOperators.contains name then some .choiceOperator
          else if quantifierWitnesses.contains name then some .quantifierWitness
          else if differenceWitnesses.contains name then some .differenceWitness
          else if requiredSkolems.contains name then some .skolem
          else if predicateDefinitions.contains name then some .predicateDefinition
          else none
        if let some kind := kind? then
          if problem.symbols.any fun entry => entry.1 == name then
            throw s!"Vampire declared `{name}` as both an input and a fresh proof-local symbol"
          unless derived.any (·.name == name) do
            let sort ← (decodeTopLevelSort type).run context
            derived := derived.push {
              name, term := .etom nextEtom, sort, kind
            }
            nextEtom := nextEtom + 1
    | _ => pure ()
  for name in requiredSkolems ++ differenceWitnesses ++ quantifierWitnesses ++ choiceOperators ++ differenceOperators do
    unless derived.any (·.name == name) do
      throw s!"Vampire used fresh witness `{name}` without a supported type declaration"
  for name in predicateDefinitions do
    unless derived.any (·.name == name) do
      if problem.symbols.any fun entry => entry.1 == name then
        throw s!"Vampire declared `{name}` as both an input and a fresh proof-local symbol"
      -- A nullary predicate needs no domain information: it is a proposition.
      -- Do not guess argument sorts here. If Vampire actually applies this
      -- symbol to arguments, `apply` rejects the formula during decoding.
      derived := derived.push {
        name, term := .etom nextEtom, sort := .base .prop,
        kind := .predicateDefinition
      }
      nextEtom := nextEtom + 1
  for name in avatarDefinitions do
    if problem.symbols.any fun entry => entry.1 == name then
      throw s!"Vampire declared `{name}` as both an input and an AVATAR component"
    if derived.any (·.name == name) then
      throw s!"Vampire reused proof-local symbol `{name}` for an AVATAR component"
    derived := derived.push {
      name, term := .etom nextEtom, sort := .base .prop,
      kind := .avatarDefinition
    }
    nextEtom := nextEtom + 1
  -- SMT-LIB definitions use internal predicates `sFN_f(lhs,rhs)` and
  -- `sPN_p(args)`. Their single-parent `definition_unfolding` step removes
  -- this wrapper. Give it its definitional interpretation already at source
  -- decoding so source-fact verification and all later proofs check it too.
  -- Never reinterpret a symbol from the exported input signature.
  for input in inputs do
    match input with
    | .annotatedFormula (.tffAnnotated (.mk _ _ (.tffAtomTyping declaration) _)) =>
      if let some (name, type) := symbolDeclaration? declaration then
        if problem.symbols.any (fun entry => entry.1 == name) ||
            derived.any (·.name == name) then continue
        let functionWrapper := name.startsWith "sFN_"
        unless functionWrapper || name.startsWith "sPN_" do continue
        let original := (name.drop 4).toString
        let original? := (problem.symbols.find? (fun entry => entry.1 == original)).map
            (fun entry => entry.2)
          <|> (derived.find? (·.name == original)).map (fun entry => (entry.term, entry.sort))
        let some (term, originalSort) := original?
          | throw s!"internal definition predicate `{name}` has no known original symbol `{original}`"
        let sort ← (decodeTopLevelSort type).run context
        let (_, result) := signature originalSort
        let value ← if functionWrapper then do
          let expected := LamSort.func result (.func result (.base .prop))
          unless sort == expected && result != .base .prop do
            throw s!"internal function definition predicate `{name}` has an incompatible type"
          pure (.lam result (.lam result (.mkEq result (.bvar 1) (.bvar 0))))
        else do
          unless sort == originalSort && result == .base .prop do
            throw s!"internal Boolean definition predicate `{name}` has an incompatible type"
          pure term
        derived := derived.push { name, term := value, sort, kind := .internalDefinition }
    | _ => pure ()
  pure derived

end VampireHammer.Replay.Decode.Internal
