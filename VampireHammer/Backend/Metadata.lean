import VampireHammer.Backend.Types
import Tptp

/-!
Decode the generic TPTP annotation grammar into the certificates in
`Backend.Types`. Each `Inference.*?` decoder validates one certificate shape.

This layer does not instantiate variables or build Lean proofs: raw unifier
terms remain `MetadataTerm` until a handler opens the conclusion binders.
-/

namespace VampireHammer.Backend

open Lean Meta Elab Tactic
open Auto.Embedding.Lam
open Tptp.Data

namespace MetadataTerm

/-- Render metadata in TPTP-like syntax for diagnostics and rule traces. -/
partial def toTptp : MetadataTerm → String
  | .atom name => name
  | .variable name => name
  | .application name arguments =>
    s!"{name}({String.intercalate "," (arguments.map toTptp).toList})"
  | .list entries => s!"[{String.intercalate "," (entries.map toTptp).toList}]"
  | .tuple entries => s!"({String.intercalate "," (entries.map toTptp).toList})"
  | .number text => text
  | .distinctObject text => s!"\"{text}\""
  | .annotated head tail => s!"{toTptp head}:{toTptp tail}"
  | .formula => "<formula>"
  | .higherOrder (.ok term) => "$thf(" ++ THF.Syntax.render term ++ ")"
  | .higherOrder (.error message) => "<unsupported THF: " ++ message ++ ">"

private def word : AtomicWord → String
  | .lowerWord (.mk text) => text
  | .singleQuoted (.mk text) => text
  | .backQuoted (.mk (.mk text)) => text

private def variableName : Variable → String
  | .mk (.mk text) => text

private def numberText : Tptp.Data.Number → String
  | .integer (.mk value) => toString value
  | value => reprStr value

/- Convert TPTP's generic annotation AST to the reconstruction API. -/
mutual

private partial def ofGeneralTerm : GeneralTerm → MetadataTerm
  | .generalData (.atomicWord name) => .atom (word name)
  | .generalData (.generalFunction (.mk name args)) => .application (word name) (ofTerms args)
  | .generalData (.variable name) => .variable (variableName name)
  | .generalData (Tptp.Data.GeneralData.number value) => .number (numberText value)
  | .generalData (.distinctObject (.mk text)) => .distinctObject text
  | .generalData (.formulaData (.thfFormula (.thfLogicFormula rawFormula))) =>
    .higherOrder (THF.Syntax.term rawFormula)
  | .generalData (.formulaData _) => .formula
  | .generalDataGeneralTerm head tail => .annotated (ofGeneralData head) (ofGeneralTerm tail)
  | .generalList entries => .list (ofList entries)

private partial def ofGeneralData : GeneralData → MetadataTerm
  | .atomicWord name => .atom (word name)
  | .generalFunction (.mk name args) => .application (word name) (ofTerms args)
  | .variable name => .variable (variableName name)
  | Tptp.Data.GeneralData.number value => .number (numberText value)
  | .distinctObject (.mk text) => .distinctObject text
  | .formulaData (.thfFormula (.thfLogicFormula rawFormula)) =>
    .higherOrder (THF.Syntax.term rawFormula)
  | .formulaData _ => .formula

private partial def ofTerms : GeneralTerms → Array MetadataTerm
  | .mk first rest => #[ofGeneralTerm first] ++ rest.toArray.map fun | .mk term => ofGeneralTerm term

private partial def ofList : GeneralList → Array MetadataTerm
  | .empty => #[]
  | .generalTerms ts => ofTerms ts

end

end MetadataTerm

private def names : GeneralTerms → Array MetadataTerm
  | .mk first rest => #[MetadataTerm.ofGeneralTerm first] ++
    rest.toArray.map fun | .mk entry => MetadataTerm.ofGeneralTerm entry

private def metadataList : UsefulInfo → Array MetadataTerm
  | .mk .empty => #[]
  | .mk (.generalTerms entries) => names entries

private def parentName? : Source → Option String
  | .dagSource (.name (.atomicWord (.lowerWord (.mk text)))) => some text
  | .dagSource (.name (.atomicWord (.singleQuoted (.mk text)))) => some text
  | .dagSource (.name (.atomicWord (.backQuoted (.mk (.mk text))))) => some text
  | _ => none

private def parentRef? : ParentInfo → Option ParentRef
  | .mk source _ => do
    let name ← parentName? source
    pure { name }

private def parentRefs : Parents → Array ParentRef
  | .empty => #[]
  | .parentList (.mk first rest) =>
    (parentRef? first).toArray ++ rest.toArray.flatMap fun | .mk entry => (parentRef? entry).toArray

private def ruleName : InferenceRule → String
  | .mk (.lowerWord (.mk text)) => text
  | .mk (.singleQuoted (.mk text)) => text
  | .mk (.backQuoted (.mk (.mk text))) => text

/-- Preserve a parser inference record in the reconstruction representation. -/
def Inference.ofTptp : InferenceRule → UsefulInfo → Parents → Inference
  | rule, info, parentList =>
    { rule := ruleName rule, info := metadataList info, parents := parentRefs parentList }

/-- Normalize TPTP's internal `introduced(definition, ...)` source to the
same rule-facing representation as ordinary inference annotations. The marker
in the parent position (`[avatar_definition]` or
`[predicate_definition_introduction]`) is provenance, not a proof-DAG edge, so
it becomes the rule name and the node has no logical parents. Unmarked
definitions keep the historical AVATAR interpretation. -/
def Inference.ofDefinition (info : UsefulInfo) (marker : Parents) : Inference :=
  let rule := match (parentRefs marker).map (·.name) with
    | #["predicate_definition_introduction"] => "predicate_definition_introduction"
    | #["function_definition"] => "function_definition"
    | #["fool_ite_definition"] => "fool_ite_definition"
    | #["general_splitting_component_introduction"] => "general_splitting_component_introduction"
    | #["inequality_splitting_name_introduction"] => "inequality_splitting_name_introduction"
    | #["equality_proxy_definition"] => "equality_proxy_definition"
    | _ => "avatar_definition"
  { rule, info := metadataList info, parents := #[] }

/-- Only the EUF conflict marker and the FOOL exhaustiveness and distinctness
axioms are accepted here. Their handlers independently prove the purported theory axiom; other
introduced theory nodes stay unsupported. -/
def Inference.ofTheory? (info : UsefulInfo) : Option Inference := do
  let entries := metadataList info
  let rule ← match entries with
    | #[.atom "theory_tautology_sat_conflict"] => some "theory_tautology_sat_conflict"
    | #[.atom "fool_exhaustiveness_axiom"] => some "fool_exhaustiveness_axiom"
    | #[.atom "fool_distinctness_axiom"] => some "fool_distinctness_axiom"
    | _ => none
  pure { rule, info := #[], parents := #[] }

private def substitution? : MetadataTerm → Option ParentSubstitution
  | .application "subs" #[.atom parent, .list bindings] => do
    let bindings ← bindings.mapM fun
      | .application "b" #[.variable name, term] => some (name, term)
      | _ => none
    pure { parent, bindings }
  | _ => none

private def literal? : MetadataTerm → Option LiteralRef
  | .application "literal" #[.atom parent, .number text] => do
    let index ← text.toNat?
    pure { parent, index }
  | _ => none

/-- Proposed certificate for a pure higher-order specialization. Require a
single unifier record; never infer the selected substitution from the child. -/
def Inference.higherOrderInstantiation? (inference : Inference) :
    Option (Array ParentSubstitution) := do
  guard (#["primitive_instantiation", "heuristic_instantiation", "imitation",
    "projection", "leibniz_equality_elimination", "flex-flex_simplification",
    "flex_flex_simplification"].contains inference.rule)
  let #[.application "unifier" #[.list entries]] := inference.info | none
  let substitutions ← entries.mapM substitution?
  guard (substitutions.size == 1)
  pure substitutions

def Inference.quantifierInstance? (inference : Inference) : Option QuantifierInstanceInfo := do
  guard (inference.rule == "heuristic_instantiation")
  let mut substitutions := #[]
  let mut instance? := none
  for entry in inference.info do
    match entry with
    | .application "unifier" #[.list entries] =>
      guard substitutions.isEmpty
      substitutions ← entries.mapM substitution?
    | .application "quantifier_instance" #[selected, term] =>
      guard instance?.isNone
      instance? := some (← literal? selected, term)
    | _ => none
  let (literal, term) ← instance?
  guard (substitutions.size ≤ 1 && substitutions.all (·.parent == literal.parent))
  pure { substitutions, literal, term }

def Inference.booleanCase? (inference : Inference) : Option BooleanCaseInfo := do
  guard (#["fool_paramodulation", "cases_simplifying"].contains inference.rule)
  let #[.application "boolean_case" arguments] := inference.info | none
  let (selected, term, truth, occurrence?) ← match arguments with
    | #[selected, term, .atom truth] => pure (selected, term, truth, none)
    | #[selected, term, .atom truth, .application "occurrence" #[.number number]] =>
      pure (selected, term, truth, some (← number.toNat?))
    | _ => none
  let literal ← literal? selected
  guard (truth == "true" || truth == "false")
  pure { literal, term, replaceWithTrue := truth == "true", occurrence? }

private def witnessBinderMapping? (info : Array MetadataTerm) :
    Option (Option (Array (String × String))) := do
  let entries := info.filter fun
    | .application "binder_mapping" _ | .atom "binder_mapping" => true
    | _ => false
  if entries.isEmpty then return none
  let #[.application "binder_mapping" #[.list bindings]] := entries | none
  let mapping ← bindings.mapM fun
    | .application "b" #[.variable source, .variable target] => some (source, target)
    | _ => none
  guard ((mapping.map (·.1)).toList.eraseDups.length == mapping.size)
  guard ((mapping.map (·.2)).toList.eraseDups.length == mapping.size)
  pure (some mapping)

/-- A unifier record that binds no variable. Vampire attaches one to
clausification steps that only select a literal of their parent. -/
private def emptyUnifier : MetadataTerm → Bool
  | .application "unifier" #[.list entries] =>
    entries.all fun entry => (substitution? entry).any (·.bindings.isEmpty)
  | _ => false

def Inference.quantifierWitness? (inference : Inference) : Option QuantifierWitnessInfo := do
  guard (#["sigma_proxy_clausification", "sigma_proxy_clausification_(simplifying)"].contains inference.rule)
  let binderMapping? ← witnessBinderMapping? inference.info
  let core := inference.info.filter fun
    | .application "binder_mapping" _ => false
    | entry => !emptyUnifier entry
  let (introduce, selected, symbol, raw) ← match core with
    | #[.application "new_symbols" #[.atom "skolem", .list #[.atom declared]],
        .application "quantifier_witness" #[selected, .atom symbol, .list raw]] =>
      guard (declared == symbol)
      pure (true, selected, symbol, raw)
    | #[.application "quantifier_witness" #[selected, .atom symbol, .list raw]] =>
      pure (false, selected, symbol, raw)
    | _ => none
  let literal ← literal? selected
  -- Variable dependencies name parent binders; anything else is a term.
  match raw.mapM fun | .variable name => some name | _ => none with
  | some dependencies =>
    guard (dependencies.toList.eraseDups.length == dependencies.size)
    pure { literal, symbol, dependencies, binderMapping?, introduce }
  | none =>
    pure { literal, symbol, dependencies := #[], binderMapping?, dependencyTerms := raw, introduce }

def Inference.choiceAxiom? (inference : Inference) : Option ChoiceAxiomInfo := do
  guard (#["Hilbertian_choice_axiom_instance", "hilbertian_choice_axiom_instance"].contains inference.rule)
  let (entry, introduced) ← match inference.info with
    | #[.application "new_symbols" #[.atom "choice", .list #[.atom declared]], entry] =>
      pure (entry, some declared)
    | #[entry] => pure (entry, none)
    | _ => none
  let .application "choice_axiom" #[.atom symbol, predicate, .variable variableName] := entry | none
  guard (introduced.isNone || introduced == some symbol)
  pure { symbol, predicate, variableName, introduce := introduced.isSome }

def Inference.functionalExtensionality? (inference : Inference) : Option FunctionalExtensionalityInfo := do
  guard (inference.rule == "functional_extensionality_axiom")
  let (entry, introduced) ← match inference.info with
    | #[.application "new_symbols" #[.atom "extensionality", .list #[.atom declared]], entry] =>
      pure (entry, some declared)
    | #[entry] => pure (entry, none)
    | _ => none
  let .application "extensionality_axiom" #[.atom symbol, .variable leftVariable, .variable rightVariable] := entry | none
  guard (introduced.isNone || introduced == some symbol)
  guard (leftVariable != rightVariable)
  pure { symbol, leftVariable, rightVariable, introduce := introduced.isSome }

/-- Detect the annotation even when malformed, so it cannot fall through to
the legacy identity conversion. -/
def Inference.hasAvatarMap (inference : Inference) : Bool :=
  inference.info.any fun
    | .application "avatar_map" _ => true
    | .atom "avatar_map" => true
    | _ => false

def Inference.avatarMap? (inference : Inference) : Option (Array AvatarMapping) := do
  guard (inference.rule == "sat_conversion")
  let #[.application "avatar_map" #[.list entries]] := inference.info | none
  entries.mapM fun
    | .application "map" #[source, .application sign #[.atom symbol], .atom definition] => do
      let source ← literal? source
      guard (sign == "positive" || sign == "negative")
      pure { source, symbol, positive := sign == "positive", definition }
    | _ => none

/-- Decode the common certificate now printed for ordinary resolution and
forward subsumption resolution: one unifier plus one selected occurrence per
parent. Unrecognised entries remain available through `Inference.info`. -/
private def Inference.binaryResolutionInfo? (inference : Inference)
    (expectedRule : String) : Option ResolutionInfo := do
  guard (inference.rule == expectedRule)
  let mut substitutions := #[]
  let mut resolvedLiterals := #[]
  for entry in inference.info do
    match entry with
    | .application "unifier" #[.list entries] =>
      let some parsed := entries.mapM substitution?
        | continue
      substitutions := substitutions ++ parsed
    | .application "resolved_literals" #[.list entries] =>
      let some parsed := entries.mapM literal?
        | continue
      resolvedLiterals := resolvedLiterals ++ parsed
    | _ => continue
  pure { substitutions, resolvedLiterals }

/-- Decode an ordinary binary-resolution certificate. -/
def Inference.resolution? (inference : Inference) : Option ResolutionInfo :=
  inference.binaryResolutionInfo? "resolution"

/-- `extensionality_resolution` resolves a positive variable equation with a
negative equation; its certificate has the binary-resolution shape. -/
def Inference.extensionalityResolution? (inference : Inference) : Option ResolutionInfo :=
  inference.binaryResolutionInfo? "extensionality_resolution"

/-- `forward_literal_rewriting` is resolution with a two-literal side clause
whose selected literal matches the complement of the rewritten one. Besides
`rewritten_literal`, it prints the two resolved positions. -/
def Inference.forwardLiteralRewriting? (inference : Inference) : Option ResolutionInfo :=
  inference.binaryResolutionInfo? "forward_literal_rewriting"

/-- `unit_resulting_resolution`: one `subs` record per parent, in parent
order (a unit clause may occur in several positions), and a
`literal(nucleus, i), literal(unit, 0)` pair per unit. -/
def Inference.unitResultingResolution? (inference : Inference) : Option ResolutionInfo :=
  inference.binaryResolutionInfo? "unit_resulting_resolution"

/-- `constrained_resolution`: binary resolution modulo the printed
`constraints([disequality(sort, left, right), ...])`. -/
def Inference.constrainedResolution? (inference : Inference) :
    Option ConstrainedResolutionInfo := do
  let resolution ← inference.binaryResolutionInfo? "constrained_resolution"
  let mut constraintCount := 0
  for entry in inference.info do
    if let .application "constraints" #[.list entries] := entry then
      constraintCount := constraintCount + entries.size
  guard (constraintCount > 0)
  pure { resolution, constraintCount }

/-- Decode Vampire's current forward-subsumption certificate.

The rule is spelled `removed_literals` despite naming one selected main-clause
occurrence. Accept the former singular spelling as well so stored proof files
remain replayable. -/
def Inference.forwardSubsumptionResolution? (inference : Inference) : Option ForwardSubsumptionInfo := do
  -- Backward subsumption resolution prints the same certificate, with the
  -- simplified (main) clause as the first parent.
  guard (inference.rule == "forward_subsumption_resolution" ||
    inference.rule == "backward_subsumption_resolution")
  let mut substitutions := #[]
  let mut removedLiteral? := none
  for entry in inference.info do
    match entry with
    | .application "unifier" #[.list entries] =>
      let some parsed := entries.mapM substitution? | continue
      substitutions := substitutions ++ parsed
    | .application "removed_literals" #[literal]
    | .application "removed_literal" #[literal] =>
      if let some parsed := literal? literal then
        removedLiteral? := some parsed
    | _ => continue
  let some removedLiteral := removedLiteral? | none
  pure { substitutions, removedLiteral }

/-- Decode the one-parent factoring certificate emitted by Vampire.
Condensation prints the same shape: the parent substitution and the removed
occurrence, which duplicates another literal after instantiation. -/
private def Inference.duplicateRemovalInfo? (inference : Inference) (expectedRule : String) :
    Option FactoringInfo := do
  guard (inference.rule == expectedRule)
  let mut substitutions := #[]
  let mut removedLiteral? := none
  for entry in inference.info do
    match entry with
    | .application "unifier" #[.list entries] =>
      let some parsed := entries.mapM substitution? | continue
      substitutions := substitutions ++ parsed
    | .application "removed_literal" #[literal]
    | .application "removed_literals" #[literal] =>
      if let some removedLiteral := literal? literal then
        removedLiteral? := some removedLiteral
    | _ => continue
  let some removedLiteral := removedLiteral? | none
  pure { substitutions, removedLiteral }

def Inference.factoring? (inference : Inference) : Option FactoringInfo :=
  inference.duplicateRemovalInfo? "factoring"

def Inference.condensation? (inference : Inference) : Option FactoringInfo :=
  inference.duplicateRemovalInfo? "condensation"

/-- Decode the unifier emitted for `equality_resolution`. -/
def Inference.equalityResolution? (inference : Inference) : Option EqualityResolutionInfo := do
  -- `subsumption_equality_resolution` also deletes one negative equation
  -- made reflexive by its unifier; its `removed_literals` entry is redundant.
  guard (inference.rule == "equality_resolution" ||
    inference.rule == "subsumption_equality_resolution")
  let mut substitutions := #[]
  for entry in inference.info do
    match entry with
    | .application "unifier" #[.list entries] =>
      let some parsed := entries.mapM substitution? | continue
      substitutions := substitutions ++ parsed
    | _ => continue
  guard (!substitutions.isEmpty)
  pure { substitutions }

/-- Decode the unifier emitted for `equality_factoring`. The current backend
does not require literal positions because it checks every candidate pair
against the instantiated conclusion. -/
def Inference.equalityFactoring? (inference : Inference) : Option EqualityFactoringInfo := do
  guard (inference.rule == "equality_factoring")
  let mut substitutions := #[]
  for entry in inference.info do
    match entry with
    | .application "unifier" #[.list entries] =>
      let some parsed := entries.mapM substitution? | continue
      substitutions := substitutions ++ parsed
    | _ => continue
  guard (!substitutions.isEmpty)
  pure { substitutions }

/-- Decode the metadata used by the first ground-superposition handler. -/
def Inference.superposition? (inference : Inference) : Option SuperpositionInfo := do
  guard (inference.rule == "superposition")
  let mut substitutions := #[]
  let mut rewrittenLiteral? := none
  for entry in inference.info do
    match entry with
    | .application "unifier" #[.list entries] =>
      let some parsed := entries.mapM substitution? | continue
      substitutions := substitutions ++ parsed
    | .application "rewritten_literal" #[literal] =>
      if let some rewrittenLiteral := literal? literal then
        rewrittenLiteral? := some rewrittenLiteral
    | _ => continue
  let some rewrittenLiteral := rewrittenLiteral? | none
  pure { substitutions, rewrittenLiteral }

/-- Decode a forward-demodulation certificate.

Besides the usual parent-local substitutions, newer Vampire output records
`rewritten_literal(literal(parent,index))`. We require that annotation rather
than inferring the rewritten parent from its position in the proof DAG. -/
def Inference.forwardDemodulation? (inference : Inference) : Option ForwardDemodulationInfo := do
  guard (inference.rule == "forward_demodulation")
  let mut substitutions := #[]
  let mut rewrittenLiteral? := none
  for entry in inference.info do
    match entry with
    | .application "unifier" #[.list entries] =>
      let some parsed := entries.mapM substitution? | continue
      substitutions := substitutions ++ parsed
    | .application "rewritten_literal" #[literal] =>
      if let some rewrittenLiteral := literal? literal then
        rewrittenLiteral? := some rewrittenLiteral
    | _ => continue
  let some rewrittenLiteral := rewrittenLiteral? | none
  pure { substitutions, rewrittenLiteral }

/-- Decode the explicit rewrite certificate shared by demodulation, inner
rewriting, and superposition with abstraction. Terms are already in the
conclusion variable namespace; parent substitutions are applied separately. -/
def Inference.certifiedRewrite? (inference : Inference) : Option CertifiedRewriteInfo := do
  guard (#["backward_demodulation", "forward_subsumption_demodulation",
      "backward_subsumption_demodulation",
    "inner_rewriting", "constrained_superposition", "definition_unfolding"].contains inference.rule)
  let mut substitutions := #[]
  let mut rewrittenLiterals := #[]
  let mut equality? := none
  let mut from? := none
  let mut to? := none
  let mut constraints := #[]
  let mut occurrence? := none
  for entry in inference.info do
    match entry with
    | .application "unifier" #[.list entries] =>
      substitutions := substitutions ++ (← entries.mapM substitution?)
    | .application "rewritten_literal" #[literal] =>
      rewrittenLiterals := rewrittenLiterals.push (← literal? literal)
    | .application "rewritten_literals" #[.list literals] =>
      rewrittenLiterals := rewrittenLiterals ++ (← literals.mapM literal?)
    | .application "rewrite" #[.list entries] =>
      for entry in entries do
        match entry with
        | .application "equality" #[literal] => equality? := literal? literal
        | .application "from" #[term] => from? := some term
        | .application "to" #[term] => to? := some term
        | .application "occurrence" arguments =>
          guard occurrence?.isNone
          let #[.number number] := arguments | none
          occurrence? := some (← number.toNat?)
        | .atom "occurrence" => none
        | _ => pure ()
    | .application "constraints" #[.list entries] => constraints := entries
    | _ => pure ()
  guard (!rewrittenLiterals.isEmpty)
  let equality ← equality?
  let fromTerm ← from?
  let toTerm ← to?
  pure { substitutions, rewrittenLiterals, equality, fromTerm, toTerm, constraints, occurrence? }

/-- Mocked extension of the Vampire replay protocol; no witness is inferred
from its name or its type declaration alone. -/
def Inference.negativeExtensionality? (inference : Inference) : Option NegativeExtensionalityInfo := do
  guard (inference.rule == "negative_extensionality")
  let binderMapping? ← witnessBinderMapping? inference.info
  let mut declared := #[]
  let mut witnesses := #[]
  for entry in inference.info do
    match entry with
    | .application "new_symbols" #[.atom "skolem", .list names] =>
      declared := declared ++ (← names.mapM fun | .atom name => some name | _ => none)
    | .application "extensionality_witness" #[literal, .atom symbol, .list dependencies] =>
      let literal ← literal? literal
      let dependencies ← dependencies.mapM fun | .variable name => some name | _ => none
      witnesses := witnesses.push { literal, symbol, dependencies : NegativeExtensionalityInfo }
    | _ => pure ()
  let #[info] := witnesses | none
  guard (declared == #[info.symbol])
  guard (info.dependencies.toList.eraseDups.length == info.dependencies.size)
  pure { info with binderMapping? }

/-- Decode the one fresh propositional symbol certified by an AVATAR
definition. The initial implementation intentionally accepts one nullary
symbol per node, which is the certificate shape emitted by Vampire. -/
def Inference.avatarDefinition? (inference : Inference) : Option AvatarDefinitionInfo := do
  guard (inference.rule == "avatar_definition")
  for entry in inference.info do
    match entry with
    | .application "new_symbols" #[.atom "definition", .list #[.atom symbol]] =>
      return { symbol }
    | _ => continue
  none

/-- Parentless definitions that introduce one fresh symbol whose meaning
replay reads off the definition itself (see `Replay/Symbols.lean`). -/
def symbolDefinitionRules : Array String :=
  #["predicate_definition_introduction", "function_definition", "fool_ite_definition",
    "general_splitting_component_introduction", "inequality_splitting_name_introduction",
    "equality_proxy_definition"]

/-- Decode the one fresh symbol certified by a formula-naming definition, or
by one of the other `symbolDefinitionRules`. -/
def Inference.predicateDefinition? (inference : Inference) : Option PredicateDefinitionInfo := do
  guard (symbolDefinitionRules.contains inference.rule)
  for entry in inference.info do
    match entry with
    | .application "new_symbols" #[.atom "definition", .list #[.atom symbol]] =>
      return { symbol }
    | _ => continue
  none

/-- Decode the extra AVATAR split annotation requested with
`--proof_extra avatar_split`.

Vampire writes one `b(sourceVariable, arg(definitionParent, definitionVariable))`
entry for every source variable whose value comes from an expanded split
definition.  Keep it separate from calculus substitutions: `arg(...)` is a
reference to a target binder, not a TPTP term that `materializeTerm` can
interpret. -/
def Inference.avatarSplit? (inference : Inference) : Option AvatarSplitInfo := do
  guard (inference.rule == "avatar_split_clause")
  for entry in inference.info do
    match entry with
    | .application "post_rewrite_instantiation" #[.list entries] =>
      let bindings ← entries.mapM fun
        | .application "b" #[.variable sourceVariable,
            .application "arg" #[.atom definitionParent, .variable definitionVariable]] =>
          some { sourceVariable, definitionParent, definitionVariable }
        | _ => none
      guard (!bindings.isEmpty)
      return { bindings }
    | _ => continue
  none

/-- Decode all replacements certified by a Vampire `skolemize` node.

Both `new_symbols(skolem, [...])` and one `skolemize(variable, replacement)`
entry per symbol are required.  This rejects an incidental term named `sK0`
and also rejects incomplete multi-symbol annotations before replay reaches
Lean metaprogramming. -/
def Inference.skolemization? (inference : Inference) : Option SkolemizationInfo := do
  guard (inference.rule == "skolemize" || inference.rule == "skolemisation")
  let mut declared : Array String := #[]
  let mut bindings : Array SkolemBinding := #[]
  for entry in inference.info do
    match entry with
    | .application "new_symbols" #[.atom "skolem", .list symbols] =>
      let names? := symbols.mapM fun
        | .atom name => some name
        | _ => none
      match names? with
      | some names => declared := declared ++ names
      | none => continue
    | .application "skolemize" #[.variable variableName, replacement] =>
      match replacement with
      | .atom symbol =>
        bindings := bindings.push { existentialVariable := variableName, symbol, arguments := #[] }
      | .application symbol arguments =>
        let arguments? := arguments.mapM fun
          | .variable name => some name
          | _ => none
        match arguments? with
        | some arguments =>
          bindings := bindings.push { existentialVariable := variableName, symbol, arguments }
        | none => continue
      | _ => continue
    | _ => continue
  guard (!bindings.isEmpty)
  -- Every replacement must be a declared fresh symbol, and every declared
  -- symbol must have one replacement.  Duplicates would make the local `let`
  -- environment ambiguous, so reject them rather than choosing one silently.
  guard (bindings.all (fun binding => declared.contains binding.symbol))
  guard (declared.all fun symbol => (bindings.filter (·.symbol == symbol)).size == 1)
  guard (bindings.all fun binding =>
    (bindings.filter (·.existentialVariable == binding.existentialVariable)).size == 1)
  pure { bindings }

/-- Decode the permutation carried by an explicit parser-side clause bridge.
The entry at output position `i` is the source-clause position that supplies
that literal. -/
def Inference.associativityCommutativity? (inference : Inference) : Option (Array Nat) := do
  guard (inference.rule == "associativity_commutativity")
  for entry in inference.info do
    match entry with
    | .application "permutation" #[.list entries] =>
      return ← entries.mapM fun
        | .number text => text.toNat?
        | _ => none
    | _ => continue
  none

/-- Recognize partial certificates as well, so malformed annotations cannot
silently fall back to searching for a different derivation. -/
def Inference.hasCnfCertificate (inference : Inference) : Bool :=
  inference.info.any fun
    | .application name _ => #["binder_mapping", "literal_permutation", "swapped_equalities"].contains name
    | _ => false

def Inference.cnfCertificate? (inference : Inference) : Option CnfCertificate := do
  guard (inference.rule == "cnf_transformation")
  let entry (name : String) : Option (Array MetadataTerm) := do
    let entries := inference.info.filter fun
      | .application key _ => key == name
      | _ => false
    guard (entries.size == 1)
    let value : MetadataTerm ← entries[0]?
    match value with
    | .application _ #[.list values] => pure values
    | _ => none
  let binders ← (← entry "binder_mapping").mapM fun
    | .application "b" #[.variable source, .variable target] => some (source, target)
    | _ => none
  let indices (name : String) := do
    (← entry name).mapM fun
      | .number value => value.toNat?
      | _ => none
  let permutation ← indices "literal_permutation"
  let swapped ← indices "swapped_equalities"
  pure { binders, permutation, swapped }

end VampireHammer.Backend
