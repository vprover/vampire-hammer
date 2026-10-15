import VampireHammer.Preprocess.Basic

/-!
Generic TPTP annotation helpers, selected literal occurrences, and syntax-level substitutions.
-/

namespace VampireHammer.Preprocess.Internal

open Tptp.Data

/-! ## Small AST utilities

The TPTP parser keeps generic annotations in `GeneralTerm`.  The utilities in
this section only inspect the small `inference(...)` fragment needed to change
the names and indices of a resolution certificate.  Keeping this code here,
rather than in `Backend`, makes the boundary explicit: the backend receives a
certificate which has already been put into its intended surface form.
-/

def wordText : AtomicWord → String
  | .lowerWord (.mk text) => text
  | .singleQuoted (.mk text) => text
  | .backQuoted (.mk (.mk text)) => text

def nameText? : Name → Option String
  | .atomicWord word => some (wordText word)
  | .integer _ => none

def lowerName (text : String) : Name :=
  .atomicWord (.lowerWord (.mk text))

def atom (text : String) : GeneralTerm :=
  .generalData (.atomicWord (.lowerWord (.mk text)))

def number (value : Nat) : GeneralTerm :=
  .generalData (.number (.integer (.mk value)))

private def terms? : List GeneralTerm → Option GeneralTerms
  | [] => none
  | first :: rest => some (.mk first (rest.map CommaGeneralTerm.mk))

def list (entries : List GeneralTerm) : GeneralTerm :=
  match terms? entries with
  | none => .generalList .empty
  | some entries => .generalList (.generalTerms entries)

def application (name : String) (arguments : List GeneralTerm) : GeneralTerm :=
  match terms? arguments with
  | none => atom name
  | some arguments => .generalData (.generalFunction (.mk (.lowerWord (.mk name)) arguments))

private def termsToList : GeneralTerms → List GeneralTerm
  | .mk first rest => first :: rest.map (fun | .mk item => item)

def listToList : GeneralList → List GeneralTerm
  | .empty => []
  | .generalTerms terms => termsToList terms

def application? : GeneralTerm → Option (String × List GeneralTerm)
  | .generalData (.generalFunction (.mk name arguments)) => some (wordText name, termsToList arguments)
  | _ => none

private def atomText? : GeneralTerm → Option String
  | .generalData (.atomicWord name) => some (wordText name)
  | _ => none

def nat? : GeneralTerm → Option Nat
  | .generalData (.number (.integer (.mk value))) => value.toNat?
  | _ => none

def infoToList : UsefulInfo → List GeneralTerm
  | .mk info => listToList info

def info (entries : List GeneralTerm) : UsefulInfo :=
  .mk <| match terms? entries with
    | none => .empty
    | some entries => .generalTerms entries

private def parentName? : ParentInfo → Option String
  | .mk (.dagSource (.name name)) _ => nameText? name
  | _ => none

def parentNames : Parents → Option (List String)
  | .empty => some []
  | .parentList (.mk first rest) => do
    let first ← parentName? first
    let rest ← rest.mapM fun | .mk parent => parentName? parent
    pure (first :: rest)

def parents (names : List String) : Parents :=
  match names with
  | [] => .empty
  | first :: rest =>
    let parent (name : String) : ParentInfo :=
      .mk (.dagSource (.name (lowerName name))) .nothing
    .parentList (.mk (parent first) (rest.map fun name => .mk (parent name)))

def ruleText : InferenceRule → String
  | .mk word => wordText word

def resolutionRecord? : Annotations → Option (InferenceRule × UsefulInfo × Parents × OptionalInfo)
  | .sourceOptionalInfo (.dagSource (.inferenceRecord (.mk rule details proofParents))) optional
    => guard (ruleText rule == "resolution") *> some (rule, details, proofParents, optional)
  | _ => none

def resolutionAnnotations (rule : InferenceRule) (details : UsefulInfo)
    (proofParents : Parents) (optional : OptionalInfo) : Annotations :=
  .sourceOptionalInfo (.dagSource (.inferenceRecord (.mk rule details proofParents))) optional

def forwardSubsumptionRecord? : Annotations →
    Option (InferenceRule × UsefulInfo × Parents × OptionalInfo)
  | .sourceOptionalInfo (.dagSource (.inferenceRecord (.mk rule details proofParents))) optional
    => guard (ruleText rule == "forward_subsumption_resolution") *>
      some (rule, details, proofParents, optional)
  | _ => none

/-- Recognize equality resolution while retaining its original certificate.

Unlike ordinary resolution, this one-parent rule does not identify the removed
literal by position.  Its `unifier` makes a negative equality reflexive; the
preprocessing pass below recovers that occurrence from the instantiated parent
syntax. -/
def equalityResolutionRecord? : Annotations →
    Option (InferenceRule × UsefulInfo × Parents × OptionalInfo)
  | .sourceOptionalInfo (.dagSource (.inferenceRecord (.mk rule details proofParents))) optional
    => guard (ruleText rule == "equality_resolution") *>
      some (rule, details, proofParents, optional)
  | _ => none

/-- Recognize Vampire's annotation-free duplicate-contraction rule. -/
def duplicateLiteralRemovalRecord? : Annotations → Option Parents
  | .sourceOptionalInfo (.dagSource (.inferenceRecord (.mk rule _ proofParents))) _ =>
    guard (ruleText rule == "duplicate_literal_removal") *> some proofParents
  | _ => none

/-! ## Resolution metadata

`ResolutionSelection` is intentionally a parser-side type.  It contains no
decoded formulas and no Lean values: it merely says which source spelling and
literal position Vampire recorded for one parent.
-/

structure ResolutionSelection where
  reportedParent : String
  index : Nat

private def selection? : GeneralTerm → Option ResolutionSelection
  | entry => do
  let (name, arguments) ← application? entry
  guard (name == "literal")
  let [parent, index] := arguments | none
  pure { reportedParent := ← atomText? parent, index := ← nat? index }

def selections? (details : UsefulInfo) : Option (List ResolutionSelection) := do
  let metadata ← (infoToList details).find? fun entry =>
    match application? entry with
    | some ("resolved_literals", _) => true
    | _ => false
  let (_, arguments) ← application? metadata
  let [entries] := arguments | none
  let .generalList entries := entries | none
  (listToList entries).mapM selection?

/-- Read the selected main-parent occurrence from Vampire's current
`forward_subsumption_resolution` certificate.

Unlike ordinary resolution, forward subsumption does not print the selected
side occurrence: it prints only the literal deleted from the main clause.  The
new Vampire spelling is plural (`removed_literals`) although its argument is
one `literal(parent, index)` term.  Accepting the earlier singular spelling
keeps archived certificates usable too. -/
def removedLiteral? (details : UsefulInfo) : Option ResolutionSelection := do
  let metadata ← (infoToList details).find? fun entry =>
    match application? entry with
    | some ("removed_literals", _) | some ("removed_literal", _) => true
    | _ => false
  let (_, arguments) ← application? metadata
  let [literal] := arguments | none
  selection? literal

private def rewriteSubstitutions (parentNames : List String) : GeneralTerm → GeneralTerm
  | entry => match application? entry with
    | some ("unifier", [entries]) =>
      match entries with
      | .generalList values =>
        let values := List.zipWith (fun value parent =>
          match application? value with
          | some ("subs", [_oldParent, bindings]) => application "subs" [atom parent, bindings]
          | _ => value) (listToList values) parentNames
        application "unifier" [list values]
      | _ => entry
    | _ => entry

private def rewriteSelections (parentNames : List String) (indices : List Nat) : GeneralTerm → GeneralTerm
  | entry => match application? entry with
    | some ("resolved_literals", [entries]) =>
      match entries with
      | .generalList values =>
        let values := List.zipWith (fun (value, parent) index =>
            match application? value with
            | some ("literal", [_oldParent, _oldIndex]) =>
              application "literal" [atom parent, number index]
            | _ => value) (List.zipWith (fun value parent => (value, parent))
              (listToList values) parentNames) indices
        application "resolved_literals" [list values]
      | _ => entry
    | _ => entry

def rewriteResolutionDetails (details : UsefulInfo) (parentNames : List String)
    (indices : List Nat) : UsefulInfo :=
  info <| (infoToList details).map (rewriteSelections parentNames indices ∘ rewriteSubstitutions parentNames)

/-- Rewrite the one main-parent position in a forward-subsumption certificate.

This is deliberately separate from `rewriteResolutionDetails`: the latter
rewrites a list with one entry per parent, while `removed_literals` contains
exactly one direct `literal(...)` argument. -/
def rewriteForwardSubsumptionDetails (details : UsefulInfo)
    (parentReplacements : List (String × String)) (mainParent : String) (mainIndex : Nat) : UsefulInfo :=
  let replacementFor (reported : String) : String :=
    (parentReplacements.find? (fun (source, _) => source == reported)).map Prod.snd |>.getD reported
  let rewriteSubstitution : GeneralTerm → GeneralTerm
    | entry => match application? entry with
      | some ("subs", [reported, bindings]) =>
        match atomText? reported with
        | some reported => application "subs" [atom (replacementFor reported), bindings]
        | none => entry
      | _ => entry
  let rewriteEntry : GeneralTerm → GeneralTerm
    | entry => match application? entry with
      | some ("unifier", [entries]) =>
        match entries with
        | .generalList values => application "unifier" [list ((listToList values).map rewriteSubstitution)]
        | _ => entry
      | some ("removed_literals", [_]) =>
        application "removed_literals" [application "literal" [atom mainParent, number mainIndex]]
      | some ("removed_literal", [_]) =>
        application "removed_literal" [application "literal" [atom mainParent, number mainIndex]]
      | _ => entry
  info <| (infoToList details).map rewriteEntry

/-- A substitution is still represented entirely in TPTP syntax.  We only
interpret enough of Vampire's `unifier([subs(...)])` annotation to instantiate
the predicate arguments occurring in a clause tail. -/
abbrev Substitution := List (String × TffTerm)

def variableText : Variable → String
  | .mk (.mk text) => text

private def variableOf (text : String) : Variable :=
  .mk (.mk text)

private def variableTerm (text : String) : TffTerm :=
  .tffLogicFormula (.tffUnitaryFormula (.txfUnitaryFormula (.mk (variableOf text))))

private def constantTerm (text : String) : TffTerm :=
  .tffLogicFormula (.tffUnitaryFormula (.tffAtomicFormula
    (.tffPlainAtomic (.constant (.mk (.mk (.lowerWord (.mk text))))))))

private def tffArguments? : List TffTerm → Option TffArguments
  | [] => none
  | first :: rest => some (.mk first (rest.map CommaTffTerm.mk))

private partial def tffTerm? : GeneralTerm → Option TffTerm
  | .generalData (.variable name) => some (variableTerm (variableText name))
  | .generalData (.atomicWord name) => some (constantTerm (wordText name))
  | .generalData (.generalFunction (.mk name arguments)) => do
    let arguments ← termsToList arguments |>.mapM tffTerm?
    let arguments ← tffArguments? arguments
    pure <| .tffLogicFormula (.tffUnitaryFormula (.tffAtomicFormula
      (.tffPlainAtomic (.functorTffArguments (.mk name) arguments))))
  | _ => none

private def substitution? : GeneralTerm → Option (String × Substitution)
  | entry => do
  let (name, arguments) ← application? entry
  guard (name == "subs")
  let [parent, bindings] := arguments | none
  let parent ← atomText? parent
  let .generalList bindings := bindings | none
  let bindings ← (listToList bindings).mapM fun binding => do
    let (name, arguments) ← application? binding
    guard (name == "b")
    let [boundVar, value] := arguments | none
    let .generalData (.variable boundVar) := boundVar | none
    pure (variableText boundVar, ← tffTerm? value)
  pure (parent, bindings)

def substitutions? (details : UsefulInfo) : Option (List (String × Substitution)) := do
  let metadata ← (infoToList details).find? fun entry =>
    match application? entry with
    | some ("unifier", _) => true
    | _ => false
  let (_, arguments) ← application? metadata
  let [entries] := arguments | none
  let .generalList entries := entries | none
  (listToList entries).mapM substitution?

end VampireHammer.Preprocess.Internal
