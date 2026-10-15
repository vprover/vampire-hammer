import Tptp
import VampireHammer.THF.Syntax

/-!
A deliberately small TPTP writer for the TF0/TSTP fragment used by this
project. The upstream parser is read-only, so the standalone preprocessor
needs a writer to make its transformed AST useful outside Lean.

Every unsupported grammar alternative returns an error. This is preferable to
quietly omitting certificate data or emitting text with a different meaning.
-/

namespace VampireHammer.TptpPrinter

open Tptp.Data

abbrev PrintM := Except String

private def join (separator : String) (items : List String) : String :=
  String.intercalate separator items

private def atomicWord : AtomicWord → String
  | .lowerWord (.mk text) => text
  | .singleQuoted (.mk text) => s!"'{text}'"
  | .backQuoted (.mk (.mk text)) => s!"`{text}"

private def nameText : Name → String
  | .atomicWord word => atomicWord word
  | .integer (.mk value) => toString value

private def varText : Variable → String
  | .mk (.mk text) => text

private def functorText : Functor → String
  | .mk word => atomicWord word

private def constantText : Constant → String
  | .mk func => functorText func

private def definedFunctor : DefinedFunctor → String
  | .mk (.mk (.mk text)) => "$" ++ text

private def definedConstant : DefinedConstant → String
  | .mk functor => definedFunctor functor

private def number : Number → PrintM String
  | .integer (.mk value) => pure (toString value)
  | .rational (.mk numerator denominator) => pure s!"{numerator}/{denominator}"
  | .real (.mk mantissa exponent) => pure s!"{mantissa}E{exponent}"

mutual

private partial def tffArguments : TffArguments → PrintM String
  | .mk first rest => do
    let rest ← rest.mapM fun | .mk term => tffTerm term
    pure (join ", " ((← tffTerm first) :: rest))

private partial def tffTypeArguments : TffTypeArguments → PrintM String
  | .tffAtomicType first => tffAtomicType first
  | .tffAtomicTypeTffTypeArguments first rest => do
    pure <| (← tffAtomicType first) ++ ", " ++ (← tffTypeArguments rest)

private partial def tffVariable : TffVariable → PrintM String
  | .tffTypedVariable (.mk boundVar sort) => do
    pure <| (varText boundVar) ++ " : " ++ (← tffAtomicType sort)
  | .variable boundVar => pure (varText boundVar)

private partial def tffVariables : TffVariableList → PrintM String
  | .tffVariable boundVar => tffVariable boundVar
  | .tffVariableTffVariableList boundVar rest => do
    pure <| (← tffVariable boundVar) ++ ", " ++ (← tffVariables rest)

private partial def tffAtomicType : TffAtomicType → PrintM String
  | .typeConstant (.mk (.mk word)) => pure (atomicWord word)
  | .definedType (.mk (.mk (.mk word))) => pure ("$" ++ word)
  | .variable boundVar => pure (varText boundVar)
  | .typeFunctorTffTypeArguments (.mk word) arguments => do
    pure <| (atomicWord word) ++ "(" ++ (← tffTypeArguments arguments) ++ ")"
  | .tffAtomicType sort => tffAtomicType sort
  | .txfTupleType (.mk types) => do pure <| "(" ++ (← tffTypeList types) ++ ")"

private partial def tffUnitaryType : TffUnitaryType → PrintM String
  | .tffAtomicType sort => tffAtomicType sort
  | .tffXprodType product => do pure <| "(" ++ (← tffXprodType product) ++ ")"

private partial def tffXprodType : TffXprodType → PrintM String
  | .tffUnitaryTypeTffAtomicType left right => do
    pure <| (← tffUnitaryType left) ++ " * " ++ (← tffAtomicType right)
  | .tffXprodTypeTffAtomicType left right => do
    pure <| (← tffXprodType left) ++ " * " ++ (← tffAtomicType right)

private partial def tffMappingType : TffMappingType → PrintM String
  | .mk domain result => do
    pure <| "(" ++ (← tffUnitaryType domain) ++ " > " ++ (← tffAtomicType result) ++ ")"

private partial def tffNonAtomicType : TffNonAtomicType → PrintM String
  | .tffMappingType mapping => tffMappingType mapping
  | .tffNonAtomicType sort => tffNonAtomicType sort
  | .tf1QuantifiedType _ => throw "the TPTP writer does not support TF1 quantified types"

private partial def tffTopLevelType : TffTopLevelType → PrintM String
  | .tffAtomicType sort => tffAtomicType sort
  | .tffNonAtomicType sort => tffNonAtomicType sort

private partial def tffTypeList : TffTypeList → PrintM String
  | .tffTopLevelType sort => tffTopLevelType sort
  | .tffTopLevelTypeTffTypeList sort rest => do
    pure <| (← tffTopLevelType sort) ++ ", " ++ (← tffTypeList rest)

private partial def tffTerm : TffTerm → PrintM String
  | .tffLogicFormula formula => tffLogic formula
  | .definedTerm (.number value) => number value
  | .definedTerm (.distinctObject (.mk text)) => pure s!"\"{text}\""
  | .txfTuple _ => throw "the TPTP writer does not support TF0 tuple terms"

private partial def tffPlainAtomic : TffPlainAtomic → PrintM String
  | .constant const => pure (constantText const)
  | .functorTffArguments func arguments => do
    pure <| (functorText func) ++ "(" ++ (← tffArguments arguments) ++ ")"

private partial def tffAtomic : TffAtomicFormula → PrintM String
  | .tffPlainAtomic atomic => tffPlainAtomic atomic
  | .tffDefinedAtomic (.mk (.definedConstant const)) => pure (definedConstant const)
  | .tffDefinedAtomic (.mk (.definedFunctorTffArguments func arguments)) => do
    let name := definedFunctor func
    unless name == "$ite" do throw "unsupported defined TFF function"
    pure <| name ++ "(" ++ (← tffArguments arguments) ++ ")"
  | _ => throw "the TPTP writer does not support this TF0 atomic formula"

private partial def tffUnitaryTerm : TffUnitaryTerm → PrintM String
  | .tffAtomicFormula atomic => tffAtomic atomic
  | .definedTerm (.number value) => number value
  | .definedTerm (.distinctObject (.mk text)) => pure s!"\"{text}\""
  | .variable boundVar => pure (varText boundVar)
  | .tffLogicFormula formula => do pure <| "(" ++ (← tffLogic formula) ++ ")"
  | _ => throw "the TPTP writer does not support this TF0 unitary term"

private partial def tffPreunit : TffPreunitFormula → PrintM String
  | .tffUnitaryFormula formula => tffUnitary formula
  | .tffPrefixUnary formula => tffPrefix formula

private partial def tffPrefix : TffPrefixUnary → PrintM String
  | .mk _ formula => do pure <| "~ " ++ (← tffPreunit formula)

private partial def tffUnitary : TffUnitaryFormula → PrintM String
  | .tffQuantifiedFormula (.mk quantifier variables body) => do
    let quantifier ← match quantifier with
      | .fofQuantifier .exclamation => pure "!"
      | .fofQuantifier .question => pure "?"
      | .hash => throw "the TPTP writer does not support choice quantifiers"
    pure <| quantifier ++ " [" ++ (← tffVariables variables) ++ "] : (" ++ (← tffUnit body) ++ ")"
  | .tffAtomicFormula atomic => tffAtomic atomic
  | .txfUnitaryFormula (.mk boundVar) => pure (varText boundVar)
  | .tffLogicFormula formula => do pure <| "(" ++ (← tffLogic formula) ++ ")"

private partial def tffUnit : TffUnitFormula → PrintM String
  | .tffUnitaryFormula formula => tffUnitary formula
  | .tffUnaryFormula (.tffPrefixUnary formula) => tffPrefix formula
  | .tffUnaryFormula (.tffInfixUnary (.mk left _ right)) => do
    pure <| (← tffUnitaryTerm left) ++ " != " ++ (← tffUnitaryTerm right)
  | .tffDefinedInfix (.mk left _ right) => do
    pure <| (← tffUnitaryTerm left) ++ " = " ++ (← tffUnitaryTerm right)

private partial def tffOr : TffOrFormula → PrintM String
  | .tffUnitFormulaTffUnitFormula left right => do
    pure <| "(" ++ (← tffUnit left) ++ " | " ++ (← tffUnit right) ++ ")"
  | .tffOrFormulaTffUnitFormula left right => do
    pure <| "(" ++ (← tffOr left) ++ " | " ++ (← tffUnit right) ++ ")"

private partial def tffAnd : TffAndFormula → PrintM String
  | .tffUnitFormulaTffUnitFormula left right => do
    pure <| "(" ++ (← tffUnit left) ++ " & " ++ (← tffUnit right) ++ ")"
  | .tffAndFormulaTffUnitFormula left right => do
    pure <| "(" ++ (← tffAnd left) ++ " & " ++ (← tffUnit right) ++ ")"

private partial def tffLogic : TffLogicFormula → PrintM String
  | .tffUnitaryFormula formula => tffUnitary formula
  | .tffUnaryFormula (.tffPrefixUnary formula) => tffPrefix formula
  | .tffUnaryFormula (.tffInfixUnary (.mk left _ right)) => do
    pure <| (← tffUnitaryTerm left) ++ " != " ++ (← tffUnitaryTerm right)
  | .tffBinaryFormula (.tffBinaryAssoc (.tffOrFormula formula)) => tffOr formula
  | .tffBinaryFormula (.tffBinaryAssoc (.tffAndFormula formula)) => tffAnd formula
  | .tffBinaryFormula (.tffBinaryNonassoc (.mk left connective right)) => do
    let connective ← match connective with
      | .iff => pure "<=>"
      | .fi => pure "<="
      | .if => pure "=>"
      | .xor => pure "<~>"
      | .nor => pure "~|"
      | .nand => pure "~&"
    pure <| "(" ++ (← tffUnit left) ++ " " ++ connective ++ " " ++ (← tffUnit right) ++ ")"
  | .tffDefinedInfix (.mk left _ right) => do
    pure <| (← tffUnitaryTerm left) ++ " = " ++ (← tffUnitaryTerm right)
  | _ => throw "the TPTP writer does not support this TF0 logic formula"

end

mutual

private partial def generalTerms : GeneralTerms → PrintM String
  | .mk first rest => do
    let rest ← rest.mapM fun | .mk term => generalTerm term
    pure (join ", " ((← generalTerm first) :: rest))

private partial def generalList : GeneralList → PrintM String
  | .empty => pure "[]"
  | .generalTerms terms => do pure <| "[" ++ (← generalTerms terms) ++ "]"

private partial def generalData : GeneralData → PrintM String
  | .atomicWord word => pure (atomicWord word)
  | .generalFunction (.mk name arguments) => do
    pure <| (atomicWord name) ++ "(" ++ (← generalTerms arguments) ++ ")"
  | .variable boundVar => pure (varText boundVar)
  | .number value => number value
  | .distinctObject (.mk text) => pure s!"\"{text}\""
  | .formulaData (.thfFormula (.thfLogicFormula value)) => do
    pure ("$thf(" ++ THF.Syntax.render (← THF.Syntax.term value) ++ ")")
  | .formulaData _ => throw "the TPTP writer does not support this embedded annotation formula"

private partial def generalTerm : GeneralTerm → PrintM String
  | .generalData data => generalData data
  | .generalDataGeneralTerm head tail => do
    pure <| (← generalData head) ++ " : " ++ (← generalTerm tail)
  | .generalList list => generalList list

private partial def usefulInfo : UsefulInfo → PrintM String
  | .mk list => generalList list

private partial def parents : Parents → PrintM String
  | .empty => pure "[]"
  | .parentList (.mk first rest) => do
    let first ← parentInfo first
    let rest ← rest.mapM fun | .mk parent => parentInfo parent
    pure <| "[" ++ join ", " (first :: rest) ++ "]"

private partial def parentInfo : ParentInfo → PrintM String
  | .mk source .nothing => sourceText source
  | .mk source (.generalTerm details) => do
    pure <| (← sourceText source) ++ " : " ++ (← generalTerm details)

private partial def optionalInfo : OptionalInfo → PrintM String
  | .nothing => pure ""
  | .usefulInfo info => do pure <| ", " ++ (← usefulInfo info)

private partial def sources : Sources → PrintM String
  | .source source => sourceText source
  | .sourceSources source rest => do
    pure <| (← sourceText source) ++ ", " ++ (← sources rest)

private partial def sourceText : Source → PrintM String
  | .dagSource (.name stepName) => pure (nameText stepName)
  | .dagSource (.inferenceRecord (.mk (.mk rule) details proofParents)) => do
    pure <| "inference(" ++ atomicWord rule ++ ", " ++ (← usefulInfo details) ++
      ", " ++ (← parents proofParents) ++ ")"
  | .internalSource (.mk (.mk introType) details proofParents) => do
    pure <| "introduced(" ++ atomicWord introType ++ ", " ++ (← usefulInfo details) ++
      ", " ++ (← parents proofParents) ++ ")"
  | .externalSource (.fileSource (.mk (.mk file) info)) =>
    match info with
    | .name fact => pure ("file(" ++ atomicWord file ++ ", " ++ nameText fact ++ ")")
    | .nothing => pure ("file(" ++ atomicWord file ++ ")")
  | .externalSource (.theory (.mk (.mk name) info)) => do
    pure <| "theory(" ++ atomicWord name ++ (← optionalInfo info) ++ ")"
  | .externalSource (.creatorSource (.mk (.mk name) details proofParents)) => do
    pure <| "creator(" ++ atomicWord name ++ ", " ++ (← usefulInfo details) ++
      ", " ++ (← parents proofParents) ++ ")"
  | .unknown => pure "unknown"
  | .sources list => do pure <| "[" ++ (← sources list) ++ "]"

private partial def annotations : Annotations → PrintM String
  | .nothing => pure ""
  | .sourceOptionalInfo source info => do
    pure <| ", " ++ (← sourceText source) ++ (← optionalInfo info)

end

private def role : FormulaRole → PrintM String
  | .lowerWord (.mk role) => pure role
  | .lowerWordGeneralTerm (.mk role) info => do
    pure <| role ++ "-" ++ (← generalTerm info)

private def tffFormula : TffFormula → PrintM String
  | .tffLogicFormula formula => tffLogic formula
  | .tffAtomTyping (.untypedAtomTffTopLevelType (.constant const) sort) => do
    pure <| (constantText const) ++ " : " ++ (← tffTopLevelType sort)
  | .tffAtomTyping (.tffAtomTyping typing) => tffFormula (.tffAtomTyping typing)
  | _ => throw "the TPTP writer does not support this TFF formula"

private def input : TptpInput → PrintM String
  | .annotatedFormula (.thfAnnotated (.mk formulaName formulaRole formula formulaAnnotations)) => do
    let text ← match formula with
      | .thfLogicFormula value => THF.Syntax.render <$> THF.Syntax.term value
      | .thfAtomTyping value =>
        let rec typing : ThfAtomTyping → PrintM String
          | .untypedAtomThfTopLevelType (.constant name) sort => do
            pure (constantText name ++ " : " ++ (← THF.Syntax.renderDeclarationSort sort))
          | .thfAtomTyping value => typing value
          | _ => throw "unsupported THF symbol declaration"
        typing value
      | _ => throw "unsupported THF formula"
    pure ("thf(" ++ nameText formulaName ++ ", " ++ (← role formulaRole) ++ ", (" ++
      text ++ ")" ++ (← annotations formulaAnnotations) ++ ").")
  | .annotatedFormula (.tffAnnotated (.mk formulaName formulaRole formula formulaAnnotations)) => do
    pure <| "tff(" ++ nameText formulaName ++ ", " ++ (← role formulaRole) ++ ", (" ++
      (← tffFormula formula) ++ ")" ++ (← annotations formulaAnnotations) ++ ")."
  | _ => throw "the TPTP writer currently emits only TFF and THF items"

/-- Render the supported TF0/TSTP subset as a standalone parseable TPTP file. -/
def render : TptpFile → PrintM String
  | .mk inputs => do
    let inputs ← inputs.mapM input
    pure (join "\n" inputs ++ "\n")

end VampireHammer.TptpPrinter
