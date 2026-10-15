import Tptp

/-! Named, lossless term syntax shared by TH0 formulas and embedded replay
certificates. Types and binder names survive until checked interpretation. -/

namespace VampireHammer.THF

inductive SortExpr where
  | named (name : String)
  | prop
  | func (domain range : SortExpr)
  deriving Repr, BEq, Nonempty

inductive Connective where
  | not | and | or | imp | reverseImp | iff | xor | nor | nand
  deriving Repr, BEq, Nonempty

inductive Term where
  | constant (name : String)
  | variable (name : String)
  | truth (value : Bool)
  | connective (op : Connective)
  | choice (sort : SortExpr)
  | app (function argument : Term)
  | lam (name : String) (sort : SortExpr) (body : Term)
  | forallE (name : String) (sort : SortExpr) (body : Term)
  | existsE (name : String) (sort : SortExpr) (body : Term)
  | not (body : Term)
  | binary (op : Connective) (left right : Term)
  | eq (left right : Term)
  | eqPartial (left : Term)
  | ite (condition left right : Term)
  | group (body : Term)
  deriving Repr, BEq, Nonempty

namespace Syntax
open Tptp.Data

private partial def mentionsName (name : String) : Term → Bool
  | .variable value => value == name
  | .lam binder _ body | .forallE binder _ body | .existsE binder _ body =>
    binder == name || mentionsName name body
  | .app fn arg | .eq fn arg | .binary _ fn arg => mentionsName name fn || mentionsName name arg
  | .group body | .not body | .eqPartial body => mentionsName name body
  | .ite condition left right =>
    mentionsName name condition || mentionsName name left || mentionsName name right
  | _ => false

private def freshQuantifierName (predicate : Term) : String := Id.run do
  let mut index := 0
  let mut name := "VampireQuantified0"
  while mentionsName name predicate do
    index := index + 1
    name := "VampireQuantified" ++ toString index
  return name

private def monomorphicOperator (operator : Th1DefinedTerm) (sort : SortExpr) : Except String Term :=
  match operator with
  | .doubleExclamation => pure (.lam "VampirePredicate" (.func sort .prop)
      (.forallE "VampireQuantified" sort
        (.app (.variable "VampirePredicate") (.variable "VampireQuantified"))))
  | .doubleQuestion => pure (.lam "VampirePredicate" (.func sort .prop)
      (.existsE "VampireQuantified" sort
        (.app (.variable "VampirePredicate") (.variable "VampireQuantified"))))
  | .atEquals => pure (.lam "VampireLeft" sort (.lam "VampireRight" sort
      (.eq (.variable "VampireLeft") (.variable "VampireRight"))))
  | .doubleAtPlus => pure (.choice sort)
  | _ => throw "THF definite description operators are not yet supported"

private partial def definedOperator? : ThfUnitaryFormula → Option Th1DefinedTerm
  | .thfAtomicFormula (.thfDefinedAtomic (.thfDefinedTerm (.th1DefinedTerm operator))) => some operator
  | .thfLogicFormula (.thfUnitaryFormula inner) => definedOperator? inner
  | _ => none

private partial def equalityOperator : ThfUnitaryFormula → Bool
  | .thfAtomicFormula (.thfDefinedAtomic (.thfConnTerm (.infixEquality _))) => true
  | .thfLogicFormula (.thfUnitaryFormula inner) => equalityOperator inner
  | _ => false

def word : AtomicWord → Except String String
  | .lowerWord (.mk name) | .singleQuoted (.mk name) => pure name
  | _ => throw "back-quoted THF names are unsupported"

private def constantName : Constant → Except String String
  | .mk (.mk name) => word name

private def definedName : DefinedConstant → String
  | .mk (.mk (.mk (.mk name))) => name

private def variableName : Variable → String
  | .mk (.mk name) => name

mutual
def sort : ThfTopLevelType → Except String SortExpr
  | .thfUnitaryType (.mk value) => unitarySortExpr value
  | .thfMappingType value => mappingSortExpr value
  | _ => throw "polymorphic or applied THF types are unsupported"

private def unitarySortExpr : ThfUnitaryFormula → Except String SortExpr
  | .thfAtomicFormula (.thfPlainAtomic (.constant name)) =>
    SortExpr.named <$> constantName name
  | .thfAtomicFormula (.thfDefinedAtomic (.definedConstant name)) =>
    match definedName name with
    | "o" | "$o" => pure .prop
    | name => throw s!"unsupported defined THF type `${name}`"
  | .thfLogicFormula (.thfUnitaryFormula value) => unitarySortExpr value
  | .thfLogicFormula (.thfBinaryFormula (.thfBinaryType (.thfMappingType value))) =>
    mappingSortExpr value
  | _ => throw "unsupported THF type (expected an atomic sort or arrow type)"

private def mappingSortExpr : ThfMappingType → Except String SortExpr
  | .thfUnitaryTypeThfUnitaryType (.mk domain) (.mk range) =>
    .func <$> unitarySortExpr domain <*> unitarySortExpr range
  | .thfUnitaryTypeThfMappingType (.mk domain) range =>
    .func <$> unitarySortExpr domain <*> mappingSortExpr range
end

def variables : ThfVariableList → Except String (List (String × SortExpr))
  | .thfTypedVariable (.mk name type) => do pure [(variableName name, ← sort type)]
  | .thfTypedVariableThfVariableList (.mk name type) rest => do
    pure ((variableName name, ← sort type) :: (← variables rest))

private def nonassoc : NonassocConnective → Connective
  | .iff => .iff
  | .fi => .imp
  | .if => .reverseImp
  | .xor => .xor
  | .nor => .nor
  | .nand => .nand

private def connTerm : ThfConnTerm → Except String Term
  | .nonassocConnective op => pure (.connective (nonassoc op))
  | .assocConnective .and => pure (.connective .and)
  | .assocConnective .or => pure (.connective .or)
  | .thfUnaryConnective (.unaryConnective _) => pure (.connective .not)
  | _ => throw "polymorphic equality/choice connective values are unsupported"

mutual
partial def term : ThfLogicFormula → Except String Term
  | .thfUnitaryFormula value => unitary value
  | .thfUnaryFormula value => unary value
  | .thfBinaryFormula (.thfBinaryNonassoc (.mk left op right)) =>
    .binary (nonassoc op) <$> unit left <*> unit right
  | .thfBinaryFormula (.thfBinaryAssoc (.thfApplyFormula value)) => application value
  | .thfBinaryFormula (.thfBinaryAssoc (.thfAndFormula value)) => conjunction value
  | .thfBinaryFormula (.thfBinaryAssoc (.thfOrFormula value)) => disjunction value
  | .thfDefinedInfix (.mk left _ right) => .eq <$> unitaryTerm left <*> unitaryTerm right
  | .thfDefinition (.mk left _ right) => .eq <$> atomic left <*> term right
  | _ => throw "unsupported THF formula (types, tuples and sequents are not terms)"

private partial def atomic : ThfAtomicFormula → Except String Term
  | .thfPlainAtomic (.constant name) => Term.constant <$> constantName name
  | .thfDefinedAtomic (.definedConstant name) =>
    match definedName name with
    | "true" | "$true" => pure (.truth true)
    | "false" | "$false" => pure (.truth false)
    | name => throw s!"unsupported defined THF constant `${name}`"
  | .thfDefinedAtomic (.thfConnTerm value) => connTerm value
  | .thfFofFunction (.functorThfArguments (.mk name) (.mk (.mk first rest))) => do
    let head := Term.constant (← word name)
    let args ← (first :: rest.map (fun | .mk value => value)).mapM term
    pure (args.foldl Term.app head)
  | .thfFofFunction (.definedFunctorThfArguments (.mk (.mk (.mk name))) (.mk (.mk first rest))) => do
    unless name == "ite" || name == "$ite" do throw s!"unsupported defined THF function `${name}`"
    let [condition, left, right] ← (first :: rest.map (fun | .mk value => value)).mapM term
      | throw "THF conditional requires three arguments"
    pure (.ite condition left right)
  | _ => throw "unsupported THF atom"

private partial def unitary : ThfUnitaryFormula → Except String Term
  | .thfAtomicFormula value => atomic value
  | .variable name => pure (.variable (variableName name))
  | .thfLogicFormula value => Term.group <$> term value
  | .thfQuantifiedFormula (.mk (.mk quantifier binders) body) => do
    let binders ← variables binders
    let body ← unit body
    if let .th0Quantifier .atPlus := quantifier then
      let [(name, sort)] := binders | throw "THF choice requires exactly one typed binder"
      return .app (.choice sort) (.lam name sort body)
    let wrap ← match quantifier with
      | .tffQuantifier (.fofQuantifier .exclamation) => pure Term.forallE
      | .tffQuantifier (.fofQuantifier .question) => pure Term.existsE
      | .th0Quantifier .caret => pure Term.lam
      | _ => throw "THF description and type quantification are not yet supported"
    pure (binders.foldr (fun (name, sort) body => wrap name sort body) body)

private partial def unitaryTerm : ThfUnitaryTerm → Except String Term
  | .thfAtomicFormula value => atomic value
  | .variable name => pure (.variable (variableName name))
  | .thfLogicFormula value => Term.group <$> term value

private partial def unit : ThfUnitFormula → Except String Term
  | .thfUnitaryFormula value => unitary value
  | .thfUnaryFormula value => unary value
  | .thfDefinedInfix (.mk left _ right) => .eq <$> unitaryTerm left <*> unitaryTerm right

private partial def preunit : ThfPreunitFormula → Except String Term
  | .thfUnitaryFormula value => unitary value
  | .thfPrefixUnary value => decodePrefix value

private partial def decodePrefix : ThfPrefixUnary → Except String Term
  | .mk (.unaryConnective _) body => Term.not <$> preunit body
  | _ => throw "unsupported modal THF connective"

private partial def unary : ThfUnaryFormula → Except String Term
  | .thfPrefixUnary value => decodePrefix value
  | .thfInfixUnary (.mk left _ right) => Term.not <$> (.eq <$> unitaryTerm left <*> unitaryTerm right)

private partial def application : ThfApplyFormula → Except String Term
  | .thfApplyFormulaThfUnitFormula
      (.thfUnitFormulaThfUnitFormula
        (.thfUnitaryFormula operator)
        (.thfUnitaryFormula type)) predicate => do
    let some quantifier := definedOperator? operator
      | return .app (← application (.thfUnitFormulaThfUnitFormula
        (.thfUnitaryFormula operator) (.thfUnitaryFormula type))) (← unit predicate)
    let sort ← unitarySortExpr type
    let predicate ← unit predicate
    let name := freshQuantifierName predicate
    let body := Term.app predicate (.variable name)
    match quantifier with
    | .doubleExclamation => pure (.forallE name sort body)
    | .doubleQuestion => pure (.existsE name sort body)
    | _ => pure (.app (← monomorphicOperator quantifier sort) predicate)
  | .thfUnitFormulaThfUnitFormula
      (.thfUnitaryFormula operator)
      (.thfUnitaryFormula type) => do
    if equalityOperator operator then
      return .eqPartial (← unitary type)
    else if let some operator := definedOperator? operator then
      monomorphicOperator operator (← unitarySortExpr type)
    else .app <$> unitary operator <*> unitary type
  | .thfUnitFormulaThfUnitFormula left right => .app <$> unit left <*> unit right
  | .thfApplyFormulaThfUnitFormula left right => .app <$> application left <*> unit right

private partial def conjunction : ThfAndFormula → Except String Term
  | .thfUnitFormulaThfUnitFormula left right => .binary .and <$> unit left <*> unit right
  | .thfAndFormulaThfUnitFormula left right => .binary .and <$> conjunction left <*> unit right

private partial def disjunction : ThfOrFormula → Except String Term
  | .thfUnitFormulaThfUnitFormula left right => .binary .or <$> unit left <*> unit right
  | .thfOrFormulaThfUnitFormula left right => .binary .or <$> disjunction left <*> unit right
end

def nameText (name : String) : String :=
  if name.toList.head?.any Char.isLower && name.toList.all (fun c => c.isAlphanum || c == '_')
  then name else "'" ++ (name.replace "\\" "\\\\").replace "'" "\\'" ++ "'"

def renderSortExpr : SortExpr → String
  | .named name => nameText name
  | .prop => "$o"
  | .func domain range => s!"({renderSortExpr domain} > {renderSortExpr range})"

/-- `$tType` is allowed only on a declaration of an atomic domain, not as
the sort of a term-level variable in this monomorphic fragment. -/
def renderDeclarationSort (value : ThfTopLevelType) : Except String String := do
  if let .thfUnitaryType (.mk (.thfAtomicFormula (.thfDefinedAtomic (.definedConstant name)))) := value then
    if definedName name == "tType" || definedName name == "$tType" then return "$tType"
  renderSortExpr <$> sort value

private def connectiveText : Connective → String
  | .not => "~" | .and => "&" | .or => "|" | .imp => "=>"
  | .reverseImp => "<=" | .iff => "<=>" | .xor => "<~>" | .nor => "~|" | .nand => "~&"

def render : Term → String
  | .constant name => nameText name
  | .variable name => name
  | .truth true => "$true"
  | .truth false => "$false"
  | .connective op => s!"({connectiveText op})"
  | .choice sort => s!"(@@+ @ {renderSortExpr sort})"
  | .app fn arg => s!"({render fn} @ {render arg})"
  | .lam name sort body => s!"(^ [{name}: {renderSortExpr sort}] : {render body})"
  | .forallE name sort body => s!"(! [{name}: {renderSortExpr sort}] : {render body})"
  | .existsE name sort body => s!"(? [{name}: {renderSortExpr sort}] : {render body})"
  | .not body => s!"(~ {render body})"
  | .binary op left right => s!"({render left} {connectiveText op} {render right})"
  | .eq left right => s!"({render left} = {render right})"
  | .eqPartial left => s!"((=) @ {render left})"
  | .ite condition left right => s!"$ite({render condition}, {render left}, {render right})"
  | .group body => s!"({render body})"

end Syntax

/-- Only free names belong to the certificate's conclusion/unifier namespace. -/
def Term.freeVariables (value : Term) (bound : List String := []) : Array String :=
  match value with
  | .variable name => if bound.contains name then #[] else #[name]
  | .app fn arg | .binary _ fn arg | .eq fn arg =>
    fn.freeVariables bound ++ arg.freeVariables bound
  | .lam name _ body | .forallE name _ body | .existsE name _ body =>
    body.freeVariables (name :: bound)
  | .not body | .group body | .eqPartial body => body.freeVariables bound
  | .ite condition left right =>
    condition.freeVariables bound ++ left.freeVariables bound ++ right.freeVariables bound
  | _ => #[]

end VampireHammer.THF
