namespace Tptp.Data

inductive Integer where
  | mk : Int → Integer
deriving Repr

inductive Real where
  | mk (mantisse : Int) (decimalExponent : Int) : Real
deriving Repr

inductive Rational where
  | mk (numerator : Int) (denominator : Nat) : Rational
deriving Repr

inductive LowerWord where
  | mk : String → LowerWord
deriving Repr

inductive UpperWord where
  | mk : String → UpperWord
deriving Repr

inductive DollarWord where
  | mk : String → DollarWord
deriving Repr

inductive DollarDollarWord where
  | mk : String → DollarDollarWord
deriving Repr

inductive SingleQuoted where
  | mk : String → SingleQuoted
deriving Repr

inductive BackQuoted where
  | mk : UpperWord → BackQuoted
deriving Repr

inductive DistinctObject where
  | mk : String → DistinctObject
deriving Repr

--------------------------------------------------------------------------------

inductive AtomicWord where
  | lowerWord : LowerWord → AtomicWord
  | singleQuoted : SingleQuoted → AtomicWord
  | backQuoted : BackQuoted → AtomicWord
deriving Repr

inductive Name where
  | atomicWord : AtomicWord → Name
  | integer : Integer → Name
deriving Repr

inductive Number where
  | integer : Integer → Number
  | rational : Rational → Number
  | real : Real → Number
deriving Repr

inductive AtomicSystemWord where
  | mk : DollarDollarWord → AtomicSystemWord
deriving Repr

inductive SystemFunctor where
  | mk : AtomicSystemWord → SystemFunctor
deriving Repr

inductive SystemConstant where
  | mk : SystemFunctor → SystemConstant
deriving Repr

inductive Functor where
  | mk : AtomicWord → Functor
deriving Repr

inductive Constant where
  | mk : Functor → Constant
deriving Repr

inductive UntypedAtom where
  | constant : Constant → UntypedAtom
  | systemConstant : SystemConstant → UntypedAtom
deriving Repr

inductive Variable where
  | mk : UpperWord → Variable
deriving Repr

inductive Th1DefinedTerm where
  | doubleExclamation
  | doubleQuestion
  | doubleAtPlus
  | doubleAtMinus
  | atEquals
deriving Repr

inductive DefinedTerm where
  | number : Number → DefinedTerm
  | distinctObject : DistinctObject → DefinedTerm
deriving Repr

inductive ThfDefinedTerm where
  | definedTerm : DefinedTerm → ThfDefinedTerm
  | th1DefinedTerm : Th1DefinedTerm → ThfDefinedTerm
deriving Repr

inductive Assignment where
  | mk
deriving Repr

inductive UnaryConnective where
  | mk
deriving Repr

inductive NtfShortConnective where
  | bracket
  | angle
  | brace
  | parens
deriving Repr

inductive ThfUnaryConnective where
  | unaryConnective : UnaryConnective → ThfUnaryConnective
  | ntfShortConnective : NtfShortConnective → ThfUnaryConnective
deriving Repr

inductive NonassocConnective where
  | iff
  | fi
  | if
  | xor
  | nor
  | nand
deriving Repr

inductive AssocConnective where
  | or
  | and
deriving Repr

inductive InfixEquality where
  | mk
deriving Repr

inductive InfixInequality where
  | mk
deriving Repr

inductive ThfConnTerm where
  | nonassocConnective : NonassocConnective → ThfConnTerm
  | assocConnective : AssocConnective → ThfConnTerm
  | infixEquality : InfixEquality → ThfConnTerm
  | infixInequality : InfixInequality → ThfConnTerm
  | thfUnaryConnective : ThfUnaryConnective → ThfConnTerm
deriving Repr

inductive AtomicDefinedWord where
  | mk : DollarWord → AtomicDefinedWord
deriving Repr

inductive DefinedFunctor where
  | mk : AtomicDefinedWord → DefinedFunctor
deriving Repr

inductive DefinedConstant where
  | mk : DefinedFunctor → DefinedConstant
deriving Repr

inductive DefOrSysConstant where
  | definedConstant : DefinedConstant → DefOrSysConstant
  | systemConstant : SystemConstant → DefOrSysConstant
deriving Repr

inductive NtfConnectiveName where
  | mk : DefOrSysConstant → NtfConnectiveName
deriving Repr

inductive TxfUnitaryFormula where
  | mk : Variable → TxfUnitaryFormula
deriving Repr

inductive TypeQuantifier where
  | exclamationArrow
  | questionStar
deriving Repr

inductive TypeFunctor where
  | mk : AtomicWord → TypeFunctor
deriving Repr

inductive TypeConstant where
  | mk : TypeFunctor → TypeConstant
deriving Repr

inductive DefinedType where
  | mk : AtomicDefinedWord → DefinedType
deriving Repr

--------------------------------------------------------------------------------

mutual

inductive TffTypeList where
  | tffTopLevelType : TffTopLevelType → TffTypeList
  | tffTopLevelTypeTffTypeList : TffTopLevelType → TffTypeList → TffTypeList
deriving Repr

inductive TxfTupleType where
  | mk : TffTypeList → TxfTupleType
deriving Repr

inductive TffXprodType where
  | tffUnitaryTypeTffAtomicType : TffUnitaryType → TffAtomicType → TffXprodType
  | tffXprodTypeTffAtomicType : TffXprodType → TffAtomicType → TffXprodType
deriving Repr

inductive TffMappingType where
  | mk : TffUnitaryType → TffAtomicType → TffMappingType
deriving Repr

inductive TffTypeArguments where
  | tffAtomicType : TffAtomicType → TffTypeArguments
  | tffAtomicTypeTffTypeArguments : TffAtomicType → TffTypeArguments → TffTypeArguments
deriving Repr

inductive TffAtomicType where
  | typeConstant : TypeConstant → TffAtomicType
  | definedType : DefinedType → TffAtomicType
  | variable : Variable → TffAtomicType
  | typeFunctorTffTypeArguments : TypeFunctor → TffTypeArguments → TffAtomicType
  | tffAtomicType : TffAtomicType → TffAtomicType
  | txfTupleType : TxfTupleType → TffAtomicType
deriving Repr

inductive TffUnitaryType where
  | tffAtomicType : TffAtomicType → TffUnitaryType
  | tffXprodType : TffXprodType → TffUnitaryType
deriving Repr

inductive TffMonotype where
  | tffAtomicType : TffAtomicType → TffMonotype
  | tffMappingType : TffMappingType → TffMonotype
  | tf1QuantifiedType : Tf1QuantifiedType → TffMonotype
deriving Repr

inductive Tf1QuantifiedType where
  | mk : TypeQuantifier → TffVariableList → TffMonotype → Tf1QuantifiedType
deriving Repr

inductive TffNonAtomicType where
  | tffMappingType : TffMappingType → TffNonAtomicType
  | tf1QuantifiedType : Tf1QuantifiedType → TffNonAtomicType
  | tffNonAtomicType : TffNonAtomicType → TffNonAtomicType
deriving Repr

inductive TffTopLevelType where
  | tffAtomicType : TffAtomicType → TffTopLevelType
  | tffNonAtomicType : TffNonAtomicType → TffTopLevelType
deriving Repr

inductive TffTypedVariable where
  | mk : Variable → TffAtomicType → TffTypedVariable
deriving Repr

inductive TffVariable where
  | tffTypedVariable : TffTypedVariable → TffVariable
  | variable : Variable → TffVariable
deriving Repr

inductive TffVariableList where
  | tffVariable : TffVariable → TffVariableList
  | tffVariableTffVariableList : TffVariable → TffVariableList → TffVariableList
deriving Repr

end

--------------------------------------------------------------------------------

inductive DefinedInfixPred where
  | mk : InfixEquality → DefinedInfixPred
deriving Repr

inductive TffUnaryConnective where
  | unaryConnective : UnaryConnective → TffUnaryConnective
  | ntfShortConnective : NtfShortConnective → TffUnaryConnective
deriving Repr

inductive FofQuantifier where
  | exclamation
  | question
deriving Repr

inductive TffQuantifier where
  | fofQuantifier : FofQuantifier → TffQuantifier
  | hash
deriving Repr

inductive Identical where
  | mk
deriving Repr

inductive GentzenArrow where
  | mk
deriving Repr

inductive TffAtomTyping where
  | untypedAtomTffTopLevelType : UntypedAtom → TffTopLevelType → TffAtomTyping
  | tffAtomTyping : TffAtomTyping → TffAtomTyping
deriving Repr

inductive TffAtomTypingList where
  | tffAtomTyping : TffAtomTyping → TffAtomTypingList
  | tffAtomTypingTffAtomTypingList : TffAtomTyping → TffAtomTypingList → TffAtomTypingList
deriving Repr

inductive TxfLetTypes where
  | tffAtomTyping : TffAtomTyping → TxfLetTypes
  | tffAtomTypingList : TffAtomTypingList → TxfLetTypes
deriving Repr

--------------------------------------------------------------------------------

mutual

inductive NtfIndex where
  | mk : TffUnitaryTerm → NtfIndex
deriving Repr

inductive NxfKeyPair where
  | mk : TxfDefinition → NxfKeyPair
deriving Repr

inductive NxfParameter where
  | ntfIndex : NtfIndex → NxfParameter
  | nxfKeyPair : NxfKeyPair → NxfParameter
deriving Repr

inductive NxfParameterList where
  | nxfParameter : NxfParameter → NxfParameterList
  | nxfParameterNxfParameterList : NxfParameter → NxfParameterList → NxfParameterList
deriving Repr

inductive NxfLongConnective where
  | ntfConnectiveName : NtfConnectiveName → NxfLongConnective
  | ntfConnectiveNameNxfParameterList : NtfConnectiveName → NxfParameterList → NxfLongConnective
deriving Repr

inductive TxfSequent where
  | mk : TxfTuple → GentzenArrow → TxfTuple → TxfSequent
deriving Repr

inductive TxfDefinition where
  | mk : TffAtomicFormula → Identical → TffTerm → TxfDefinition
deriving Repr

inductive CommaTffTerm where
  | mk : TffTerm → CommaTffTerm
deriving Repr

inductive TffArguments where
  | mk : TffTerm → List CommaTffTerm → TffArguments
deriving Repr

inductive TxfTuple where
  | empty
  | tffArguments : TffArguments → TxfTuple
deriving Repr

inductive TffUnitaryTerm where
  | tffAtomicFormula : TffAtomicFormula → TffUnitaryTerm
  | definedTerm : DefinedTerm → TffUnitaryTerm
  | txfTuple : TxfTuple → TffUnitaryTerm
  | variable : Variable → TffUnitaryTerm
  | tffLogicFormula : TffLogicFormula → TffUnitaryTerm
deriving Repr

inductive TffTerm where
  | tffLogicFormula : TffLogicFormula → TffTerm
  | definedTerm : DefinedTerm → TffTerm
  | txfTuple : TxfTuple → TffTerm
deriving Repr

inductive NxfAtom where
  | mk : NxfLongConnective → TffArguments → NxfAtom
deriving Repr

inductive TxfLetDefnList where
  | txfLetDefn : TxfLetDefn → TxfLetDefnList
  | txfLetDefnTxfLetDefnList : TxfLetDefn → TxfLetDefnList → TxfLetDefnList
deriving Repr

inductive TxfLetLHS where
  | tffPlainAtomic : TffPlainAtomic → TxfLetLHS
  | txfTuple : TxfTuple → TxfLetLHS
deriving Repr

inductive TxfLetDefn where
  | mk : TxfLetLHS → Assignment → TffTerm → TxfLetDefn
deriving Repr

inductive TxfLetDefns where
  | txfLetDefn : TxfLetDefn → TxfLetDefns
  | txfLetDefnList : TxfLetDefnList → TxfLetDefns
deriving Repr

inductive TxfLet where
  | mk : TxfLetTypes → TxfLetDefns → TffTerm → TxfLet
deriving Repr

inductive TffSystemAtomic where
  | systemConstant : SystemConstant → TffSystemAtomic
  | systemFunctorTffArguments : SystemFunctor → TffArguments → TffSystemAtomic
deriving Repr

inductive TffDefinedInfix where
  | mk : TffUnitaryTerm → DefinedInfixPred → TffUnitaryTerm → TffDefinedInfix
deriving Repr

inductive TffDefinedPlain where
  | definedConstant : DefinedConstant → TffDefinedPlain
  | definedFunctorTffArguments : DefinedFunctor → TffArguments → TffDefinedPlain
  | nxfAtom : NxfAtom → TffDefinedPlain
  | txfLet : TxfLet → TffDefinedPlain
deriving Repr

inductive TffDefinedAtomic where
  | mk : TffDefinedPlain → TffDefinedAtomic
deriving Repr

inductive TffPlainAtomic where
  | constant : Constant → TffPlainAtomic
  | functorTffArguments : Functor → TffArguments → TffPlainAtomic
deriving Repr

inductive TffAtomicFormula where
  | tffPlainAtomic : TffPlainAtomic → TffAtomicFormula
  | tffDefinedAtomic : TffDefinedAtomic → TffAtomicFormula
  | tffSystemAtomic : TffSystemAtomic → TffAtomicFormula
deriving Repr

inductive TffInfixUnary where
  | mk : TffUnitaryTerm → InfixInequality → TffUnitaryTerm → TffInfixUnary
deriving Repr

inductive TffPrefixUnary where
  | mk : TffUnaryConnective → TffPreunitFormula → TffPrefixUnary
deriving Repr

inductive TffUnaryFormula where
  | tffPrefixUnary : TffPrefixUnary → TffUnaryFormula
  | tffInfixUnary : TffInfixUnary → TffUnaryFormula
deriving Repr

inductive TffQuantifiedFormula where
  | mk : TffQuantifier → TffVariableList → TffUnitFormula → TffQuantifiedFormula
deriving Repr

inductive TffUnitaryFormula where
  | tffQuantifiedFormula : TffQuantifiedFormula → TffUnitaryFormula
  | tffAtomicFormula : TffAtomicFormula → TffUnitaryFormula
  | txfUnitaryFormula : TxfUnitaryFormula → TffUnitaryFormula
  | tffLogicFormula : TffLogicFormula → TffUnitaryFormula
deriving Repr

inductive TffPreunitFormula where
  | tffUnitaryFormula : TffUnitaryFormula → TffPreunitFormula
  | tffPrefixUnary : TffPrefixUnary → TffPreunitFormula
deriving Repr

inductive TffUnitFormula where
  | tffUnitaryFormula : TffUnitaryFormula → TffUnitFormula
  | tffUnaryFormula : TffUnaryFormula → TffUnitFormula
  | tffDefinedInfix : TffDefinedInfix → TffUnitFormula
deriving Repr

inductive TffAndFormula where
  | tffUnitFormulaTffUnitFormula : TffUnitFormula → TffUnitFormula → TffAndFormula
  | tffAndFormulaTffUnitFormula : TffAndFormula → TffUnitFormula → TffAndFormula
deriving Repr

inductive TffOrFormula where
  | tffUnitFormulaTffUnitFormula : TffUnitFormula → TffUnitFormula → TffOrFormula
  | tffOrFormulaTffUnitFormula : TffOrFormula → TffUnitFormula → TffOrFormula
deriving Repr

inductive TffBinaryAssoc where
  | tffOrFormula : TffOrFormula → TffBinaryAssoc
  | tffAndFormula : TffAndFormula → TffBinaryAssoc
deriving Repr

inductive TffBinaryNonassoc where
  | mk : TffUnitFormula → NonassocConnective → TffUnitFormula → TffBinaryNonassoc
deriving Repr

inductive TffBinaryFormula where
  | tffBinaryNonassoc : TffBinaryNonassoc → TffBinaryFormula
  | tffBinaryAssoc : TffBinaryAssoc → TffBinaryFormula
deriving Repr

inductive TffLogicFormula where
  | tffUnitaryFormula : TffUnitaryFormula → TffLogicFormula
  | tffUnaryFormula : TffUnaryFormula → TffLogicFormula
  | tffBinaryFormula : TffBinaryFormula → TffLogicFormula
  | tffDefinedInfix : TffDefinedInfix → TffLogicFormula
  | txfDefinition : TxfDefinition → TffLogicFormula
  | txfSequent : TxfSequent → TffLogicFormula
deriving Repr

end

--------------------------------------------------------------------------------

inductive ThfSystemAtomic where
  | mk : SystemConstant → ThfSystemAtomic
deriving Repr

inductive Th0Quantifier where
  | caret
  | atPlus
  | atMinus
deriving Repr

inductive ThfQuantifier where
  | tffQuantifier : TffQuantifier → ThfQuantifier
  | th0Quantifier : Th0Quantifier → ThfQuantifier
  | typeQuantifier : TypeQuantifier → ThfQuantifier
deriving Repr

--------------------------------------------------------------------------------

mutual

inductive NhfKeyPair where
  | mk : ThfDefinition → NhfKeyPair
deriving Repr

inductive NhfParameter where
  | ntfIndex : NtfIndex → NhfParameter
  | nhfKeyPair : NhfKeyPair → NhfParameter
deriving Repr

inductive NhfParameterList where
  | nhfParameter : NhfParameter → NhfParameterList
  | nhfParameterNhfParameterList : NhfParameter → NhfParameterList → NhfParameterList
deriving Repr

inductive NhfLongConnective where
  | ntfConnectiveName : NtfConnectiveName → NhfLongConnective
  | ntfConnectiveNameNhfParameterList : NtfConnectiveName → NhfParameterList → NhfLongConnective
deriving Repr

inductive ThfSequent where
  | mk : ThfTuple → GentzenArrow → ThfTuple → ThfSequent
deriving Repr

inductive ThfDefinition where
  | mk : ThfAtomicFormula → Identical → ThfLogicFormula → ThfDefinition
deriving Repr

inductive ThfUnionType where
  | thfUnitaryTypeThfUnitaryType : ThfUnitaryType → ThfUnitaryType → ThfUnionType
  | thfUnionTypeThfUnitaryType : ThfUnionType → ThfUnitaryType → ThfUnionType
deriving Repr

inductive ThfXprodType where
  | thfUnitaryTypeThfUnitaryType : ThfUnitaryType → ThfUnitaryType → ThfXprodType
  | thfXprodTypeThfUnitaryType : ThfXprodType → ThfUnitaryType → ThfXprodType
deriving Repr

inductive ThfMappingType where
  | thfUnitaryTypeThfUnitaryType : ThfUnitaryType → ThfUnitaryType → ThfMappingType
  | thfUnitaryTypeThfMappingType : ThfUnitaryType → ThfMappingType → ThfMappingType
deriving Repr

inductive ThfBinaryType where
  | thfMappingType : ThfMappingType → ThfBinaryType
  | thfXprodType : ThfXprodType → ThfBinaryType
  | thfUnionType : ThfUnionType → ThfBinaryType
deriving Repr

inductive ThfApplyType where
  | mk : ThfApplyFormula → ThfApplyType
deriving Repr

inductive ThfUnitaryType where
  | mk : ThfUnitaryFormula → ThfUnitaryType
deriving Repr

inductive ThfTopLevelType where
  | thfUnitaryType : ThfUnitaryType → ThfTopLevelType
  | thfMappingType : ThfMappingType → ThfTopLevelType
  | thfApplyType : ThfApplyType → ThfTopLevelType
deriving Repr

inductive ThfAtomTyping where
  | untypedAtomThfTopLevelType : UntypedAtom → ThfTopLevelType → ThfAtomTyping
  | thfAtomTyping : ThfAtomTyping → ThfAtomTyping
deriving Repr

inductive CommaThfLogicFormula where
  | mk : ThfLogicFormula → CommaThfLogicFormula
deriving Repr

inductive ThfFormulaList where
  | mk : ThfLogicFormula → List CommaThfLogicFormula → ThfFormulaList
deriving Repr

inductive ThfArguments where
  | mk : ThfFormulaList → ThfArguments
deriving Repr

inductive ThfFofFunction where
  | functorThfArguments : Functor → ThfArguments → ThfFofFunction
  | definedFunctorThfArguments : DefinedFunctor → ThfArguments → ThfFofFunction
  | systemFunctorThfArguments : SystemFunctor → ThfArguments → ThfFofFunction
deriving Repr

inductive ThfTuple where
  | empty
  | thfFormulaList : ThfFormulaList → ThfTuple
deriving Repr

inductive ThfUnitaryTerm where
  | thfAtomicFormula : ThfAtomicFormula → ThfUnitaryTerm
  | variable : Variable → ThfUnitaryTerm
  | thfLogicFormula : ThfLogicFormula → ThfUnitaryTerm
deriving Repr

inductive ThfLetDefnList where
  | thfLetDefn : ThfLetDefn → ThfLetDefnList
  | thfLetDefnThfLetDefnList : ThfLetDefn → ThfLetDefnList → ThfLetDefnList
deriving Repr

inductive ThfLetDefn where
  | mk : ThfLogicFormula → Assignment → ThfLogicFormula → ThfLetDefn
deriving Repr

inductive ThfLetDefns where
  | thfLetDefn : ThfLetDefn → ThfLetDefns
  | thfLetDefnList : ThfLetDefnList → ThfLetDefns
deriving Repr

inductive ThfAtomTypingList where
  | thfAtomTyping : ThfAtomTyping → ThfAtomTypingList
  | thfAtomTypingThfAtomTypingList : ThfAtomTyping → ThfAtomTypingList → ThfAtomTypingList
deriving Repr

inductive ThfLetTypes where
  | thfAtomTyping : ThfAtomTyping → ThfLetTypes
  | thfAtomTypingList : ThfAtomTypingList → ThfLetTypes
deriving Repr

inductive ThfLet where
  | mk : ThfLetTypes → ThfLetDefns → ThfLogicFormula → ThfLet
deriving Repr

inductive ThfDefinedInfix where
  | mk : ThfUnitaryTerm → DefinedInfixPred → ThfUnitaryTerm → ThfDefinedInfix
deriving Repr

inductive ThfDefinedAtomic where
  | definedConstant : DefinedConstant → ThfDefinedAtomic
  | thfDefinedTerm : ThfDefinedTerm → ThfDefinedAtomic
  | thfConnTerm : ThfConnTerm → ThfDefinedAtomic
  | nhfLongConnective : NhfLongConnective → ThfDefinedAtomic
  | thfLet : ThfLet → ThfDefinedAtomic
deriving Repr

inductive ThfPlainAtomic where
  | constant : Constant → ThfPlainAtomic
  | thfTuple : ThfTuple → ThfPlainAtomic
deriving Repr

inductive ThfAtomicFormula where
  | thfPlainAtomic : ThfPlainAtomic → ThfAtomicFormula
  | thfDefinedAtomic : ThfDefinedAtomic → ThfAtomicFormula
  | thfSystemAtomic : ThfSystemAtomic → ThfAtomicFormula
  | thfFofFunction : ThfFofFunction → ThfAtomicFormula
deriving Repr

inductive ThfInfixUnary where
  | mk : ThfUnitaryTerm → InfixInequality → ThfUnitaryTerm → ThfInfixUnary
deriving Repr

inductive ThfPrefixUnary where
  | mk : ThfUnaryConnective → ThfPreunitFormula → ThfPrefixUnary
deriving Repr

inductive ThfUnaryFormula where
  | thfPrefixUnary : ThfPrefixUnary → ThfUnaryFormula
  | thfInfixUnary : ThfInfixUnary → ThfUnaryFormula
deriving Repr

inductive ThfTypedVariable where
  | mk : Variable → ThfTopLevelType → ThfTypedVariable
deriving Repr

inductive ThfVariableList where
  | thfTypedVariable : ThfTypedVariable → ThfVariableList
  | thfTypedVariableThfVariableList : ThfTypedVariable → ThfVariableList → ThfVariableList
deriving Repr

inductive ThfQuantification where
  | mk : ThfQuantifier → ThfVariableList → ThfQuantification
deriving Repr

inductive ThfQuantifiedFormula where
  | mk : ThfQuantification → ThfUnitFormula → ThfQuantifiedFormula
deriving Repr

inductive ThfUnitaryFormula where
  | thfQuantifiedFormula : ThfQuantifiedFormula → ThfUnitaryFormula
  | thfAtomicFormula : ThfAtomicFormula → ThfUnitaryFormula
  | variable : Variable → ThfUnitaryFormula
  | thfLogicFormula : ThfLogicFormula → ThfUnitaryFormula
deriving Repr

inductive ThfPreunitFormula where
  | thfUnitaryFormula : ThfUnitaryFormula → ThfPreunitFormula
  | thfPrefixUnary : ThfPrefixUnary → ThfPreunitFormula
deriving Repr

inductive ThfUnitFormula where
  | thfUnitaryFormula : ThfUnitaryFormula → ThfUnitFormula
  | thfUnaryFormula : ThfUnaryFormula → ThfUnitFormula
  | thfDefinedInfix : ThfDefinedInfix → ThfUnitFormula
deriving Repr

inductive ThfApplyFormula where
  | thfUnitFormulaThfUnitFormula : ThfUnitFormula → ThfUnitFormula → ThfApplyFormula
  | thfApplyFormulaThfUnitFormula : ThfApplyFormula → ThfUnitFormula → ThfApplyFormula
deriving Repr

inductive ThfAndFormula where
  | thfUnitFormulaThfUnitFormula : ThfUnitFormula → ThfUnitFormula → ThfAndFormula
  | thfAndFormulaThfUnitFormula : ThfAndFormula → ThfUnitFormula → ThfAndFormula
deriving Repr

inductive ThfOrFormula where
  | thfUnitFormulaThfUnitFormula : ThfUnitFormula → ThfUnitFormula → ThfOrFormula
  | thfOrFormulaThfUnitFormula : ThfOrFormula → ThfUnitFormula → ThfOrFormula
deriving Repr

inductive ThfBinaryAssoc where
  | thfOrFormula : ThfOrFormula → ThfBinaryAssoc
  | thfAndFormula : ThfAndFormula → ThfBinaryAssoc
  | thfApplyFormula : ThfApplyFormula → ThfBinaryAssoc
deriving Repr

inductive ThfBinaryNonassoc where
  | mk : ThfUnitFormula → NonassocConnective → ThfUnitFormula → ThfBinaryNonassoc
deriving Repr

inductive ThfBinaryFormula where
  | thfBinaryNonassoc : ThfBinaryNonassoc → ThfBinaryFormula
  | thfBinaryAssoc : ThfBinaryAssoc → ThfBinaryFormula
  | thfBinaryType : ThfBinaryType → ThfBinaryFormula
deriving Repr

inductive ThfLogicFormula where
  | thfUnitaryFormula : ThfUnitaryFormula → ThfLogicFormula
  | thfUnaryFormula : ThfUnaryFormula → ThfLogicFormula
  | thfBinaryFormula : ThfBinaryFormula → ThfLogicFormula
  | thfDefinedInfix : ThfDefinedInfix → ThfLogicFormula
  | thfDefinition : ThfDefinition → ThfLogicFormula
  | thfSequent : ThfSequent → ThfLogicFormula
deriving Repr

end

--------------------------------------------------------------------------------

inductive Atom where
  | untypedAtom : UntypedAtom → Atom
  | definedConstant : DefinedConstant → Atom
deriving Repr

inductive SubtypeSign where
  | mk
deriving Repr

inductive ThfSubtype where
  | mk : UntypedAtom → SubtypeSign → Atom → ThfSubtype
deriving Repr

inductive ThfFormula where
  | thfLogicFormula : ThfLogicFormula → ThfFormula
  | thfAtomTyping : ThfAtomTyping → ThfFormula
  | thfSubtype : ThfSubtype → ThfFormula
deriving Repr

--------------------------------------------------------------------------------

mutual

inductive FofFunctionTerm where
  | fofPlainTerm : FofPlainTerm → FofFunctionTerm
  | fofDefinedTerm : FofDefinedTerm → FofFunctionTerm
  | fofSystemTerm : FofSystemTerm → FofFunctionTerm
deriving Repr

inductive FofTerm where
  | fofFunctionTerm : FofFunctionTerm → FofTerm
  | variable : Variable → FofTerm
deriving Repr

inductive FofArguments where
  | fofTerm : FofTerm → FofArguments
  | fofTermFofArguments : FofTerm → FofArguments → FofArguments
deriving Repr

inductive FofSystemTerm where
  | systemConstant : SystemConstant → FofSystemTerm
  | systemFunctorFofArguments : SystemFunctor → FofArguments → FofSystemTerm
deriving Repr

inductive FofDefinedPlainTerm where
  | definedConstant : DefinedConstant → FofDefinedPlainTerm
  | definedFunctorFofArguments : DefinedFunctor → FofArguments → FofDefinedPlainTerm
deriving Repr

inductive FofDefinedAtomicTerm where
  | mk : FofDefinedPlainTerm → FofDefinedAtomicTerm
deriving Repr

inductive FofDefinedTerm where
  | definedTerm : DefinedTerm → FofDefinedTerm
  | fofDefinedAtomicTerm : FofDefinedAtomicTerm → FofDefinedTerm
deriving Repr

inductive FofPlainTerm where
  | constant : Constant → FofPlainTerm
  | functorFofArguments : Functor → FofArguments → FofPlainTerm
deriving Repr

end

--------------------------------------------------------------------------------

inductive TffSubtype where
  | mk : UntypedAtom → SubtypeSign → Atom → TffSubtype
deriving Repr

inductive TffFormula where
  | tffLogicFormula : TffLogicFormula → TffFormula
  | tffAtomTyping : TffAtomTyping → TffFormula
  | tffSubtype : TffSubtype → TffFormula
deriving Repr

inductive FofSystemAtomicFormula where
  | mk : FofSystemTerm → FofSystemAtomicFormula
deriving Repr

inductive FofPlainAtomicFormula where
  | mk : FofPlainTerm → FofPlainAtomicFormula
deriving Repr

inductive FofDefinedPlainFormula where
  | mk : FofDefinedPlainTerm → FofDefinedPlainFormula
deriving Repr

inductive FofDefinedInfixFormula where
  | mk : FofTerm → DefinedInfixPred → FofTerm → FofDefinedInfixFormula
deriving Repr

inductive FofDefinedAtomicFormula where
  | fofDefinedPlainFormula : FofDefinedPlainFormula → FofDefinedAtomicFormula
  | fofDefinedInfixFormula : FofDefinedInfixFormula → FofDefinedAtomicFormula
deriving Repr

inductive FofAtomicFormula where
  | fofPlainAtomicFormula : FofPlainAtomicFormula → FofAtomicFormula
  | fofDefinedAtomicFormula : FofDefinedAtomicFormula → FofAtomicFormula
  | fofSystemAtomicFormula : FofSystemAtomicFormula → FofAtomicFormula
deriving Repr

inductive FofInfixUnary where
  | mk : FofTerm → InfixInequality → FofTerm → FofInfixUnary
deriving Repr

inductive CnfLiteral where
  | fofAtomicFormula : FofAtomicFormula → CnfLiteral
  | fofAtomicFormulaNegated : FofAtomicFormula → CnfLiteral
  | fofInfixUnary : FofInfixUnary → CnfLiteral
deriving Repr

inductive CnfDisjunction where
  | cnfLiteral : CnfLiteral → CnfDisjunction
  | cnfDisjunctionCnfLiteral : CnfDisjunction → CnfLiteral → CnfDisjunction
deriving Repr

inductive CnfFormula where
  | cnfDisjunction : CnfDisjunction → CnfFormula
  | cnfFormula : CnfFormula → CnfFormula
deriving Repr

inductive FofVariableList where
  | variable : Variable → FofVariableList
  | variableFofVariableList : Variable → FofVariableList → FofVariableList
deriving Repr

--------------------------------------------------------------------------------

mutual

inductive FofQuantifiedFormula where
  | mk : FofQuantifier → FofVariableList → FofUnitFormula → FofQuantifiedFormula
deriving Repr

inductive FofUnitaryFormula where
  | fofQuantifiedFormula : FofQuantifiedFormula → FofUnitaryFormula
  | fofAtomicFormula : FofAtomicFormula → FofUnitaryFormula
  | fofLogicFormula : FofLogicFormula → FofUnitaryFormula
deriving Repr

inductive FofUnitFormula where
  | fofUnitaryFormula : FofUnitaryFormula → FofUnitFormula
  | fofUnaryFormula : FofUnaryFormula → FofUnitFormula
deriving Repr

inductive FofUnaryFormula where
  | unaryConnectiveFofUnitFormula : UnaryConnective → FofUnitFormula → FofUnaryFormula
  | fofInfixUnary : FofInfixUnary → FofUnaryFormula
deriving Repr

inductive FofAndFormula where
  | fofUnitFormulaFofUnitFormula : FofUnitFormula → FofUnitFormula → FofAndFormula
  | fofAndFormulaFofUnitFormula : FofAndFormula → FofUnitFormula → FofAndFormula
deriving Repr

inductive FofOrFormula where
  | fofUnitFormulaFofUnitFormula : FofUnitFormula → FofUnitFormula → FofOrFormula
  | fofOrFormulaFofUnitFormula : FofOrFormula → FofUnitFormula → FofOrFormula
deriving Repr

inductive FofBinaryAssoc where
  | fofOrFormula : FofOrFormula → FofBinaryAssoc
  | fofAndFormula : FofAndFormula → FofBinaryAssoc
deriving Repr

inductive FofBinaryNonassoc where
  | mk : FofUnitFormula → NonassocConnective → FofUnitFormula → FofBinaryNonassoc
deriving Repr

inductive FofBinaryFormula where
  | fofBinaryNonassoc : FofBinaryNonassoc → FofBinaryFormula
  | fofBinaryAssoc : FofBinaryAssoc → FofBinaryFormula
deriving Repr

inductive FofLogicFormula where
  | fofBinaryFormula : FofBinaryFormula → FofLogicFormula
  | fofUnaryFormula : FofUnaryFormula → FofLogicFormula
  | fofUnitaryFormula : FofUnitaryFormula → FofLogicFormula
deriving Repr

end

--------------------------------------------------------------------------------

inductive CommaFofLogicFormula where
  | mk : FofLogicFormula → CommaFofLogicFormula
deriving Repr

inductive FofFormulaTupleList where
  | mk : FofLogicFormula → List CommaFofLogicFormula → FofFormulaTupleList
deriving Repr

inductive FofFormulaTuple where
  | empty
  | fofFormulaTupleList : FofFormulaTupleList → FofFormulaTuple
deriving Repr

inductive FofSequent where
  | fofFormulaTupleGentzenArrowFofFormulaTuple : FofFormulaTuple → GentzenArrow → FofFormulaTuple → FofSequent
  | fofSequent : FofSequent → FofSequent
deriving Repr

inductive FofFormula where
  | fofLogicFormula : FofLogicFormula → FofFormula
  | fofSequent : FofSequent → FofFormula
deriving Repr

inductive FormulaData where
  | thfFormula : ThfFormula → FormulaData
  | tffFormula : TffFormula → FormulaData
  | fofFormula : FofFormula → FormulaData
  | cnfFormula : CnfFormula → FormulaData
  | fofTerm : FofTerm → FormulaData
deriving Repr

--------------------------------------------------------------------------------

mutual

inductive CommaGeneralTerm where
  | mk : GeneralTerm → CommaGeneralTerm
deriving Repr

inductive GeneralTerms where
  | mk : GeneralTerm → List CommaGeneralTerm → GeneralTerms
deriving Repr

inductive GeneralList where
  | empty
  | generalTerms : GeneralTerms → GeneralList
deriving Repr

inductive GeneralFunction where
  | mk : AtomicWord → GeneralTerms → GeneralFunction
deriving Repr

inductive GeneralData where
  | atomicWord : AtomicWord → GeneralData
  | generalFunction : GeneralFunction → GeneralData
  | variable : Variable → GeneralData
  | number : Number → GeneralData
  | distinctObject : DistinctObject → GeneralData
  | formulaData : FormulaData → GeneralData
deriving Repr

inductive GeneralTerm where
  | generalData : GeneralData → GeneralTerm
  | generalDataGeneralTerm : GeneralData → GeneralTerm → GeneralTerm
  | generalList : GeneralList → GeneralTerm
deriving Repr

end

--------------------------------------------------------------------------------

inductive UsefulInfo where
  | mk : GeneralList → UsefulInfo
deriving Repr

inductive InferenceRule where
  | mk : AtomicWord → InferenceRule
deriving Repr

inductive ParentDetails where
  | generalTerm : GeneralTerm → ParentDetails
  | nothing : ParentDetails
deriving Repr

inductive IntroType where
  | mk : AtomicWord → IntroType
deriving Repr

inductive FileInfo where
  | name : Name → FileInfo
  | nothing : FileInfo
deriving Repr

inductive FileName where
  | mk : AtomicWord → FileName
deriving Repr

inductive FileSource where
  | mk : FileName → FileInfo → FileSource
deriving Repr

inductive TheoryName where
  | mk : AtomicWord → TheoryName
deriving Repr

inductive OptionalInfo where
  | usefulInfo : UsefulInfo → OptionalInfo
  | nothing : OptionalInfo
deriving Repr

inductive Theory where
  | mk : TheoryName → OptionalInfo → Theory
deriving Repr

inductive CreatorName where
  | mk : AtomicWord → CreatorName
deriving Repr

--------------------------------------------------------------------------------

mutual

inductive ParentInfo where
  | mk : Source → ParentDetails → ParentInfo
deriving Repr

inductive CommaParentInfo where
  | mk : ParentInfo → CommaParentInfo
deriving Repr

inductive ParentList where
  | mk : ParentInfo → List CommaParentInfo → ParentList
deriving Repr

inductive Parents where
  | empty
  | parentList : ParentList → Parents
deriving Repr

inductive CreatorSource where
  | mk : CreatorName → UsefulInfo → Parents → CreatorSource
deriving Repr

inductive ExternalSource where
  | fileSource : FileSource → ExternalSource
  | theory : Theory → ExternalSource
  | creatorSource : CreatorSource → ExternalSource
deriving Repr

inductive InternalSource where
  | mk : IntroType → UsefulInfo → Parents → InternalSource
deriving Repr

inductive InferenceRecord where
  | mk : InferenceRule → UsefulInfo → Parents → InferenceRecord
deriving Repr

inductive DagSource where
  | name : Name → DagSource
  | inferenceRecord : InferenceRecord → DagSource
deriving Repr

inductive Sources where
  | source : Source → Sources
  | sourceSources : Source → Sources → Sources
deriving Repr

inductive Source where
  | dagSource : DagSource → Source
  | internalSource : InternalSource → Source
  | externalSource : ExternalSource → Source
  | unknown
  | sources : Sources → Source
deriving Repr

end

--------------------------------------------------------------------------------

inductive Annotations where
  | sourceOptionalInfo : Source → OptionalInfo → Annotations
  | nothing : Annotations
deriving Repr

inductive FormulaRole where
  | lowerWord : LowerWord → FormulaRole
  | lowerWordGeneralTerm : LowerWord → GeneralTerm → FormulaRole
deriving Repr

inductive TpiFormula where
  | mk : FofFormula → TpiFormula
deriving Repr

inductive TpiAnnotated where
  | mk : Name → FormulaRole → TpiFormula → Annotations → TpiAnnotated
deriving Repr

inductive ThfAnnotated where
  | mk : Name → FormulaRole → ThfFormula → Annotations → ThfAnnotated
deriving Repr

inductive TffAnnotated where
  | mk : Name → FormulaRole → TffFormula → Annotations → TffAnnotated
deriving Repr

--------------------------------------------------------------------------------

mutual

inductive TcfQuantifiedFormula where
  | mk : TffVariableList → TcfLogicFormula → TcfQuantifiedFormula
deriving Repr

inductive TcfLogicFormula where
  | tcfQuantifiedFormula : TcfQuantifiedFormula → TcfLogicFormula
  | cnfFormula : CnfFormula → TcfLogicFormula
deriving Repr

end

--------------------------------------------------------------------------------

inductive TcfFormula where
  | tcfLogicFormula : TcfLogicFormula → TcfFormula
  | tffAtomTyping : TffAtomTyping → TcfFormula
deriving Repr

inductive TcfAnnotated where
  | mk : Name → FormulaRole → TcfFormula → Annotations → TcfAnnotated
deriving Repr

inductive FofAnnotated where
  | mk : Name → FormulaRole → FofFormula → Annotations → FofAnnotated
deriving Repr

inductive CnfAnnotated where
  | mk : Name → FormulaRole → CnfFormula → Annotations → CnfAnnotated
deriving Repr

inductive AnnotatedFormula where
  | thfAnnotated : ThfAnnotated → AnnotatedFormula
  | tffAnnotated : TffAnnotated → AnnotatedFormula
  | tcfAnnotated : TcfAnnotated → AnnotatedFormula
  | fofAnnotated : FofAnnotated → AnnotatedFormula
  | cnfAnnotated : CnfAnnotated → AnnotatedFormula
  | tpiAnnotated : TpiAnnotated → AnnotatedFormula
deriving Repr

inductive SpaceName where
  | mk : Name → SpaceName
deriving Repr

inductive NameList where
  | name : Name → NameList
  | nameNameList : Name → NameList → NameList
deriving Repr

inductive FormulaSelection where
  | nameList : NameList → FormulaSelection
  | star
deriving Repr

inductive IncludeOptionals where
  | nothing : IncludeOptionals
  | formulaSelection : FormulaSelection → IncludeOptionals
  | formulaSelectionSpaceName : FormulaSelection → SpaceName → IncludeOptionals
deriving Repr

inductive Include where
  | mk : FileName → IncludeOptionals → Include
deriving Repr

inductive TptpInput where
  | annotatedFormula : AnnotatedFormula → TptpInput
  | include : Include → TptpInput
deriving Repr

inductive TptpFile where
  | mk : List TptpInput → TptpFile
deriving Repr

end Tptp.Data
