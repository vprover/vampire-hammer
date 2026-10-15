import Data

namespace Tptp.Data.Export

@[export Tptp_mk_Integer_mk]
def Integer.mkMk : Int → Integer := Integer.mk

@[export Tptp_mk_Real_mk]
def Real.mkMk : Int → Int → Real := Real.mk

@[export Tptp_mk_Rational_mk]
def Rational.mkMk : Int → Nat → Rational := Rational.mk

@[export Tptp_mk_LowerWord_mk]
def LowerWord.mkMk : String → LowerWord := LowerWord.mk

@[export Tptp_mk_UpperWord_mk]
def UpperWord.mkMk : String → UpperWord := UpperWord.mk

@[export Tptp_mk_DollarWord_mk]
def DollarWord.mkMk : String → DollarWord := DollarWord.mk

@[export Tptp_mk_DollarDollarWord_mk]
def DollarDollarWord.mkMk : String → DollarDollarWord := DollarDollarWord.mk

@[export Tptp_mk_SingleQuoted_mk]
def SingleQuoted.mkMk : String → SingleQuoted := SingleQuoted.mk

@[export Tptp_mk_BackQuoted_mk]
def BackQuoted.mkMk : UpperWord → BackQuoted := BackQuoted.mk

@[export Tptp_mk_DistinctObject_mk]
def DistinctObject.mkMk : String → DistinctObject := DistinctObject.mk

@[export Tptp_mk_AtomicWord_lowerWord]
def AtomicWord.mkLowerWord : LowerWord → AtomicWord := AtomicWord.lowerWord

@[export Tptp_mk_AtomicWord_singleQuoted]
def AtomicWord.mkSingleQuoted : SingleQuoted → AtomicWord := AtomicWord.singleQuoted

@[export Tptp_mk_AtomicWord_backQuoted]
def AtomicWord.mkBackQuoted : BackQuoted → AtomicWord := AtomicWord.backQuoted

@[export Tptp_mk_Name_atomicWord]
def Name.mkAtomicWord : AtomicWord → Name := Name.atomicWord

@[export Tptp_mk_Name_integer]
def Name.mkInteger : Integer → Name := Name.integer

@[export Tptp_mk_Number_integer]
def Number.mkInteger : Integer → Number := Number.integer

@[export Tptp_mk_Number_rational]
def Number.mkRational : Rational → Number := Number.rational

@[export Tptp_mk_Number_real]
def Number.mkReal : Real → Number := Number.real

@[export Tptp_mk_AtomicSystemWord_mk]
def AtomicSystemWord.mkMk : DollarDollarWord → AtomicSystemWord := AtomicSystemWord.mk

@[export Tptp_mk_SystemFunctor_mk]
def SystemFunctor.mkMk : AtomicSystemWord → SystemFunctor := SystemFunctor.mk

@[export Tptp_mk_SystemConstant_mk]
def SystemConstant.mkMk : SystemFunctor → SystemConstant := SystemConstant.mk

@[export Tptp_mk_Functor_mk]
def Functor.mkMk : AtomicWord → Functor := Functor.mk

@[export Tptp_mk_Constant_mk]
def Constant.mkMk : Functor → Constant := Constant.mk

@[export Tptp_mk_UntypedAtom_constant]
def UntypedAtom.mkConstant : Constant → UntypedAtom := UntypedAtom.constant

@[export Tptp_mk_UntypedAtom_systemConstant]
def UntypedAtom.mkSystemConstant : SystemConstant → UntypedAtom := UntypedAtom.systemConstant

@[export Tptp_mk_Variable_mk]
def Variable.mkMk : UpperWord → Variable := Variable.mk

@[export Tptp_mk_Th1DefinedTerm_doubleExclamation]
def Th1DefinedTerm.mkDoubleExclamation : Th1DefinedTerm := Th1DefinedTerm.doubleExclamation

@[export Tptp_mk_Th1DefinedTerm_doubleQuestion]
def Th1DefinedTerm.mkDoubleQuestion : Th1DefinedTerm := Th1DefinedTerm.doubleQuestion

@[export Tptp_mk_Th1DefinedTerm_doubleAtPlus]
def Th1DefinedTerm.mkDoubleAtPlus : Th1DefinedTerm := Th1DefinedTerm.doubleAtPlus

@[export Tptp_mk_Th1DefinedTerm_doubleAtMinus]
def Th1DefinedTerm.mkDoubleAtMinus : Th1DefinedTerm := Th1DefinedTerm.doubleAtMinus

@[export Tptp_mk_Th1DefinedTerm_atEquals]
def Th1DefinedTerm.mkAtEquals : Th1DefinedTerm := Th1DefinedTerm.atEquals

@[export Tptp_mk_DefinedTerm_number]
def DefinedTerm.mkNumber : Number → DefinedTerm := DefinedTerm.number

@[export Tptp_mk_DefinedTerm_distinctObject]
def DefinedTerm.mkDistinctObject : DistinctObject → DefinedTerm := DefinedTerm.distinctObject

@[export Tptp_mk_ThfDefinedTerm_definedTerm]
def ThfDefinedTerm.mkDefinedTerm : DefinedTerm → ThfDefinedTerm := ThfDefinedTerm.definedTerm

@[export Tptp_mk_ThfDefinedTerm_th1DefinedTerm]
def ThfDefinedTerm.mkTh1DefinedTerm : Th1DefinedTerm → ThfDefinedTerm := ThfDefinedTerm.th1DefinedTerm

@[export Tptp_mk_Assignment_mk]
def Assignment.mkMk : Assignment := Assignment.mk

@[export Tptp_mk_UnaryConnective_mk]
def UnaryConnective.mkMk : UnaryConnective := UnaryConnective.mk

@[export Tptp_mk_NtfShortConnective_bracket]
def NtfShortConnective.mkBracket : NtfShortConnective := NtfShortConnective.bracket

@[export Tptp_mk_NtfShortConnective_angle]
def NtfShortConnective.mkAngle : NtfShortConnective := NtfShortConnective.angle

@[export Tptp_mk_NtfShortConnective_brace]
def NtfShortConnective.mkBrace : NtfShortConnective := NtfShortConnective.brace

@[export Tptp_mk_NtfShortConnective_parens]
def NtfShortConnective.mkParens : NtfShortConnective := NtfShortConnective.parens

@[export Tptp_mk_ThfUnaryConnective_unaryConnective]
def ThfUnaryConnective.mkUnaryConnective : UnaryConnective → ThfUnaryConnective := ThfUnaryConnective.unaryConnective

@[export Tptp_mk_ThfUnaryConnective_ntfShortConnective]
def ThfUnaryConnective.mkNtfShortConnective : NtfShortConnective → ThfUnaryConnective := ThfUnaryConnective.ntfShortConnective

@[export Tptp_mk_NonassocConnective_iff]
def NonassocConnective.mkIff : NonassocConnective := NonassocConnective.iff

@[export Tptp_mk_NonassocConnective_fi]
def NonassocConnective.mkFi : NonassocConnective := NonassocConnective.fi

@[export Tptp_mk_NonassocConnective_if]
def NonassocConnective.mkIf : NonassocConnective := NonassocConnective.if

@[export Tptp_mk_NonassocConnective_xor]
def NonassocConnective.mkXor : NonassocConnective := NonassocConnective.xor

@[export Tptp_mk_NonassocConnective_nor]
def NonassocConnective.mkNor : NonassocConnective := NonassocConnective.nor

@[export Tptp_mk_NonassocConnective_nand]
def NonassocConnective.mkNand : NonassocConnective := NonassocConnective.nand

@[export Tptp_mk_AssocConnective_or]
def AssocConnective.mkOr : AssocConnective := AssocConnective.or

@[export Tptp_mk_AssocConnective_and]
def AssocConnective.mkAnd : AssocConnective := AssocConnective.and

@[export Tptp_mk_InfixEquality_mk]
def InfixEquality.mkMk : InfixEquality := InfixEquality.mk

@[export Tptp_mk_InfixInequality_mk]
def InfixInequality.mkMk : InfixInequality := InfixInequality.mk

@[export Tptp_mk_ThfConnTerm_nonassocConnective]
def ThfConnTerm.mkNonassocConnective : NonassocConnective → ThfConnTerm := ThfConnTerm.nonassocConnective

@[export Tptp_mk_ThfConnTerm_assocConnective]
def ThfConnTerm.mkAssocConnective : AssocConnective → ThfConnTerm := ThfConnTerm.assocConnective

@[export Tptp_mk_ThfConnTerm_infixEquality]
def ThfConnTerm.mkInfixEquality : InfixEquality → ThfConnTerm := ThfConnTerm.infixEquality

@[export Tptp_mk_ThfConnTerm_infixInequality]
def ThfConnTerm.mkInfixInequality : InfixInequality → ThfConnTerm := ThfConnTerm.infixInequality

@[export Tptp_mk_ThfConnTerm_thfUnaryConnective]
def ThfConnTerm.mkThfUnaryConnective : ThfUnaryConnective → ThfConnTerm := ThfConnTerm.thfUnaryConnective

@[export Tptp_mk_AtomicDefinedWord_mk]
def AtomicDefinedWord.mkMk : DollarWord → AtomicDefinedWord := AtomicDefinedWord.mk

@[export Tptp_mk_DefinedFunctor_mk]
def DefinedFunctor.mkMk : AtomicDefinedWord → DefinedFunctor := DefinedFunctor.mk

@[export Tptp_mk_DefinedConstant_mk]
def DefinedConstant.mkMk : DefinedFunctor → DefinedConstant := DefinedConstant.mk

@[export Tptp_mk_DefOrSysConstant_definedConstant]
def DefOrSysConstant.mkDefinedConstant : DefinedConstant → DefOrSysConstant := DefOrSysConstant.definedConstant

@[export Tptp_mk_DefOrSysConstant_systemConstant]
def DefOrSysConstant.mkSystemConstant : SystemConstant → DefOrSysConstant := DefOrSysConstant.systemConstant

@[export Tptp_mk_NtfConnectiveName_mk]
def NtfConnectiveName.mkMk : DefOrSysConstant → NtfConnectiveName := NtfConnectiveName.mk

@[export Tptp_mk_TxfUnitaryFormula_mk]
def TxfUnitaryFormula.mkMk : Variable → TxfUnitaryFormula := TxfUnitaryFormula.mk

@[export Tptp_mk_TypeQuantifier_exclamationArrow]
def TypeQuantifier.mkExclamationArrow : TypeQuantifier := TypeQuantifier.exclamationArrow

@[export Tptp_mk_TypeQuantifier_questionStar]
def TypeQuantifier.mkQuestionStar : TypeQuantifier := TypeQuantifier.questionStar

@[export Tptp_mk_TypeFunctor_mk]
def TypeFunctor.mkMk : AtomicWord → TypeFunctor := TypeFunctor.mk

@[export Tptp_mk_TypeConstant_mk]
def TypeConstant.mkMk : TypeFunctor → TypeConstant := TypeConstant.mk

@[export Tptp_mk_DefinedType_mk]
def DefinedType.mkMk : AtomicDefinedWord → DefinedType := DefinedType.mk

@[export Tptp_mk_TffTypeList_tffTopLevelType]
def TffTypeList.mkTffTopLevelType : TffTopLevelType → TffTypeList := TffTypeList.tffTopLevelType

@[export Tptp_mk_TffTypeList_tffTopLevelTypeTffTypeList]
def TffTypeList.mkTffTopLevelTypeTffTypeList : TffTopLevelType → TffTypeList → TffTypeList := TffTypeList.tffTopLevelTypeTffTypeList

@[export Tptp_mk_TxfTupleType_mk]
def TxfTupleType.mkMk : TffTypeList → TxfTupleType := TxfTupleType.mk

@[export Tptp_mk_TffXprodType_tffUnitaryTypeTffAtomicType]
def TffXprodType.mkTffUnitaryTypeTffAtomicType : TffUnitaryType → TffAtomicType → TffXprodType := TffXprodType.tffUnitaryTypeTffAtomicType

@[export Tptp_mk_TffXprodType_tffXprodTypeTffAtomicType]
def TffXprodType.mkTffXprodTypeTffAtomicType : TffXprodType → TffAtomicType → TffXprodType := TffXprodType.tffXprodTypeTffAtomicType

@[export Tptp_mk_TffMappingType_mk]
def TffMappingType.mkMk : TffUnitaryType → TffAtomicType → TffMappingType := TffMappingType.mk

@[export Tptp_mk_TffTypeArguments_tffAtomicType]
def TffTypeArguments.mkTffAtomicType : TffAtomicType → TffTypeArguments := TffTypeArguments.tffAtomicType

@[export Tptp_mk_TffTypeArguments_tffAtomicTypeTffTypeArguments]
def TffTypeArguments.mkTffAtomicTypeTffTypeArguments : TffAtomicType → TffTypeArguments → TffTypeArguments := TffTypeArguments.tffAtomicTypeTffTypeArguments

@[export Tptp_mk_TffAtomicType_typeConstant]
def TffAtomicType.mkTypeConstant : TypeConstant → TffAtomicType := TffAtomicType.typeConstant

@[export Tptp_mk_TffAtomicType_definedType]
def TffAtomicType.mkDefinedType : DefinedType → TffAtomicType := TffAtomicType.definedType

@[export Tptp_mk_TffAtomicType_variable]
def TffAtomicType.mkVariable : Variable → TffAtomicType := TffAtomicType.variable

@[export Tptp_mk_TffAtomicType_typeFunctorTffTypeArguments]
def TffAtomicType.mkTypeFunctorTffTypeArguments : TypeFunctor → TffTypeArguments → TffAtomicType := TffAtomicType.typeFunctorTffTypeArguments

@[export Tptp_mk_TffAtomicType_tffAtomicType]
def TffAtomicType.mkTffAtomicType : TffAtomicType → TffAtomicType := TffAtomicType.tffAtomicType

@[export Tptp_mk_TffAtomicType_txfTupleType]
def TffAtomicType.mkTxfTupleType : TxfTupleType → TffAtomicType := TffAtomicType.txfTupleType

@[export Tptp_mk_TffUnitaryType_tffAtomicType]
def TffUnitaryType.mkTffAtomicType : TffAtomicType → TffUnitaryType := TffUnitaryType.tffAtomicType

@[export Tptp_mk_TffUnitaryType_tffXprodType]
def TffUnitaryType.mkTffXprodType : TffXprodType → TffUnitaryType := TffUnitaryType.tffXprodType

@[export Tptp_mk_TffMonotype_tffAtomicType]
def TffMonotype.mkTffAtomicType : TffAtomicType → TffMonotype := TffMonotype.tffAtomicType

@[export Tptp_mk_TffMonotype_tffMappingType]
def TffMonotype.mkTffMappingType : TffMappingType → TffMonotype := TffMonotype.tffMappingType

@[export Tptp_mk_TffMonotype_tf1QuantifiedType]
def TffMonotype.mkTf1QuantifiedType : Tf1QuantifiedType → TffMonotype := TffMonotype.tf1QuantifiedType

@[export Tptp_mk_Tf1QuantifiedType_mk]
def Tf1QuantifiedType.mkMk : TypeQuantifier → TffVariableList → TffMonotype → Tf1QuantifiedType := Tf1QuantifiedType.mk

@[export Tptp_mk_TffNonAtomicType_tffMappingType]
def TffNonAtomicType.mkTffMappingType : TffMappingType → TffNonAtomicType := TffNonAtomicType.tffMappingType

@[export Tptp_mk_TffNonAtomicType_tf1QuantifiedType]
def TffNonAtomicType.mkTf1QuantifiedType : Tf1QuantifiedType → TffNonAtomicType := TffNonAtomicType.tf1QuantifiedType

@[export Tptp_mk_TffNonAtomicType_tffNonAtomicType]
def TffNonAtomicType.mkTffNonAtomicType : TffNonAtomicType → TffNonAtomicType := TffNonAtomicType.tffNonAtomicType

@[export Tptp_mk_TffTopLevelType_tffAtomicType]
def TffTopLevelType.mkTffAtomicType : TffAtomicType → TffTopLevelType := TffTopLevelType.tffAtomicType

@[export Tptp_mk_TffTopLevelType_tffNonAtomicType]
def TffTopLevelType.mkTffNonAtomicType : TffNonAtomicType → TffTopLevelType := TffTopLevelType.tffNonAtomicType

@[export Tptp_mk_TffTypedVariable_mk]
def TffTypedVariable.mkMk : Variable → TffAtomicType → TffTypedVariable := TffTypedVariable.mk

@[export Tptp_mk_TffVariable_tffTypedVariable]
def TffVariable.mkTffTypedVariable : TffTypedVariable → TffVariable := TffVariable.tffTypedVariable

@[export Tptp_mk_TffVariable_variable]
def TffVariable.mkVariable : Variable → TffVariable := TffVariable.variable

@[export Tptp_mk_TffVariableList_tffVariable]
def TffVariableList.mkTffVariable : TffVariable → TffVariableList := TffVariableList.tffVariable

@[export Tptp_mk_TffVariableList_tffVariableTffVariableList]
def TffVariableList.mkTffVariableTffVariableList : TffVariable → TffVariableList → TffVariableList := TffVariableList.tffVariableTffVariableList

@[export Tptp_mk_DefinedInfixPred_mk]
def DefinedInfixPred.mkMk : InfixEquality → DefinedInfixPred := DefinedInfixPred.mk

@[export Tptp_mk_TffUnaryConnective_unaryConnective]
def TffUnaryConnective.mkUnaryConnective : UnaryConnective → TffUnaryConnective := TffUnaryConnective.unaryConnective

@[export Tptp_mk_TffUnaryConnective_ntfShortConnective]
def TffUnaryConnective.mkNtfShortConnective : NtfShortConnective → TffUnaryConnective := TffUnaryConnective.ntfShortConnective

@[export Tptp_mk_FofQuantifier_exclamation]
def FofQuantifier.mkExclamation : FofQuantifier := FofQuantifier.exclamation

@[export Tptp_mk_FofQuantifier_question]
def FofQuantifier.mkQuestion : FofQuantifier := FofQuantifier.question

@[export Tptp_mk_TffQuantifier_fofQuantifier]
def TffQuantifier.mkFofQuantifier : FofQuantifier → TffQuantifier := TffQuantifier.fofQuantifier

@[export Tptp_mk_TffQuantifier_hash]
def TffQuantifier.mkHash : TffQuantifier := TffQuantifier.hash

@[export Tptp_mk_Identical_mk]
def Identical.mkMk : Identical := Identical.mk

@[export Tptp_mk_GentzenArrow_mk]
def GentzenArrow.mkMk : GentzenArrow := GentzenArrow.mk

@[export Tptp_mk_TffAtomTyping_untypedAtomTffTopLevelType]
def TffAtomTyping.mkUntypedAtomTffTopLevelType : UntypedAtom → TffTopLevelType → TffAtomTyping := TffAtomTyping.untypedAtomTffTopLevelType

@[export Tptp_mk_TffAtomTyping_tffAtomTyping]
def TffAtomTyping.mkTffAtomTyping : TffAtomTyping → TffAtomTyping := TffAtomTyping.tffAtomTyping

@[export Tptp_mk_TffAtomTypingList_tffAtomTyping]
def TffAtomTypingList.mkTffAtomTyping : TffAtomTyping → TffAtomTypingList := TffAtomTypingList.tffAtomTyping

@[export Tptp_mk_TffAtomTypingList_tffAtomTypingTffAtomTypingList]
def TffAtomTypingList.mkTffAtomTypingTffAtomTypingList : TffAtomTyping → TffAtomTypingList → TffAtomTypingList := TffAtomTypingList.tffAtomTypingTffAtomTypingList

@[export Tptp_mk_TxfLetTypes_tffAtomTyping]
def TxfLetTypes.mkTffAtomTyping : TffAtomTyping → TxfLetTypes := TxfLetTypes.tffAtomTyping

@[export Tptp_mk_TxfLetTypes_tffAtomTypingList]
def TxfLetTypes.mkTffAtomTypingList : TffAtomTypingList → TxfLetTypes := TxfLetTypes.tffAtomTypingList

@[export Tptp_mk_NtfIndex_mk]
def NtfIndex.mkMk : TffUnitaryTerm → NtfIndex := NtfIndex.mk

@[export Tptp_mk_NxfKeyPair_mk]
def NxfKeyPair.mkMk : TxfDefinition → NxfKeyPair := NxfKeyPair.mk

@[export Tptp_mk_NxfParameter_ntfIndex]
def NxfParameter.mkNtfIndex : NtfIndex → NxfParameter := NxfParameter.ntfIndex

@[export Tptp_mk_NxfParameter_nxfKeyPair]
def NxfParameter.mkNxfKeyPair : NxfKeyPair → NxfParameter := NxfParameter.nxfKeyPair

@[export Tptp_mk_NxfParameterList_nxfParameter]
def NxfParameterList.mkNxfParameter : NxfParameter → NxfParameterList := NxfParameterList.nxfParameter

@[export Tptp_mk_NxfParameterList_nxfParameterNxfParameterList]
def NxfParameterList.mkNxfParameterNxfParameterList : NxfParameter → NxfParameterList → NxfParameterList := NxfParameterList.nxfParameterNxfParameterList

@[export Tptp_mk_NxfLongConnective_ntfConnectiveName]
def NxfLongConnective.mkNtfConnectiveName : NtfConnectiveName → NxfLongConnective := NxfLongConnective.ntfConnectiveName

@[export Tptp_mk_NxfLongConnective_ntfConnectiveNameNxfParameterList]
def NxfLongConnective.mkNtfConnectiveNameNxfParameterList : NtfConnectiveName → NxfParameterList → NxfLongConnective := NxfLongConnective.ntfConnectiveNameNxfParameterList

@[export Tptp_mk_TxfSequent_mk]
def TxfSequent.mkMk : TxfTuple → GentzenArrow → TxfTuple → TxfSequent := TxfSequent.mk

@[export Tptp_mk_TxfDefinition_mk]
def TxfDefinition.mkMk : TffAtomicFormula → Identical → TffTerm → TxfDefinition := TxfDefinition.mk

@[export Tptp_mk_CommaTffTerm_mk]
def CommaTffTerm.mkMk : TffTerm → CommaTffTerm := CommaTffTerm.mk

@[export Tptp_mk_TffArguments_mk]
def TffArguments.mkMk : TffTerm → List CommaTffTerm → TffArguments := TffArguments.mk

@[export Tptp_mk_TxfTuple_empty]
def TxfTuple.mkEmpty : TxfTuple := TxfTuple.empty

@[export Tptp_mk_TxfTuple_tffArguments]
def TxfTuple.mkTffArguments : TffArguments → TxfTuple := TxfTuple.tffArguments

@[export Tptp_mk_TffUnitaryTerm_tffAtomicFormula]
def TffUnitaryTerm.mkTffAtomicFormula : TffAtomicFormula → TffUnitaryTerm := TffUnitaryTerm.tffAtomicFormula

@[export Tptp_mk_TffUnitaryTerm_definedTerm]
def TffUnitaryTerm.mkDefinedTerm : DefinedTerm → TffUnitaryTerm := TffUnitaryTerm.definedTerm

@[export Tptp_mk_TffUnitaryTerm_txfTuple]
def TffUnitaryTerm.mkTxfTuple : TxfTuple → TffUnitaryTerm := TffUnitaryTerm.txfTuple

@[export Tptp_mk_TffUnitaryTerm_variable]
def TffUnitaryTerm.mkVariable : Variable → TffUnitaryTerm := TffUnitaryTerm.variable

@[export Tptp_mk_TffUnitaryTerm_tffLogicFormula]
def TffUnitaryTerm.mkTffLogicFormula : TffLogicFormula → TffUnitaryTerm := TffUnitaryTerm.tffLogicFormula

@[export Tptp_mk_TffTerm_tffLogicFormula]
def TffTerm.mkTffLogicFormula : TffLogicFormula → TffTerm := TffTerm.tffLogicFormula

@[export Tptp_mk_TffTerm_definedTerm]
def TffTerm.mkDefinedTerm : DefinedTerm → TffTerm := TffTerm.definedTerm

@[export Tptp_mk_TffTerm_txfTuple]
def TffTerm.mkTxfTuple : TxfTuple → TffTerm := TffTerm.txfTuple

@[export Tptp_mk_NxfAtom_mk]
def NxfAtom.mkMk : NxfLongConnective → TffArguments → NxfAtom := NxfAtom.mk

@[export Tptp_mk_TxfLetDefnList_txfLetDefn]
def TxfLetDefnList.mkTxfLetDefn : TxfLetDefn → TxfLetDefnList := TxfLetDefnList.txfLetDefn

@[export Tptp_mk_TxfLetDefnList_txfLetDefnTxfLetDefnList]
def TxfLetDefnList.mkTxfLetDefnTxfLetDefnList : TxfLetDefn → TxfLetDefnList → TxfLetDefnList := TxfLetDefnList.txfLetDefnTxfLetDefnList

@[export Tptp_mk_TxfLetLHS_tffPlainAtomic]
def TxfLetLHS.mkTffPlainAtomic : TffPlainAtomic → TxfLetLHS := TxfLetLHS.tffPlainAtomic

@[export Tptp_mk_TxfLetLHS_txfTuple]
def TxfLetLHS.mkTxfTuple : TxfTuple → TxfLetLHS := TxfLetLHS.txfTuple

@[export Tptp_mk_TxfLetDefn_mk]
def TxfLetDefn.mkMk : TxfLetLHS → Assignment → TffTerm → TxfLetDefn := TxfLetDefn.mk

@[export Tptp_mk_TxfLetDefns_txfLetDefn]
def TxfLetDefns.mkTxfLetDefn : TxfLetDefn → TxfLetDefns := TxfLetDefns.txfLetDefn

@[export Tptp_mk_TxfLetDefns_txfLetDefnList]
def TxfLetDefns.mkTxfLetDefnList : TxfLetDefnList → TxfLetDefns := TxfLetDefns.txfLetDefnList

@[export Tptp_mk_TxfLet_mk]
def TxfLet.mkMk : TxfLetTypes → TxfLetDefns → TffTerm → TxfLet := TxfLet.mk

@[export Tptp_mk_TffSystemAtomic_systemConstant]
def TffSystemAtomic.mkSystemConstant : SystemConstant → TffSystemAtomic := TffSystemAtomic.systemConstant

@[export Tptp_mk_TffSystemAtomic_systemFunctorTffArguments]
def TffSystemAtomic.mkSystemFunctorTffArguments : SystemFunctor → TffArguments → TffSystemAtomic := TffSystemAtomic.systemFunctorTffArguments

@[export Tptp_mk_TffDefinedInfix_mk]
def TffDefinedInfix.mkMk : TffUnitaryTerm → DefinedInfixPred → TffUnitaryTerm → TffDefinedInfix := TffDefinedInfix.mk

@[export Tptp_mk_TffDefinedPlain_definedConstant]
def TffDefinedPlain.mkDefinedConstant : DefinedConstant → TffDefinedPlain := TffDefinedPlain.definedConstant

@[export Tptp_mk_TffDefinedPlain_definedFunctorTffArguments]
def TffDefinedPlain.mkDefinedFunctorTffArguments : DefinedFunctor → TffArguments → TffDefinedPlain := TffDefinedPlain.definedFunctorTffArguments

@[export Tptp_mk_TffDefinedPlain_nxfAtom]
def TffDefinedPlain.mkNxfAtom : NxfAtom → TffDefinedPlain := TffDefinedPlain.nxfAtom

@[export Tptp_mk_TffDefinedPlain_txfLet]
def TffDefinedPlain.mkTxfLet : TxfLet → TffDefinedPlain := TffDefinedPlain.txfLet

@[export Tptp_mk_TffDefinedAtomic_mk]
def TffDefinedAtomic.mkMk : TffDefinedPlain → TffDefinedAtomic := TffDefinedAtomic.mk

@[export Tptp_mk_TffPlainAtomic_constant]
def TffPlainAtomic.mkConstant : Constant → TffPlainAtomic := TffPlainAtomic.constant

@[export Tptp_mk_TffPlainAtomic_functorTffArguments]
def TffPlainAtomic.mkFunctorTffArguments : Functor → TffArguments → TffPlainAtomic := TffPlainAtomic.functorTffArguments

@[export Tptp_mk_TffAtomicFormula_tffPlainAtomic]
def TffAtomicFormula.mkTffPlainAtomic : TffPlainAtomic → TffAtomicFormula := TffAtomicFormula.tffPlainAtomic

@[export Tptp_mk_TffAtomicFormula_tffDefinedAtomic]
def TffAtomicFormula.mkTffDefinedAtomic : TffDefinedAtomic → TffAtomicFormula := TffAtomicFormula.tffDefinedAtomic

@[export Tptp_mk_TffAtomicFormula_tffSystemAtomic]
def TffAtomicFormula.mkTffSystemAtomic : TffSystemAtomic → TffAtomicFormula := TffAtomicFormula.tffSystemAtomic

@[export Tptp_mk_TffInfixUnary_mk]
def TffInfixUnary.mkMk : TffUnitaryTerm → InfixInequality → TffUnitaryTerm → TffInfixUnary := TffInfixUnary.mk

@[export Tptp_mk_TffPrefixUnary_mk]
def TffPrefixUnary.mkMk : TffUnaryConnective → TffPreunitFormula → TffPrefixUnary := TffPrefixUnary.mk

@[export Tptp_mk_TffUnaryFormula_tffPrefixUnary]
def TffUnaryFormula.mkTffPrefixUnary : TffPrefixUnary → TffUnaryFormula := TffUnaryFormula.tffPrefixUnary

@[export Tptp_mk_TffUnaryFormula_tffInfixUnary]
def TffUnaryFormula.mkTffInfixUnary : TffInfixUnary → TffUnaryFormula := TffUnaryFormula.tffInfixUnary

@[export Tptp_mk_TffQuantifiedFormula_mk]
def TffQuantifiedFormula.mkMk : TffQuantifier → TffVariableList → TffUnitFormula → TffQuantifiedFormula := TffQuantifiedFormula.mk

@[export Tptp_mk_TffUnitaryFormula_tffQuantifiedFormula]
def TffUnitaryFormula.mkTffQuantifiedFormula : TffQuantifiedFormula → TffUnitaryFormula := TffUnitaryFormula.tffQuantifiedFormula

@[export Tptp_mk_TffUnitaryFormula_tffAtomicFormula]
def TffUnitaryFormula.mkTffAtomicFormula : TffAtomicFormula → TffUnitaryFormula := TffUnitaryFormula.tffAtomicFormula

@[export Tptp_mk_TffUnitaryFormula_txfUnitaryFormula]
def TffUnitaryFormula.mkTxfUnitaryFormula : TxfUnitaryFormula → TffUnitaryFormula := TffUnitaryFormula.txfUnitaryFormula

@[export Tptp_mk_TffUnitaryFormula_tffLogicFormula]
def TffUnitaryFormula.mkTffLogicFormula : TffLogicFormula → TffUnitaryFormula := TffUnitaryFormula.tffLogicFormula

@[export Tptp_mk_TffPreunitFormula_tffUnitaryFormula]
def TffPreunitFormula.mkTffUnitaryFormula : TffUnitaryFormula → TffPreunitFormula := TffPreunitFormula.tffUnitaryFormula

@[export Tptp_mk_TffPreunitFormula_tffPrefixUnary]
def TffPreunitFormula.mkTffPrefixUnary : TffPrefixUnary → TffPreunitFormula := TffPreunitFormula.tffPrefixUnary

@[export Tptp_mk_TffUnitFormula_tffUnitaryFormula]
def TffUnitFormula.mkTffUnitaryFormula : TffUnitaryFormula → TffUnitFormula := TffUnitFormula.tffUnitaryFormula

@[export Tptp_mk_TffUnitFormula_tffUnaryFormula]
def TffUnitFormula.mkTffUnaryFormula : TffUnaryFormula → TffUnitFormula := TffUnitFormula.tffUnaryFormula

@[export Tptp_mk_TffUnitFormula_tffDefinedInfix]
def TffUnitFormula.mkTffDefinedInfix : TffDefinedInfix → TffUnitFormula := TffUnitFormula.tffDefinedInfix

@[export Tptp_mk_TffAndFormula_tffUnitFormulaTffUnitFormula]
def TffAndFormula.mkTffUnitFormulaTffUnitFormula : TffUnitFormula → TffUnitFormula → TffAndFormula := TffAndFormula.tffUnitFormulaTffUnitFormula

@[export Tptp_mk_TffAndFormula_tffAndFormulaTffUnitFormula]
def TffAndFormula.mkTffAndFormulaTffUnitFormula : TffAndFormula → TffUnitFormula → TffAndFormula := TffAndFormula.tffAndFormulaTffUnitFormula

@[export Tptp_mk_TffOrFormula_tffUnitFormulaTffUnitFormula]
def TffOrFormula.mkTffUnitFormulaTffUnitFormula : TffUnitFormula → TffUnitFormula → TffOrFormula := TffOrFormula.tffUnitFormulaTffUnitFormula

@[export Tptp_mk_TffOrFormula_tffOrFormulaTffUnitFormula]
def TffOrFormula.mkTffOrFormulaTffUnitFormula : TffOrFormula → TffUnitFormula → TffOrFormula := TffOrFormula.tffOrFormulaTffUnitFormula

@[export Tptp_mk_TffBinaryAssoc_tffOrFormula]
def TffBinaryAssoc.mkTffOrFormula : TffOrFormula → TffBinaryAssoc := TffBinaryAssoc.tffOrFormula

@[export Tptp_mk_TffBinaryAssoc_tffAndFormula]
def TffBinaryAssoc.mkTffAndFormula : TffAndFormula → TffBinaryAssoc := TffBinaryAssoc.tffAndFormula

@[export Tptp_mk_TffBinaryNonassoc_mk]
def TffBinaryNonassoc.mkMk : TffUnitFormula → NonassocConnective → TffUnitFormula → TffBinaryNonassoc := TffBinaryNonassoc.mk

@[export Tptp_mk_TffBinaryFormula_tffBinaryNonassoc]
def TffBinaryFormula.mkTffBinaryNonassoc : TffBinaryNonassoc → TffBinaryFormula := TffBinaryFormula.tffBinaryNonassoc

@[export Tptp_mk_TffBinaryFormula_tffBinaryAssoc]
def TffBinaryFormula.mkTffBinaryAssoc : TffBinaryAssoc → TffBinaryFormula := TffBinaryFormula.tffBinaryAssoc

@[export Tptp_mk_TffLogicFormula_tffUnitaryFormula]
def TffLogicFormula.mkTffUnitaryFormula : TffUnitaryFormula → TffLogicFormula := TffLogicFormula.tffUnitaryFormula

@[export Tptp_mk_TffLogicFormula_tffUnaryFormula]
def TffLogicFormula.mkTffUnaryFormula : TffUnaryFormula → TffLogicFormula := TffLogicFormula.tffUnaryFormula

@[export Tptp_mk_TffLogicFormula_tffBinaryFormula]
def TffLogicFormula.mkTffBinaryFormula : TffBinaryFormula → TffLogicFormula := TffLogicFormula.tffBinaryFormula

@[export Tptp_mk_TffLogicFormula_tffDefinedInfix]
def TffLogicFormula.mkTffDefinedInfix : TffDefinedInfix → TffLogicFormula := TffLogicFormula.tffDefinedInfix

@[export Tptp_mk_TffLogicFormula_txfDefinition]
def TffLogicFormula.mkTxfDefinition : TxfDefinition → TffLogicFormula := TffLogicFormula.txfDefinition

@[export Tptp_mk_TffLogicFormula_txfSequent]
def TffLogicFormula.mkTxfSequent : TxfSequent → TffLogicFormula := TffLogicFormula.txfSequent

@[export Tptp_mk_ThfSystemAtomic_mk]
def ThfSystemAtomic.mkMk : SystemConstant → ThfSystemAtomic := ThfSystemAtomic.mk

@[export Tptp_mk_Th0Quantifier_caret]
def Th0Quantifier.mkCaret : Th0Quantifier := Th0Quantifier.caret

@[export Tptp_mk_Th0Quantifier_atPlus]
def Th0Quantifier.mkAtPlus : Th0Quantifier := Th0Quantifier.atPlus

@[export Tptp_mk_Th0Quantifier_atMinus]
def Th0Quantifier.mkAtMinus : Th0Quantifier := Th0Quantifier.atMinus

@[export Tptp_mk_ThfQuantifier_tffQuantifier]
def ThfQuantifier.mkTffQuantifier : TffQuantifier → ThfQuantifier := ThfQuantifier.tffQuantifier

@[export Tptp_mk_ThfQuantifier_th0Quantifier]
def ThfQuantifier.mkTh0Quantifier : Th0Quantifier → ThfQuantifier := ThfQuantifier.th0Quantifier

@[export Tptp_mk_ThfQuantifier_typeQuantifier]
def ThfQuantifier.mkTypeQuantifier : TypeQuantifier → ThfQuantifier := ThfQuantifier.typeQuantifier

@[export Tptp_mk_NhfKeyPair_mk]
def NhfKeyPair.mkMk : ThfDefinition → NhfKeyPair := NhfKeyPair.mk

@[export Tptp_mk_NhfParameter_ntfIndex]
def NhfParameter.mkNtfIndex : NtfIndex → NhfParameter := NhfParameter.ntfIndex

@[export Tptp_mk_NhfParameter_nhfKeyPair]
def NhfParameter.mkNhfKeyPair : NhfKeyPair → NhfParameter := NhfParameter.nhfKeyPair

@[export Tptp_mk_NhfParameterList_nhfParameter]
def NhfParameterList.mkNhfParameter : NhfParameter → NhfParameterList := NhfParameterList.nhfParameter

@[export Tptp_mk_NhfParameterList_nhfParameterNhfParameterList]
def NhfParameterList.mkNhfParameterNhfParameterList : NhfParameter → NhfParameterList → NhfParameterList := NhfParameterList.nhfParameterNhfParameterList

@[export Tptp_mk_NhfLongConnective_ntfConnectiveName]
def NhfLongConnective.mkNtfConnectiveName : NtfConnectiveName → NhfLongConnective := NhfLongConnective.ntfConnectiveName

@[export Tptp_mk_NhfLongConnective_ntfConnectiveNameNhfParameterList]
def NhfLongConnective.mkNtfConnectiveNameNhfParameterList : NtfConnectiveName → NhfParameterList → NhfLongConnective := NhfLongConnective.ntfConnectiveNameNhfParameterList

@[export Tptp_mk_ThfSequent_mk]
def ThfSequent.mkMk : ThfTuple → GentzenArrow → ThfTuple → ThfSequent := ThfSequent.mk

@[export Tptp_mk_ThfDefinition_mk]
def ThfDefinition.mkMk : ThfAtomicFormula → Identical → ThfLogicFormula → ThfDefinition := ThfDefinition.mk

@[export Tptp_mk_ThfUnionType_thfUnitaryTypeThfUnitaryType]
def ThfUnionType.mkThfUnitaryTypeThfUnitaryType : ThfUnitaryType → ThfUnitaryType → ThfUnionType := ThfUnionType.thfUnitaryTypeThfUnitaryType

@[export Tptp_mk_ThfUnionType_thfUnionTypeThfUnitaryType]
def ThfUnionType.mkThfUnionTypeThfUnitaryType : ThfUnionType → ThfUnitaryType → ThfUnionType := ThfUnionType.thfUnionTypeThfUnitaryType

@[export Tptp_mk_ThfXprodType_thfUnitaryTypeThfUnitaryType]
def ThfXprodType.mkThfUnitaryTypeThfUnitaryType : ThfUnitaryType → ThfUnitaryType → ThfXprodType := ThfXprodType.thfUnitaryTypeThfUnitaryType

@[export Tptp_mk_ThfXprodType_thfXprodTypeThfUnitaryType]
def ThfXprodType.mkThfXprodTypeThfUnitaryType : ThfXprodType → ThfUnitaryType → ThfXprodType := ThfXprodType.thfXprodTypeThfUnitaryType

@[export Tptp_mk_ThfMappingType_thfUnitaryTypeThfUnitaryType]
def ThfMappingType.mkThfUnitaryTypeThfUnitaryType : ThfUnitaryType → ThfUnitaryType → ThfMappingType := ThfMappingType.thfUnitaryTypeThfUnitaryType

@[export Tptp_mk_ThfMappingType_thfUnitaryTypeThfMappingType]
def ThfMappingType.mkThfUnitaryTypeThfMappingType : ThfUnitaryType → ThfMappingType → ThfMappingType := ThfMappingType.thfUnitaryTypeThfMappingType

@[export Tptp_mk_ThfBinaryType_thfMappingType]
def ThfBinaryType.mkThfMappingType : ThfMappingType → ThfBinaryType := ThfBinaryType.thfMappingType

@[export Tptp_mk_ThfBinaryType_thfXprodType]
def ThfBinaryType.mkThfXprodType : ThfXprodType → ThfBinaryType := ThfBinaryType.thfXprodType

@[export Tptp_mk_ThfBinaryType_thfUnionType]
def ThfBinaryType.mkThfUnionType : ThfUnionType → ThfBinaryType := ThfBinaryType.thfUnionType

@[export Tptp_mk_ThfApplyType_mk]
def ThfApplyType.mkMk : ThfApplyFormula → ThfApplyType := ThfApplyType.mk

@[export Tptp_mk_ThfUnitaryType_mk]
def ThfUnitaryType.mkMk : ThfUnitaryFormula → ThfUnitaryType := ThfUnitaryType.mk

@[export Tptp_mk_ThfTopLevelType_thfUnitaryType]
def ThfTopLevelType.mkThfUnitaryType : ThfUnitaryType → ThfTopLevelType := ThfTopLevelType.thfUnitaryType

@[export Tptp_mk_ThfTopLevelType_thfMappingType]
def ThfTopLevelType.mkThfMappingType : ThfMappingType → ThfTopLevelType := ThfTopLevelType.thfMappingType

@[export Tptp_mk_ThfTopLevelType_thfApplyType]
def ThfTopLevelType.mkThfApplyType : ThfApplyType → ThfTopLevelType := ThfTopLevelType.thfApplyType

@[export Tptp_mk_ThfAtomTyping_untypedAtomThfTopLevelType]
def ThfAtomTyping.mkUntypedAtomThfTopLevelType : UntypedAtom → ThfTopLevelType → ThfAtomTyping := ThfAtomTyping.untypedAtomThfTopLevelType

@[export Tptp_mk_ThfAtomTyping_thfAtomTyping]
def ThfAtomTyping.mkThfAtomTyping : ThfAtomTyping → ThfAtomTyping := ThfAtomTyping.thfAtomTyping

@[export Tptp_mk_CommaThfLogicFormula_mk]
def CommaThfLogicFormula.mkMk : ThfLogicFormula → CommaThfLogicFormula := CommaThfLogicFormula.mk

@[export Tptp_mk_ThfFormulaList_mk]
def ThfFormulaList.mkMk : ThfLogicFormula → List CommaThfLogicFormula → ThfFormulaList := ThfFormulaList.mk

@[export Tptp_mk_ThfArguments_mk]
def ThfArguments.mkMk : ThfFormulaList → ThfArguments := ThfArguments.mk

@[export Tptp_mk_ThfFofFunction_functorThfArguments]
def ThfFofFunction.mkFunctorThfArguments : Functor → ThfArguments → ThfFofFunction := ThfFofFunction.functorThfArguments

@[export Tptp_mk_ThfFofFunction_definedFunctorThfArguments]
def ThfFofFunction.mkDefinedFunctorThfArguments : DefinedFunctor → ThfArguments → ThfFofFunction := ThfFofFunction.definedFunctorThfArguments

@[export Tptp_mk_ThfFofFunction_systemFunctorThfArguments]
def ThfFofFunction.mkSystemFunctorThfArguments : SystemFunctor → ThfArguments → ThfFofFunction := ThfFofFunction.systemFunctorThfArguments

@[export Tptp_mk_ThfTuple_empty]
def ThfTuple.mkEmpty : ThfTuple := ThfTuple.empty

@[export Tptp_mk_ThfTuple_thfFormulaList]
def ThfTuple.mkThfFormulaList : ThfFormulaList → ThfTuple := ThfTuple.thfFormulaList

@[export Tptp_mk_ThfUnitaryTerm_thfAtomicFormula]
def ThfUnitaryTerm.mkThfAtomicFormula : ThfAtomicFormula → ThfUnitaryTerm := ThfUnitaryTerm.thfAtomicFormula

@[export Tptp_mk_ThfUnitaryTerm_variable]
def ThfUnitaryTerm.mkVariable : Variable → ThfUnitaryTerm := ThfUnitaryTerm.variable

@[export Tptp_mk_ThfUnitaryTerm_thfLogicFormula]
def ThfUnitaryTerm.mkThfLogicFormula : ThfLogicFormula → ThfUnitaryTerm := ThfUnitaryTerm.thfLogicFormula

@[export Tptp_mk_ThfLetDefnList_thfLetDefn]
def ThfLetDefnList.mkThfLetDefn : ThfLetDefn → ThfLetDefnList := ThfLetDefnList.thfLetDefn

@[export Tptp_mk_ThfLetDefnList_thfLetDefnThfLetDefnList]
def ThfLetDefnList.mkThfLetDefnThfLetDefnList : ThfLetDefn → ThfLetDefnList → ThfLetDefnList := ThfLetDefnList.thfLetDefnThfLetDefnList

@[export Tptp_mk_ThfLetDefn_mk]
def ThfLetDefn.mkMk : ThfLogicFormula → Assignment → ThfLogicFormula → ThfLetDefn := ThfLetDefn.mk

@[export Tptp_mk_ThfLetDefns_thfLetDefn]
def ThfLetDefns.mkThfLetDefn : ThfLetDefn → ThfLetDefns := ThfLetDefns.thfLetDefn

@[export Tptp_mk_ThfLetDefns_thfLetDefnList]
def ThfLetDefns.mkThfLetDefnList : ThfLetDefnList → ThfLetDefns := ThfLetDefns.thfLetDefnList

@[export Tptp_mk_ThfAtomTypingList_thfAtomTyping]
def ThfAtomTypingList.mkThfAtomTyping : ThfAtomTyping → ThfAtomTypingList := ThfAtomTypingList.thfAtomTyping

@[export Tptp_mk_ThfAtomTypingList_thfAtomTypingThfAtomTypingList]
def ThfAtomTypingList.mkThfAtomTypingThfAtomTypingList : ThfAtomTyping → ThfAtomTypingList → ThfAtomTypingList := ThfAtomTypingList.thfAtomTypingThfAtomTypingList

@[export Tptp_mk_ThfLetTypes_thfAtomTyping]
def ThfLetTypes.mkThfAtomTyping : ThfAtomTyping → ThfLetTypes := ThfLetTypes.thfAtomTyping

@[export Tptp_mk_ThfLetTypes_thfAtomTypingList]
def ThfLetTypes.mkThfAtomTypingList : ThfAtomTypingList → ThfLetTypes := ThfLetTypes.thfAtomTypingList

@[export Tptp_mk_ThfLet_mk]
def ThfLet.mkMk : ThfLetTypes → ThfLetDefns → ThfLogicFormula → ThfLet := ThfLet.mk

@[export Tptp_mk_ThfDefinedInfix_mk]
def ThfDefinedInfix.mkMk : ThfUnitaryTerm → DefinedInfixPred → ThfUnitaryTerm → ThfDefinedInfix := ThfDefinedInfix.mk

@[export Tptp_mk_ThfDefinedAtomic_definedConstant]
def ThfDefinedAtomic.mkDefinedConstant : DefinedConstant → ThfDefinedAtomic := ThfDefinedAtomic.definedConstant

@[export Tptp_mk_ThfDefinedAtomic_thfDefinedTerm]
def ThfDefinedAtomic.mkThfDefinedTerm : ThfDefinedTerm → ThfDefinedAtomic := ThfDefinedAtomic.thfDefinedTerm

@[export Tptp_mk_ThfDefinedAtomic_thfConnTerm]
def ThfDefinedAtomic.mkThfConnTerm : ThfConnTerm → ThfDefinedAtomic := ThfDefinedAtomic.thfConnTerm

@[export Tptp_mk_ThfDefinedAtomic_nhfLongConnective]
def ThfDefinedAtomic.mkNhfLongConnective : NhfLongConnective → ThfDefinedAtomic := ThfDefinedAtomic.nhfLongConnective

@[export Tptp_mk_ThfDefinedAtomic_thfLet]
def ThfDefinedAtomic.mkThfLet : ThfLet → ThfDefinedAtomic := ThfDefinedAtomic.thfLet

@[export Tptp_mk_ThfPlainAtomic_constant]
def ThfPlainAtomic.mkConstant : Constant → ThfPlainAtomic := ThfPlainAtomic.constant

@[export Tptp_mk_ThfPlainAtomic_thfTuple]
def ThfPlainAtomic.mkThfTuple : ThfTuple → ThfPlainAtomic := ThfPlainAtomic.thfTuple

@[export Tptp_mk_ThfAtomicFormula_thfPlainAtomic]
def ThfAtomicFormula.mkThfPlainAtomic : ThfPlainAtomic → ThfAtomicFormula := ThfAtomicFormula.thfPlainAtomic

@[export Tptp_mk_ThfAtomicFormula_thfDefinedAtomic]
def ThfAtomicFormula.mkThfDefinedAtomic : ThfDefinedAtomic → ThfAtomicFormula := ThfAtomicFormula.thfDefinedAtomic

@[export Tptp_mk_ThfAtomicFormula_thfSystemAtomic]
def ThfAtomicFormula.mkThfSystemAtomic : ThfSystemAtomic → ThfAtomicFormula := ThfAtomicFormula.thfSystemAtomic

@[export Tptp_mk_ThfAtomicFormula_thfFofFunction]
def ThfAtomicFormula.mkThfFofFunction : ThfFofFunction → ThfAtomicFormula := ThfAtomicFormula.thfFofFunction

@[export Tptp_mk_ThfInfixUnary_mk]
def ThfInfixUnary.mkMk : ThfUnitaryTerm → InfixInequality → ThfUnitaryTerm → ThfInfixUnary := ThfInfixUnary.mk

@[export Tptp_mk_ThfPrefixUnary_mk]
def ThfPrefixUnary.mkMk : ThfUnaryConnective → ThfPreunitFormula → ThfPrefixUnary := ThfPrefixUnary.mk

@[export Tptp_mk_ThfUnaryFormula_thfPrefixUnary]
def ThfUnaryFormula.mkThfPrefixUnary : ThfPrefixUnary → ThfUnaryFormula := ThfUnaryFormula.thfPrefixUnary

@[export Tptp_mk_ThfUnaryFormula_thfInfixUnary]
def ThfUnaryFormula.mkThfInfixUnary : ThfInfixUnary → ThfUnaryFormula := ThfUnaryFormula.thfInfixUnary

@[export Tptp_mk_ThfTypedVariable_mk]
def ThfTypedVariable.mkMk : Variable → ThfTopLevelType → ThfTypedVariable := ThfTypedVariable.mk

@[export Tptp_mk_ThfVariableList_thfTypedVariable]
def ThfVariableList.mkThfTypedVariable : ThfTypedVariable → ThfVariableList := ThfVariableList.thfTypedVariable

@[export Tptp_mk_ThfVariableList_thfTypedVariableThfVariableList]
def ThfVariableList.mkThfTypedVariableThfVariableList : ThfTypedVariable → ThfVariableList → ThfVariableList := ThfVariableList.thfTypedVariableThfVariableList

@[export Tptp_mk_ThfQuantification_mk]
def ThfQuantification.mkMk : ThfQuantifier → ThfVariableList → ThfQuantification := ThfQuantification.mk

@[export Tptp_mk_ThfQuantifiedFormula_mk]
def ThfQuantifiedFormula.mkMk : ThfQuantification → ThfUnitFormula → ThfQuantifiedFormula := ThfQuantifiedFormula.mk

@[export Tptp_mk_ThfUnitaryFormula_thfQuantifiedFormula]
def ThfUnitaryFormula.mkThfQuantifiedFormula : ThfQuantifiedFormula → ThfUnitaryFormula := ThfUnitaryFormula.thfQuantifiedFormula

@[export Tptp_mk_ThfUnitaryFormula_thfAtomicFormula]
def ThfUnitaryFormula.mkThfAtomicFormula : ThfAtomicFormula → ThfUnitaryFormula := ThfUnitaryFormula.thfAtomicFormula

@[export Tptp_mk_ThfUnitaryFormula_variable]
def ThfUnitaryFormula.mkVariable : Variable → ThfUnitaryFormula := ThfUnitaryFormula.variable

@[export Tptp_mk_ThfUnitaryFormula_thfLogicFormula]
def ThfUnitaryFormula.mkThfLogicFormula : ThfLogicFormula → ThfUnitaryFormula := ThfUnitaryFormula.thfLogicFormula

@[export Tptp_mk_ThfPreunitFormula_thfUnitaryFormula]
def ThfPreunitFormula.mkThfUnitaryFormula : ThfUnitaryFormula → ThfPreunitFormula := ThfPreunitFormula.thfUnitaryFormula

@[export Tptp_mk_ThfPreunitFormula_thfPrefixUnary]
def ThfPreunitFormula.mkThfPrefixUnary : ThfPrefixUnary → ThfPreunitFormula := ThfPreunitFormula.thfPrefixUnary

@[export Tptp_mk_ThfUnitFormula_thfUnitaryFormula]
def ThfUnitFormula.mkThfUnitaryFormula : ThfUnitaryFormula → ThfUnitFormula := ThfUnitFormula.thfUnitaryFormula

@[export Tptp_mk_ThfUnitFormula_thfUnaryFormula]
def ThfUnitFormula.mkThfUnaryFormula : ThfUnaryFormula → ThfUnitFormula := ThfUnitFormula.thfUnaryFormula

@[export Tptp_mk_ThfUnitFormula_thfDefinedInfix]
def ThfUnitFormula.mkThfDefinedInfix : ThfDefinedInfix → ThfUnitFormula := ThfUnitFormula.thfDefinedInfix

@[export Tptp_mk_ThfApplyFormula_thfUnitFormulaThfUnitFormula]
def ThfApplyFormula.mkThfUnitFormulaThfUnitFormula : ThfUnitFormula → ThfUnitFormula → ThfApplyFormula := ThfApplyFormula.thfUnitFormulaThfUnitFormula

@[export Tptp_mk_ThfApplyFormula_thfApplyFormulaThfUnitFormula]
def ThfApplyFormula.mkThfApplyFormulaThfUnitFormula : ThfApplyFormula → ThfUnitFormula → ThfApplyFormula := ThfApplyFormula.thfApplyFormulaThfUnitFormula

@[export Tptp_mk_ThfAndFormula_thfUnitFormulaThfUnitFormula]
def ThfAndFormula.mkThfUnitFormulaThfUnitFormula : ThfUnitFormula → ThfUnitFormula → ThfAndFormula := ThfAndFormula.thfUnitFormulaThfUnitFormula

@[export Tptp_mk_ThfAndFormula_thfAndFormulaThfUnitFormula]
def ThfAndFormula.mkThfAndFormulaThfUnitFormula : ThfAndFormula → ThfUnitFormula → ThfAndFormula := ThfAndFormula.thfAndFormulaThfUnitFormula

@[export Tptp_mk_ThfOrFormula_thfUnitFormulaThfUnitFormula]
def ThfOrFormula.mkThfUnitFormulaThfUnitFormula : ThfUnitFormula → ThfUnitFormula → ThfOrFormula := ThfOrFormula.thfUnitFormulaThfUnitFormula

@[export Tptp_mk_ThfOrFormula_thfOrFormulaThfUnitFormula]
def ThfOrFormula.mkThfOrFormulaThfUnitFormula : ThfOrFormula → ThfUnitFormula → ThfOrFormula := ThfOrFormula.thfOrFormulaThfUnitFormula

@[export Tptp_mk_ThfBinaryAssoc_thfOrFormula]
def ThfBinaryAssoc.mkThfOrFormula : ThfOrFormula → ThfBinaryAssoc := ThfBinaryAssoc.thfOrFormula

@[export Tptp_mk_ThfBinaryAssoc_thfAndFormula]
def ThfBinaryAssoc.mkThfAndFormula : ThfAndFormula → ThfBinaryAssoc := ThfBinaryAssoc.thfAndFormula

@[export Tptp_mk_ThfBinaryAssoc_thfApplyFormula]
def ThfBinaryAssoc.mkThfApplyFormula : ThfApplyFormula → ThfBinaryAssoc := ThfBinaryAssoc.thfApplyFormula

@[export Tptp_mk_ThfBinaryNonassoc_mk]
def ThfBinaryNonassoc.mkMk : ThfUnitFormula → NonassocConnective → ThfUnitFormula → ThfBinaryNonassoc := ThfBinaryNonassoc.mk

@[export Tptp_mk_ThfBinaryFormula_thfBinaryNonassoc]
def ThfBinaryFormula.mkThfBinaryNonassoc : ThfBinaryNonassoc → ThfBinaryFormula := ThfBinaryFormula.thfBinaryNonassoc

@[export Tptp_mk_ThfBinaryFormula_thfBinaryAssoc]
def ThfBinaryFormula.mkThfBinaryAssoc : ThfBinaryAssoc → ThfBinaryFormula := ThfBinaryFormula.thfBinaryAssoc

@[export Tptp_mk_ThfBinaryFormula_thfBinaryType]
def ThfBinaryFormula.mkThfBinaryType : ThfBinaryType → ThfBinaryFormula := ThfBinaryFormula.thfBinaryType

@[export Tptp_mk_ThfLogicFormula_thfUnitaryFormula]
def ThfLogicFormula.mkThfUnitaryFormula : ThfUnitaryFormula → ThfLogicFormula := ThfLogicFormula.thfUnitaryFormula

@[export Tptp_mk_ThfLogicFormula_thfUnaryFormula]
def ThfLogicFormula.mkThfUnaryFormula : ThfUnaryFormula → ThfLogicFormula := ThfLogicFormula.thfUnaryFormula

@[export Tptp_mk_ThfLogicFormula_thfBinaryFormula]
def ThfLogicFormula.mkThfBinaryFormula : ThfBinaryFormula → ThfLogicFormula := ThfLogicFormula.thfBinaryFormula

@[export Tptp_mk_ThfLogicFormula_thfDefinedInfix]
def ThfLogicFormula.mkThfDefinedInfix : ThfDefinedInfix → ThfLogicFormula := ThfLogicFormula.thfDefinedInfix

@[export Tptp_mk_ThfLogicFormula_thfDefinition]
def ThfLogicFormula.mkThfDefinition : ThfDefinition → ThfLogicFormula := ThfLogicFormula.thfDefinition

@[export Tptp_mk_ThfLogicFormula_thfSequent]
def ThfLogicFormula.mkThfSequent : ThfSequent → ThfLogicFormula := ThfLogicFormula.thfSequent

@[export Tptp_mk_Atom_untypedAtom]
def Atom.mkUntypedAtom : UntypedAtom → Atom := Atom.untypedAtom

@[export Tptp_mk_Atom_definedConstant]
def Atom.mkDefinedConstant : DefinedConstant → Atom := Atom.definedConstant

@[export Tptp_mk_SubtypeSign_mk]
def SubtypeSign.mkMk : SubtypeSign := SubtypeSign.mk

@[export Tptp_mk_ThfSubtype_mk]
def ThfSubtype.mkMk : UntypedAtom → SubtypeSign → Atom → ThfSubtype := ThfSubtype.mk

@[export Tptp_mk_ThfFormula_thfLogicFormula]
def ThfFormula.mkThfLogicFormula : ThfLogicFormula → ThfFormula := ThfFormula.thfLogicFormula

@[export Tptp_mk_ThfFormula_thfAtomTyping]
def ThfFormula.mkThfAtomTyping : ThfAtomTyping → ThfFormula := ThfFormula.thfAtomTyping

@[export Tptp_mk_ThfFormula_thfSubtype]
def ThfFormula.mkThfSubtype : ThfSubtype → ThfFormula := ThfFormula.thfSubtype

@[export Tptp_mk_FofFunctionTerm_fofPlainTerm]
def FofFunctionTerm.mkFofPlainTerm : FofPlainTerm → FofFunctionTerm := FofFunctionTerm.fofPlainTerm

@[export Tptp_mk_FofFunctionTerm_fofDefinedTerm]
def FofFunctionTerm.mkFofDefinedTerm : FofDefinedTerm → FofFunctionTerm := FofFunctionTerm.fofDefinedTerm

@[export Tptp_mk_FofFunctionTerm_fofSystemTerm]
def FofFunctionTerm.mkFofSystemTerm : FofSystemTerm → FofFunctionTerm := FofFunctionTerm.fofSystemTerm

@[export Tptp_mk_FofTerm_fofFunctionTerm]
def FofTerm.mkFofFunctionTerm : FofFunctionTerm → FofTerm := FofTerm.fofFunctionTerm

@[export Tptp_mk_FofTerm_variable]
def FofTerm.mkVariable : Variable → FofTerm := FofTerm.variable

@[export Tptp_mk_FofArguments_fofTerm]
def FofArguments.mkFofTerm : FofTerm → FofArguments := FofArguments.fofTerm

@[export Tptp_mk_FofArguments_fofTermFofArguments]
def FofArguments.mkFofTermFofArguments : FofTerm → FofArguments → FofArguments := FofArguments.fofTermFofArguments

@[export Tptp_mk_FofSystemTerm_systemConstant]
def FofSystemTerm.mkSystemConstant : SystemConstant → FofSystemTerm := FofSystemTerm.systemConstant

@[export Tptp_mk_FofSystemTerm_systemFunctorFofArguments]
def FofSystemTerm.mkSystemFunctorFofArguments : SystemFunctor → FofArguments → FofSystemTerm := FofSystemTerm.systemFunctorFofArguments

@[export Tptp_mk_FofDefinedPlainTerm_definedConstant]
def FofDefinedPlainTerm.mkDefinedConstant : DefinedConstant → FofDefinedPlainTerm := FofDefinedPlainTerm.definedConstant

@[export Tptp_mk_FofDefinedPlainTerm_definedFunctorFofArguments]
def FofDefinedPlainTerm.mkDefinedFunctorFofArguments : DefinedFunctor → FofArguments → FofDefinedPlainTerm := FofDefinedPlainTerm.definedFunctorFofArguments

@[export Tptp_mk_FofDefinedAtomicTerm_mk]
def FofDefinedAtomicTerm.mkMk : FofDefinedPlainTerm → FofDefinedAtomicTerm := FofDefinedAtomicTerm.mk

@[export Tptp_mk_FofDefinedTerm_definedTerm]
def FofDefinedTerm.mkDefinedTerm : DefinedTerm → FofDefinedTerm := FofDefinedTerm.definedTerm

@[export Tptp_mk_FofDefinedTerm_fofDefinedAtomicTerm]
def FofDefinedTerm.mkFofDefinedAtomicTerm : FofDefinedAtomicTerm → FofDefinedTerm := FofDefinedTerm.fofDefinedAtomicTerm

@[export Tptp_mk_FofPlainTerm_constant]
def FofPlainTerm.mkConstant : Constant → FofPlainTerm := FofPlainTerm.constant

@[export Tptp_mk_FofPlainTerm_functorFofArguments]
def FofPlainTerm.mkFunctorFofArguments : Functor → FofArguments → FofPlainTerm := FofPlainTerm.functorFofArguments

@[export Tptp_mk_TffSubtype_mk]
def TffSubtype.mkMk : UntypedAtom → SubtypeSign → Atom → TffSubtype := TffSubtype.mk

@[export Tptp_mk_TffFormula_tffLogicFormula]
def TffFormula.mkTffLogicFormula : TffLogicFormula → TffFormula := TffFormula.tffLogicFormula

@[export Tptp_mk_TffFormula_tffAtomTyping]
def TffFormula.mkTffAtomTyping : TffAtomTyping → TffFormula := TffFormula.tffAtomTyping

@[export Tptp_mk_TffFormula_tffSubtype]
def TffFormula.mkTffSubtype : TffSubtype → TffFormula := TffFormula.tffSubtype

@[export Tptp_mk_FofSystemAtomicFormula_mk]
def FofSystemAtomicFormula.mkMk : FofSystemTerm → FofSystemAtomicFormula := FofSystemAtomicFormula.mk

@[export Tptp_mk_FofPlainAtomicFormula_mk]
def FofPlainAtomicFormula.mkMk : FofPlainTerm → FofPlainAtomicFormula := FofPlainAtomicFormula.mk

@[export Tptp_mk_FofDefinedPlainFormula_mk]
def FofDefinedPlainFormula.mkMk : FofDefinedPlainTerm → FofDefinedPlainFormula := FofDefinedPlainFormula.mk

@[export Tptp_mk_FofDefinedInfixFormula_mk]
def FofDefinedInfixFormula.mkMk : FofTerm → DefinedInfixPred → FofTerm → FofDefinedInfixFormula := FofDefinedInfixFormula.mk

@[export Tptp_mk_FofDefinedAtomicFormula_fofDefinedPlainFormula]
def FofDefinedAtomicFormula.mkFofDefinedPlainFormula : FofDefinedPlainFormula → FofDefinedAtomicFormula := FofDefinedAtomicFormula.fofDefinedPlainFormula

@[export Tptp_mk_FofDefinedAtomicFormula_fofDefinedInfixFormula]
def FofDefinedAtomicFormula.mkFofDefinedInfixFormula : FofDefinedInfixFormula → FofDefinedAtomicFormula := FofDefinedAtomicFormula.fofDefinedInfixFormula

@[export Tptp_mk_FofAtomicFormula_fofPlainAtomicFormula]
def FofAtomicFormula.mkFofPlainAtomicFormula : FofPlainAtomicFormula → FofAtomicFormula := FofAtomicFormula.fofPlainAtomicFormula

@[export Tptp_mk_FofAtomicFormula_fofDefinedAtomicFormula]
def FofAtomicFormula.mkFofDefinedAtomicFormula : FofDefinedAtomicFormula → FofAtomicFormula := FofAtomicFormula.fofDefinedAtomicFormula

@[export Tptp_mk_FofAtomicFormula_fofSystemAtomicFormula]
def FofAtomicFormula.mkFofSystemAtomicFormula : FofSystemAtomicFormula → FofAtomicFormula := FofAtomicFormula.fofSystemAtomicFormula

@[export Tptp_mk_FofInfixUnary_mk]
def FofInfixUnary.mkMk : FofTerm → InfixInequality → FofTerm → FofInfixUnary := FofInfixUnary.mk

@[export Tptp_mk_CnfLiteral_fofAtomicFormula]
def CnfLiteral.mkFofAtomicFormula : FofAtomicFormula → CnfLiteral := CnfLiteral.fofAtomicFormula

@[export Tptp_mk_CnfLiteral_fofAtomicFormulaNegated]
def CnfLiteral.mkFofAtomicFormulaNegated : FofAtomicFormula → CnfLiteral := CnfLiteral.fofAtomicFormulaNegated

@[export Tptp_mk_CnfLiteral_fofInfixUnary]
def CnfLiteral.mkFofInfixUnary : FofInfixUnary → CnfLiteral := CnfLiteral.fofInfixUnary

@[export Tptp_mk_CnfDisjunction_cnfLiteral]
def CnfDisjunction.mkCnfLiteral : CnfLiteral → CnfDisjunction := CnfDisjunction.cnfLiteral

@[export Tptp_mk_CnfDisjunction_cnfDisjunctionCnfLiteral]
def CnfDisjunction.mkCnfDisjunctionCnfLiteral : CnfDisjunction → CnfLiteral → CnfDisjunction := CnfDisjunction.cnfDisjunctionCnfLiteral

@[export Tptp_mk_CnfFormula_cnfDisjunction]
def CnfFormula.mkCnfDisjunction : CnfDisjunction → CnfFormula := CnfFormula.cnfDisjunction

@[export Tptp_mk_CnfFormula_cnfFormula]
def CnfFormula.mkCnfFormula : CnfFormula → CnfFormula := CnfFormula.cnfFormula

@[export Tptp_mk_FofVariableList_variable]
def FofVariableList.mkVariable : Variable → FofVariableList := FofVariableList.variable

@[export Tptp_mk_FofVariableList_variableFofVariableList]
def FofVariableList.mkVariableFofVariableList : Variable → FofVariableList → FofVariableList := FofVariableList.variableFofVariableList

@[export Tptp_mk_FofQuantifiedFormula_mk]
def FofQuantifiedFormula.mkMk : FofQuantifier → FofVariableList → FofUnitFormula → FofQuantifiedFormula := FofQuantifiedFormula.mk

@[export Tptp_mk_FofUnitaryFormula_fofQuantifiedFormula]
def FofUnitaryFormula.mkFofQuantifiedFormula : FofQuantifiedFormula → FofUnitaryFormula := FofUnitaryFormula.fofQuantifiedFormula

@[export Tptp_mk_FofUnitaryFormula_fofAtomicFormula]
def FofUnitaryFormula.mkFofAtomicFormula : FofAtomicFormula → FofUnitaryFormula := FofUnitaryFormula.fofAtomicFormula

@[export Tptp_mk_FofUnitaryFormula_fofLogicFormula]
def FofUnitaryFormula.mkFofLogicFormula : FofLogicFormula → FofUnitaryFormula := FofUnitaryFormula.fofLogicFormula

@[export Tptp_mk_FofUnitFormula_fofUnitaryFormula]
def FofUnitFormula.mkFofUnitaryFormula : FofUnitaryFormula → FofUnitFormula := FofUnitFormula.fofUnitaryFormula

@[export Tptp_mk_FofUnitFormula_fofUnaryFormula]
def FofUnitFormula.mkFofUnaryFormula : FofUnaryFormula → FofUnitFormula := FofUnitFormula.fofUnaryFormula

@[export Tptp_mk_FofUnaryFormula_unaryConnectiveFofUnitFormula]
def FofUnaryFormula.mkUnaryConnectiveFofUnitFormula : UnaryConnective → FofUnitFormula → FofUnaryFormula := FofUnaryFormula.unaryConnectiveFofUnitFormula

@[export Tptp_mk_FofUnaryFormula_fofInfixUnary]
def FofUnaryFormula.mkFofInfixUnary : FofInfixUnary → FofUnaryFormula := FofUnaryFormula.fofInfixUnary

@[export Tptp_mk_FofAndFormula_fofUnitFormulaFofUnitFormula]
def FofAndFormula.mkFofUnitFormulaFofUnitFormula : FofUnitFormula → FofUnitFormula → FofAndFormula := FofAndFormula.fofUnitFormulaFofUnitFormula

@[export Tptp_mk_FofAndFormula_fofAndFormulaFofUnitFormula]
def FofAndFormula.mkFofAndFormulaFofUnitFormula : FofAndFormula → FofUnitFormula → FofAndFormula := FofAndFormula.fofAndFormulaFofUnitFormula

@[export Tptp_mk_FofOrFormula_fofUnitFormulaFofUnitFormula]
def FofOrFormula.mkFofUnitFormulaFofUnitFormula : FofUnitFormula → FofUnitFormula → FofOrFormula := FofOrFormula.fofUnitFormulaFofUnitFormula

@[export Tptp_mk_FofOrFormula_fofOrFormulaFofUnitFormula]
def FofOrFormula.mkFofOrFormulaFofUnitFormula : FofOrFormula → FofUnitFormula → FofOrFormula := FofOrFormula.fofOrFormulaFofUnitFormula

@[export Tptp_mk_FofBinaryAssoc_fofOrFormula]
def FofBinaryAssoc.mkFofOrFormula : FofOrFormula → FofBinaryAssoc := FofBinaryAssoc.fofOrFormula

@[export Tptp_mk_FofBinaryAssoc_fofAndFormula]
def FofBinaryAssoc.mkFofAndFormula : FofAndFormula → FofBinaryAssoc := FofBinaryAssoc.fofAndFormula

@[export Tptp_mk_FofBinaryNonassoc_mk]
def FofBinaryNonassoc.mkMk : FofUnitFormula → NonassocConnective → FofUnitFormula → FofBinaryNonassoc := FofBinaryNonassoc.mk

@[export Tptp_mk_FofBinaryFormula_fofBinaryNonassoc]
def FofBinaryFormula.mkFofBinaryNonassoc : FofBinaryNonassoc → FofBinaryFormula := FofBinaryFormula.fofBinaryNonassoc

@[export Tptp_mk_FofBinaryFormula_fofBinaryAssoc]
def FofBinaryFormula.mkFofBinaryAssoc : FofBinaryAssoc → FofBinaryFormula := FofBinaryFormula.fofBinaryAssoc

@[export Tptp_mk_FofLogicFormula_fofBinaryFormula]
def FofLogicFormula.mkFofBinaryFormula : FofBinaryFormula → FofLogicFormula := FofLogicFormula.fofBinaryFormula

@[export Tptp_mk_FofLogicFormula_fofUnaryFormula]
def FofLogicFormula.mkFofUnaryFormula : FofUnaryFormula → FofLogicFormula := FofLogicFormula.fofUnaryFormula

@[export Tptp_mk_FofLogicFormula_fofUnitaryFormula]
def FofLogicFormula.mkFofUnitaryFormula : FofUnitaryFormula → FofLogicFormula := FofLogicFormula.fofUnitaryFormula

@[export Tptp_mk_CommaFofLogicFormula_mk]
def CommaFofLogicFormula.mkMk : FofLogicFormula → CommaFofLogicFormula := CommaFofLogicFormula.mk

@[export Tptp_mk_FofFormulaTupleList_mk]
def FofFormulaTupleList.mkMk : FofLogicFormula → List CommaFofLogicFormula → FofFormulaTupleList := FofFormulaTupleList.mk

@[export Tptp_mk_FofFormulaTuple_empty]
def FofFormulaTuple.mkEmpty : FofFormulaTuple := FofFormulaTuple.empty

@[export Tptp_mk_FofFormulaTuple_fofFormulaTupleList]
def FofFormulaTuple.mkFofFormulaTupleList : FofFormulaTupleList → FofFormulaTuple := FofFormulaTuple.fofFormulaTupleList

@[export Tptp_mk_FofSequent_fofFormulaTupleGentzenArrowFofFormulaTuple]
def FofSequent.mkFofFormulaTupleGentzenArrowFofFormulaTuple : FofFormulaTuple → GentzenArrow → FofFormulaTuple → FofSequent := FofSequent.fofFormulaTupleGentzenArrowFofFormulaTuple

@[export Tptp_mk_FofSequent_fofSequent]
def FofSequent.mkFofSequent : FofSequent → FofSequent := FofSequent.fofSequent

@[export Tptp_mk_FofFormula_fofLogicFormula]
def FofFormula.mkFofLogicFormula : FofLogicFormula → FofFormula := FofFormula.fofLogicFormula

@[export Tptp_mk_FofFormula_fofSequent]
def FofFormula.mkFofSequent : FofSequent → FofFormula := FofFormula.fofSequent

@[export Tptp_mk_FormulaData_thfFormula]
def FormulaData.mkThfFormula : ThfFormula → FormulaData := FormulaData.thfFormula

@[export Tptp_mk_FormulaData_tffFormula]
def FormulaData.mkTffFormula : TffFormula → FormulaData := FormulaData.tffFormula

@[export Tptp_mk_FormulaData_fofFormula]
def FormulaData.mkFofFormula : FofFormula → FormulaData := FormulaData.fofFormula

@[export Tptp_mk_FormulaData_cnfFormula]
def FormulaData.mkCnfFormula : CnfFormula → FormulaData := FormulaData.cnfFormula

@[export Tptp_mk_FormulaData_fofTerm]
def FormulaData.mkFofTerm : FofTerm → FormulaData := FormulaData.fofTerm

@[export Tptp_mk_CommaGeneralTerm_mk]
def CommaGeneralTerm.mkMk : GeneralTerm → CommaGeneralTerm := CommaGeneralTerm.mk

@[export Tptp_mk_GeneralTerms_mk]
def GeneralTerms.mkMk : GeneralTerm → List CommaGeneralTerm → GeneralTerms := GeneralTerms.mk

@[export Tptp_mk_GeneralList_empty]
def GeneralList.mkEmpty : GeneralList := GeneralList.empty

@[export Tptp_mk_GeneralList_generalTerms]
def GeneralList.mkGeneralTerms : GeneralTerms → GeneralList := GeneralList.generalTerms

@[export Tptp_mk_GeneralFunction_mk]
def GeneralFunction.mkMk : AtomicWord → GeneralTerms → GeneralFunction := GeneralFunction.mk

@[export Tptp_mk_GeneralData_atomicWord]
def GeneralData.mkAtomicWord : AtomicWord → GeneralData := GeneralData.atomicWord

@[export Tptp_mk_GeneralData_generalFunction]
def GeneralData.mkGeneralFunction : GeneralFunction → GeneralData := GeneralData.generalFunction

@[export Tptp_mk_GeneralData_variable]
def GeneralData.mkVariable : Variable → GeneralData := GeneralData.variable

@[export Tptp_mk_GeneralData_number]
def GeneralData.mkNumber : Number → GeneralData := GeneralData.number

@[export Tptp_mk_GeneralData_distinctObject]
def GeneralData.mkDistinctObject : DistinctObject → GeneralData := GeneralData.distinctObject

@[export Tptp_mk_GeneralData_formulaData]
def GeneralData.mkFormulaData : FormulaData → GeneralData := GeneralData.formulaData

@[export Tptp_mk_GeneralTerm_generalData]
def GeneralTerm.mkGeneralData : GeneralData → GeneralTerm := GeneralTerm.generalData

@[export Tptp_mk_GeneralTerm_generalDataGeneralTerm]
def GeneralTerm.mkGeneralDataGeneralTerm : GeneralData → GeneralTerm → GeneralTerm := GeneralTerm.generalDataGeneralTerm

@[export Tptp_mk_GeneralTerm_generalList]
def GeneralTerm.mkGeneralList : GeneralList → GeneralTerm := GeneralTerm.generalList

@[export Tptp_mk_UsefulInfo_mk]
def UsefulInfo.mkMk : GeneralList → UsefulInfo := UsefulInfo.mk

@[export Tptp_mk_InferenceRule_mk]
def InferenceRule.mkMk : AtomicWord → InferenceRule := InferenceRule.mk

@[export Tptp_mk_ParentDetails_generalTerm]
def ParentDetails.mkGeneralTerm : GeneralTerm → ParentDetails := ParentDetails.generalTerm

@[export Tptp_mk_ParentDetails_nothing]
def ParentDetails.mkNothing : ParentDetails := ParentDetails.nothing

@[export Tptp_mk_IntroType_mk]
def IntroType.mkMk : AtomicWord → IntroType := IntroType.mk

@[export Tptp_mk_FileInfo_name]
def FileInfo.mkName : Name → FileInfo := FileInfo.name

@[export Tptp_mk_FileInfo_nothing]
def FileInfo.mkNothing : FileInfo := FileInfo.nothing

@[export Tptp_mk_FileName_mk]
def FileName.mkMk : AtomicWord → FileName := FileName.mk

@[export Tptp_mk_FileSource_mk]
def FileSource.mkMk : FileName → FileInfo → FileSource := FileSource.mk

@[export Tptp_mk_TheoryName_mk]
def TheoryName.mkMk : AtomicWord → TheoryName := TheoryName.mk

@[export Tptp_mk_OptionalInfo_usefulInfo]
def OptionalInfo.mkUsefulInfo : UsefulInfo → OptionalInfo := OptionalInfo.usefulInfo

@[export Tptp_mk_OptionalInfo_nothing]
def OptionalInfo.mkNothing : OptionalInfo := OptionalInfo.nothing

@[export Tptp_mk_Theory_mk]
def Theory.mkMk : TheoryName → OptionalInfo → Theory := Theory.mk

@[export Tptp_mk_CreatorName_mk]
def CreatorName.mkMk : AtomicWord → CreatorName := CreatorName.mk

@[export Tptp_mk_ParentInfo_mk]
def ParentInfo.mkMk : Source → ParentDetails → ParentInfo := ParentInfo.mk

@[export Tptp_mk_CommaParentInfo_mk]
def CommaParentInfo.mkMk : ParentInfo → CommaParentInfo := CommaParentInfo.mk

@[export Tptp_mk_ParentList_mk]
def ParentList.mkMk : ParentInfo → List CommaParentInfo → ParentList := ParentList.mk

@[export Tptp_mk_Parents_empty]
def Parents.mkEmpty : Parents := Parents.empty

@[export Tptp_mk_Parents_parentList]
def Parents.mkParentList : ParentList → Parents := Parents.parentList

@[export Tptp_mk_CreatorSource_mk]
def CreatorSource.mkMk : CreatorName → UsefulInfo → Parents → CreatorSource := CreatorSource.mk

@[export Tptp_mk_ExternalSource_fileSource]
def ExternalSource.mkFileSource : FileSource → ExternalSource := ExternalSource.fileSource

@[export Tptp_mk_ExternalSource_theory]
def ExternalSource.mkTheory : Theory → ExternalSource := ExternalSource.theory

@[export Tptp_mk_ExternalSource_creatorSource]
def ExternalSource.mkCreatorSource : CreatorSource → ExternalSource := ExternalSource.creatorSource

@[export Tptp_mk_InternalSource_mk]
def InternalSource.mkMk : IntroType → UsefulInfo → Parents → InternalSource := InternalSource.mk

@[export Tptp_mk_InferenceRecord_mk]
def InferenceRecord.mkMk : InferenceRule → UsefulInfo → Parents → InferenceRecord := InferenceRecord.mk

@[export Tptp_mk_DagSource_name]
def DagSource.mkName : Name → DagSource := DagSource.name

@[export Tptp_mk_DagSource_inferenceRecord]
def DagSource.mkInferenceRecord : InferenceRecord → DagSource := DagSource.inferenceRecord

@[export Tptp_mk_Sources_source]
def Sources.mkSource : Source → Sources := Sources.source

@[export Tptp_mk_Sources_sourceSources]
def Sources.mkSourceSources : Source → Sources → Sources := Sources.sourceSources

@[export Tptp_mk_Source_dagSource]
def Source.mkDagSource : DagSource → Source := Source.dagSource

@[export Tptp_mk_Source_internalSource]
def Source.mkInternalSource : InternalSource → Source := Source.internalSource

@[export Tptp_mk_Source_externalSource]
def Source.mkExternalSource : ExternalSource → Source := Source.externalSource

@[export Tptp_mk_Source_unknown]
def Source.mkUnknown : Source := Source.unknown

@[export Tptp_mk_Source_sources]
def Source.mkSources : Sources → Source := Source.sources

@[export Tptp_mk_Annotations_sourceOptionalInfo]
def Annotations.mkSourceOptionalInfo : Source → OptionalInfo → Annotations := Annotations.sourceOptionalInfo

@[export Tptp_mk_Annotations_nothing]
def Annotations.mkNothing : Annotations := Annotations.nothing

@[export Tptp_mk_FormulaRole_lowerWord]
def FormulaRole.mkLowerWord : LowerWord → FormulaRole := FormulaRole.lowerWord

@[export Tptp_mk_FormulaRole_lowerWordGeneralTerm]
def FormulaRole.mkLowerWordGeneralTerm : LowerWord → GeneralTerm → FormulaRole := FormulaRole.lowerWordGeneralTerm

@[export Tptp_mk_TpiFormula_mk]
def TpiFormula.mkMk : FofFormula → TpiFormula := TpiFormula.mk

@[export Tptp_mk_TpiAnnotated_mk]
def TpiAnnotated.mkMk : Name → FormulaRole → TpiFormula → Annotations → TpiAnnotated := TpiAnnotated.mk

@[export Tptp_mk_ThfAnnotated_mk]
def ThfAnnotated.mkMk : Name → FormulaRole → ThfFormula → Annotations → ThfAnnotated := ThfAnnotated.mk

@[export Tptp_mk_TffAnnotated_mk]
def TffAnnotated.mkMk : Name → FormulaRole → TffFormula → Annotations → TffAnnotated := TffAnnotated.mk

@[export Tptp_mk_TcfQuantifiedFormula_mk]
def TcfQuantifiedFormula.mkMk : TffVariableList → TcfLogicFormula → TcfQuantifiedFormula := TcfQuantifiedFormula.mk

@[export Tptp_mk_TcfLogicFormula_tcfQuantifiedFormula]
def TcfLogicFormula.mkTcfQuantifiedFormula : TcfQuantifiedFormula → TcfLogicFormula := TcfLogicFormula.tcfQuantifiedFormula

@[export Tptp_mk_TcfLogicFormula_cnfFormula]
def TcfLogicFormula.mkCnfFormula : CnfFormula → TcfLogicFormula := TcfLogicFormula.cnfFormula

@[export Tptp_mk_TcfFormula_tcfLogicFormula]
def TcfFormula.mkTcfLogicFormula : TcfLogicFormula → TcfFormula := TcfFormula.tcfLogicFormula

@[export Tptp_mk_TcfFormula_tffAtomTyping]
def TcfFormula.mkTffAtomTyping : TffAtomTyping → TcfFormula := TcfFormula.tffAtomTyping

@[export Tptp_mk_TcfAnnotated_mk]
def TcfAnnotated.mkMk : Name → FormulaRole → TcfFormula → Annotations → TcfAnnotated := TcfAnnotated.mk

@[export Tptp_mk_FofAnnotated_mk]
def FofAnnotated.mkMk : Name → FormulaRole → FofFormula → Annotations → FofAnnotated := FofAnnotated.mk

@[export Tptp_mk_CnfAnnotated_mk]
def CnfAnnotated.mkMk : Name → FormulaRole → CnfFormula → Annotations → CnfAnnotated := CnfAnnotated.mk

@[export Tptp_mk_AnnotatedFormula_thfAnnotated]
def AnnotatedFormula.mkThfAnnotated : ThfAnnotated → AnnotatedFormula := AnnotatedFormula.thfAnnotated

@[export Tptp_mk_AnnotatedFormula_tffAnnotated]
def AnnotatedFormula.mkTffAnnotated : TffAnnotated → AnnotatedFormula := AnnotatedFormula.tffAnnotated

@[export Tptp_mk_AnnotatedFormula_tcfAnnotated]
def AnnotatedFormula.mkTcfAnnotated : TcfAnnotated → AnnotatedFormula := AnnotatedFormula.tcfAnnotated

@[export Tptp_mk_AnnotatedFormula_fofAnnotated]
def AnnotatedFormula.mkFofAnnotated : FofAnnotated → AnnotatedFormula := AnnotatedFormula.fofAnnotated

@[export Tptp_mk_AnnotatedFormula_cnfAnnotated]
def AnnotatedFormula.mkCnfAnnotated : CnfAnnotated → AnnotatedFormula := AnnotatedFormula.cnfAnnotated

@[export Tptp_mk_AnnotatedFormula_tpiAnnotated]
def AnnotatedFormula.mkTpiAnnotated : TpiAnnotated → AnnotatedFormula := AnnotatedFormula.tpiAnnotated

@[export Tptp_mk_SpaceName_mk]
def SpaceName.mkMk : Name → SpaceName := SpaceName.mk

@[export Tptp_mk_NameList_name]
def NameList.mkName : Name → NameList := NameList.name

@[export Tptp_mk_NameList_nameNameList]
def NameList.mkNameNameList : Name → NameList → NameList := NameList.nameNameList

@[export Tptp_mk_FormulaSelection_nameList]
def FormulaSelection.mkNameList : NameList → FormulaSelection := FormulaSelection.nameList

@[export Tptp_mk_FormulaSelection_star]
def FormulaSelection.mkStar : FormulaSelection := FormulaSelection.star

@[export Tptp_mk_IncludeOptionals_nothing]
def IncludeOptionals.mkNothing : IncludeOptionals := IncludeOptionals.nothing

@[export Tptp_mk_IncludeOptionals_formulaSelection]
def IncludeOptionals.mkFormulaSelection : FormulaSelection → IncludeOptionals := IncludeOptionals.formulaSelection

@[export Tptp_mk_IncludeOptionals_formulaSelectionSpaceName]
def IncludeOptionals.mkFormulaSelectionSpaceName : FormulaSelection → SpaceName → IncludeOptionals := IncludeOptionals.formulaSelectionSpaceName

@[export Tptp_mk_Include_mk]
def Include.mkMk : FileName → IncludeOptionals → Include := Include.mk

@[export Tptp_mk_TptpInput_annotatedFormula]
def TptpInput.mkAnnotatedFormula : AnnotatedFormula → TptpInput := TptpInput.annotatedFormula

@[export Tptp_mk_TptpInput_include]
def TptpInput.mkInclude : Include → TptpInput := TptpInput.include

@[export Tptp_mk_TptpFile_mk]
def TptpFile.mkMk : List TptpInput → TptpFile := TptpFile.mk

end Tptp.Data.Export
