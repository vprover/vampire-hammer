import VampireHammer.Replay.Decode.Context

/-!
Typed TFF, restricted FOF, and CNF formula decoding. All dialects use the same checked signature
and binder environment.
-/

namespace VampireHammer.Replay.Decode.Internal

open Lean Meta Elab Tactic
open Auto.Embedding.Lam
open Tptp.Data
open VampireHammer.Backend
open VampireHammer.Replay.Internal

mutual

/-- Decode arguments before applying their head. The resulting order is the
surface TPTP order and is consumed left-to-right by `apply`. -/
private partial def decodeArguments (args : TffArguments) : DecodeM (List TypedTerm) := do
  let .mk first rest := args
  let first ← decodeTerm first
  let rest ← rest.mapM fun | .mk term => decodeTerm term
  pure (first :: rest)

/-- Decode an exported symbol or a fully applied function/predicate. Names are
resolved through `TFF.Problem`, then `apply` checks every argument sort. -/
private partial def decodePlain (plain : TffPlainAtomic) : DecodeM TypedTerm := do
  let (tffName, args) ← match plain with
    | .constant c => pure (← constant c, [])
    | .functorTffArguments f args => pure (← functor f, ← decodeArguments args)
  let (head, sort) ← lookupSymbol tffName
  apply head sort args

/-- Decode the small set of TPTP built-ins that the exporter deliberately
emits. Other built-ins are rejected at this boundary rather than approximated
by unrelated Lean constants. -/
private partial def decodeDefined (defined : TffDefinedAtomic) : DecodeM TypedTerm := do
  let .mk plain := defined
  match plain with
  | .definedConstant c =>
    match ← definedFunctor (match c with | .mk f => f) with
    | "true" | "$true" => pure { term := .base .trueE, sort := .base .prop }
    | "false" | "$false" => pure { term := .base .falseE, sort := .base .prop }
    | other => fail s!"unsupported defined TFF constant `{other}`"
  | .definedFunctorTffArguments f args =>
    let f ← definedFunctor f
    if f == "ite" || f == "$ite" then
      let [condition, left, right] ← decodeArguments args
        | fail "TFF conditional requires three arguments"
      unless condition.sort == .base .prop && left.sort == right.sort do
        fail "TFF conditional argument sort mismatch"
      return ← apply (.base (.ite left.sort))
        (.func (.base .prop) (.func left.sort (.func left.sort left.sort)))
        [condition, left, right]
    fail s!"unsupported defined TFF function `{f}`"
  | _ => fail "unsupported defined TFF atom"

private partial def decodeAtomic (atomic : TffAtomicFormula) : DecodeM TypedTerm :=
  match atomic with
  | .tffPlainAtomic plain => decodePlain plain
  | .tffDefinedAtomic defined => decodeDefined defined
  | .tffSystemAtomic _ => fail "system TFF atoms are unsupported"

private partial def decodeUnitaryTerm (term : TffUnitaryTerm) : DecodeM TypedTerm :=
  match term with
  | .tffAtomicFormula atomic => decodeAtomic atomic
  | .variable var => lookupBound (varName var)
  | .tffLogicFormula formula => decodeLogic formula
  | _ => fail "unsupported TFF term"

private partial def decodeTerm (term : TffTerm) : DecodeM TypedTerm :=
  match term with
  | .tffLogicFormula formula => decodeLogic formula
  | _ => fail "unsupported TFF term"

private partial def decodePreunit (formula : TffPreunitFormula) : DecodeM TypedTerm :=
  match formula with
  | .tffUnitaryFormula formula => decodeUnitary formula
  | .tffPrefixUnary unary => decodePrefix unary

private partial def decodePrefix (unary : TffPrefixUnary) : DecodeM TypedTerm := do
  let .mk _ formula := unary
  let formula ← decodePreunit formula
  unless formula.sort == .base .prop do
    fail "TFF negation requires a proposition"
  pure { term := .mkNot formula.term, sort := .base .prop }

/-- Decode TPTP's `s != t` spelling as `¬ (s = t)`.  The grammar permits this
in both a `TffUnitFormula` and a top-level `TffLogicFormula`, so both decoder
entry points share this one typed conversion. -/
private partial def decodeInequality (lhs rhs : TffUnitaryTerm) : DecodeM TypedTerm := do
  let lhs ← decodeUnitaryTerm lhs
  let rhs ← decodeUnitaryTerm rhs
  unless lhs.sort == rhs.sort do
    fail "TFF inequality has arguments of different sorts"
  pure { term := .mkNot (.mkEq lhs.sort lhs.term rhs.term), sort := .base .prop }

private partial def decodeUnitFormula (formula : TffUnitFormula) : DecodeM TypedTerm :=
  match formula with
  | .tffUnitaryFormula formula => decodeUnitary formula
  | .tffUnaryFormula (.tffPrefixUnary unary) => decodePrefix unary
  | .tffUnaryFormula (.tffInfixUnary (.mk lhs _ rhs)) => decodeInequality lhs rhs
  | .tffDefinedInfix (.mk lhs _ rhs) => do
    let lhs ← decodeUnitaryTerm lhs
    let rhs ← decodeUnitaryTerm rhs
    unless lhs.sort == rhs.sort do
      fail "TFF equality has arguments of different sorts"
    pure { term := .mkEq lhs.sort lhs.term rhs.term, sort := .base .prop }

private partial def decodeAnd (formula : TffAndFormula) : DecodeM TypedTerm := do
  if (← read).flattenConjunctions then
    match formula with
    | .tffUnitFormulaTffUnitFormula lhs rhs =>
      normalizeAnd <$> combine .mkAnd (decodeUnitFormula lhs) (decodeUnitFormula rhs)
    | .tffAndFormulaTffUnitFormula lhs rhs =>
      normalizeAnd <$> combine .mkAnd (decodeAnd lhs) (decodeUnitFormula rhs)
  else
    let rec units : TffAndFormula → List TffUnitFormula
      | .tffUnitFormulaTffUnitFormula lhs rhs => [lhs, rhs]
      | .tffAndFormulaTffUnitFormula lhs rhs => units lhs ++ [rhs]
    rightChain (units formula) decodeUnitFormula .mkAnd

private partial def decodeOr (formula : TffOrFormula) : DecodeM TypedTerm := do
  if (← read).rightChains then
    let rec units : TffOrFormula → List TffUnitFormula
      | .tffUnitFormulaTffUnitFormula lhs rhs => [lhs, rhs]
      | .tffOrFormulaTffUnitFormula lhs rhs => units lhs ++ [rhs]
    rightChain (units formula) decodeUnitFormula
  else match formula with
    | .tffUnitFormulaTffUnitFormula lhs rhs =>
      combine .mkOr (decodeUnitFormula lhs) (decodeUnitFormula rhs)
    | .tffOrFormulaTffUnitFormula lhs rhs =>
      combine .mkOr (decodeOr lhs) (decodeUnitFormula rhs)

/-- Decode the members of one unparenthesized disjunction chain and combine
them right-associatively. -/
private partial def rightChain {α : Type} (members : List α)
    (decode : α → DecodeM TypedTerm) (op : LamTerm → LamTerm → LamTerm := .mkOr) :
    DecodeM TypedTerm :=
  match members with
  | [] => fail "empty TFF connective chain"
  | [member] => decode member
  | member :: rest => combine op (decode member) (rightChain rest decode op)

/-- Form a propositional connective after both sides have been decoded.  The
sort check is repeated here because TPTP's grammar alone permits terms where a
formula is required. -/
private partial def combine (op : LamTerm → LamTerm → LamTerm)
    (lhs rhs : DecodeM TypedTerm) : DecodeM TypedTerm := do
  let lhs ← lhs
  let rhs ← rhs
  unless lhs.sort == .base .prop && rhs.sort == .base .prop do
    fail "TFF connective requires propositions"
  pure { term := op lhs.term rhs.term, sort := .base .prop }

/-- Decode a TFF quantifier while maintaining the de Bruijn convention used by
`LamTerm`: index zero denotes the innermost binder.  The TFF list is therefore
prepended in reverse order before decoding its body. -/
private partial def decodeQuantified (quantified : TffQuantifiedFormula) : DecodeM TypedTerm := do
  let .mk quantifier variables body := quantified
  let variables ← decodeVariables variables
  let previous ← read
  let body ← decodeUnitFormula body |>.run { previous with bound := variables.reverse ++ previous.bound }
  unless body.sort == .base .prop do
    fail "TFF quantified body is not a proposition"
  let wrap := match quantifier with
    | .fofQuantifier .exclamation => LamTerm.mkForallEF
    | .fofQuantifier .question => LamTerm.mkExistEF
    | .hash => fun _ _ => .base .falseE
  match quantifier with
  | .hash => fail "TFF choice quantification is unsupported"
  | _ => pure { term := variables.foldr (fun entry result => wrap entry.2 result) body.term, sort := .base .prop }

private partial def decodeUnitary (formula : TffUnitaryFormula) : DecodeM TypedTerm :=
  match formula with
  | .tffQuantifiedFormula quantified => decodeQuantified quantified
  | .tffAtomicFormula atomic => decodeAtomic atomic
  | .txfUnitaryFormula (.mk var) => lookupBound (varName var)
  | .tffLogicFormula formula => decodeLogic formula

private partial def decodeBinary (formula : TffBinaryFormula) : DecodeM TypedTerm :=
  match formula with
  | .tffBinaryAssoc (.tffAndFormula formula) => decodeAnd formula
  | .tffBinaryAssoc (.tffOrFormula formula) => decodeOr formula
  | .tffBinaryNonassoc (.mk lhs connective rhs) =>
    match connective with
    | .iff => combine .mkIff (decodeUnitFormula lhs) (decodeUnitFormula rhs)
    | .fi => combine .mkImp (decodeUnitFormula lhs) (decodeUnitFormula rhs)
    | .if => combine .mkImp (decodeUnitFormula rhs) (decodeUnitFormula lhs)
    | .xor => combine (fun a b => .mkNot (.mkIff a b)) (decodeUnitFormula lhs) (decodeUnitFormula rhs)
    | .nor => combine (fun a b => .mkNot (.mkOr a b)) (decodeUnitFormula lhs) (decodeUnitFormula rhs)
    | .nand => combine (fun a b => .mkNot (.mkAnd a b)) (decodeUnitFormula lhs) (decodeUnitFormula rhs)

partial def decodeLogic (formula : TffLogicFormula) : DecodeM TypedTerm :=
  match formula with
  | .tffUnitaryFormula formula => decodeUnitary formula
  | .tffUnaryFormula (.tffPrefixUnary unary) => decodePrefix unary
  | .tffUnaryFormula (.tffInfixUnary (.mk lhs _ rhs)) => decodeInequality lhs rhs
  | .tffBinaryFormula binary => decodeBinary binary
  | .tffDefinedInfix (.mk lhs _ rhs) => do
    let lhs ← decodeUnitaryTerm lhs
    let rhs ← decodeUnitaryTerm rhs
    unless lhs.sort == rhs.sort do fail "TFF equality has arguments of different sorts"
    pure { term := .mkEq lhs.sort lhs.term rhs.term, sort := .base .prop }
  | _ => fail "unsupported TFF formula"

end

/-- Vampire prints a proof as FOF when its input property scan found no
non-default sort.  That scan ignores quantifier binder sorts, so a problem whose
only use of a sort is a vacuous binder (`∃ X : α, c`) comes back as untyped
`? [X] : c`.  The exporter never uses `$i`, so in such a proof no variable can
occur as a symbol argument and the binder sort is not recoverable from the
text; it is determined only when the problem declares a single sort. -/
private def untypedFofBinderSort : DecodeM LamSort := do
  match (← read).problem.sorts with
  | #[(_, sort)] => pure sort
  | sorts => fail s!"untyped FOF binder is ambiguous among {sorts.size} exported sorts"

private def fofVariableNames : FofVariableList → List String
  | .variable var => [varName var]
  | .variableFofVariableList var rest => varName var :: fofVariableNames rest

mutual

/-- Vampire prints a purely propositional TF0 problem as FOF in some proof
configurations. The exporter still supplies the symbol mapping and all symbols
still have sort `prop`; this decoder supports that quantifier-free FOF subset
so replay does not lose an otherwise ordinary proof merely because Vampire
omitted redundant type declarations. Untyped FOF variables and quantifiers are
rejected because FOF contains no sort information from which to rebuild their
`LamSort`. -/
private partial def decodeFofArguments : FofArguments → DecodeM (List TypedTerm)
  | .fofTerm term => do pure [← decodeFofTerm term]
  | .fofTermFofArguments term rest => do
    let first ← decodeFofTerm term
    pure (first :: (← decodeFofArguments rest))

private partial def decodeFofPlainTerm : FofPlainTerm → DecodeM TypedTerm
  | .constant c => do
    let (head, sort) ← lookupSymbol (← constant c)
    apply head sort []
  | .functorFofArguments f arguments => do
    let (head, sort) ← lookupSymbol (← functor f)
    apply head sort (← decodeFofArguments arguments)

private partial def decodeFofTerm : FofTerm → DecodeM TypedTerm
  | .fofFunctionTerm (.fofPlainTerm term) => decodeFofPlainTerm term
  | .variable var => fail s!"untyped FOF variable `{varName var}` is unsupported"
  | _ => fail "unsupported FOF term"

private partial def decodeFofDefinedAtomic : FofDefinedAtomicFormula → DecodeM TypedTerm
  | .fofDefinedPlainFormula (.mk (.definedConstant constant)) => do
    match ← definedFunctor (match constant with | .mk functor => functor) with
    | "true" | "$true" => pure { term := .base .trueE, sort := .base .prop }
    | "false" | "$false" => pure { term := .base .falseE, sort := .base .prop }
    | other => fail s!"unsupported FOF defined constant `{other}`"
  | _ => fail "unsupported FOF defined atom"

private partial def decodeFofAtomic : FofAtomicFormula → DecodeM TypedTerm
  | .fofPlainAtomicFormula (.mk term) => decodeFofPlainTerm term
  | .fofDefinedAtomicFormula defined => decodeFofDefinedAtomic defined
  | _ => fail "unsupported FOF system atom"

private partial def decodeFofQuantified : FofQuantifiedFormula → DecodeM TypedTerm
  | .mk quantifier variables body => do
    let sort ← untypedFofBinderSort
    let variables := (fofVariableNames variables).map (·, sort)
    let previous ← read
    let body ← decodeFofUnit body |>.run { previous with bound := variables.reverse ++ previous.bound }
    unless body.sort == .base .prop do
      fail "FOF quantified body is not a proposition"
    let wrap := match quantifier with
      | .exclamation => LamTerm.mkForallEF
      | .question => LamTerm.mkExistEF
    pure { term := variables.foldr (fun entry result => wrap entry.2 result) body.term, sort := .base .prop }

private partial def decodeFofUnitary : FofUnitaryFormula → DecodeM TypedTerm
  | .fofAtomicFormula atomic => decodeFofAtomic atomic
  | .fofLogicFormula formula => decodeFofLogic formula
  | .fofQuantifiedFormula formula => decodeFofQuantified formula

private partial def decodeFofUnit : FofUnitFormula → DecodeM TypedTerm
  | .fofUnitaryFormula formula => decodeFofUnitary formula
  | .fofUnaryFormula formula => decodeFofUnary formula

private partial def decodeFofUnary : FofUnaryFormula → DecodeM TypedTerm
  | .unaryConnectiveFofUnitFormula _ formula => do
    let formula ← decodeFofUnit formula
    unless formula.sort == .base .prop do
      fail "FOF negation requires a proposition"
    pure { term := .mkNot formula.term, sort := .base .prop }
  | .fofInfixUnary _ => fail "FOF inequality is unsupported"

private partial def decodeFofAnd (formula : FofAndFormula) : DecodeM TypedTerm := do
  if (← read).flattenConjunctions then
    match formula with
    | .fofUnitFormulaFofUnitFormula lhs rhs =>
      normalizeAnd <$> combine .mkAnd (decodeFofUnit lhs) (decodeFofUnit rhs)
    | .fofAndFormulaFofUnitFormula lhs rhs =>
      normalizeAnd <$> combine .mkAnd (decodeFofAnd lhs) (decodeFofUnit rhs)
  else
    let rec units : FofAndFormula → List FofUnitFormula
      | .fofUnitFormulaFofUnitFormula lhs rhs => [lhs, rhs]
      | .fofAndFormulaFofUnitFormula lhs rhs => units lhs ++ [rhs]
    rightChain (units formula) decodeFofUnit .mkAnd

private partial def decodeFofOr (formula : FofOrFormula) : DecodeM TypedTerm := do
  if (← read).rightChains then
    let rec units : FofOrFormula → List FofUnitFormula
      | .fofUnitFormulaFofUnitFormula lhs rhs => [lhs, rhs]
      | .fofOrFormulaFofUnitFormula lhs rhs => units lhs ++ [rhs]
    rightChain (units formula) decodeFofUnit
  else match formula with
    | .fofUnitFormulaFofUnitFormula lhs rhs =>
      combine .mkOr (decodeFofUnit lhs) (decodeFofUnit rhs)
    | .fofOrFormulaFofUnitFormula lhs rhs =>
      combine .mkOr (decodeFofOr lhs) (decodeFofUnit rhs)

private partial def decodeFofBinary : FofBinaryFormula → DecodeM TypedTerm
  | .fofBinaryAssoc (.fofAndFormula formula) => decodeFofAnd formula
  | .fofBinaryAssoc (.fofOrFormula formula) => decodeFofOr formula
  | .fofBinaryNonassoc (.mk lhs connective rhs) =>
    match connective with
    | .iff => combine .mkIff (decodeFofUnit lhs) (decodeFofUnit rhs)
    | .fi => combine .mkImp (decodeFofUnit lhs) (decodeFofUnit rhs)
    | .if => combine .mkImp (decodeFofUnit rhs) (decodeFofUnit lhs)
    | .xor => combine (fun a b => .mkNot (.mkIff a b)) (decodeFofUnit lhs) (decodeFofUnit rhs)
    | .nor => combine (fun a b => .mkNot (.mkOr a b)) (decodeFofUnit lhs) (decodeFofUnit rhs)
    | .nand => combine (fun a b => .mkNot (.mkAnd a b)) (decodeFofUnit lhs) (decodeFofUnit rhs)

partial def decodeFofLogic : FofLogicFormula → DecodeM TypedTerm
  | .fofUnitaryFormula formula => decodeFofUnitary formula
  | .fofUnaryFormula formula => decodeFofUnary formula
  | .fofBinaryFormula formula => decodeFofBinary formula

end

/-! Vampire's AVATAR SAT tail is printed as `cnf(...)`, even when the main
proof uses TFF or FOF. These clauses are ground and use the same nullary split
symbols as the preceding AVATAR nodes, so the existing typed FOF atom decoder
is sufficient once the CNF literal/disjunction wrappers are removed. -/

private def decodeCnfLiteral : CnfLiteral → DecodeM TypedTerm
  | .fofAtomicFormula atom => decodeFofAtomic atom
  | .fofAtomicFormulaNegated atom => do
    let decoded ← decodeFofAtomic atom
    unless decoded.sort == .base .prop do fail "CNF negation requires a proposition"
    pure { term := .mkNot decoded.term, sort := .base .prop }
  | .fofInfixUnary (.mk lhs _ rhs) => do
    let lhs ← decodeFofTerm lhs
    let rhs ← decodeFofTerm rhs
    unless lhs.sort == rhs.sort do fail "CNF inequality has arguments of different sorts"
    pure { term := .mkNot (.mkEq lhs.sort lhs.term rhs.term), sort := .base .prop }

private partial def decodeCnfDisjunction : CnfDisjunction → DecodeM TypedTerm
  | .cnfLiteral literal => decodeCnfLiteral literal
  | .cnfDisjunctionCnfLiteral preceding literal =>
    combine .mkOr (decodeCnfDisjunction preceding) (decodeCnfLiteral literal)

partial def decodeCnfFormula : CnfFormula → DecodeM TypedTerm
  | .cnfDisjunction disjunction => decodeCnfDisjunction disjunction
  | .cnfFormula formula => decodeCnfFormula formula

end VampireHammer.Replay.Decode.Internal
