import VampireHammer.Replay.Decode.Context
import VampireHammer.THF.Syntax

namespace VampireHammer.Replay.Decode.Internal
open Auto.Embedding.Lam
open VampireHammer.Backend
open VampireHammer.Replay.Internal

def decodeHigherOrderSort : THF.SortExpr → DecodeM LamSort
  | .named name => lookupSort name
  | .prop => pure (.base .prop)
  | .func domain range => .func <$> decodeHigherOrderSort domain <*> decodeHigherOrderSort range

/-- Logical values and infix connectives have the same interpretation. -/
def higherOrderConnective : THF.Connective → LamTerm
  | .not => .base .not
  | .and => .base .and
  | .or => .base .or
  | .imp => .base .imp
  | .iff => .base .iff
  | .reverseImp => .lam (.base .prop) (.lam (.base .prop) (.mkImp (.bvar 0) (.bvar 1)))
  | .xor => .lam (.base .prop) (.lam (.base .prop) (.mkNot (.mkIff (.bvar 1) (.bvar 0))))
  | .nor => .lam (.base .prop) (.lam (.base .prop) (.mkNot (.mkOr (.bvar 1) (.bvar 0))))
  | .nand => .lam (.base .prop) (.lam (.base .prop) (.mkNot (.mkAnd (.bvar 1) (.bvar 0))))

private def connectiveSort (op : THF.Connective) : LamSort :=
  let prop := LamSort.base .prop
  if op == .not then .func prop prop else .func prop (.func prop prop)

private def orChain : THF.Term → List THF.Term
  | .binary .or left right => orChain left ++ orChain right
  | term => [term]

partial def decodeHigherOrderTerm : THF.Term → DecodeM TypedTerm
  | .constant name => do
    let (term, sort) ← lookupSymbol name
    pure ⟨term, sort⟩
  | .variable name => lookupBound name
  | .truth value => pure ⟨.base (if value then .trueE else .falseE), .base .prop⟩
  | .connective op => pure ⟨higherOrderConnective op, connectiveSort op⟩
  | .choice _ => fail "builtin THF choice in proof formulas requires an interpreted logical symbol"
  | .eqPartial left => do
    let left ← decodeHigherOrderTerm left
    pure ⟨.app left.sort (.base (.eq left.sort)) left.term,
      .func left.sort (.base .prop)⟩
  | .group body => decodeHigherOrderTerm body
  | .ite condition left right => do
    let condition ← decodeHigherOrderTerm condition
    let left ← decodeHigherOrderTerm left
    let right ← decodeHigherOrderTerm right
    unless condition.sort == .base .prop && left.sort == right.sort do
      fail "THF conditional argument sort mismatch"
    apply (.base (.ite left.sort))
      (.func (.base .prop) (.func left.sort (.func left.sort left.sort)))
      [condition, left, right]
  | .app fn arg => do
    let fn ← decodeHigherOrderTerm fn
    let arg ← decodeHigherOrderTerm arg
    apply fn.term fn.sort [arg]
  | .lam name sort body => binder name sort body false false
  | .forallE name sort body => binder name sort body true false
  | .existsE name sort body => binder name sort body true true
  | .not body => do
    let body ← decodeHigherOrderTerm body
    apply (.base .not) (connectiveSort .not) [body]
  | value@(.binary op left right) => do
    if op == .or && (← read).rightChains then
      let parts ← (orChain value).mapM decodeHigherOrderTerm
      unless parts.all (·.sort == .base .prop) do fail "THF disjunction requires propositions"
      let some result := rightAssociate? .mkOr (parts.map (·.term))
        | fail "empty THF disjunction"
      return ⟨result, .base .prop⟩
    let left ← decodeHigherOrderTerm left
    let right ← decodeHigherOrderTerm right
    let decoded ← apply (higherOrderConnective op) (connectiveSort op) [left, right]
    if op == .and && (← read).flattenConjunctions then pure (normalizeAnd decoded)
    else pure decoded
  | .eq left right => do
    let left ← decodeHigherOrderTerm left
    let right ← decodeHigherOrderTerm right
    unless left.sort == right.sort do fail "THF equality has arguments of different sorts"
    pure ⟨.mkEq left.sort left.term right.term, .base .prop⟩
where
  binder name sort body quantified existential := do
    let sort ← decodeHigherOrderSort sort
    let previous ← read
    let body ← decodeHigherOrderTerm body |>.run { previous with bound := (name, sort) :: previous.bound }
    if quantified then
      unless body.sort == .base .prop do fail "THF quantified body is not a proposition"
      let term := if existential then LamTerm.mkExistEF sort body.term else LamTerm.mkForallEF sort body.term
      pure ⟨term, .base .prop⟩
    else pure ⟨.lam sort body.term, .func sort body.sort⟩

def higherOrderOuterBinders : THF.Term → DecodeM (Array FormulaBinder)
  | .group body => higherOrderOuterBinders body
  | .forallE name sort body => do
    let sort ← decodeHigherOrderSort sort
    pure (#[⟨name, sort⟩] ++ (← higherOrderOuterBinders body))
  | _ => pure #[]

def higherOrderExistentialVariables : THF.Term → Array String
  | .ite condition left right =>
    higherOrderExistentialVariables condition ++ higherOrderExistentialVariables left ++
      higherOrderExistentialVariables right
  | .existsE name _ body => #[name] ++ higherOrderExistentialVariables body
  | .forallE _ _ body | .lam _ _ body | .not body | .group body | .eqPartial body =>
    higherOrderExistentialVariables body
  | .binary _ left right | .eq left right | .app left right =>
    higherOrderExistentialVariables left ++ higherOrderExistentialVariables right
  | _ => #[]

def higherOrderComponentBinders : THF.Term → DecodeM (Array FormulaBinder)
  | .group body => higherOrderComponentBinders body
  | .binary .iff _ component => higherOrderOuterBinders component
  | _ => pure #[]

def higherOrderNestedBinders : THF.Term → DecodeM (Option (Array FormulaBinder))
  | .group body => higherOrderNestedBinders body
  | value@(.forallE _ _ _) => some <$> higherOrderOuterBinders value
  | .binary .or left right => do
    if let some binders ← higherOrderNestedBinders left then return some binders
    higherOrderNestedBinders right
  | _ => pure none

end VampireHammer.Replay.Decode.Internal
