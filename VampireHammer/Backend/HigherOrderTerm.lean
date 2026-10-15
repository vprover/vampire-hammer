import VampireHammer.Backend.Types
import VampireHammer.Backend.LogicalWitness

/-! Typed materialization of embedded THF substitutions. Lambda-bound names
are local to their term, not members of the free MGU-variable namespace. -/
namespace VampireHammer.Backend.Internal
open Lean Meta

private def certificateSort : THF.SortExpr → MetaM Expr
  | .prop => pure (mkSort .zero)
  | .func domain range => do mkArrow (← certificateSort domain) (← certificateSort range)
  | .named name => do
    if name == "s_nat" then return mkConst ``Nat
    if name == "s_int" then return mkConst ``Int
    for declaration in (← getLCtx) do
      if declaration.userName == Name.mkSimple name then
        if (← whnf (← inferType declaration.toExpr)).isSort then
          return declaration.toExpr
    throwError "unknown higher-order certificate sort `{name}`"

private def logicalConnective (op : THF.Connective) : MetaM Expr := do
  match op with
  | .not => pure (mkConst ``Not)
  | .and => pure (mkConst ``And)
  | .or => pure (mkConst ``Or)
  | .imp | .reverseImp | .iff | .xor | .nor | .nand =>
    withLocalDeclD `THFLeft (mkSort .zero) fun left =>
      withLocalDeclD `THFRight (mkSort .zero) fun right => do
        let body ← match op with
          | .imp => mkArrow left right
          | .reverseImp => mkArrow right left
          | .iff => pure (mkApp2 (mkConst ``Iff) left right)
          | .xor => pure (mkNot (mkApp2 (mkConst ``Iff) left right))
          | .nor => pure (mkNot (mkOr left right))
          | .nand => pure (mkNot (mkAnd left right))
          | _ => pure (mkConst ``False)
        mkLambdaFVars #[left, right] body

private partial def higherOrderExpr (term : THF.Term)
    (symbols : Std.HashMap String Expr) (variables : Array (String × Expr)) : MetaM Expr := do
  match term with
  | .constant name =>
    let some value := symbols[name]? | throwError "unknown higher-order symbol `{name}`"
    pure value
  | .variable name =>
    let some (_, value) := variables.find? (·.1 == name)
      | throwError "unbound higher-order variable `{name}`"
    pure value
  | .truth value => pure (mkConst (if value then ``True else ``False))
  | .connective op => logicalConnective op
  | .eqPartial left => do
    let left ← higherOrderExpr left symbols variables
    mkAppM ``Eq #[left]
  | .choice sort => do
    let domain ← certificateSort sort
    withLocalDeclD `THFPredicate (← mkArrow domain (mkSort .zero)) fun predicate => do
      mkLambdaFVars #[predicate] (← mkAppM ``VampireHammer.Backend.quantifierWitness #[predicate])
  | .group body => higherOrderExpr body symbols variables
  | .ite condition left right => do
    let condition ← higherOrderExpr condition symbols variables
    let left ← higherOrderExpr left symbols variables
    let right ← higherOrderExpr right symbols variables
    unless ← isProp condition do throwError "higher-order conditional requires a proposition"
    unless ← isDefEq (← inferType left) (← inferType right) do
      throwError "higher-order conditional branches have different types"
    mkAppM ``Auto.Bool.ite' #[condition, left, right]
  | .app fn arg => do
    let fn ← higherOrderExpr fn symbols variables
    let arg ← higherOrderExpr arg symbols variables
    let range ← mkFreshTypeMVar
    unless ← isDefEq (← inferType fn) (← mkArrow (← inferType arg) range) do
      throwError "higher-order certificate application type mismatch"
    pure (mkApp fn arg)
  | .lam name sort body | .forallE name sort body | .existsE name sort body => do
    let sort ← certificateSort sort
    withLocalDeclD (Name.mkSimple name) sort fun boundValue => do
      let body ← higherOrderExpr body symbols (#[(name, boundValue)] ++ variables)
      match term with
      | .lam .. => mkLambdaFVars #[boundValue] body
      | .forallE .. =>
        unless ← isProp body do throwError "higher-order universal body is not a proposition"
        mkForallFVars #[boundValue] body
      | _ =>
        unless ← isProp body do throwError "higher-order existential body is not a proposition"
        mkAppM ``Exists #[← mkLambdaFVars #[boundValue] body]
  | .not body => do
    let body ← higherOrderExpr body symbols variables
    unless ← isProp body do throwError "higher-order negation requires a proposition"
    pure (mkNot body)
  | .binary op left right => do
    let left ← higherOrderExpr left symbols variables
    let right ← higherOrderExpr right symbols variables
    unless ← (isProp left <&&> isProp right) do
      throwError "higher-order connective requires propositions"
    pure (mkApp2 (← logicalConnective op) left right)
  | .eq left right => do
    let left ← higherOrderExpr left symbols variables
    let right ← higherOrderExpr right symbols variables
    unless ← isDefEq (← inferType left) (← inferType right) do
      throwError "higher-order equality has arguments of different types"
    mkEq left right

def materializeHigherOrderTerm (term : THF.Term)
    (symbols : Std.HashMap String Expr) (variables : Array (String × Expr)) :
    MetaM (Option Expr) := do
  try
    let value ← higherOrderExpr term symbols variables
    let value ← instantiateMVars value
    if value.hasExprMVar then return none
    pure (some value)
  catch _ => pure none

/-- Provisional term metavariables infer only the sorts of otherwise erased
free variables. Actual parent instantiation uses checked canonical witnesses. -/
def inferHigherOrderVariableDomains (term : THF.Term) (expected : Expr)
    (symbols : Std.HashMap String Expr) (targetBindings : Array (String × Expr))
    (inferred : Std.HashMap String Expr) : MetaM (Option (Std.HashMap String Expr)) := do
  try
    let mut variables := targetBindings
    let mut inferred := inferred
    for name in term.freeVariables do
      if variables.any (·.1 == name) then continue
      let domain ← match inferred[name]? with
        | some domain => pure domain
        | none => mkFreshTypeMVar
      let value ← mkFreshExprMVar domain
      variables := variables.push (name, value)
      inferred := inferred.insert name domain
    let value ← higherOrderExpr term symbols variables
    unless ← isDefEq (← inferType value) expected do return none
    pure (some inferred)
  catch _ => pure none

end VampireHammer.Backend.Internal
