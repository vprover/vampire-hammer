import VampireHammer.Backend.Common

namespace VampireHammer.Backend.Internal
open Lean Meta

/-- Match typed terms in preorder (application function, then argument;
lambda/forall body). A matching node counts once and hides its descendants.
Binder bodies are opened before comparison, so alpha-renaming is respected
and a lambda-bound variable cannot capture a certificate's free variable. -/
private partial def replaceOccurrences (sourceType source replacement expression : Expr)
    (selected : Option Nat) (count : Nat) : MetaM (Expr × Nat) := do
  let expression := expression.consumeMData
  if ← ((do isDefEq (← inferType expression) sourceType) <&&> isDefEq expression source) then
    return (if selected.isNone || selected == some count then replacement else expression, count + 1)
  match expression with
  | .app fn argument =>
    let (fn, count) ← replaceOccurrences sourceType source replacement fn selected count
    let (argument, count) ← replaceOccurrences sourceType source replacement argument selected count
    pure (mkApp fn argument, count)
  | .lam name domain body binderInfo =>
    withLocalDecl name binderInfo domain fun boundValue => do
      let (body, count) ← replaceOccurrences sourceType source replacement
        (body.instantiate1 boundValue) selected count
      pure (← mkLambdaFVars #[boundValue] body, count)
  | .forallE name domain body binderInfo =>
    withLocalDecl name binderInfo domain fun boundValue => do
      let (body, count) ← replaceOccurrences sourceType source replacement
        (body.instantiate1 boundValue) selected count
      pure (← mkForallFVars #[boundValue] body, count)
  | _ => pure (expression, count)

/-- Compute the certified replacement. The calculus handler separately
constructs the equality proof and checks the entire displayed child clause. -/
def rewriteTermOccurrences (source replacement expression : Expr)
    (selected : Option Nat := none) : MetaM (Option Expr) := do
  let sourceType ← inferType source
  unless ← isDefEq sourceType (← inferType replacement) do return none
  let (rewritten, count) ← replaceOccurrences sourceType source replacement expression selected 0
  if selected.any (· ≥ count) then return none
  pure (some (if count == 0 then expression else rewritten))

end VampireHammer.Backend.Internal
