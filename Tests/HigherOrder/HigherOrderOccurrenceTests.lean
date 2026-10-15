import VampireHammer.Backend.Occurrence

open Lean Meta Elab Tactic VampireHammer.Backend.Internal

private def lookup (name : String) : MetaM Expr := do
  for declaration in ← getLCtx do
    if declaration.userName.toString == name then return declaration.toExpr
  throwError "missing local {name}"

example (f g : Nat → Nat) (Q : Nat → Nat → Prop) : True := by
  run_tac withMainContext do
    let f ← lookup "f"
    let g ← lookup "g"
    let q ← lookup "Q"
    let source ← withLocalDeclD `x (mkConst ``Nat) fun x =>
      mkLambdaFVars #[x] (mkApp2 q (mkApp f x) (mkApp f x))
    let first ← withLocalDeclD `y (mkConst ``Nat) fun y =>
      mkLambdaFVars #[y] (mkApp2 q (mkApp g y) (mkApp f y))
    let second ← withLocalDeclD `y (mkConst ``Nat) fun y =>
      mkLambdaFVars #[y] (mkApp2 q (mkApp f y) (mkApp g y))
    let some actual ← rewriteTermOccurrences f g source (some 0)
      | throwError "first occurrence declined"
    unless ← isDefEq actual first do throwError "rewrote the wrong occurrence under a binder"
    let some actual ← rewriteTermOccurrences f g source (some 1)
      | throwError "second occurrence declined"
    unless ← isDefEq actual second do throwError "rewrote both occurrences"
    if (← rewriteTermOccurrences f g source (some 2)).isSome then
      throwError "accepted an out-of-range occurrence"
  trivial

example (f g : Nat → Nat) (R : (Nat → Nat) → Prop) : True := by
  run_tac withMainContext do
    let f ← lookup "f"
    let g ← lookup "g"
    let r ← lookup "R"
    let fromTerm ← withLocalDeclD `certificateBinder (mkConst ``Nat) fun x =>
      mkLambdaFVars #[x] (mkApp f x)
    let literal ← withLocalDeclD `printedBinder (mkConst ``Nat) fun x => do
      pure (mkApp r (← mkLambdaFVars #[x] (mkApp f x)))
    let some actual ← rewriteTermOccurrences fromTerm g literal (some 0)
      | throwError "alpha-renamed occurrence declined"
    unless ← isDefEq actual (mkApp r g) do throwError "lost beta/eta matching"
    if (← rewriteTermOccurrences fromTerm g literal (some 1)).isSome then
      throwError "counted descendants of a matching lambda"
  trivial

example (x y : Nat) (Q : Nat → Prop) : True := by
  run_tac withMainContext do
    let outer ← lookup "x"
    let to ← lookup "y"
    let q ← lookup "Q"
    let literal ← withLocalDeclD `x (mkConst ``Nat) fun inner =>
      mkLambdaFVars #[inner] (mkApp q inner)
    if (← rewriteTermOccurrences outer to literal (some 0)).isSome then
      throwError "captured a lambda-bound variable as a free certificate variable"
  trivial
