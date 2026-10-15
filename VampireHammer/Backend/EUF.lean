import VampireHammer.Backend.Common
import VampLean

/-! Checked EUF consequences using Lean's existing congruence closure.
Vampire conflict labels are never accepted as axioms. -/
namespace VampireHammer.Backend.Internal
open Lean Meta
open VampireHammer.ClauseMeta

structure GroundClause where
  literals : Array Expr
  proof : Expr
deriving Inhabited

/-- Turn the two stored A-clause lists into one ordinary clause. -/
def groundClause (proof type : Expr) : MetaM (Option GroundClause) := do
  let some view ← resolutionClauseView proof type | return none
  let proof ← if view.isAClause then
    mkAppM ``VampireHammer.Clause.AClause.toClause
      #[mkPropList view.regular.toList,
        mkPropList view.avatar.toList, view.proof]
    else pure view.proof
  pure (some ⟨view.regular ++ view.avatar, proof⟩)

/-- Inject a literal proof at a checked occurrence in a clause. -/
def injectLiteral (literals : Array Expr) (index : Nat) (proof : Expr) : MetaM Expr := do
  let after := mkPropList (literals.drop (index + 1)).toList
  let mut result ← mkAppOptM ``Or.inl #[some literals[index]!, some (mkApp
    (mkConst ``VampireHammer.Clause.Holds) after), some proof]
  for i in (List.range index).reverse do
    let tail ← holdsType (literals.drop (i + 1))
    result ← mkAppOptM ``Or.inr #[some literals[i]!, some tail, some result]
  pure result

/-- Extract complements from the assumption that an entire clause is false. -/
def negatedClauseFacts (literals : Array Expr) (negative : Expr) : MetaM (Array Expr) := do
  let mut facts := #[]
  for (literal, index) in literals.zipIdx do
    let negativeLiteral ← withLocalDeclD `conflictLiteral literal fun h => do
      mkLambdaFVars #[h] (mkApp negative (← injectLiteral literals index h))
    let fact ← if let some atom ← notArgument? literal then
      mkAppOptM ``Classical.byContradiction #[some atom, some negativeLiteral]
      else pure negativeLiteral
    facts := facts.push fact
  pure facts

/-- Check a small ground EUF consequence with Lean's existing congruence
closure. The local theorem contains only its named premises and target symbols;
source facts are removed before `grind only` runs. -/
def eufConsequence (parents : Array GroundClause) (target : Array Expr) :
    MetaM (Option Expr) := do
  if parents.foldl (fun n clause => n + clause.literals.size) target.size > 1024 then return none
  let rawClause (literals : Array Expr) := literals.toList.foldr mkOr (mkConst ``False)
  let mut theoremType := rawClause target
  for parent in parents.reverse do
    theoremType ← mkArrow (rawClause parent.literals) theoremType
  -- Some source hypotheses cannot be cleared because a Skolem let depends
  -- on them. Keep such dependencies well scoped, but hide them from grind's
  -- hypothesis assertion pass. Only the theorem's newly introduced premises
  -- are available as facts.
  let mut lctx ← getLCtx
  for decl in ← getLCtx do
    if ← isProp decl.type then lctx := lctx.setKind decl.fvarId .implDetail
  let theoremProof ← mkFreshExprMVarAt lctx (← getLocalInstances) theoremType .syntheticOpaque
  let goal ← theoremProof.mvarId!.clearAllExcept
    (Lean.collectFVars {} theoremType).fvarIds
  let proof? ← try
    let (remaining, _) ← Lean.Elab.runTactic goal (← `(tactic| intros; grind only))
    if !remaining.isEmpty then pure none else
      pure (some (← instantiateMVars theoremProof))
  catch _ => pure none
  let some checked := proof? | return none
  let result := mkAppN checked (parents.map (·.proof))
  asExpectedType result (← holdsType target)

end VampireHammer.Backend.Internal
