import Lean

/-!
Structural, tactic-free transport between nearly identical formulas.

Many of Vampire's preprocessing inferences only restate their parent:
`rectify` renames bound variables and may reorient equations,
`flattening` regroups `∧`/`∨`, `definition_folding` replaces a named
subformula by its predicate, and ENNF/NNF push negations inward and turn
implications into disjunctions.  Running `simp` for these steps produces long
`congrArg`/`Eq.trans`/`propext` rewrite chains.  `transport` instead proves
`parent → target` by a simultaneous walk over both formulas:

* congruence for `¬`, `→`, `↔` (with the antecedent transported backwards);
* `∀`/`∃` binders, opened on the side where this is reversible first;
* `∧` and `∨` up to associativity, commutativity and duplication, by matching
  conjuncts/disjuncts individually;
* literals up to the orientation of an equation;
* one-step classical equivalences of ENNF/NNF (`¬(a ∧ b)` and `¬a ∨ ¬b`, ...),
  each a single application of a lemma below;
* proof-local `let`-bound predicates (named formulas, AVATAR components) by
  unfolding them, which the kernel checks by `zeta`-reduction.

The resulting proof contains only introductions, eliminations and the lemmas
of this file.  `splitClause` is the AVATAR counterpart: it proves a split of a
clause into variable-disjoint components by refutation.
-/

namespace VampireHammer.Structural

open Lean Meta

register_option vampire.structural : Bool := {
  defValue := true
  descr := "reconstruct preprocessing steps and AVATAR splits structurally \
    before falling back to the simp-based tactics"
}

/-! ### One-step classical equivalences, in both directions -/

theorem imp_to_or {a b : Prop} (h : a → b) : ¬a ∨ b :=
  (Classical.em a).elim (fun ha => Or.inr (h ha)) Or.inl
theorem or_to_imp {a b : Prop} (h : ¬a ∨ b) : a → b :=
  fun ha => h.elim (fun n => absurd ha n) id
theorem not_and_to_or {a b : Prop} (h : ¬(a ∧ b)) : ¬a ∨ ¬b :=
  (Classical.em a).elim (fun ha => Or.inr fun hb => h ⟨ha, hb⟩) Or.inl
theorem or_to_not_and {a b : Prop} (h : ¬a ∨ ¬b) : ¬(a ∧ b) :=
  fun ⟨ha, hb⟩ => h.elim (· ha) (· hb)
theorem not_or_to_and {a b : Prop} (h : ¬(a ∨ b)) : ¬a ∧ ¬b :=
  ⟨fun ha => h (Or.inl ha), fun hb => h (Or.inr hb)⟩
theorem and_to_not_or {a b : Prop} (h : ¬a ∧ ¬b) : ¬(a ∨ b) :=
  fun o => o.elim h.1 h.2
theorem not_imp_to_and {a b : Prop} (h : ¬(a → b)) : a ∧ ¬b :=
  ⟨Classical.byContradiction fun na => h fun ha => absurd ha na, fun hb => h fun _ => hb⟩
theorem and_to_not_imp {a b : Prop} (h : a ∧ ¬b) : ¬(a → b) :=
  fun f => h.2 (f h.1)
theorem not_not_elim {a : Prop} (h : ¬¬a) : a := Classical.byContradiction h
theorem not_not_intro {a : Prop} (h : a) : ¬¬a := fun n => n h
theorem not_iff_to_iff_not {a b : Prop} (h : ¬(a ↔ b)) : a ↔ ¬b :=
  ⟨fun ha hb => h ⟨fun _ => hb, fun _ => ha⟩,
   fun nb => Classical.byContradiction fun na =>
     h ⟨fun ha => absurd ha na, fun hb => absurd hb nb⟩⟩
theorem iff_not_to_not_iff {a b : Prop} (h : a ↔ ¬b) : ¬(a ↔ b) :=
  fun e => have nb : ¬b := fun hb => h.mp (e.mpr hb) hb; nb (e.mp (h.mpr nb))
theorem not_iff_to_not_iff {a b : Prop} (h : ¬(a ↔ b)) : ¬a ↔ b :=
  ⟨fun na => Classical.byContradiction fun nb =>
     h ⟨fun ha => absurd ha na, fun hb => absurd hb nb⟩,
   fun hb ha => h ⟨fun _ => hb, fun _ => ha⟩⟩
theorem not_iff_from_not_iff {a b : Prop} (h : ¬a ↔ b) : ¬(a ↔ b) :=
  fun e => have na : ¬a := fun ha => h.mpr (e.mp ha) ha; na (e.mpr (h.mp na))

universe u

theorem not_forall_to_exists {α : Sort u} {p : α → Prop} (h : ¬∀ x, p x) : ∃ x, ¬p x :=
  Classical.byContradiction fun n => h fun x => Classical.byContradiction fun px => n ⟨x, px⟩
theorem exists_to_not_forall {α : Sort u} {p : α → Prop} (h : ∃ x, ¬p x) : ¬∀ x, p x :=
  fun f => h.elim fun x n => n (f x)
theorem not_exists_to_forall {α : Sort u} {p : α → Prop} (h : ¬∃ x, p x) : ∀ x, ¬p x :=
  fun x px => h ⟨x, px⟩
theorem forall_to_not_exists {α : Sort u} {p : α → Prop} (h : ∀ x, ¬p x) : ¬∃ x, p x :=
  fun ⟨x, px⟩ => h x px

/-! ### Formula views -/

/-- Beta-reduce at the head until no redex is left there.  `Expr.headBeta`
alone stops after one step, but lean-auto's translation nests its binder
wrappers: reducing `(fun x => (fun p => ∀ y, p y) B) a` exposes a new redex. -/
partial def headBetaAll (e : Expr) : Expr :=
  let reduced := e.headBeta.consumeMData
  if reduced == e then e else headBetaAll reduced

private def norm (e : Expr) : MetaM Expr :=
  return headBetaAll (← instantiateMVars e)

/-- The top-level connective of a proposition. -/
private inductive Shape where
  | not (a : Expr)
  | and (a b : Expr)
  | or (a b : Expr)
  | iff (a b : Expr)
  | imp (a b : Expr)
  /-- A universal quantifier over a type; `body` has loose bound variable 0. -/
  | all (name : Name) (domain body : Expr)
  /-- `@Exists.{u} domain pred`. -/
  | ex (u : Level) (domain pred : Expr)
  | eq (u : Level) (type lhs rhs : Expr)
  | tru
  | fls
  | atom

private def shape (e : Expr) : MetaM Shape := do
  match e with
  | .app (.const ``Not _) a => return .not a
  | .app (.app (.const ``And _) a) b => return .and a b
  | .app (.app (.const ``Or _) a) b => return .or a b
  | .app (.app (.const ``Iff _) a) b => return .iff a b
  | .app (.app (.const ``Exists [u]) α) p => return .ex u α p
  | .app (.app (.app (.const ``Eq [u]) α) a) b => return .eq u α a b
  | .app (.app (.app (.const ``Ne [u]) α) a) b =>
    return .not (mkApp3 (mkConst ``Eq [u]) α a b)
  | .const ``True _ => return .tru
  | .const ``False _ => return .fls
  | .forallE name domain body _ =>
    if ← isProp domain then
      if body.hasLooseBVars then return .atom
      if body.consumeMData.isConstOf ``False then return .not domain
      return .imp domain body
    return .all name domain body
  | _ => return .atom

/-- The predicate `fun x => body` of a universal quantifier. -/
private def predicate (name : Name) (domain body : Expr) : Expr :=
  .lam name domain body .default

/-- Instantiate an existential's predicate at `x`. -/
private def instPred (pred x : Expr) : Expr := headBetaAll (mkApp pred x)

/-- The binder name of an existential's predicate, for readable proofs. -/
private def predName (pred : Expr) : Name :=
  match pred with
  | .lam name .. => name
  | _ => `x

/-- Unfold a proof-local `let`-bound predicate at the head of `e`. -/
private def unfoldLetHead? (e : Expr) : MetaM (Option (FVarId × Expr)) := do
  let .fvar id := e.getAppFn | return none
  let some value ← id.getValue? | return none
  return some (id, headBetaAll (value.beta e.getAppArgs))

/-! ### Transport -/

private structure Context where
  /-- Remaining recursive calls; bounds the search on unrelated formulas. -/
  fuel : IO.Ref Nat
  /-- Proof-local lets unfolded by the walk. The final type check must be
  allowed to unfold exactly these. -/
  unfolded : IO.Ref FVarIdSet
  /-- Pairs `(S, T)` already known not to be related; avoids re-exploring
  them when the AC search revisits a subformula. -/
  failed : IO.Ref (Std.HashSet (Expr × Expr))
  /-- Atom signatures by formula; see `signature`. -/
  signatures : IO.Ref (Std.HashMap Expr (Array String))

private def tick (ctx : Context) : MetaM Bool := do
  let n ← ctx.fuel.get
  if n == 0 then return false
  ctx.fuel.set (n - 1)
  return true

/-- Witness candidates of type `domain`: the variables opened by the walk,
most recent first, or any local of that type when none of them fits. -/
private def candidates (vars : Array Expr) (domain : Expr) : MetaM (Array Expr) := do
  let mut out := #[]
  for v in vars.reverse do
    if ← isDefEq (← inferType v) domain then out := out.push v
  unless out.isEmpty do return out
  for decl in ← getLCtx do
    if decl.isImplementationDetail then continue
    if ← isDefEq decl.type domain then return #[decl.toExpr]
  return #[]

/-- The name of a term's head, with variables collapsed to `_`. -/
private def headKey (vars : Array Expr) (e : Expr) : String :=
  match e.getAppFn with
  | .bvar _ => "_"
  | .fvar id => if vars.any (·.fvarId? == some id) then "_" else toString id.name
  | .const name _ => toString name
  | _ => "?"

private partial def signatureInto (vars : Array Expr) (e : Expr) (acc : Std.HashSet String)
    (depth : Nat) : MetaM (Std.HashSet String) := do
  let e ← norm e
  match e with
  | .forallE _ domain body _ =>
    -- A domain with loose bound variables is a formula; a closed one may be
    -- a sort, which contributes nothing.
    let acc ← if ← (pure domain.hasLooseBVars <||> isProp domain) then
      signatureInto vars domain acc depth else pure acc
    return ← signatureInto vars body acc depth
  | _ => pure ()
  match ← shape e with
  | .not a => signatureInto vars a acc depth
  | .and a b | .or a b | .iff a b | .imp a b =>
    signatureInto vars b (← signatureInto vars a acc depth) depth
  | .ex _ _ pred =>
    match pred with
    | .lam _ _ body _ => signatureInto vars body acc depth
    | _ => return acc.insert (headKey vars pred)
  | .eq _ _ a b =>
    let ka := headKey vars a
    let kb := headKey vars b
    return acc.insert (if ka ≤ kb then s!"={ka},{kb}" else s!"={kb},{ka}")
  | .tru | .fls => return acc
  | _ =>
    if depth < 8 then
      if let some (_, e') ← unfoldLetHead? e then
        return ← signatureInto vars e' acc (depth + 1)
    return acc.insert (headKey vars e)

/-- The set of atom heads of a formula, with let-bound predicates unfolded.
Every step `transport` supports preserves it, so it filters the pairings tried
by the AC search. -/
private def signature (ctx : Context) (vars : Array Expr) (e : Expr) : MetaM (Array String) := do
  if let some s := (← ctx.signatures.get)[e]? then return s
  let s := (← signatureInto vars e {} 0).toArray.qsort (· < ·)
  ctx.signatures.modify (·.insert e s)
  return s

private def mkOrInl (a b h : Expr) : Expr := mkApp3 (mkConst ``Or.inl) a b h
private def mkOrInr (a b h : Expr) : Expr := mkApp3 (mkConst ``Or.inr) a b h
private def mkOrElim (a b c h l r : Expr) : Expr := mkApp6 (mkConst ``Or.elim) a b c h l r

/-- `fun h : type => k h`, or `none` when `k` fails. -/
private def withHyp (name : Name) (type : Expr) (k : Expr → MetaM (Option Expr)) :
    MetaM (Option Expr) :=
  withLocalDeclD name type fun h => do
    let some body ← k h | return none
    return some (← mkLambdaFVars #[h] body)

/-- Literals that agree up to the orientation of an equation. -/
private def literal (p S T : Expr) : MetaM (Option Expr) := do
  if ← isDefEq S T then return some p
  let .eq u α a b ← shape S | return none
  let .eq _ _ a' b' ← shape T | return none
  unless ← isDefEq a b' do return none
  unless ← isDefEq b a' do return none
  return some (mkApp4 (mkConst ``Eq.symm [u]) α a b p)

mutual

/-- Prove `T` from `p : S`. -/
private partial def tr (ctx : Context) (vars : Array Expr) (p S T : Expr) :
    MetaM (Option Expr) := do
  let S ← norm S
  let T ← norm T
  if S == T then return some p
  if (← ctx.failed.get).contains (S, T) then return none
  unless ← tick ctx do return none
  let r ← trCore ctx vars p S T
  if r.isNone then ctx.failed.modify (·.insert (S, T))
  return r

private partial def trCore (ctx : Context) (vars : Array Expr) (p S T : Expr) :
    MetaM (Option Expr) := do
  let sS ← shape S
  let sT ← shape T
  -- TPTP represents equality of propositions as equivalence. Keep this
  -- conversion in the recursive walk so nested equalities are covered too.
  if let .eq _ type a b := sS then
    if type == mkSort .zero then
      return ← tr ctx vars (mkApp3 (mkConst ``Iff.of_eq) a b p) (mkIff a b) T
  if let .eq _ type a b := sT then
    if type == mkSort .zero then
      let some equivalent ← tr ctx vars p S (mkIff a b) | return none
      return some (mkApp3 (mkConst ``propext) a b equivalent)
  -- Target universals are introduced first; a source universal over the
  -- same type is instantiated with the new variable.
  if let .all name domain body := sT then
    return ← withLocalDeclD name domain fun y => do
      let T' := body.instantiate1 y
      let vars' := vars.push y
      let r ← match sS with
        | .all _ domain' body' =>
          if ← isDefEq domain domain' then
            tr ctx vars' (mkApp p y) (body'.instantiate1 y) T'
          else tr ctx vars' p S T'
        | _ => tr ctx vars' p S T'
      r.mapM (mkLambdaFVars #[y])
  -- Opening a source existential is always safe.
  if let .ex u domain pred := sS then
    return ← withLocalDeclD (predName pred) domain fun w => do
      let body := instPred pred w
      withLocalDeclD `vampireWitness body fun hw => do
        let some r ← tr ctx (vars.push w) hw body T | return none
        let lam ← mkLambdaFVars #[w, hw] r
        return some (mkApp5 (mkConst ``Exists.elim [u]) domain pred T p lam)
  -- Congruence for connectives present on both sides.
  if let some r ← congruence ctx vars p sS sT then return some r
  -- Named predicates and AVATAR components.
  if let .atom := sS then
    if let some (id, S') ← unfoldLetHead? S then
      ctx.unfolded.modify (·.insert id)
      return ← tr ctx vars p S' T
  if let .atom := sT then
    if let some (id, T') ← unfoldLetHead? T then
      ctx.unfolded.modify (·.insert id)
      -- `r : T'` is accepted at `T` by unfolding; the final check states it.
      return ← tr ctx vars p S T'
  -- Double negations and negated quantifiers and equivalences are rewritten
  -- at once; these steps are equivalences, so nothing is lost by committing.
  if let some r ← redex ctx vars p S sS T sT then return r
  -- Target conjunctions are proved conjunct by conjunct.
  match sT with
  | .tru => return some (mkConst ``True.intro)
  | .and a b =>
    let some ra ← tr ctx vars p S a | return none
    let some rb ← tr ctx vars p S b | return none
    return some (mkApp4 (mkConst ``And.intro) a b ra rb)
  | .iff a b =>
    let some mp ← tr ctx vars p S (mkForall `vampireIffMp .default a b) | return none
    let some mpr ← tr ctx vars p S (mkForall `vampireIffMpr .default b a) | return none
    return some (mkApp4 (mkConst ``Iff.intro) a b mp mpr)
  | .not inner =>
    match ← shape (← norm inner) with
    | .or a b =>
      if !(sS matches .not _) then
        let some r ← tr ctx vars p S (mkAnd (mkNot a) (mkNot b)) | return none
        return some (mkApp3 (mkConst ``and_to_not_or) a b r)
    | .imp a b =>
      if !(sS matches .not _) then
        let some r ← tr ctx vars p S (mkAnd a (mkNot b)) | return none
        return some (mkApp3 (mkConst ``and_to_not_imp) a b r)
    | _ => pure ()
  | _ => pure ()
  if let .fls := sS then
    return some (mkApp2 (mkConst ``False.elim [Level.zero]) T p)
  -- Source universals and target existentials need a witness.
  if let .all _ domain body := sS then
    for c in ← candidates vars domain do
      if let some r ← tr ctx vars (mkApp p c) (body.instantiate1 c) T then
        return some r
    return none
  if let .ex u domain pred := sT then
    for c in ← candidates vars domain do
      if let some r ← tr ctx vars p S (instPred pred c) then
        return some (mkApp4 (mkConst ``Exists.intro [u]) domain pred c r)
    return none
  -- Conjunctive source: one conjunct must suffice.
  if ← conjunctive S then
    let leaves ← conjuncts p S
    for (leaf, hl) in leaves do
      if leaf == T then return some hl
    let key ← signature ctx vars T
    for (leaf, hl) in leaves do
      unless (← signature ctx vars leaf) == key do continue
      if let some r ← tr ctx vars hl leaf T then return some r
    unless ← disjunctive T do return none
  -- Disjunctions up to associativity and commutativity.
  if ← (disjunctive S <||> disjunctive T) then
    return ← sourceCases ctx p S T fun leaf hl => inject ctx vars hl leaf T
  literal p S T

/-- Congruence for a connective at the head of both sides. -/
private partial def congruence (ctx : Context) (vars : Array Expr) (p : Expr) :
    Shape → Shape → MetaM (Option Expr)
  | .not a, .not b =>
    withHyp `vampireNeg b fun hb => do
      let some q ← tr ctx vars hb b a | return none
      return some (mkApp p q)
  | .imp a b, .imp a' b' =>
    withHyp `vampireAnte a' fun ha' => do
      let some q ← tr ctx vars ha' a' a | return none
      tr ctx vars (mkApp p q) b b'
  | .iff a b, .iff a' b' => do
    if let some r ← iffCongr ctx vars p a b a' b' then return some r
    iffCongr ctx vars (mkApp3 (mkConst ``Iff.symm) a b p) b a a' b'
  | .and a b, .and a' b' => do
    let some f ← withHyp `vampireLeft a fun ha => tr ctx vars ha a a' | return none
    let some g ← withHyp `vampireRight b fun hb => tr ctx vars hb b b' | return none
    return some (mkAppN (mkConst ``And.imp) #[a, a', b, b', f, g, p])
  | .or a b, .or a' b' => do
    let some f ← withHyp `vampireLeft a fun ha => tr ctx vars ha a a' | return none
    let some g ← withHyp `vampireRight b fun hb => tr ctx vars hb b b' | return none
    return some (mkAppN (mkConst ``Or.imp) #[a, a', b, b', f, g, p])
  | _, _ => pure none

private partial def iffCongr (ctx : Context) (vars : Array Expr) (p a b a' b' : Expr) :
    MetaM (Option Expr) := do
  let some mp ← withHyp `vampireIffMp a' fun x => do
      let some q ← tr ctx vars x a' a | return none
      tr ctx vars (mkApp4 (mkConst ``Iff.mp) a b p q) b b'
    | return none
  let some mpr ← withHyp `vampireIffMpr b' fun y => do
      let some q ← tr ctx vars y b' b | return none
      tr ctx vars (mkApp4 (mkConst ``Iff.mpr) a b p q) a a'
    | return none
  return some (mkApp4 (mkConst ``Iff.intro) a' b' mp mpr)

/-- `e` is a disjunction, possibly after one ENNF step. -/
private partial def disjunctive (e : Expr) : MetaM Bool := do
  match ← shape e with
  | .or .. | .imp .. => return true
  | .not inner => return ((← shape (← norm inner)) matches .and ..)
  | _ => return false

/-- `e` is a conjunction, possibly after one NNF step. -/
private partial def conjunctive (e : Expr) : MetaM Bool := do
  match ← shape e with
  | .and .. | .iff .. => return true
  | .not inner =>
    match ← shape (← norm inner) with
    | .or .. | .imp .. => return true
    | _ => return false
  | _ => return false

/-- Case split on the disjuncts of `p : S`, proving `motive` in each leaf. -/
private partial def sourceCases (ctx : Context) (p S motive : Expr)
    (k : Expr → Expr → MetaM (Option Expr)) : MetaM (Option Expr) := do
  let S ← norm S
  match ← shape S with
  | .or a b =>
    let some left ← withHyp `vampireLeft a fun ha => sourceCases ctx ha a motive k | return none
    let some right ← withHyp `vampireRight b fun hb => sourceCases ctx hb b motive k | return none
    return some (mkOrElim a b motive p left right)
  | .imp a b =>
    sourceCases ctx (mkApp3 (mkConst ``imp_to_or) a b p) (mkOr (mkNot a) b) motive k
  | .not inner =>
    match ← shape (← norm inner) with
    | .and a b =>
      sourceCases ctx (mkApp3 (mkConst ``not_and_to_or) a b p)
        (mkOr (mkNot a) (mkNot b)) motive k
    | _ => k S p
  | .fls => return some (mkApp2 (mkConst ``False.elim [Level.zero]) motive p)
  | _ => k S p

/-- The disjuncts of `T`, each with the injection of its proof into `T`. -/
private partial def targetLeaves (T : Expr) (wrap : Expr → Expr) :
    MetaM (Array (Expr × (Expr → Expr))) := do
  let T ← norm T
  match ← shape T with
  | .or a b =>
    return (← targetLeaves a (wrap ∘ mkOrInl a b)) ++ (← targetLeaves b (wrap ∘ mkOrInr a b))
  | .imp a b =>
    targetLeaves (mkOr (mkNot a) b) (wrap ∘ mkApp3 (mkConst ``or_to_imp) a b)
  | .not inner =>
    match ← shape (← norm inner) with
    | .and a b =>
      targetLeaves (mkOr (mkNot a) (mkNot b)) (wrap ∘ mkApp3 (mkConst ``or_to_not_and) a b)
    | _ => return #[(T, wrap)]
  | .fls => return #[]
  | _ => return #[(T, wrap)]

/-- Prove the disjunction `T` from one source disjunct `hl : leaf`. -/
private partial def inject (ctx : Context) (vars : Array Expr) (hl leaf T : Expr) :
    MetaM (Option Expr) := do
  let leaves ← targetLeaves T id
  for (t, wrap) in leaves do
    if t == leaf then return some (wrap hl)
  let key ← signature ctx vars leaf
  for (t, wrap) in leaves do
    if t == leaf then continue
    unless (← signature ctx vars t) == key do continue
    if let some r ← tr ctx vars hl leaf t then return some (wrap r)
  return none

/-- The conjuncts of `p : S`, each with its projection. -/
private partial def conjuncts (p S : Expr) : MetaM (Array (Expr × Expr)) := do
  let S ← norm S
  match ← shape S with
  | .and a b =>
    return (← conjuncts (mkApp3 (mkConst ``And.left) a b p) a) ++
      (← conjuncts (mkApp3 (mkConst ``And.right) a b p) b)
  | .iff a b =>
    return #[(mkForall `vampireIffMp .default a b, mkApp3 (mkConst ``Iff.mp) a b p),
      (mkForall `vampireIffMpr .default b a, mkApp3 (mkConst ``Iff.mpr) a b p)]
  | .not inner =>
    match ← shape (← norm inner) with
    | .or a b =>
      conjuncts (mkApp3 (mkConst ``not_or_to_and) a b p) (mkAnd (mkNot a) (mkNot b))
    | .imp a b =>
      conjuncts (mkApp3 (mkConst ``not_imp_to_and) a b p) (mkAnd a (mkNot b))
    | _ => return #[(S, p)]
  | _ => return #[(S, p)]

/-- The remaining NNF steps: double negations and negated quantifiers and
equivalences, on either side. -/
private partial def redex (ctx : Context) (vars : Array Expr) (p S : Expr) (sS : Shape)
    (T : Expr) (sT : Shape) : MetaM (Option (Option Expr)) := do
  if let .not inner := sS then
    let inner ← norm inner
    match ← shape inner with
    | .not a => return some (← tr ctx vars (mkApp2 (mkConst ``not_not_elim) a p) a T)
    | .all name domain body =>
      let u ← getLevel domain
      let S' := mkApp2 (mkConst ``Exists [u]) domain (predicate name domain (mkNot body))
      let p' := mkApp3 (mkConst ``not_forall_to_exists [u]) domain
        (predicate name domain body) p
      return some (← tr ctx vars p' S' T)
    | .ex u domain pred =>
      let S' := Expr.forallE (predName pred) domain
        (mkNot (headBetaAll (mkApp pred (.bvar 0)))) .default
      let p' := mkApp3 (mkConst ``not_exists_to_forall [u]) domain pred p
      return some (← tr ctx vars p' S' T)
    | .iff a b =>
      if let some r ← tr ctx vars (mkApp3 (mkConst ``not_iff_to_iff_not) a b p)
          (mkIff a (mkNot b)) T then
        return some (some r)
      return some (← tr ctx vars (mkApp3 (mkConst ``not_iff_to_not_iff) a b p) (mkIff (mkNot a) b) T)
    | _ => pure ()
  if let .not inner := sT then
    let inner ← norm inner
    match ← shape inner with
    | .not a =>
      let some r ← tr ctx vars p S a | return some none
      return some (some (mkApp2 (mkConst ``not_not_intro) a r))
    | .all name domain body =>
      let u ← getLevel domain
      let T' := mkApp2 (mkConst ``Exists [u]) domain (predicate name domain (mkNot body))
      let some r ← tr ctx vars p S T' | return some none
      return some (some (mkApp3 (mkConst ``exists_to_not_forall [u]) domain
        (predicate name domain body) r))
    | .ex u domain pred =>
      let T' := Expr.forallE (predName pred) domain
        (mkNot (headBetaAll (mkApp pred (.bvar 0)))) .default
      let some r ← tr ctx vars p S T' | return some none
      return some (some (mkApp3 (mkConst ``forall_to_not_exists [u]) domain pred r))
    | .iff a b =>
      if let some r ← tr ctx vars p S (mkIff a (mkNot b)) then
        return some (some (mkApp3 (mkConst ``iff_not_to_not_iff) a b r))
      let some r ← tr ctx vars p S (mkIff (mkNot a) b) | return some none
      return some (some (mkApp3 (mkConst ``not_iff_from_not_iff) a b r))
    | _ => pure ()
  return none

end

/-- Prove `target` from `proof` structurally; see the module comment.
Returns `none` when the two formulas are not related by the supported steps,
so callers can fall back to a tactic. -/
def transport (proof target : Expr) (fuel : Nat := 20000) : MetaM (Option Expr) := do
  unless vampire.structural.get (← getOptions) do return none
  withNewMCtxDepth do
    let source ← inferType proof
    let ctx : Context := {
      fuel := ← IO.mkRef fuel
      unfolded := ← IO.mkRef {}
      failed := ← IO.mkRef {}
      signatures := ← IO.mkRef {} }
    -- Proof-local Skolem functions stay folded while comparing literals:
    -- unfolding one exposes a large `Classical.choose` term.  Named
    -- predicates are unfolded explicitly by the walk instead.
    let result ← withConfig (fun config => { config with zetaDelta := false }) <|
      tr ctx #[] proof source target
    let some proof := result | do
      trace[vampire.replay] "structural transport failed (fuel left {← ctx.fuel.get}):\nsource {source}\ntarget {target}"
      return none
    let proof ← instantiateMVars proof
    -- Metavariables of the surrounding elaboration (e.g. universe levels)
    -- may legitimately occur; only ones created here must be resolved.
    if ← hasAssignableMVar proof then return none
    let unfolded ← ctx.unfolded.get
    let ok ← withConfig (fun config => { config with zetaDelta := false }) <|
      withZetaDeltaSet unfolded (isDefEq (← inferType proof) target)
    unless ok do
      trace[vampire.replay] "structural transport produced an unexpected type"
      return none
    return some (← mkExpectedTypeHint proof target)

/-! ### AVATAR splits by refutation

`avatar_split_clause` derives `spl₁ ∨ … ∨ splₙ` from a clause
`∀ x̄, C₁ ∨ … ∨ Cₙ` whose components `Cᵢ` share no variables, where each
`splᵢ` is let-bound to `∀ ȳᵢ, Cᵢ` (or names a ground literal `L` and occurs as
`¬splᵢ` for the component `¬L`).  Assuming the negated target gives, for every
component, Skolem witnesses `ȳᵢ` and the negation of each of its literals; the
source clause instantiated at those witnesses is then refuted literal by
literal.  The instantiation is found by unification. -/

/-- A proof of `False` from `hl : L`, given that `F` holds by `hF`. -/
private def refutation (L F : Expr) : MetaM (Option (Expr → Expr → Expr)) := do
  if let .not A ← shape (← norm F) then
    if ← isDefEq L A then return some fun hl hF => mkApp hF hl
    if let .eq u α a b ← shape L then
      if let .eq _ _ a' b' ← shape (← norm A) then
        if ← (isDefEq a b' <&&> isDefEq b a') then
          return some fun hl hF => mkApp hF (mkApp4 (mkConst ``Eq.symm [u]) α a b hl)
  if let .not A ← shape L then
    let A ← norm A
    if ← isDefEq A F then return some fun hl hF => mkApp hl hF
    if let .eq u α a b ← shape (← norm F) then
      if let .eq _ _ a' b' ← shape A then
        if ← (isDefEq a b' <&&> isDefEq b a') then
          return some fun hl hF => mkApp hl (mkApp4 (mkConst ``Eq.symm [u]) α a b hF)
  return none

/-- Turn the pending negated target disjuncts into facts, opening negated
universals as witnesses; `k` receives the facts and the witnesses. -/
private partial def targetFacts (splitAtoms : FVarIdSet)
    (pending : List (Expr × Expr)) (facts : Array (Expr × Expr))
    (vars : Array Expr) (k : Array (Expr × Expr) → Array Expr → MetaM (Option Expr)) :
    MetaM (Option Expr) := do
  match pending with
  | [] => k facts vars
  | (D, nD) :: rest =>
    let D ← norm D
    match ← shape D with
    | .or a b =>
      let left ← withLocalDeclD `vampireLeft a fun x => do
        mkLambdaFVars #[x] (mkApp nD (mkOrInl a b x))
      let right ← withLocalDeclD `vampireRight b fun x => do
        mkLambdaFVars #[x] (mkApp nD (mkOrInr a b x))
      targetFacts splitAtoms ((a, left) :: (b, right) :: rest) facts vars k
    | .all name domain body =>
      let u ← getLevel domain
      let negated := predicate name domain (mkNot body)
      let ex := mkApp3 (mkConst ``not_forall_to_exists [u]) domain
        (predicate name domain body) nD
      withLocalDeclD name domain fun x => do
        let body := body.instantiate1 x
        withLocalDeclD `vampireCounter (mkNot body) fun hx => do
          let some r ← targetFacts splitAtoms ((body, hx) :: rest) facts (vars.push x) k | return none
          let lam ← mkLambdaFVars #[x, hx] r
          return some (mkApp5 (mkConst ``Exists.elim [u]) domain negated (mkConst ``False) ex lam)
    | .not a =>
      let mut a ← norm a
      while a.isFVar && splitAtoms.contains a.fvarId! do
        let some (_, a') ← unfoldLetHead? a | break
        a ← norm a'
      targetFacts splitAtoms rest (facts.push (a, mkApp2 (mkConst ``not_not_elim) a nD)) vars k
    | .fls => targetFacts splitAtoms rest facts vars k
    | .atom =>
      -- Only the split symbols themselves are unfolded; a named predicate
      -- `sP x̄` inside a component stays folded, as in the source clause.
      if let some (_, D') ← if D.isFVar && splitAtoms.contains D.fvarId! then
          unfoldLetHead? D else pure none then
        targetFacts splitAtoms ((D', nD) :: rest) facts vars k
      else
        targetFacts splitAtoms rest (facts.push (mkNot D, nD)) vars k
    | _ => targetFacts splitAtoms rest (facts.push (mkNot D, nD)) vars k

/-- The disjuncts of a clause. -/
private partial def clauseLeaves (e : Expr) : MetaM (Array Expr) := do
  let e ← norm e
  match ← shape e with
  | .or a b => return (← clauseLeaves a) ++ (← clauseLeaves b)
  | .fls => return #[]
  | _ => return #[e]

/-- Assign the source variables so that every literal is refuted by a fact. -/
private partial def assignLeaves (leaves : List Expr) (facts : Array (Expr × Expr)) :
    MetaM Bool := do
  match leaves with
  | [] => return true
  | leaf :: rest =>
    for (F, _) in facts do
      let saved ← saveState
      if (← refutation (← norm leaf) F).isSome then
        if ← assignLeaves rest facts then return true
      saved.restore
    return false

/-- Refute the instantiated source clause `hp : body` by case analysis. -/
private partial def refuteSource (body hp : Expr) (facts : Array (Expr × Expr)) :
    MetaM (Option Expr) := do
  let body ← norm body
  match ← shape body with
  | .or a b =>
    let some left ← withHyp `vampireLeft a fun ha => refuteSource a ha facts | return none
    let some right ← withHyp `vampireRight b fun hb => refuteSource b hb facts | return none
    return some (mkOrElim a b (mkConst ``False) hp left right)
  | .fls => return some hp
  | _ =>
    for (F, hF) in facts do
      if let some f ← refutation body F then return some (f hp hF)
    return none

/-- Prove an AVATAR split `target` from the clause `source`; see above.
`expandOnly?` restricts unfolding to fresh components, keeping carried AVATAR
conditions atomic. Omitting it retains the standalone tactic's behavior. -/
def splitClause (source target : Expr) (expandOnly? : Option (Array Expr) := none) :
    MetaM (Option Expr) := do
  unless vampire.structural.get (← getOptions) do return none
  withNewMCtxDepth <| withConfig (fun config => { config with zetaDelta := false }) do
    let target ← norm target
    -- Only the selected split atoms in the propositional goal are definitions
    -- to expand. In particular a nullary naming predicate such as `sP3` inside
    -- a component is an ordinary clause literal, even though it too is a let.
    -- Expanding it would lose the literal `¬sP3` needed to refute the source.
    let mut splitAtoms : FVarIdSet := {}
    let expandable ← match expandOnly? with
      | some atoms => pure atoms
      | none => (← clauseLeaves target).mapM fun literal => pure (literal.not?.getD literal)
    for atom in expandable do
      if let some id := atom.fvarId? then splitAtoms := splitAtoms.insert id
    let some proof ← withHyp `vampireSplitNegation (mkNot target) fun h =>
        targetFacts splitAtoms [(target, h)] #[] #[] fun facts vars => do
          let mut sourceType ← norm (← inferType source)
          let mut sourceProof := source
          let mut mvars := #[]
          while true do
            let .all _ domain body ← shape sourceType | break
            let m ← mkFreshExprMVar domain
            mvars := mvars.push m
            sourceProof := mkApp sourceProof m
            sourceType ← norm (body.instantiate1 m)
          unless ← assignLeaves (← clauseLeaves sourceType).toList facts do
            trace[vampire.replay] "structural split: no refuting assignment\nsource {sourceType}\nfacts {facts.map (·.1)}"
            return none
          -- A variable that occurs in no literal still needs some value.
          for m in mvars do
            let m ← instantiateMVars m
            let .mvar id := m | continue
            let some c := (← candidates vars (← inferType m))[0]? | return none
            id.assign c
          refuteSource (← instantiateMVars sourceType) (← instantiateMVars sourceProof) facts
      | return none
    let proof ← instantiateMVars (mkApp2 (mkConst ``Classical.byContradiction) target proof)
    if ← hasAssignableMVar proof then return none
    return some proof

end VampireHammer.Structural
