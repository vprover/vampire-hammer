import VampireHammer

open VampireHammer Auto.Embedding.Lam

-- Roles follow explicit provenance, not position or the presence of negation.
#eval show IO Unit from do
  let facts := #[LamTerm.mkNot (.atom 0), LamTerm.mkNot (.atom 1)]
  for higherOrder in [false, true] do
    let dialect := if higherOrder then "thf" else "tff"
    let exporter := fun roles => if higherOrder then
      THF.exportProblem #[.base .prop, .base .prop] #[] #[] facts roles
      else TFF.exportProblem #[.base .prop, .base .prop] #[] #[] facts roles
    let problem ← IO.ofExcept <| exporter #[false, true]
    unless problem.text.contains s!"{dialect}(fact0, axiom," &&
        problem.text.contains s!"{dialect}(fact1, negated_conjecture," do
      throw <| IO.userError "exporter lost explicit conjecture roles"
    let ordinary ← IO.ofExcept <| exporter #[]
    if ordinary.text.contains "negated_conjecture" then
      throw <| IO.userError "exporter guessed conjecture roles from negative facts"
    unless problem.facts == ordinary.facts do
      throw <| IO.userError "role annotations changed replay source formulas"

set_option vampire.outputPath "artifacts/conjecture-role-fo.p" in
example {α : Type} (a : α) (P Q R : α → Prop)
    (h : ∀ x, P x → Q x) (hp : P a) (negativePremise : ¬R a) : Q a := by
  vampire_export [h, hp, negativePremise]
  exact h a hp

set_option vampire.higherOrder true in
set_option vampire.outputPath "artifacts/conjecture-role-ho.p" in
example {α : Type} (a : α) (P Q R : α → Prop)
    (h : ∀ x, P x → Q x) (hp : P a) (negativePremise : ¬R a) : Q a := by
  vampire_export [h, hp, negativePremise]
  exact h a hp

#eval show IO Unit from do
  for path in ["artifacts/conjecture-role-fo.p", "artifacts/conjecture-role-ho.p"] do
    let text ← IO.FS.readFile path
    let roles := text.splitOn "negated_conjecture"
    unless roles.length == 2 do
      throw <| IO.userError s!"expected exactly one goal-derived fact in {path}"
  IO.println "Conjecture roles: FO/HO preserve goal provenance and ordinary negative premises"
