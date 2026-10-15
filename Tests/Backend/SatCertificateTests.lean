import VampireHammer.Backend.SatCertificate

open VampireHammer.SatCertificate Std.Tactic.BVDecide

#eval show IO Unit from do
  let boundary := #[
    ("a", #[(0, true), (1, true)]),
    ("b", #[(0, false)]),
    ("c", #[(1, false)])]
  let trail : Array RupStep := #[⟨"root", #[], #["a", "b", "c"]⟩]
  let some actions := compile boundary trail "root"
    | throw <| IO.userError "failed to order valid RUP hints"
  unless actions == #[.addEmpty 4 #[2, 3, 1]] do
    throw <| IO.userError s!"unexpected ordered hints: {repr actions}"
  let cnf : Std.Sat.CNF Nat := ⟨boundary.map (·.2.toList)⟩
  unless LRAT.check actions cnf do
    throw <| IO.userError "standard checker rejected a valid compiled certificate"
  let satisfiable : Std.Sat.CNF Nat := ⟨#[boundary[0]!.2.toList, boundary[1]!.2.toList]⟩
  if LRAT.check actions satisfiable then
    throw <| IO.userError "checker accepted a certificate for a changed, satisfiable CNF"
  let conversion : Array RupStep := #[
    ⟨"converted", #[(1, true), (0, true)], #["a"]⟩,
    ⟨"root", #[], #["converted", "b", "c"]⟩]
  let some converted := compile boundary conversion "root"
    | throw <| IO.userError "failed on a reordered sat_conversion clause"
  unless LRAT.check converted cnf do
    throw <| IO.userError "checker rejected reordered conversion"
  let missing : Array RupStep := #[⟨"root", #[], #["missing"]⟩]
  unless (compile boundary missing "root").isNone do
    throw <| IO.userError "accepted an unknown parent"
  unless (compile #[boundary[0]!] #[⟨"root", #[], #["a"]⟩] "root").isNone do
    throw <| IO.userError "compiled a satisfiable boundary as a RUP refutation"
  unless (compile boundary trail "otherRoot").isNone do
    throw <| IO.userError "ignored the supplied root"
  unless (compile #[("tautology", #[(0, true), (0, false)])] trail "root").isNone do
    throw <| IO.userError "initial tautology did not decline before ID remapping"

-- Kernel checks for the CNF-to-Boolean bridge, independent of certificate compilation.
example (assign : Nat → Bool) (c : List Literal) (cs : List (List Literal))
    (head : clauseValue assign c = true)
    (tail : cs.all (Std.Sat.CNF.Clause.eval assign) = true) :
    (c :: cs).all (Std.Sat.CNF.Clause.eval assign) = true :=
  satCons assign c cs head tail

example (assign : Nat → Bool) :
    clauseValue assign [(0, true), (1, false)] =
      Std.Sat.CNF.Clause.eval assign [(0, true), (1, false)] :=
  clauseValue_eq_eval assign _

-- Exercise native checking together with the proved bridge. The resulting
-- contradiction applies to any assignment, not to a chosen test value.
example (assign : Nat → Bool)
    (satisfied : [[(0, true)], [(0, false)]].all
      (Std.Sat.CNF.Clause.eval assign) = true) : False :=
  refute [[(0, true)], [(0, false)]] #[.addEmpty 3 #[1, 2]] (by native_decide) assign satisfied

-- The same refutation with the hints in LRAT text form, as the handler emits
-- them; the serialization round-trips through the standard parser.
example (assign : Nat → Bool)
    (satisfied : [[(0, true)], [(0, false)]].all
      (Std.Sat.CNF.Clause.eval assign) = true) : False :=
  refuteCert [[(0, true)], [(0, false)]]
    (Std.Tactic.BVDecide.LRAT.lratProofToString #[.addEmpty 3 #[1, 2]])
    (by native_decide) assign satisfied

-- `Assignment` lookups reduce in the kernel. This is the layout the AVATAR
-- SAT bridge builds for six variables: the first child holds positions 1, 3,
-- 5, the second 2, 4 (subtree index `j` is position `stride * j + offset`).
section
variable (v0 v1 v2 v3 v4 v5 : Bool)
private def sixAssignment : Assignment :=
  .node v0 (.node v1 (.node v3 .leaf .leaf) (.node v5 .leaf .leaf)) (.node v2 (.node v4 .leaf .leaf) .leaf)
example : (sixAssignment v0 v1 v2 v3 v4 v5).get 0 = v0 := rfl
example : (sixAssignment v0 v1 v2 v3 v4 v5).get 1 = v1 := rfl
example : (sixAssignment v0 v1 v2 v3 v4 v5).get 2 = v2 := rfl
example : (sixAssignment v0 v1 v2 v3 v4 v5).get 3 = v3 := rfl
example : (sixAssignment v0 v1 v2 v3 v4 v5).get 4 = v4 := rfl
example : (sixAssignment v0 v1 v2 v3 v4 v5).get 5 = v5 := rfl
example : (sixAssignment v0 v1 v2 v3 v4 v5).get 6 = false := rfl
end
