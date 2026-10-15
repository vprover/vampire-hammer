import VampireHammer
import VampireHammer.TptpPrinter

/-! Check the shared-forward-parent graph through actual proof reconstruction,
and again after standalone printing. The final contradiction is reconstructed
from its local parents through the ordinary checked fallback. -/

#eval show IO Unit from do
  let original ← IO.ofExcept (← VampireHammer.parseVampireTSTP
    "" "Tests/testdata/shared-forward-parents.tstp")
  let text ← IO.ofExcept (VampireHammer.TptpPrinter.render original)
  IO.FS.createDirAll "artifacts"
  IO.FS.writeFile "artifacts/forward-dependency-rendered.tstp" text

set_option vampire.executable "Tests/testdata/scripts/mock-fixture.sh"

set_option vampire.strategy "shared-forward-parents" in
set_option vampire.outputPath "artifacts/forward-dependency.p" in
theorem sharedForwardParents (P : Prop) (positive : P) (negative : ¬P) : False := by
  vampire [positive, negative]

set_option vampire.strategy "../artifacts/forward-dependency-rendered" in
set_option vampire.outputPath "artifacts/forward-dependency-printed.p" in
theorem printedSharedForwardParents (P : Prop) (positive : P) (negative : ¬P) : False := by
  vampire [positive, negative]

#print axioms sharedForwardParents
#print axioms printedSharedForwardParents
