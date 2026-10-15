import Lean

namespace BenchmarkReplayFixture

-- The imported namespace and instance require the replay to load environment
-- extensions, as Lean's frontend does.
open Lean

theorem premise : (default : Name) = default := rfl
theorem target : (default : Name) = default := premise
theorem future : (default : Name) = default := target

theorem excluded : (0 : Nat) = 0 := helper
where
  helper : (0 : Nat) = 0 := rfl

end BenchmarkReplayFixture
