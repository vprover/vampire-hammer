import Lean

namespace ComparisonBenchmarkFixture

opaque f : Nat → Nat
axiom f_eq (n : Nat) : f n = n
theorem premise (n : Nat) : f n = n := f_eq n
theorem target (n : Nat) : f n = n := premise n
theorem future (n : Nat) : f n = n := target n

theorem excluded : (0 : Nat) = 0 := helper
where
  helper : (0 : Nat) = 0 := rfl

end ComparisonBenchmarkFixture
