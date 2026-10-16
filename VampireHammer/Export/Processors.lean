import VampireHammer.Options

namespace VampireHammer.Export.Internal.Processors

open Lean

/-- A query inherits its enclosing search's allocation. Otherwise use all
hardware processors. The internal override also permits deterministic tests. -/
def budget (options : Options) : Nat :=
  max 1 (options.get `vampire.internal.processorBudget
    (System.Platform.Internal.getHardwareConcurrency ()).toNat)

def withBudget (options : Options) (processors : Nat) : Options :=
  options.set `vampire.internal.processorBudget (max 1 processors)

/-- Positive user settings cap the portfolio; zero fills its allocation. -/
def portfolioWorkers (options : Options) : Nat :=
  let available := budget options
  let requested := vampire.portfolioCores.get options
  if requested == 0 then available else min requested available

/-- Direct search gets the extra processor when the budget is odd. -/
def split (processors : Nat) : Nat × Nat :=
  ((processors + 1) / 2, processors / 2)

end VampireHammer.Export.Internal.Processors
