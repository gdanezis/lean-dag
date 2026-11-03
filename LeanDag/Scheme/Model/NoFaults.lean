import LeanDag.Common.Validators
/-!
# A fault model with no faults

The core's fault class asks `n ≥ 3f + 1`, which the hybrid committees
(`3f + 2c + 1`, `2c + 1`) do not meet at `f + c`. Structures that the
development states over the core's class are read here at `f = 0`, where
every committee is admitted, and the quorum they need is supplied apart:
Steelhead's coin counts (`Helpers/AsyncCoin.lean`) and the reactive pacing
trunk (`Model/Reactive.lean`).

Definitions only.
-/

namespace LeanDag

namespace Scheme

variable {Validator : Type} [Fintype Validator] [DecidableEq Validator] [Nonempty Validator]

/-- A fault model with no faults. -/
def noFaults : Faults Validator where
  f := 0
  byzantine := ∅
  card_validators := by have := Fintype.card_pos (α := Validator); omega
  card_byzantine := by simp

end Scheme

end LeanDag
