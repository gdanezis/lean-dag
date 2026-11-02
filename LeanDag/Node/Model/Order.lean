import LeanDag.Node.Model.Step
import LeanDag.Common.BypassView
/-!
# An honest node — what it orders

`docs/dos-bounds.md` §5, Phase 3.1. A node's verdict for slot `k` is its kept
decision for `k` (`verdictIn`). The blocks it ordered after `n` slots are the
ledger of its verdicts under bypass below the decided horizon, read from its
disk (`State.ordered`, `ledgerOn`).

Definitions only.
-/

namespace LeanDag

namespace Node

variable {Validator BlockId Payload : Type} [DecidableEq Validator] [LinearOrder BlockId]

/-- The verdict a list of decisions gives slot `k`, if it decides it. -/
def verdictIn (ds : List (ℕ × Option BlockId)) (k : ℕ) : Option BlockId :=
  ((ds.find? fun e => e.1 == k).map Prod.snd).join

/-- **The blocks a node ordered after `n` slots**: the ledger of its verdicts,
read from its disk. -/
def State.ordered [S : Slots Validator] (q : ℕ) (s : State Validator BlockId Payload) (n : ℕ) :
    Finset BlockId :=
  ledgerOn s.disk.blk q (verdictIn s.decided) n

end Node

end LeanDag
