import LeanDag.FinWhale.Model.Verdict
import Mathlib.Data.Finset.Sort

/-!
# FinWhale — the committed sequence, and the delivery order

What a validator outputs, in two steps. `commitSeq` reads the verdicts of
the first `k` slots in slot order and keeps the committed blocks;
`linearise` walks that sequence and, after each leader, appends the
blocks of its causal history that no earlier leader delivered.

The list a leader contributes is a parameter here. `Model/Liveness.lean`
fixes it as `histOf`, the causal history sorted by identifier, which is
all the paper's "deterministic sort" is read for.
-/


namespace LeanDag

namespace FinWhale

variable {Validator : Type*} [Fintype Validator] [DecidableEq Validator]
variable [Faults Validator] [Params Validator]
variable {BlockId : Type*} [DecidableEq BlockId] {Payload : Type*}

/-- **The committed leader sequence** of the first `k` slots. -/
def commitSeq (dec : ℕ → Verdict BlockId) : ℕ → List BlockId
  | 0 => []
  | k + 1 => commitSeq dec k ++ (match dec k with
      | Verdict.commit b => [b]
      | Verdict.skip => []
      | Verdict.undecided => [])

/-- **The delivery order.** Each committed leader contributes the blocks
of its causal history that no earlier leader delivered. -/
def linearise (hist : BlockId → List BlockId) (ls : List BlockId) : List BlockId :=
  ls.foldl (fun acc l => acc ++ (hist l).filter (fun b => b ∉ acc)) []

/-- **The delivery order's input, concretely.** A leader contributes its
causal history, computed by `historyFrom` and listed in the identifier
order — the cheapest deterministic sort that lists each block once, and
all that Theorems 24 and 26 read of it. -/
def histOf [LinearOrder BlockId] (D : Dag Validator BlockId Payload) (l : BlockId) :
    List BlockId :=
  (historyFrom D.block l).sort (· ≤ ·)

end FinWhale

end LeanDag
