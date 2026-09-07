import LeanDag.OptimalHydrozoan.Model.Decided
import LeanDag.Hydrozoan.IndirectLiveness.Statement
/-!
# Optimal-Hydrozoan: indirect liveness — the graded rule is total

Hydrozoan's `IndirectLiveness` read over `DecidedOpt`. Direct liveness
commits a synchronised wave's slot; the ledger advances only when *every*
slot below gets a verdict, including slots whose leader was faulty or
whose wave predates synchrony — the indirect rule's job. Two claims:

- `AnchoredTotality`: once a nearest eligible committed anchor exists,
  the three-rung ladder always returns a verdict — a certificate rung
  hit, else an evidence-quorum hit, else a skip. Without the tie-break of
  Hydrozoan's weak rung (decision D3), the evidence rung fires on *any*
  candidate clearing it; that this is at most one candidate is slot
  agreement's business, not totality's.
- `DecidedBelowRun`: a run of `c` consecutive committed slots, long
  enough that its last slot anchors everything below (`SpansEligible`,
  reused from Hydrozoan — a schedule-only notion), decides every slot
  below it.

Both claims are pure decision-relation combinatorics: no synchrony,
population, or fault-count hypothesis appears. The witness models
exercise the run length `c ∈ {3, 4}` under the pipelined schedule only;
a non-pipelined schedule (one slot per wave) satisfies `SpansEligible 1`,
where a single committed slot decides everything below — a residual no
witness pins.

This file imports Hydrozoan's `IndirectLiveness.Statement` for
`SpansEligible`: a reviewed file importing the reviewed file it mirrors,
as the other Optimal statements do (recorded in `optimal-hydrozoan.md`).
-/

namespace LeanDag

namespace OptimalHydrozoan

open LeanDag.Hydrozoan

namespace IndirectLiveness

variable {Replica BlockId : Type*} [Fintype Replica] [DecidableEq Replica]
  [DecidableEq BlockId] [O : OptimalFaults Replica] [S : Slots Replica]

/-- Indirect liveness of Optimal-Hydrozoan, over every fault
configuration, schedule, and universe the model admits. -/
def Statement : Prop :=
  ∀ (Replica BlockId : Type) [Fintype Replica] [DecidableEq Replica]
    [DecidableEq BlockId] [OptimalFaults Replica] [Slots Replica]
    (U : OptUniverse Replica BlockId),
    (optimalAnchored Replica BlockId).Total U.toBlockRecord ∧
      (optimalAnchored Replica BlockId).DecidedBelowRun U.toBlockRecord

end IndirectLiveness

end OptimalHydrozoan

end LeanDag
