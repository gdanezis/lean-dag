import LeanDag.Hydrozoan.Model.Decided
/-!
# Statement: indirect liveness — the graded rule is total

Direct liveness commits a synchronised wave's slot; the ledger advances
only when *every* slot below gets a verdict, including slots whose
leader was faulty or whose wave predates synchrony. That is the indirect
rule's job (the paper's `TryIndirectDecide`), and this claim is that it
does that job. Two Props:

- `AnchoredTotality`: once a nearest eligible committed anchor exists,
  the three-rung ladder always returns a verdict — a certificate rung
  hit, else a weak-quorum hit with the deterministic least-candidate
  tie-break, else a skip. No rung combination leaves a slot underivable.
- `DecidedBelowRun`: a run of `c` consecutive committed slots, long
  enough that its last slot is an eligible anchor for everything below
  (the relation's `SpansEligible`; under the pipelined schedule, one
  slot per round, exactly when `c ≥ 3`), decides *every* slot below it. A single committed
  slot does not suffice — the slots immediately below it cannot use it
  as an anchor (it sits inside their decision rounds) — but a
  three-round run does: the slots just below the run have no eligible
  slots between themselves and the run's end, so they resolve outright,
  and everything lower descends onto them.

Both claims are pure decision-relation combinatorics: no synchrony, no
population, and no fault-count hypotheses appear. Those enter only when
committing the run itself, which is direct liveness's `CommitLiveness`;
the eventual-decision phase composes the two.
-/

namespace LeanDag

namespace Hydrozoan
namespace IndirectLiveness

variable {Replica BlockId : Type*} [Fintype Replica] [DecidableEq Replica]
  [DecidableEq BlockId] [LinearOrder BlockId] [F : LeanDag.Hydrozoan.Faults Replica]
  [S : Slots Replica]

/-- Indirect liveness, over every fault configuration, schedule,
tie-break order, and block universe the model admits. -/
def Statement : Prop :=
  ∀ (Replica BlockId : Type) [Fintype Replica] [DecidableEq Replica]
    [DecidableEq BlockId] [LinearOrder BlockId] [LeanDag.Hydrozoan.Faults Replica]
    [Slots Replica] (U : BlockUniverse Replica BlockId),
    (hydrozoanAnchored Replica BlockId).Total U ∧
      (hydrozoanAnchored Replica BlockId).DecidedBelowRun U

end IndirectLiveness
end Hydrozoan

end LeanDag
