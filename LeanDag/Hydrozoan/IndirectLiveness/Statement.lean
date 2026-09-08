import LeanDag.Hydrozoan.Model.Decided
/-!
# Statement: indirect liveness — the graded rule is total

The indirect rule's job: every slot below a committed run gets a
verdict, even one whose leader was faulty. `AnchoredTotality` says a
nearest eligible committed anchor always returns a verdict through the
three-rung ladder; `DecidedBelowRun` says a run of `c` committed slots,
long enough that its end anchors everything below, decides every slot
below it. Pure decision-relation combinatorics: no synchrony,
population or fault-count hypothesis appears.
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
