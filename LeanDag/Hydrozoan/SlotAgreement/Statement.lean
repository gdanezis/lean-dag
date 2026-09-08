import LeanDag.Hydrozoan.Model.Decided
/-!
# Slot agreement — statement

The headline safety claim for a single slot: any two verdicts agree,
across views and across routes (fast, slow, certificate rung, weak
rung, direct or indirect skip). Undecided replicas assert nothing, so
this is no-conflicting-decision, not termination. The proof (generated)
consumes `DirectSafety` and the quorum-intersection rows of
`ThresholdArithmetic`.
-/

namespace LeanDag

namespace Hydrozoan

namespace SlotAgreement

variable {Replica BlockId : Type*} [Fintype Replica] [DecidableEq Replica]
  [DecidableEq BlockId] [LinearOrder BlockId] [F : LeanDag.Hydrozoan.Faults Replica]
  [S : Slots Replica]

/-- Any two verdicts on one slot agree: across views, across routes
(fast, slow, direct skip, certificate rung, weak rung, indirect
skip). -/
def DecidedUnique (U : BlockUniverse Replica BlockId) : Prop :=
  ∀ (V₁ V₂ : View U) (k : ℕ) (v₁ v₂ : Option BlockId),
    Decided U V₁ k v₁ → Decided U V₂ k v₂ → v₁ = v₂

/-- Slot agreement, over every fault configuration, schedule, tie-break
order, and block universe the model admits. -/
def Statement : Prop :=
  ∀ (Replica BlockId : Type) [Fintype Replica] [DecidableEq Replica]
    [DecidableEq BlockId] [LinearOrder BlockId] [LeanDag.Hydrozoan.Faults Replica]
    [Slots Replica] (U : BlockUniverse Replica BlockId),
    DecidedUnique U

end SlotAgreement

end Hydrozoan

end LeanDag
