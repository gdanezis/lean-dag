import LeanDag.OptimalHydrozoan.Model.Decided
/-!
# Optimal-Hydrozoan: slot agreement — statement

Hydrozoan's `SlotAgreement` read over `DecidedOpt`, minus the tie-break
order: any two verdicts on one slot agree, across views and routes. The
fast path's own seam — a fast commit makes every decision-round block
fast evidence for the committed block, so every eligible anchor reaches
an evidence quorum, and two such quorums share a non-Byzantine creator —
is what makes the evidence rung need no tie-break.
-/

namespace LeanDag

namespace OptimalHydrozoan

open LeanDag.Hydrozoan

namespace SlotAgreement

variable {Replica BlockId : Type*} [Fintype Replica] [DecidableEq Replica]
  [DecidableEq BlockId] [O : OptimalFaults Replica] [S : Slots Replica]

/-- Any two verdicts on one slot agree: across views, across routes
(fast, slow, direct skip, certificate rung, evidence rung, indirect
skip). -/
def DecidedUnique (U : OptUniverse Replica BlockId) : Prop :=
  ∀ (V₁ V₂ : LeanDag.Hydrozoan.View U.toBlockRecord) (k : ℕ) (v₁ v₂ : Option BlockId),
    DecidedOpt U V₁ k v₁ → DecidedOpt U V₂ k v₂ → v₁ = v₂

/-- Slot agreement, over every fault configuration, schedule, and
universe the Optimal model admits. -/
def Statement : Prop :=
  ∀ (Replica BlockId : Type) [Fintype Replica] [DecidableEq Replica]
    [DecidableEq BlockId] [OptimalFaults Replica] [Slots Replica]
    (U : OptUniverse Replica BlockId),
    DecidedUnique U

end SlotAgreement

end OptimalHydrozoan

end LeanDag
