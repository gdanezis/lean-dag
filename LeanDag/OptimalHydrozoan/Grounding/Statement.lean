import LeanDag.OptimalHydrozoan.EventualDecision.Statement
import LeanDag.Hydrozoan.Grounding.Statement
/-!
# Optimal-Hydrozoan: grounding — the liveness hypotheses are dischargeable

Hydrozoan's `Grounding` read over the Optimal arc: `WaveRobinFair` is
reused verbatim, and the two universe-level conjuncts are re-stated over
`OptUniverse`. Leader exclusion is implied by the good-period scenario
(no equivocation), so this fixes the witness's type rather than adding
an obligation. `FastLatency` is not grounded.
-/

namespace LeanDag

namespace OptimalHydrozoan

open LeanDag.Hydrozoan

namespace Grounding

open LeanDag.Hydrozoan.Grounding (WaveRobinFair)

/-- **The liveness hypothesis package is realizable, by an Optimal
universe, under every schedule.** Hydrozoan's reading, at a witness
typed `OptUniverse`: a `T`-only universe synchronised from round 0
witnesses no equivocation (two same-creator blocks in one round would
both be refs of every `T`-block above, against `distinct_creators`), so
leader exclusion holds in it for free rather than as an extra
obligation. -/
def HypothesesRealizable : Prop :=
  ∀ (Replica : Type) [Fintype Replica] [DecidableEq Replica]
    [OptimalFaults Replica] [Slots Replica] (T : Finset Replica) (N : ℕ),
    q Replica ≤ T.card →                   -- a quorum-sized T:
    ∃ U : OptUniverse Replica ℕ,           -- some Optimal universe is
      (∀ b ∈ U.ids, (U.block b).creator ∈ T) ∧  -- authored by T alone,
      (∀ r, r ≤ N → PopulatedOn U.toBlockRecord T r) ∧  -- populated to N
      SynchronisedOn U.toBlockRecord T 0  -- and synchronised throughout.

/-- **Grounded progress.** Under wave-aligned round-robin, past every
point some Optimal universe authored by correct replicas alone commits a
bound with every slot below it decided, on any view caught up to the
decision round — satisfiability, as in Hydrozoan. Correct-only authorship
is what makes the claim consult the fault sets at all: without it, a
universe where every replica participates would satisfy the conclusion
trivially. -/
def GroundedProgress : Prop :=
  ∀ (n : ℕ) (hn : 0 < n) [OptimalFaults (Fin n)],
    letI : Slots (Fin n) := waveRobin n hn    -- under wave-aligned rotation,
    ∀ k : ℕ, ∃ b, k ≤ b ∧                     -- past any slot k,
      ∃ U : OptUniverse (Fin n) ℕ,            -- some Optimal universe
        (∀ i ∈ U.ids, (U.block i).creator ∈ LeanDag.Hydrozoan.Correct) ∧  -- of correct creators only:
        ∀ V : LeanDag.Hydrozoan.View U.toBlockRecord,         -- on any view caught up to
          V.CoversUpto (b + 4) →              -- ... the decision round, it
        (∃ L, DecidedOpt U V b (some L)) ∧    -- commits b
        ∀ i, i < b → ∃ v,                     -- with every slot below
          DecidedOpt U V i v                  -- decided.

/-- Grounding of the Optimal arc, over every replica count and fault
configuration the model admits: Hydrozoan's fairness claim, and the two
universe-level claims over `OptUniverse`. -/
def Statement : Prop :=
  WaveRobinFair ∧ HypothesesRealizable ∧ GroundedProgress

end Grounding

end OptimalHydrozoan

end LeanDag
