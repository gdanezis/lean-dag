import LeanDag.Hydrozoan.EventualDecision.Statement
/-!
# Statement: grounding — the liveness hypotheses are dischargeable

The liveness arc assumes schedule fairness and the synchrony/population
package of `Model/Liveness.lean`; this claim shows each is satisfiable
rather than vacuous, at every scale, under the wave-aligned round-robin
schedule. Message delivery, GST and timeouts are out of scope: this
grounds satisfiability, not operational realizability.
-/

namespace LeanDag

namespace Hydrozoan
namespace Grounding

/-- **A fair schedule exists, unconditionally.** One correct leader's
wave is a full correct 3-run by itself and recurs every cycle, so
wave-aligned round-robin is fair with no premise beyond the fault
model — unlike per-slot rotation, which needs `n` to exceed three times
the actual fault count. -/
def WaveRobinFair : Prop :=
  ∀ (n : ℕ) (hn : 0 < n) [Faults (Fin n)],
    FairRunOn (S := waveRobin n hn)
      (Correct : Finset (Fin n)) 3            -- correct 3-runs recur.

/-- **The liveness hypothesis package is realizable at every horizon.**
For any quorum-sized `T` and any horizon `N`, some universe authored
entirely by `T` has `T` filling every round to `N` and synchronised
from round 0 — the good-period scenario is jointly satisfiable, not
only witnessed in the pinned finite tables. `T`-only authorship is what
earns the `q ≤ T.card` premise: a smaller `T` cannot validly populate
any round past genesis. -/
def HypothesesRealizable : Prop :=
  ∀ (Replica : Type) [Fintype Replica] [DecidableEq Replica]
    [LeanDag.Hydrozoan.Faults Replica] (T : Finset Replica) (N : ℕ),
    q Replica ≤ T.card →                   -- a quorum-sized T:
    ∃ U : BlockUniverse Replica ℕ,         -- some universe is
      (∀ b ∈ U.ids, (U.block b).creator ∈ T) ∧  -- authored by T alone,
      (∀ r, r ≤ N → PopulatedOn U T r) ∧   -- populated to the horizon
      SynchronisedOn U T 0                 -- and synchronised throughout.

/-- **Grounded progress.** Under wave-aligned round-robin, past every
slot some bound is committed with every slot below it decided, on any
view caught up to the decision round — satisfiability, not a claim
about which rule reaches the verdict. The bound itself must commit; an
all-skip universe does not qualify. -/
def GroundedProgress : Prop :=
  ∀ (n : ℕ) (hn : 0 < n) [Faults (Fin n)],
    ∀ k : ℕ, ∃ b, k ≤ b ∧                     -- past any slot k,
      ∃ U : BlockUniverse (Fin n) ℕ,          -- some universe commits b:
        ∀ V : View U,                         -- on any view caught up to
          V.CoversUpto (b + 4) →              -- ... the decision round,
        (∃ L, Decided (S := waveRobin n hn) U V b (some L)) ∧
        ∀ i, i < b → ∃ v,                     -- with every slot below
          Decided (S := waveRobin n hn) U V i v  -- decided.

/-- Grounding, over every replica count and fault configuration the
model admits. -/
def Statement : Prop :=
  WaveRobinFair ∧ HypothesesRealizable ∧ GroundedProgress

end Grounding
end Hydrozoan

end LeanDag
