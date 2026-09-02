import LeanDag.Integration.Hydrozoan.Stack
import LeanDag.Integration.Coverage
import LeanDag.Hydrozoan.DirectLiveness.Proof
import LeanDag.Hydrozoan.IndirectLiveness.Proof

/-!
# The liveness package across the transformers

`docs/hydrozoan-integration.md` §5.2. Everything before this file is
verdict invariance — safety-flavoured. This one carries Hydrozoan's
liveness hypotheses, `PopulatedOn` and `SynchronisedOn`, across the
truncation and the fill, which is what the liveness theorems consume.

**The two packages are one.** `Model/Liveness.lean`'s `SynchronisedOn`
and the core's `SynchronisedFrom` are the same quantifier over the same
data, so through the adapter they are one proposition and the bridge is
`Iff.rfl`. `PopulatedOn` differs only in the order of a conjunction.
That is why nothing here re-renders synchrony: it is `hydrozoan.md` §7's
package throughout, moved rather than restated.

**What the two transformers do to it, and it is not the same thing.**
Truncation preserves both, at the horizon offset — coverage because it
constrains a block at the round above the cut, which the cut retains
(`integration.md` I2's reason, unchanged here). The fill preserves
production *across the gap*, with the recovering replica back in the
set (SS2), and coverage only *strictly above* itself (I4): no block
built during the outage references an identifier that did not then
exist, so a set containing the recovering replica is not covered at its
gap rounds. §5.2 records that division; this file is it, for Hydrozoan.
-/

namespace LeanDag

namespace Integration

namespace Hydrozoan

variable {Replica : Type} [Fintype Replica] [DecidableEq Replica]
variable {BlockId : Type} [DecidableEq BlockId]
variable [F : LeanDag.Hydrozoan.Faults Replica]
  [Fact (LeanDag.Hydrozoan.Faults.c Replica ≤ LeanDag.Hydrozoan.Faults.k Replica)]
variable {U : LeanDag.Hydrozoan.BlockUniverse Replica BlockId}
  {hsp : SelfParenting U} {T : Finset Replica}

/-! ## The two packages are one -/

/-- Coverage is the same proposition either side of the transport: the
core's `SynchronisedFrom` is Hydrozoan's `SynchronisedOn`, over the same
identifiers and the same references. -/
theorem synchronisedOn_ofCore {Payload : Type}
    {W : LeanDag.BlockUniverse Replica BlockId Payload} (hne : HonestNoEquiv W)
    (T : Finset Replica) (R : ℕ) :
    LeanDag.Hydrozoan.SynchronisedOn (ofCore W hne) T R
      ↔ LeanDag.SynchronisedOn W T R := Iff.rfl

/-- Production differs only in the order of a conjunction. -/
theorem populatedOn_ofCore {Payload : Type}
    {W : LeanDag.BlockUniverse Replica BlockId Payload} (hne : HonestNoEquiv W)
    (T : Finset Replica) (r : ℕ) :
    LeanDag.Hydrozoan.PopulatedOn (ofCore W hne) T r
      ↔ LeanDag.PopulatedOn W T r := by
  constructor
  · intro h v hv; obtain ⟨b, hb, hr, hc⟩ := h v hv; exact ⟨b, hb, hc, hr⟩
  · intro h v hv; obtain ⟨b, hb, hc, hr⟩ := h v hv; exact ⟨b, hb, hr, hc⟩

theorem synchronisedOn_toCore (hsp : SelfParenting U) (T : Finset Replica) (R : ℕ) :
    LeanDag.SynchronisedOn (toCore U hsp) T R
      ↔ LeanDag.Hydrozoan.SynchronisedOn U T R := Iff.rfl

theorem populatedOn_toCore (hsp : SelfParenting U) (T : Finset Replica) (r : ℕ) :
    LeanDag.PopulatedOn (toCore U hsp) T r
      ↔ LeanDag.Hydrozoan.PopulatedOn U T r :=
  (populatedOn_ofCore (honestNoEquiv_toCore U hsp) T r).symm

/-! ## Truncation preserves both, at the horizon offset -/

/-- **Production survives the cut**, at the rebased round. A block
retained by the horizon keeps its author, and its round moves down by
the cut. -/
theorem populatedOn_chopHZ {r G : ℕ} (h : LeanDag.Hydrozoan.PopulatedOn U T r)
    (hG : G ≤ r) :
    LeanDag.Hydrozoan.PopulatedOn (chopHZ U hsp G) T (r - G) := by
  intro v hv
  obtain ⟨b, hb, hbr, hbc⟩ := h v hv
  exact ⟨b, mem_chopHZ_ids.mpr ⟨hb, by omega⟩,
    by rw [chopHZ_round]; omega, by rw [chopHZ_author]; exact hbc⟩

/-- **Coverage survives the cut**, needing only the horizon offset —
`integration.md` I2, which holds because the clause constrains a block
at the round above the cut, and the cut retains its references. -/
theorem synchronisedOn_chopHZ {R R' G : ℕ}
    (hs : LeanDag.Hydrozoan.SynchronisedOn U T R) (hGR : R ≤ G + R') :
    LeanDag.Hydrozoan.SynchronisedOn (chopHZ U hsp G) T R' :=
  synchronisedOn_chop ((synchronisedOn_toCore hsp T R).mpr hs) hGR

/-! ## The fill restores production, and covers only above itself -/

variable {sk : SkipMsg (toCore U hsp)}

/-- **The gap is populated, with the recovering replica back in the
set** — SS2, which is what liveness consumes and what the mechanism
exists to supply. -/
theorem populatedOn_skipFillHZ {k : ℕ}
    (hpop : LeanDag.Hydrozoan.PopulatedOn U T k) (hk1 : sk.r0 < k) (hk2 : k ≤ sk.r) :
    LeanDag.Hydrozoan.PopulatedOn (skipFillHZ U hsp sk) (insert sk.v1 T) k := by
  intro v hv
  obtain ⟨b, hb, hc, hr⟩ :=
    sk.skipFill_populatedOn ((populatedOn_toCore hsp T k).mpr hpop) hk1 hk2 v hv
  exact ⟨b, hb, hr, hc⟩

/-- **Coverage returns strictly above the fill** — `integration.md` I4's
positive case. The strictness is not slack: at the target round the
block below may still be the last filled one. -/
theorem synchronisedOn_skipFillHZ_above {R R' : ℕ}
    (hs : LeanDag.Hydrozoan.SynchronisedOn U T R) (hR : R ≤ R') (hR' : sk.r < R') :
    LeanDag.Hydrozoan.SynchronisedOn (skipFillHZ U hsp sk) T R' :=
  synchronisedOn_skipFill_above sk ((synchronisedOn_toCore hsp T R).mpr hs) hR hR'

/-- **And for a set excluding the recovering replica it survives
outright** — the filled blocks are that replica's alone, so a clause
quantified over the others never meets them. -/
theorem synchronisedOn_skipFillHZ_of_notMem {R : ℕ}
    (hs : LeanDag.Hydrozoan.SynchronisedOn U T R) (hv1 : sk.v1 ∉ T) :
    LeanDag.Hydrozoan.SynchronisedOn (skipFillHZ U hsp sk) T R :=
  synchronisedOn_skipFill_of_notMem sk ((synchronisedOn_toCore hsp T R).mpr hs) hv1

/-! ## The stack

Both transformers at once, in the deployment order. Coverage needs a
window strictly above the fill and then offset by the horizon; production
needs only the horizon. -/

/-- **The stack is covered**, from a round above the fill, rebased. -/
theorem synchronisedOn_stackHZ {R R' R'' G : ℕ}
    (hs : LeanDag.Hydrozoan.SynchronisedOn U T R) (hR : R ≤ R') (hR' : sk.r < R')
    (hGR : R' ≤ G + R'') :
    LeanDag.Hydrozoan.SynchronisedOn (stackHZ U hsp sk G) T R'' :=
  synchronisedOn_chopHZ (synchronisedOn_skipFillHZ_above hs hR hR') hGR

/-- **The stack is populated across the gap**, with the recovered
replica counted, at the rebased round. -/
theorem populatedOn_stackHZ {k G : ℕ}
    (hpop : LeanDag.Hydrozoan.PopulatedOn U T k) (hk1 : sk.r0 < k) (hk2 : k ≤ sk.r)
    (hG : G ≤ k) :
    LeanDag.Hydrozoan.PopulatedOn (stackHZ U hsp sk G) (insert sk.v1 T) (k - G) :=
  populatedOn_chopHZ (populatedOn_skipFillHZ hpop hk1 hk2) hG

/-! ## The payoff

Hydrozoan's direct-liveness theorem is quantified over every universe,
so it holds of the stack without restatement. What was missing, and what
this file supplies, is that its *hypotheses* survive the transformers:
`SynchronisedOn` above the fill and rebased by the horizon,
`PopulatedOn` across the gap with the recovered replica counted. Neither
was available before, so nothing about progress could be said of a
recovered and pruned replica — only that it could not disagree. -/

/-- **HZ5 applies to the stack.** Its content here is the hypotheses,
which the theorems above transport. -/
theorem commitLiveness_stackHZ [LinearOrder BlockId]
    [LeanDag.Hydrozoan.Slots Replica] {G : ℕ} :
    LeanDag.Hydrozoan.DirectLiveness.CommitLiveness (stackHZ U hsp sk G) :=
  LeanDag.Hydrozoan.DirectLiveness.holds Replica BlockId _

/-- **HZ6's descent applies too**, so a run of committed slots on the
stack decides everything below it. -/
theorem anchoredTotality_stackHZ [LinearOrder BlockId]
    [LeanDag.Hydrozoan.Slots Replica] {G : ℕ} :
    LeanDag.Hydrozoan.IndirectLiveness.AnchoredTotality (stackHZ U hsp sk G) :=
  (LeanDag.Hydrozoan.IndirectLiveness.holds Replica BlockId _).1

end Hydrozoan

end Integration

end LeanDag
