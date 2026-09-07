import LeanDag.Barnacle.Model.Anchored
import LeanDag.Common.Persistence
import LeanDag.Mysticeti.Liveness
/-!
# Barnacle helpers — the delivery law

Not part of the audit surface. `LiveRule.Delivers` for every anchored
rule over the block universe at the core's fault model: coverage gives a
reliable block a quorum of supporters one round up, and T3
(`reaches_of_quorum_support`) puts it in the history of everything two
rounds up. Nemo is not covered: its persistence lemmas conclude from a
block exactly two rounds above, and the descent that would close the gap
is not in the crash arc.
-/

namespace LeanDag

namespace Barnacle

variable {Validator : Type} [Fintype Validator] [DecidableEq Validator]
variable {BlockId : Type} [DecidableEq BlockId] {Payload : Type}

/-- **A reliable block is reached from two rounds up.** Coverage gives it
a quorum of supporters one round above, and persistence carries it. -/
theorem mem_history_of_good [Faults Validator]
    {U : BlockUniverse Validator BlockId Payload} {T : Finset Validator} {Rnd r : ℕ}
    (hcard : quorumCard Validator ≤ T.card) (hs : SynchronisedOn U T Rnd) (hR : Rnd ≤ r)
    (hpop1 : PopulatedOn U T (r + 1)) {L : BlockId} (hL : L ∈ U.ids)
    (hLr : (U.block L).round = r) (hLc : (U.block L).creator ∈ T)
    {c : BlockId} (hc : c ∈ U.ids) (hcr : r + 2 ≤ (U.block c).round) :
    L ∈ historyFrom U.block c := by
  have hvotes : VotesAt U T r L := votesAt_of_synchronisedOn hs hR hL hLr hLc
  set Q : Finset BlockId := (blocksAt U (r + 1)).filter (fun q => L ∈ (U.block q).refs) with hQ
  have hQids : Q ⊆ U.ids := by
    intro q hq; rw [hQ, Finset.mem_filter, mem_blocksAt] at hq; exact hq.1.1
  have hQround : ∀ q ∈ Q, (U.block q).round = r + 1 := by
    intro q hq; rw [hQ, Finset.mem_filter, mem_blocksAt] at hq; exact hq.1.2
  have hQref : ∀ q ∈ Q, L ∈ (U.block q).refs := by
    intro q hq; rw [hQ, Finset.mem_filter] at hq; exact hq.2
  have hQsub : T ⊆ creatorsOf U.block Q := by
    intro v hv
    obtain ⟨q, hq, hqc, hqr⟩ := hpop1 v hv
    refine mem_creatorsOf.2 ⟨q, ?_, hqc⟩
    rw [hQ, Finset.mem_filter, mem_blocksAt]
    exact ⟨⟨hq, hqr⟩, hvotes v hv q hq hqc hqr⟩
  have hQcard : quorumCard Validator ≤ (creatorsOf U.block Q).card :=
    le_trans hcard (Finset.card_le_card hQsub)
  exact (mem_history_iff hc).mpr
    (reaches_of_quorum_support hQids hQround hQref hQcard hc hcr)

/-- **Every core rule delivers**, at slack `f`. -/
theorem delivers_core [F : Faults Validator]
    (R : AnchoredRule Validator BlockId Payload ValidWrt (Correct : Finset Validator)) :
    (liveOfAnchored R (coreReliability Validator)).Delivers F.f where
  reaches := by
    rintro U Rnd N ⟨T, ⟨-, hcard⟩, hsync, hpop⟩
    change Fintype.card Validator - F.f ≤ T.card at hcard
    refine ⟨T, by omega, ?_⟩
    intro b hb hbT hRnd hN c hc hcr
    exact mem_history_of_good hcard hsync hRnd (hpop _ (by omega) hN) hb rfl hbT hc hcr

end Barnacle

end LeanDag
