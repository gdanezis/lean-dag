import LeanDag.Barnacle.MysticetiLive.Statement
import LeanDag.Barnacle.Odontoceti.Statement
import LeanDag.Barnacle.Nemo.Statement
import LeanDag.Common.Persistence
/-!
# Barnacle helpers — the delivery law

Not part of the audit surface. `LiveRule.Delivers` for the three rules.
The argument is the core's, and one lemma serves the two Byzantine rules
because their `Good` is the same predicate: coverage makes every reliable
validator's round-`(r+1)` block reference a reliable round-`r` block, so
that block carries a quorum of support and T3 (`reaches_of_quorum_support`)
puts it in the history of everything two rounds up.

**Nemo-Nemo is not here.** Its persistence lemmas
(`reaches_of_honest_support`, `…_of_card`) conclude from a block at
*exactly* two rounds above, where the core's T3 concludes from every
block at two rounds or more. Closing the gap needs a descent — a block at
round `r + k` reaches one at `r + 2` — which the crash arc does not
carry. The law is stated for every live rule and BN14 consumes only the
law, so the crash rule joins by proving that descent and nothing else.
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

/-- **Mysticeti delivers**, at slack `f`. -/
theorem mysticetiLive_delivers [F : Faults Validator] :
    (mysticetiLive (Validator := Validator) (BlockId := BlockId)
      (Payload := Payload)).Delivers F.f where
  reaches := by
    intro U Rnd N hgood
    obtain ⟨T, -, hcard, hsync, hpop⟩ := hgood
    refine ⟨T, by omega, ?_⟩
    intro b hb hbT hRnd hN c hc hcr
    exact mem_history_of_good hcard hsync hRnd (hpop _ (by omega) hN) hb rfl hbT hc hcr

/-- **Odontoceti delivers**, at slack `f`; the argument is the same, its
`Good` being the same predicate. Its block identifiers carry an order, so
the binders are restated rather than taken from the section. -/
theorem odontocetiLive_delivers {Validator : Type} [Fintype Validator] [DecidableEq Validator]
    [F : Faults5 Validator] {BlockId : Type} [LinearOrder BlockId] {Payload : Type} :
    (odontocetiLive (Validator := Validator) (BlockId := BlockId)
      (Payload := Payload)).Delivers F.f where
  reaches := by
    intro U Rnd N hgood
    obtain ⟨T, -, hcard, hsync, hpop⟩ := hgood
    refine ⟨T, by omega, ?_⟩
    intro b hb hbT hRnd hN c hc hcr
    exact mem_history_of_good hcard hsync hRnd (hpop _ (by omega) hN) hb rfl hbT hc hcr

end Barnacle

end LeanDag
