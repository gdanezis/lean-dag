import LeanDag.MahiMahi.Helpers.Counting
import LeanDag.MahiMahi.Model.Unpredictable
import LeanDag.Mysticeti.Quantitative
import LeanDag.MahiMahi.Helpers.Decision
/-!
# Helpers — partial synchrony

Generated lemma infrastructure for `Synchrony/Statement.lean`; not part
of the audit surface. Coverage at one round places a reliable candidate
in every cone two rounds up and above, and the counting helpers turn
that into a direct commit.
-/

namespace LeanDag

namespace MahiMahi

variable {Validator : Type} [Fintype Validator] [DecidableEq Validator]
variable [F : Faults Validator]
variable {BlockId : Type} [LinearOrder BlockId] {Payload : Type}
variable {U : BlockUniverse Validator BlockId Payload}

omit [LinearOrder BlockId] in
/-- Under coverage at round `r`, every block at round `≥ r + 2` reaches a
reliable round-`r` block: its reference quorum meets `T` in a correct
validator, whose unique round-`(r+1)` block references the candidate. -/
theorem reaches_of_synchronisedOn {T : Finset Validator} {R r : ℕ} {L : BlockId}
    (hT : T ⊆ (Correct : Finset Validator)) (hcard : quorumCard Validator ≤ T.card)
    (hs : SynchronisedOn U T R) (hRr : R ≤ r) (hpop1 : PopulatedOn U T (r + 1))
    (hL : L ∈ U.ids) (hLr : (U.block L).round = r) (hLc : (U.block L).creator ∈ T) :
    ∀ c ∈ U.ids, r + 2 ≤ (U.block c).round → Reaches U c L := by
  have hbase : ∀ c ∈ U.ids, (U.block c).round = r + 2 → ∃ b, b = L ∧ Reaches U c b := by
    intro c hc hcr
    have hTq : ∀ v ∈ T, ∃ q ∈ U.ids, (U.block q).round = r + 1 ∧ L ∈ (U.block q).refs ∧
        (U.block q).creator = v := by
      intro v hv
      obtain ⟨q, hq, hqc, hqr⟩ := hpop1 v hv
      exact ⟨q, hq, hqr, hs r hRr q hq hqr (hqc ▸ hv) L hL hLr hLc, hqc⟩
    have hfcard : F.f + 1 ≤ T.card := by
      have := F.card_validators
      omega
    obtain ⟨q, hq, hqL⟩ := exists_mem_refs_of_honest_support_of_card
      (Q := fun q => L ∈ (U.block q).refs) hTq (fun v hv => hT hv)
      (lt_card_add_quorumCard hfcard) hc hcr
    exact ⟨L, rfl, Reaches.trans (Reaches.single hq) (Reaches.single hqL)⟩
  intro c hc hcr
  obtain ⟨b, rfl, h⟩ := reaches_pred_of_round_le (N := r + 2) hbase hc hcr
  exact h

omit [LinearOrder BlockId] in
/-- `reaches_of_synchronisedOn` with coverage cut down to the one layer
it reads: every reliable block one round up references the candidate.
The rest is quorum intersection, as before. -/
theorem reaches_of_votes {T : Finset Validator} {r : ℕ} {L : BlockId}
    (hT : T ⊆ (Correct : Finset Validator)) (hcard : quorumCard Validator ≤ T.card)
    (hpop1 : PopulatedOn U T (r + 1))
    (hL : L ∈ U.ids) (hLr : (U.block L).round = r) (hLc : (U.block L).creator ∈ T)
    (hvotes : ∀ q ∈ U.ids, (U.block q).round = r + 1 → (U.block q).creator ∈ T →
      L ∈ (U.block q).refs) :
    ∀ c ∈ U.ids, r + 2 ≤ (U.block c).round → Reaches U c L := by
  have hbase : ∀ c ∈ U.ids, (U.block c).round = r + 2 → ∃ b, b = L ∧ Reaches U c b := by
    intro c hc hcr
    have hTq : ∀ v ∈ T, ∃ q ∈ U.ids, (U.block q).round = r + 1 ∧ L ∈ (U.block q).refs ∧
        (U.block q).creator = v := by
      intro v hv
      obtain ⟨q, hq, hqc, hqr⟩ := hpop1 v hv
      exact ⟨q, hq, hqr, hvotes q hq hqr (hqc ▸ hv), hqc⟩
    have hfcard : F.f + 1 ≤ T.card := by
      have := F.card_validators
      omega
    obtain ⟨q, hq, hqL⟩ := exists_mem_refs_of_honest_support_of_card
      (Q := fun q => L ∈ (U.block q).refs) hTq (fun v hv => hT hv)
      (lt_card_add_quorumCard hfcard) hc hcr
    exact ⟨L, rfl, Reaches.trans (Reaches.single hq) (Reaches.single hqL)⟩
  intro c hc hcr
  obtain ⟨b, rfl, h⟩ := reaches_pred_of_round_le (N := r + 2) hbase hc hcr
  exact h

section Slots

variable [S : Slots Validator]

/-- **MM5a.** -/
theorem good_of_synchronisedOn {w : ℕ} {T : Finset Validator} {R k : ℕ} (hw : 4 ≤ w)
    (hT : T ⊆ (Correct : Finset Validator)) (hcard : quorumCard Validator ≤ T.card)
    (hs : SynchronisedOn U T R) (hR : R ≤ S.slotRound k)
    (hpop0 : PopulatedOn U T (S.slotRound k)) (hpop1 : PopulatedOn U T (S.slotRound k + 1))
    (hpopd : PopulatedOn U T ((mahiMahiAnchored Validator BlockId Payload w).decisionRound k))
    (hlead : S.leader k ∈ T) : S.leader k ∈ good U w k := by
  obtain ⟨L, hL, hLc, hLr⟩ := hpop0 (S.leader k) hlead
  unfold good
  rw [mem_goodAt]
  refine ⟨L, hL, hLr, hLc, ?_⟩
  rw [mahiMahiAnchored_decisionRound (by omega)] at hpopd
  refine directCommit_of_voting_reach (by omega) hcard hpopd hL (hT (hLc ▸ hlead)) ?_
  intro q hq hqr
  refine reaches_of_synchronisedOn hT hcard hs hR hpop1 hL hLr (hLc ▸ hlead) q hq ?_
  unfold votingRound at hqr
  omega

/-- **MM5b.** -/
theorem unpredictableWithin_of_synchronisedOn {w : ℕ} {T : Finset Validator} {c N : ℕ}
    (hw : 4 ≤ w) (hT : T ⊆ (Correct : Finset Validator)) (hcard : quorumCard Validator ≤ T.card)
    (hs : SynchronisedOn U T 0) (hpop : ∀ n, n ≤ N → PopulatedOn U T n)
    (fair : FairWithin T c) : UnpredictableWithin U w c N := by
  intro k hk
  obtain ⟨k', hk1, hk2, hlead⟩ := fair k
  refine ⟨k', hk1, hk2, ?_⟩
  have hmono : S.slotRound k' ≤ S.slotRound (k + c) := S.mono (by omega)
  have hd : (mahiMahiAnchored Validator BlockId Payload w).decisionRound k' ≤ N := by
    unfold AnchoredRule.decisionRound at hk ⊢
    simp only [mahiMahiAnchored_wave] at hk ⊢
    omega
  refine good_of_synchronisedOn hw hT hcard hs (Nat.zero_le _) ?_ ?_ (hpop _ hd) hlead
  · exact hpop _ (by unfold AnchoredRule.decisionRound at hd; simp only [mahiMahiAnchored_wave] at hd; omega)
  · exact hpop _ (by unfold AnchoredRule.decisionRound at hd; simp only [mahiMahiAnchored_wave] at hd; omega)

end Slots

end MahiMahi

end LeanDag
