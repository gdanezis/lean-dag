import LeanDag.MahiMahi.Model.Good
import LeanDag.MahiMahi.Helpers.Rules
import LeanDag.Common.CommonCore
import LeanDag.Mysticeti.Liveness
/-!
# Helpers — the counting layer

Generated lemma infrastructure for `Counting/Statement.lean`; not part of
the audit surface. The common core is the core's T3c carried upward;
reaching a correct block is voting for it; a decision-round block whose
references all reach a correct candidate certifies it; and a reliable set
at the decision round then commits it. The two bounds and the
multi-leader corollary are counting over these.
-/

namespace LeanDag

namespace MahiMahi

variable {Validator : Type*} [Fintype Validator] [DecidableEq Validator]
variable [F : Faults Validator]
variable {BlockId : Type*} [LinearOrder BlockId] {Payload : Type*}
variable {U : BlockUniverse Validator BlockId Payload}

theorem mem_goodAt {w r : ℕ} {v : Validator} :
    v ∈ goodAt U w r ↔ ∃ L ∈ U.ids,
      (U.block L).round = r ∧ (U.block L).creator = v ∧ DirectCommit U w L r := by
  simp [goodAt]

omit [LinearOrder BlockId] in
/-- The core's common correct ancestor (T3c), carried to every round
`≥ r + 2` through references. -/
theorem exists_commonCore {r : ℕ} {c₀ : BlockId}
    (hc₀ : c₀ ∈ U.ids) (hc₀r : (U.block c₀).round = r + 2) :
    ∃ b ∈ U.ids, (U.block b).round = r ∧ (U.block b).creator ∈ (Correct : Finset Validator) ∧
      ∀ c ∈ U.ids, r + 2 ≤ (U.block c).round → Reaches U c b := by
  obtain ⟨b, hb, hbr, hbc, hreach⟩ := exists_common_correct_ancestor hc₀ hc₀r
  refine ⟨b, hb, hbr, hbc, fun c hc hcr => ?_⟩
  obtain ⟨b', rfl, hreach'⟩ := reaches_pred_of_round_le (U := U) (Q := fun x => x = b) (N := r + 2)
    (fun c' hc' hc'r => ⟨b, rfl, hreach c' hc' hc'r⟩) hc hcr
  exact hreach'

/-- Reaching a correct block is voting for it: it is in the cone, and no
other block of that author and round exists to be smaller. -/
theorem votes_of_reaches {q L : BlockId} (hq : q ∈ U.ids) (hL : L ∈ U.ids)
    (hLc : (U.block L).creator ∈ (Correct : Finset Validator)) (h : Reaches U q L) :
    Votes U q L := by
  refine ⟨mem_candidatesAt.mpr ⟨hL, rfl, rfl, (mem_history_iff hq).mpr h⟩, ?_⟩
  intro L' hL' hlt
  obtain ⟨hL'ids, hL'r, hL'c, -⟩ := mem_candidatesAt.mp hL'
  have := U.eq_of_creator_eq hL'ids hL hLc hL'c rfl hL'r
  subst this
  exact lt_irrefl _ hlt

/-- A decision-round block all of whose references reach a correct
candidate certifies it: every reference votes, and the references are a
quorum. -/
theorem certifies_of_refs_reach {w r : ℕ} {C L : BlockId} (hw : 2 ≤ w)
    (hC : C ∈ U.ids) (hCr : (U.block C).round = decisionRoundAt w r)
    (hL : L ∈ U.ids) (hLc : (U.block L).creator ∈ (Correct : Finset Validator))
    (hall : ∀ q ∈ (U.block C).refs, Reaches U q L) : Certifies U C L := by
  have heq : votesIn U C L = (U.block C).refs := by
    apply Finset.filter_true_of_mem
    intro q hq
    exact votes_of_reaches (U.complete C hC q hq) hL hLc (hall q hq)
  unfold Certifies
  rw [heq]
  exact U.creators_quorum hC (by unfold decisionRoundAt at hCr; omega)

/-- If every voting-round block reaches a correct candidate, and a quorum
populates the decision round, the candidate is directly committed. -/
theorem directCommit_of_voting_reach {w r : ℕ} {L : BlockId} {T : Finset Validator}
    (hw : 2 ≤ w) (hcard : quorumCard Validator ≤ T.card)
    (hpop : PopulatedOn U T (decisionRoundAt w r))
    (hL : L ∈ U.ids) (hLc : (U.block L).creator ∈ (Correct : Finset Validator))
    (hreach : ∀ q ∈ U.ids, (U.block q).round = votingRound w r → Reaches U q L) :
    DirectCommit U w L r := by
  unfold DirectCommit
  refine le_trans hcard (Finset.card_le_card ?_)
  intro v hv
  obtain ⟨C, hC, hCc, hCr⟩ := hpop v hv
  rw [mem_creatorsOf]
  refine ⟨C, mem_certificates.mpr ⟨hC, hCr, ?_⟩, hCc⟩
  refine certifies_of_refs_reach hw hC hCr hL hLc ?_
  intro q hq
  have hqids := U.complete C hC q hq
  have hqr := U.round_of_mem_refs hC hq
  refine hreach q hqids ?_
  rw [decisionRoundAt_eq_votingRound_succ hw] at hCr
  omega

/-- A reliable quorum is nonempty. -/
theorem nonempty_of_quorum {T : Finset Validator} (hcard : quorumCard Validator ≤ T.card) :
    T.Nonempty := by
  rw [← Finset.card_pos]
  have := F.card_validators
  omega

/-- **MM2 at `w ≥ 4`.** -/
theorem goodNonempty {w : ℕ} {T : Finset Validator} {r : ℕ} (hw : 4 ≤ w)
    (hcard : quorumCard Validator ≤ T.card)
    (hpop2 : PopulatedOn U T (r + 2)) (hpopd : PopulatedOn U T (decisionRoundAt w r)) :
    (goodAt U w r ∩ (Correct : Finset Validator)).Nonempty := by
  obtain ⟨v₀, hv₀⟩ := nonempty_of_quorum hcard
  obtain ⟨c₀, hc₀, -, hc₀r⟩ := hpop2 v₀ hv₀
  obtain ⟨b, hb, hbr, hbc, hreach⟩ := exists_commonCore hc₀ hc₀r
  refine ⟨(U.block b).creator, Finset.mem_inter.mpr ⟨?_, hbc⟩⟩
  rw [mem_goodAt]
  refine ⟨b, hb, hbr, rfl, ?_⟩
  refine directCommit_of_voting_reach (by omega) hcard hpopd hb hbc ?_
  intro q hq hqr
  refine hreach q hq ?_
  unfold votingRound at hqr
  omega

/-- **MM2 at `w ≥ 5`.** -/
theorem goodCard {w : ℕ} {T : Finset Validator} {r : ℕ} (hw : 5 ≤ w)
    (hcard : quorumCard Validator ≤ T.card)
    (hpop3 : PopulatedOn U T (r + 3)) (hpopd : PopulatedOn U T (decisionRoundAt w r)) :
    quorumCard Validator ≤
      (goodAt U w r ∩ (Correct : Finset Validator)).card + F.byzantine.card := by
  obtain ⟨v₀, hv₀⟩ := nonempty_of_quorum hcard
  obtain ⟨c₀, hc₀, -, hc₀r⟩ := hpop3 v₀ hv₀
  obtain ⟨b', hb', hb'r, -, hreach⟩ :=
    exists_commonCore (r := r + 1) hc₀ (by omega)
  have hq : quorumCard Validator ≤ (creatorsOf U.block (U.block b').refs).card :=
    U.creators_quorum hb' (by omega)
  have hsub : creatorsOf U.block (U.block b').refs ∩ (Correct : Finset Validator) ⊆
      goodAt U w r ∩ (Correct : Finset Validator) := by
    intro v hv
    rw [Finset.mem_inter, mem_creatorsOf] at hv
    obtain ⟨⟨L, hLrefs, hLc⟩, hvc⟩ := hv
    have hL := U.complete b' hb' L hLrefs
    have hLr : (U.block L).round = r := by
      have := U.round_of_mem_refs hb' hLrefs
      omega
    have hLcorr : (U.block L).creator ∈ (Correct : Finset Validator) := by
      rw [hLc]; exact hvc
    refine Finset.mem_inter.mpr ⟨?_, hvc⟩
    rw [mem_goodAt]
    refine ⟨L, hL, hLr, hLc, ?_⟩
    refine directCommit_of_voting_reach (by omega) hcard hpopd hL hLcorr ?_
    intro q hq hqr
    have h1 : Reaches U q b' := hreach q hq (by unfold votingRound at hqr; omega)
    exact Reaches.trans h1 (Reaches.single hLrefs)
  calc quorumCard Validator
      ≤ (creatorsOf U.block (U.block b').refs).card := hq
    _ ≤ (creatorsOf U.block (U.block b').refs ∩ (Correct : Finset Validator)).card
          + F.byzantine.card := card_le_card_inter_correct_add_byzantine _
    _ ≤ (goodAt U w r ∩ (Correct : Finset Validator)).card + F.byzantine.card :=
          Nat.add_le_add_right (Finset.card_le_card hsub) _

/-- **MM2b.** `f + 1` good correct validators and `2f + 1` leaders cannot
be disjoint in `3f + 1`. -/
theorem multiLeader [S : Slots Validator] {w : ℕ} {T : Finset Validator} {r : ℕ} (hw : 5 ≤ w)
    (hcard : quorumCard Validator ≤ T.card)
    (hpop3 : PopulatedOn U T (r + 3)) (hpopd : PopulatedOn U T (decisionRoundAt w r))
    {M : Finset Validator} (hM : ∀ v ∈ M, ∃ k, S.slotRound k = r ∧ S.leader k = v)
    (hMcard : 2 * F.f + 1 ≤ M.card) :
    ∃ k, S.slotRound k = r ∧ S.leader k ∈ good U w k := by
  have hg := goodCard hw hcard hpop3 hpopd
  have hne : (M ∩ (goodAt U w r ∩ (Correct : Finset Validator))).Nonempty := by
    rw [← Finset.card_pos]
    have h1 := Finset.card_union_add_card_inter M (goodAt U w r ∩ (Correct : Finset Validator))
    have h2 : (M ∪ (goodAt U w r ∩ (Correct : Finset Validator))).card ≤ Fintype.card Validator :=
      Finset.card_le_univ _
    have h3 := F.card_byzantine
    have h4 := F.card_validators
    omega
  obtain ⟨v, hv⟩ := hne
  rw [Finset.mem_inter] at hv
  obtain ⟨k, hk, hkv⟩ := hM v hv.1
  refine ⟨k, hk, ?_⟩
  unfold good
  rw [hk, hkv]
  exact (Finset.mem_inter.mp hv.2).1

end MahiMahi

end LeanDag
