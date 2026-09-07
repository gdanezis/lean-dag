import LeanDag.Hydrozoan.Model.Decided
import LeanDag.Hydrozoan.Helpers.Counting
import LeanDag.Common.CausalHistory
import LeanDag.Hydrozoan.Helpers.DirectRules
import LeanDag.Hydrozoan.Helpers.IndirectRules
/-!
# The seam toolkit

Generated proof infrastructure for `SlotAgreement`: the "rung fires"
lemmas (an eligible anchor's history contains the evidence of any direct
commit), the starvation and skip negatives (nothing conflicting survives
on either rung), and the abstract anchor-comparison lemma. Nothing here
is part of the audit surface.
-/

namespace LeanDag

namespace Hydrozoan

variable {Replica BlockId : Type*} [Fintype Replica] [DecidableEq Replica]
  [DecidableEq BlockId] [F : LeanDag.Hydrozoan.Faults Replica]
  {U : BlockUniverse Replica BlockId}

/-! ## Arithmetic feeders -/

/-- `n + f < q + q_slow` — an anchor's refs meet any slow commit
(Phase 2's row 5). Standalone this is an identity of truncated ℕ
arithmetic (both sides of `q + q_slow` sum to `n + f + 1`); its content
materializes in consumers where `q` also bounds a real creator-set
cardinality. Same for the starvation row below. -/
theorem nf_lt_q_add_qSlow :
    Fintype.card Replica + F.f < q Replica + qSlow Replica := by
  have := F.card_replicas
  simp only [q, qSlow]
  omega

/-- `n + f < q_fast + q_weak` — a fast commit starves conflicts below
the weak rung (Phase 2's row 3). -/
theorem nf_lt_qFast_add_qWeak :
    Fintype.card Replica + F.f < qFast Replica + qWeak Replica := by
  have := F.card_replicas
  simp only [qFast, qWeak, p]
  omega

/-- The **strengthened** footprint row: `n + q_weak + f ≤ q_fast + q`.
Only the non-Byzantine overlap of an anchor's parent creators with the
fast quorum contributes anchor-linked votes — a Byzantine creator's
reachable block may be its non-voting equivocation — so the design
note's `q_fast + q − n ≥ q_weak` must absorb an extra `f`. Still holds
at every `k ≥ 0`; tight at the tight replica count when `c + k` is even
(odd `c + k` leaves one unit of slack). -/
theorem n_add_qWeak_add_f_le_qFast_add_q :
    Fintype.card Replica + qWeak Replica + F.f ≤ qFast Replica + q Replica := by
  have := F.card_replicas
  simp only [q, qFast, qWeak, p]
  omega

/-- `1 ≤ q`. -/
theorem q_pos : 1 ≤ q Replica := by
  have := F.card_replicas
  simp only [q]
  omega

/-! ## Structural plumbing -/

omit [DecidableEq BlockId] in
/-- Non-genesis universe blocks have a parent (`q ≥ 1`). -/
theorem refs_nonempty {i : BlockId} (hi : i ∈ U.ids)
    (hr : 0 < (U.block i).round) : (U.block i).refs.Nonempty := by
  by_contra h
  rw [Finset.not_nonempty_iff_eq_empty] at h
  have hq : q Replica ≤ (creatorsOf U.block (U.block i).refs).card :=
    (U.valid i hi).quorum hr
  rw [h] at hq
  simp only [creatorsOf, Finset.image_empty, Finset.card_empty] at hq
  have := q_pos (Replica := Replica)
  omega

/-- A certified-in-reach candidate has a certificate. -/
theorem certificates_nonempty_of_certifiedIn {A L : BlockId} {r : ℕ}
    (h : CertifiedIn U A L r) : (certificates U L r).Nonempty := by
  obtain ⟨C, hC, -⟩ := h
  exact ⟨C, hC⟩

/-- `CertifiedIn` is inherited upward along reachability. -/
theorem certifiedIn_of_reaches {A B L : BlockId} {r : ℕ}
    (hBA : Reaches U B A) (h : CertifiedIn U A L r) : CertifiedIn U B L r := by
  obtain ⟨C, hC, hreach⟩ := h
  exact ⟨C, hC, Reaches.trans hBA hreach⟩

omit [DecidableEq BlockId] in
/-- `WeakLinked` is inherited upward along reachability. -/
theorem weakLinked_of_reaches {A B L : BlockId} {r : ℕ}
    (hBA : Reaches U B A) (h : WeakLinked U A L r) : WeakLinked U B L r := by
  obtain ⟨s, hs, hcard⟩ := h
  exact ⟨s, fun b hb =>
    ⟨(hs b hb).1, (hs b hb).2.1, Reaches.trans hBA (hs b hb).2.2⟩, hcard⟩

/-! ## Rung 1 fires: any eligible anchor reaches a slow commit's
certificate -/

private theorem certifiedIn_of_slowCommit_base {L : BlockId} {r : ℕ}
    (h : SlowCommit U L r) {A : BlockId} (hA : A ∈ U.ids)
    (hAr : (U.block A).round = r + 3) : CertifiedIn U A L r := by
  obtain ⟨C, hC₁, hC₂⟩ :=
    exists_common_block U.noEquivOn_honest card_compl_nonByzantine_le
      (s := (U.block A).refs) (t := certificates U L r) (n := r + 2)
      (fun b hb => ⟨U.complete A hA b hb, by
        have := BlockRecord.round_of_mem_refs hA hb; omega⟩)
      (fun b hb => ⟨(mem_certificates.mp hb).1, (mem_certificates.mp hb).2.1⟩)
      (by
        have hq : q Replica ≤ (creatorsOf U.block (U.block A).refs).card :=
          (U.valid A hA).quorum (by omega)
        have h5 := nf_lt_q_add_qSlow (Replica := Replica)
        simp only [SlowCommit, certifiers] at h
        omega)
  exact ⟨C, hC₂, Reaches.single hC₁⟩

private theorem certifiedIn_of_slowCommit_aux {L : BlockId} {r : ℕ}
    (h : SlowCommit U L r) :
    ∀ d, ∀ A, A ∈ U.ids → (U.block A).round = r + 3 + d →
      CertifiedIn U A L r := by
  intro d
  induction d with
  | zero => exact fun A hA hAr => certifiedIn_of_slowCommit_base h hA hAr
  | succ d ih =>
      intro A hA hAr
      obtain ⟨b, hb⟩ := refs_nonempty hA (by omega)
      have hbi : b ∈ U.ids := U.complete A hA b hb
      have hbr := BlockRecord.round_of_mem_refs hA hb
      exact certifiedIn_of_reaches (Reaches.single hb) (ih b hbi (by omega))

/-- **Rung 1 fires.** A slow commit's certificate lies in the causal
history of every block from round `r + 3` on. -/
theorem certifiedIn_of_slowCommit {L : BlockId} {r : ℕ} (h : SlowCommit U L r)
    {A : BlockId} (hA : A ∈ U.ids) (hAr : r + 3 ≤ (U.block A).round) :
    CertifiedIn U A L r :=
  certifiedIn_of_slowCommit_aux h ((U.block A).round - (r + 3)) A hA (by omega)

/-! ## Rung 2 fires: any eligible anchor sees a fast commit's weak
footprint -/

private theorem weakLinked_of_fastCommit_base {L : BlockId} {r : ℕ}
    (h : FastCommit U L r) {A : BlockId} (hA : A ∈ U.ids)
    (hAr : (U.block A).round = r + 2) : WeakLinked U A L r := by
  refine ⟨(U.block A).refs.filter (fun b => IsVote U b L), ?_, ?_⟩
  · intro b hb
    obtain ⟨hbp, hbv⟩ := Finset.mem_filter.mp hb
    have hbi : b ∈ U.ids := U.complete A hA b hbp
    have hbr := BlockRecord.round_of_mem_refs hA hbp
    exact ⟨mem_blocksAt.mpr ⟨hbi, by omega⟩, hbv, Reaches.single hbp⟩
  · have hsub :
        (creatorsOf U.block (U.block A).refs ∩ supporters U L (r + 1)) \
            F.byzantine ⊆
          creatorsOf U.block
            ((U.block A).refs.filter (fun b => IsVote U b L)) := by
      intro v hv
      obtain ⟨hvin, hvnb⟩ := Finset.mem_sdiff.mp hv
      obtain ⟨hvP, hvS⟩ := Finset.mem_inter.mp hvin
      obtain ⟨p', hp', hpc⟩ := mem_creatorsOf.mp hvP
      obtain ⟨b, hbi, hbr, hbv, hbc⟩ := mem_supporters.mp hvS
      have hpi : p' ∈ U.ids := U.complete A hA p' hp'
      have hpr := BlockRecord.round_of_mem_refs hA hp'
      have hnb : (U.block p').creator ∈ (NonByzantine : Finset Replica) := by
        rw [mem_nonByzantine, hpc]; exact hvnb
      have hpb : p' = b :=
        U.no_equivocation p' hpi b hbi hnb (by rw [hpc, hbc]) (by omega)
      subst hpb
      exact mem_creatorsOf.mpr ⟨p', Finset.mem_filter.mpr ⟨hp', hbv⟩, hpc⟩
    have hcard := Finset.card_le_card hsub
    have hsd := Finset.le_card_sdiff F.byzantine
      (creatorsOf U.block (U.block A).refs ∩ supporters U L (r + 1))
    have hq : q Replica ≤ (creatorsOf U.block (U.block A).refs).card :=
      (U.valid A hA).quorum (by omega)
    have hinter := Finset.card_union_add_card_inter
      (creatorsOf U.block (U.block A).refs) (supporters U L (r + 1))
    have huniv : (creatorsOf U.block (U.block A).refs ∪
        supporters U L (r + 1)).card ≤ Fintype.card Replica := by
      rw [← Finset.card_univ]; exact Finset.card_le_univ _
    have hf := F.card_byzantine
    have h5 := n_add_qWeak_add_f_le_qFast_add_q (Replica := Replica)
    simp only [FastCommit] at h
    omega

private theorem weakLinked_of_fastCommit_aux {L : BlockId} {r : ℕ}
    (h : FastCommit U L r) :
    ∀ d, ∀ A, A ∈ U.ids → (U.block A).round = r + 2 + d →
      WeakLinked U A L r := by
  intro d
  induction d with
  | zero => exact fun A hA hAr => weakLinked_of_fastCommit_base h hA hAr
  | succ d ih =>
      intro A hA hAr
      obtain ⟨b, hb⟩ := refs_nonempty hA (by omega)
      have hbi : b ∈ U.ids := U.complete A hA b hb
      have hbr := BlockRecord.round_of_mem_refs hA hb
      exact weakLinked_of_reaches (Reaches.single hb) (ih b hbi (by omega))

/-- **Rung 2 fires.** A fast commit's weak footprint is visible from
every block at round `r + 2` on. -/
theorem weakLinked_of_fastCommit {L : BlockId} {r : ℕ} (h : FastCommit U L r)
    {A : BlockId} (hA : A ∈ U.ids) (hAr : r + 2 ≤ (U.block A).round) :
    WeakLinked U A L r :=
  weakLinked_of_fastCommit_aux h ((U.block A).round - (r + 2)) A hA (by omega)

/-! ## Starvation: a fast commit clears both rungs of every rival -/

private theorem supporters_capped_of_fastCommit {L L' : BlockId} {r : ℕ}
    (hne : L' ≠ L) (hcreator : (U.block L').creator = (U.block L).creator)
    (h : FastCommit U L r) :
    (supporters U L' (r + 1)).card + qFast Replica ≤
      Fintype.card Replica + F.f := by
  have := card_supporters_add_card_supporters_le U.noEquivOn_honest card_compl_nonByzantine_le
    hne hcreator (n := r + 1)
  simp only [FastCommit] at h
  omega

/-- A fast commit starves every same-creator rival (an equivocating
copy — the only kind a slot's candidates can be) off the weak rung, at
every anchor. -/
theorem not_weakLinked_of_fastCommit {L L' : BlockId} {r : ℕ} {A : BlockId}
    (hne : L' ≠ L) (hcreator : (U.block L').creator = (U.block L).creator)
    (h : FastCommit U L r) : ¬ WeakLinked U A L' r := by
  rintro ⟨s, hs, hcard⟩
  have hsub : creatorsOf U.block s ⊆ supporters U L' (r + 1) := by
    intro v hv
    obtain ⟨b, hb, hbc⟩ := mem_creatorsOf.mp hv
    obtain ⟨hb1, hb2, -⟩ := hs b hb
    obtain ⟨hbi, hbr⟩ := mem_blocksAt.mp hb1
    exact mem_supporters.mpr ⟨b, hbi, hbr, hb2, hbc⟩
  have h1 := Finset.card_le_card hsub
  have h2 := supporters_capped_of_fastCommit hne hcreator h
  have h5 := nf_lt_qFast_add_qWeak (Replica := Replica)
  omega

/-- A fast commit starves every same-creator rival off the certificate
rung too. -/
theorem certificates_eq_empty_of_fastCommit {L L' : BlockId} {r : ℕ}
    (hne : L' ≠ L) (hcreator : (U.block L').creator = (U.block L).creator)
    (h : FastCommit U L r) : certificates U L' r = ∅ := by
  rw [Finset.eq_empty_iff_forall_notMem]
  intro C hC
  obtain ⟨hCi, hCr, hcert⟩ := mem_certificates.mp hC
  have hle := Finset.card_le_card
    (creators_voteBlocks_subset_supporters (L := L') hCi hCr)
  have h2 := supporters_capped_of_fastCommit hne hcreator h
  have hqc := qWeak_le_qCert (Replica := Replica)
  have h5 := nf_lt_qFast_add_qWeak (Replica := Replica)
  simp only [IsCertificate] at hcert
  omega

/-- Starvation of same-creator rivals, rung-1 phrasing. -/
theorem not_certifiedIn_of_fastCommit {L L' : BlockId} {r : ℕ} {A : BlockId}
    (hne : L' ≠ L) (hcreator : (U.block L').creator = (U.block L).creator)
    (h : FastCommit U L r) : ¬ CertifiedIn U A L' r := by
  rintro ⟨C, hC, -⟩
  rw [certificates_eq_empty_of_fastCommit hne hcreator h] at hC
  exact Finset.notMem_empty C hC

/-! ## Skip-side negatives: a skipped slot has nothing on either rung -/

section Skip

variable [S : Slots Replica]

private theorem supporters_capped_of_skipped {k : ℕ} {L : BlockId}
    (hL : IsLeaderBlock U k L) (h : SkippedLeader U k) :
    (supporters U L (S.slotRound k + 1)).card + qFast Replica ≤
      Fintype.card Replica + F.f := by
  have := card_supporters_add_card_slotBlames_le U.noEquivOn_honest card_compl_nonByzantine_le hL
  simp only [SkippedLeader] at h
  omega

/-- A skipped slot's candidates never reach the weak rung. -/
theorem not_weakLinked_of_skipped {k : ℕ} {L : BlockId} {A : BlockId}
    (hL : IsLeaderBlock U k L) (h : SkippedLeader U k) :
    ¬ WeakLinked U A L (S.slotRound k) := by
  rintro ⟨s, hs, hcard⟩
  have hsub : creatorsOf U.block s ⊆ supporters U L (S.slotRound k + 1) := by
    intro v hv
    obtain ⟨b, hb, hbc⟩ := mem_creatorsOf.mp hv
    obtain ⟨hb1, hb2, -⟩ := hs b hb
    obtain ⟨hbi, hbr⟩ := mem_blocksAt.mp hb1
    exact mem_supporters.mpr ⟨b, hbi, hbr, hb2, hbc⟩
  have h1 := Finset.card_le_card hsub
  have h2 := supporters_capped_of_skipped hL h
  have h5 := nf_lt_qFast_add_qWeak (Replica := Replica)
  omega

/-- A skipped slot's candidates are never certified. -/
theorem certificates_eq_empty_of_skipped {k : ℕ} {L : BlockId}
    (hL : IsLeaderBlock U k L) (h : SkippedLeader U k) :
    certificates U L (S.slotRound k) = ∅ := by
  rw [Finset.eq_empty_iff_forall_notMem]
  intro C hC
  obtain ⟨hCi, hCr, hcert⟩ := mem_certificates.mp hC
  have hle := Finset.card_le_card
    (creators_voteBlocks_subset_supporters (L := L) hCi hCr)
  have h2 := supporters_capped_of_skipped hL h
  have hqc := qWeak_le_qCert (Replica := Replica)
  have h5 := nf_lt_qFast_add_qWeak (Replica := Replica)
  simp only [IsCertificate] at hcert
  omega

/-- Skip-side, rung-1 phrasing. -/
theorem not_certifiedIn_of_skipped {k : ℕ} {L : BlockId} {A : BlockId}
    (hL : IsLeaderBlock U k L) (h : SkippedLeader U k) :
    ¬ CertifiedIn U A L (S.slotRound k) := by
  rintro ⟨C, hC, -⟩
  rw [certificates_eq_empty_of_skipped hL h] at hC
  exact Finset.notMem_empty C hC

end Skip

/-! ## The rungs fire at an eligible anchor -/

section AtAnchor

variable [LinearOrder BlockId] [S : Slots Replica]

/-- The anchor's round, from its slot and eligibility. -/
theorem anchor_round {k j : ℕ} {A : BlockId} (hA : IsLeaderBlock U j A)
    (helig : (hydrozoanAnchored Replica BlockId).Eligible k j) :
    S.slotRound k + 3 ≤ (U.block A).round := by
  have := (hydrozoanAnchored Replica BlockId).anchor_round_le hA helig
  simp only [hydrozoanAnchored_wave] at this
  omega

/-- A slow commit in any view is certified at every candidate of an
eligible slot. -/
theorem certifiedIn_of_slowCommitInView_at_anchor {V : View U} {k j : ℕ}
    {L A : BlockId} (h : SlowCommitInView U V L (S.slotRound k))
    (hA : IsLeaderBlock U j A) (helig : (hydrozoanAnchored Replica BlockId).Eligible k j) :
    CertifiedIn U A L (S.slotRound k) :=
  certifiedIn_of_slowCommit (slowCommit_of_slowCommitInView h) hA.1 (anchor_round hA helig)

/-- A fast commit in any view is weak-linked at every candidate of an
eligible slot. -/
theorem weakLinked_of_fastCommitInView_at_anchor {V : View U} {k j : ℕ}
    {L A : BlockId} (h : FastCommitInView U V L (S.slotRound k))
    (hA : IsLeaderBlock U j A) (helig : (hydrozoanAnchored Replica BlockId).Eligible k j) :
    WeakLinked U A L (S.slotRound k) :=
  weakLinked_of_fastCommit (fastCommit_of_fastCommitInView h) hA.1
    (by have := anchor_round hA helig; omega)

end AtAnchor

end Hydrozoan

end LeanDag
