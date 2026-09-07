import LeanDag.MahiMahi.Model.Unpredictable
import LeanDag.MahiMahi.Helpers.Counting
import LeanDag.MahiMahi.Helpers.Decision
import LeanDag.Common.Anchored.Bounded
import LeanDag.Mysticeti.ViewPace
/-!
# Helpers — the liveness layer

Generated lemma infrastructure for `Liveness/Statement.lean`; not part of
the audit surface. Eligibility at wave `w`; a good leader's commit; the
core's descent from a committed run, transcribed; the local route on the
pacing structure with convergence read as eventual delivery; and the
congruences behind measurability, built on reachability agreeing between
universes that agree below a round.
-/

namespace LeanDag

namespace MahiMahi

variable {Validator : Type} [Fintype Validator] [DecidableEq Validator]
variable [F : Faults Validator]
variable {BlockId : Type} [LinearOrder BlockId] {Payload : Type}
variable {U : BlockUniverse Validator BlockId Payload}

/-! ## Lifting a direct commit to the full view -/

theorem directCommitIn_full {w : ℕ} {L : BlockId} {r : ℕ} (h : DirectCommit U w L r) :
    DirectCommitIn U (View.full U) w L r :=
  (HoldsAtLeast.full fun _ hC => (mem_certificatesAt.mp hC).1).mpr h

section Slots

variable [S : Slots Validator]

/-! ## A good leader commits -/

/-- **MM3a.** -/
theorem decided_of_mem_good {w k : ℕ} (h : S.leader k ∈ good U w k) :
    ∃ L, IsLeaderBlock U k L ∧ Decided w U (View.full U) k (some L) := by
  unfold good at h
  rw [mem_goodAt] at h
  obtain ⟨L, hL, hLr, hLc, hcommit⟩ := h
  exact ⟨L, ⟨hL, hLr, hLc⟩, Decided.directCommit ⟨hL, hLr, hLc⟩ (directCommitIn_full hcommit)⟩

/-! ## The descent from a committed run

Every slot below a committed run is decided: the relation's
`decided_below_of_committed_run` at wave `w`, with no tie to break. -/

/-- **MM3c.** The run form supplies the committed run; the descent does
the rest. A spanning run has at least one slot. -/
theorem allDecidedBelow {w c d N : ℕ}
    (hspan : (mahiMahiAnchored Validator BlockId Payload w).SpansEligible d)
    (hrun : UnpredictableRunWithin U w c d N) (k : ℕ)
    (hk : (mahiMahiAnchored Validator BlockId Payload w).decisionRound (k + c + d - 1) ≤ N) :
    ∃ b, k ≤ b ∧ ∀ i, i < b → ∃ v, Decided w U (View.full U) i v := by
  obtain ⟨k', hk1, hk2, hgood⟩ := hrun k hk
  have hd : 1 ≤ d := by
    have := (mahiMahiAnchored Validator BlockId Payload w).lt_of_eligible (hspan 1 0 (by omega))
    omega
  refine ⟨k', hk1, AnchoredRule.decided_below_of_run (fun hi h => exists_least hi h) hd hspan
    (Led := fun j => S.leader j ∈ good U w j) hgood fun j _ _ hj => ?_⟩
  obtain ⟨L, -, hdec⟩ := decided_of_mem_good hj
  exact ⟨L, hdec⟩

/-! ## The local route -/

omit [LinearOrder BlockId] S in
/-- Every reliable round-`n` block is held by every reliable validator by
`max (latest n) gst + delay`: its author holds it when built, `latest` is
past every build, and convergence carries it across from any time past
`gst`. Convergence is read here as eventual delivery only. -/
theorem holds_roundBlocks_eventually {T : Finset Validator} {N : ℕ} (pc : PaceCore U T N)
    {n : ℕ} (hn : n ≤ N) :
    ∀ v ∈ T, ∀ b ∈ U.ids, (U.block b).creator ∈ T → (U.block b).round = n →
      b ∈ pc.holds v (max (pc.latest n) pc.gst + pc.delay) := by
  intro v hv b hb hbT hbr
  have hown := pc.holds_own _ hbT n hn b hb rfl hbr
  have hle : pc.built (U.block b).creator n ≤ pc.latest n :=
    pc.built_le_latest _ hbT n hn
  exact pc.converges v hv _ hbT (max (pc.latest n) pc.gst) (le_max_right _ _)
    (pc.holds_mono _ _ _ (le_trans hle (le_max_left _ _)) hown)

/-- **MM3d.** The counting re-run inside the view: production gives every
reliable validator a decision-round block, the premise makes each a
certificate, and eventual delivery puts each in the view. -/
theorem localCommit {w : ℕ} (hw : 1 ≤ w) {T : Finset Validator} {N : ℕ} (pc : PaceCore U T N)
    (hcard : quorumCard Validator ≤ T.card) {k : ℕ} {L : BlockId}
    (hL : IsLeaderBlock U k L) (hN : (mahiMahiAnchored Validator BlockId Payload w).decisionRound k ≤ N)
    (hcert : ∀ u ∈ T, ∀ C ∈ U.ids, (U.block C).creator = u →
      (U.block C).round = (mahiMahiAnchored Validator BlockId Payload w).decisionRound k → Certifies U C L) :
    ∀ v ∈ T, Decided w U
      (pc.viewAt v (max (pc.latest ((mahiMahiAnchored Validator BlockId Payload w).decisionRound k)) pc.gst + pc.delay))
      k (some L) := by
  rw [mahiMahiAnchored_decisionRound hw] at hN hcert ⊢
  have hpop := pc.populatedOn hcard _ hN
  intro v hv
  refine Decided.directCommit hL (le_trans hcard (Finset.card_le_card ?_))
  intro u hu
  obtain ⟨c, hc, hcc, hcr⟩ := hpop u hu
  exact mem_heldAuthors.mpr ⟨c, mem_certificatesAt.mpr ⟨hc, hcr, hcert u hu c hc hcc hcr⟩,
    pc.mem_viewAt (holds_roundBlocks_eventually pc hN v hv c hc (hcc ▸ hu) hcr), hcc⟩

end Slots

/-! ## Measurability: agreement below a round -/

section Agree

variable {U₁ U₂ : BlockUniverse Validator BlockId Payload} {d : ℕ}

omit [LinearOrder BlockId] in
theorem AgreeUpto.symm (h : AgreeUpto U₁ U₂ d) : AgreeUpto U₂ U₁ d where
  ids i := (h.ids i).symm
  block i hi hr := by
    obtain ⟨hi₁, hr₁⟩ := (h.ids i).mpr ⟨hi, hr⟩
    exact (h.block i hi₁ hr₁).symm

omit [LinearOrder BlockId] in
/-- Reachability from a block below the round is the same in both
universes: every step stays below the round, where the blocks agree. -/
theorem AgreeUpto.reaches (h : AgreeUpto U₁ U₂ d) {q i : BlockId}
    (hq : q ∈ U₁.ids) (hqr : (U₁.block q).round ≤ d) (hr : Reaches U₁ q i) :
    Reaches U₂ q i := by
  induction hr with
  | refl => exact Relation.ReflTransGen.refl
  | @tail i j hqi hstep ih =>
    have hi : i ∈ U₁.ids := mem_ids_of_reaches hq hqi
    have hir : (U₁.block i).round ≤ d := le_trans (round_le_of_reaches hq hqi) hqr
    have hstep' : j ∈ (U₂.block i).refs := by
      have : (U₁.block i).refs = (U₂.block i).refs := by rw [h.block i hi hir]
      rw [← this]
      exact hstep
    exact Relation.ReflTransGen.tail ih hstep'

theorem AgreeUpto.history (h : AgreeUpto U₁ U₂ d) {q : BlockId}
    (hq : q ∈ U₁.ids) (hqr : (U₁.block q).round ≤ d) : history U₁ q = history U₂ q := by
  obtain ⟨hq₂, hqr₂⟩ := (h.ids q).mp ⟨hq, hqr⟩
  ext i
  rw [mem_history_iff hq, mem_history_iff hq₂]
  exact ⟨h.reaches hq hqr, h.symm.reaches hq₂ hqr₂⟩

omit [LinearOrder BlockId] in
theorem AgreeUpto.blocksAt_eq (h : AgreeUpto U₁ U₂ d) {r : ℕ} (hr : r ≤ d) :
    blocksAt U₁ r = blocksAt U₂ r := by
  ext i
  simp only [mem_blocksAt]
  constructor
  · rintro ⟨hi, hir⟩
    obtain ⟨hi₂, -⟩ := (h.ids i).mp ⟨hi, by omega⟩
    exact ⟨hi₂, by rw [← h.block i hi (by omega)]; exact hir⟩
  · rintro ⟨hi, hir⟩
    obtain ⟨hi₁, hir₁⟩ := (h.ids i).mpr ⟨hi, by omega⟩
    exact ⟨hi₁, by rw [h.block i hi₁ hir₁]; exact hir⟩

theorem AgreeUpto.candidatesAt_eq (h : AgreeUpto U₁ U₂ d) {q : BlockId} {a : Validator} {r : ℕ}
    (hq : q ∈ U₁.ids) (hqr : (U₁.block q).round ≤ d) (hr : r ≤ d) :
    candidatesAt U₁ q a r = candidatesAt U₂ q a r := by
  unfold candidatesAt
  rw [h.blocksAt_eq hr]
  apply Finset.filter_congr
  intro b hb
  obtain ⟨hb₂, hbr₂⟩ := mem_blocksAt.mp hb
  obtain ⟨hb₁, hbr₁⟩ := (h.ids b).mpr ⟨hb₂, by omega⟩
  rw [h.block b hb₁ hbr₁, h.history hq hqr]

theorem AgreeUpto.votes_iff (h : AgreeUpto U₁ U₂ d) {q L : BlockId}
    (hq : q ∈ U₁.ids) (hqr : (U₁.block q).round ≤ d)
    (hL : L ∈ U₁.ids) (hLr : (U₁.block L).round ≤ d) :
    Votes U₁ q L ↔ Votes U₂ q L := by
  unfold Votes
  have hb := h.block L hL hLr
  rw [h.candidatesAt_eq hq hqr hLr, hb]

theorem AgreeUpto.votesIn_eq (h : AgreeUpto U₁ U₂ d) {C L : BlockId}
    (hC : C ∈ U₁.ids) (hCr : (U₁.block C).round ≤ d)
    (hL : L ∈ U₁.ids) (hLr : (U₁.block L).round ≤ d) :
    votesIn U₁ C L = votesIn U₂ C L := by
  unfold votesIn carriedVotes
  rw [← h.block C hC hCr]
  apply Finset.filter_congr
  intro q hq
  have hqids := U₁.complete C hC q hq
  have hqr := U₁.round_of_mem_refs hC hq
  exact h.votes_iff hqids (by omega) hL hLr

omit [LinearOrder BlockId] in
theorem AgreeUpto.creatorsOf_eq (h : AgreeUpto U₁ U₂ d) {s : Finset BlockId}
    (hs : ∀ i ∈ s, i ∈ U₁.ids ∧ (U₁.block i).round ≤ d) :
    creatorsOf U₁.block s = creatorsOf U₂.block s := by
  unfold creatorsOf
  refine Finset.image_congr ?_
  intro i hi
  simp only
  obtain ⟨hi₁, hir₁⟩ := hs i (Finset.mem_coe.mp hi)
  rw [h.block i hi₁ hir₁]

theorem AgreeUpto.certifies_iff (h : AgreeUpto U₁ U₂ d) {C L : BlockId}
    (hC : C ∈ U₁.ids) (hCr : (U₁.block C).round ≤ d)
    (hL : L ∈ U₁.ids) (hLr : (U₁.block L).round ≤ d) :
    Certifies U₁ C L ↔ Certifies U₂ C L := by
  unfold Certifies CarriesVotes
  rw [show carriedVotes U₁ (Votes U₁) C L = carriedVotes U₂ (Votes U₂) C L from
    h.votesIn_eq hC hCr hL hLr, ← h.creatorsOf_eq]
  intro q hq
  rw [mem_carriedVotes] at hq
  rw [← h.block C hC hCr] at hq
  have hqids := U₁.complete C hC q hq.1
  have hqr := U₁.round_of_mem_refs hC hq.1
  exact ⟨hqids, by omega⟩

theorem AgreeUpto.certificates_eq (h : AgreeUpto U₁ U₂ d) {w : ℕ} {L : BlockId} {r : ℕ}
    (hd : decisionRoundAt w r ≤ d) (hL : L ∈ U₁.ids) (hLr : (U₁.block L).round ≤ d) :
    certificates U₁ w L r = certificates U₂ w L r := by
  unfold certificates certificatesAt
  rw [h.blocksAt_eq hd]
  apply Finset.filter_congr
  intro C hC
  obtain ⟨hC₂, hCr₂⟩ := mem_blocksAt.mp hC
  obtain ⟨hC₁, hCr₁⟩ := (h.ids C).mpr ⟨hC₂, by omega⟩
  exact h.certifies_iff hC₁ hCr₁ hL hLr

theorem AgreeUpto.directCommit_iff (h : AgreeUpto U₁ U₂ d) {w : ℕ} {L : BlockId} {r : ℕ}
    (hd : decisionRoundAt w r ≤ d) (hL : L ∈ U₁.ids) (hLr : (U₁.block L).round ≤ d) :
    DirectCommit U₁ w L r ↔ DirectCommit U₂ w L r := by
  unfold DirectCommit
  rw [h.certificates_eq hd hL hLr, ← h.creatorsOf_eq]
  intro C hC
  obtain ⟨hC₂, hCr₂, -⟩ := mem_certificatesAt.mp hC
  obtain ⟨hC₁, hCr₁⟩ := (h.ids C).mpr ⟨hC₂, by omega⟩
  exact ⟨hC₁, hCr₁⟩

theorem AgreeUpto.goodAt_subset (h : AgreeUpto U₁ U₂ d) {w r : ℕ} (hw : 1 ≤ w)
    (hd : decisionRoundAt w r ≤ d) : goodAt U₁ w r ⊆ goodAt U₂ w r := by
  intro v hv
  rw [mem_goodAt] at hv ⊢
  obtain ⟨L, hL, hLr, hLc, hcommit⟩ := hv
  have hrd : r ≤ d := by unfold decisionRoundAt at hd; omega
  obtain ⟨hL₂, -⟩ := (h.ids L).mp ⟨hL, by omega⟩
  have hb := h.block L hL (by omega)
  refine ⟨L, hL₂, by rw [← hb]; exact hLr, by rw [← hb]; exact hLc, ?_⟩
  exact (h.directCommit_iff hd hL (by omega)).mp hcommit

/-- **MM2′.** -/
theorem AgreeUpto.goodAt_eq (h : AgreeUpto U₁ U₂ d) {w r : ℕ} (hw : 1 ≤ w)
    (hd : decisionRoundAt w r ≤ d) : goodAt U₁ w r = goodAt U₂ w r :=
  Finset.Subset.antisymm (h.goodAt_subset hw hd) (h.symm.goodAt_subset hw hd)

end Agree

end MahiMahi

end LeanDag
