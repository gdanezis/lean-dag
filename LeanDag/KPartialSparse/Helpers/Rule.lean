import LeanDag.KPartialSparse.Model.Rule
import LeanDag.KPartialSparse.Helpers.Avail
/-!
# Sparse K-partial DAG — the commit rule, helpers

`docs/kpartial-sparse.md` §4. A direct commit names a block certified at the
row's commit strength (`certified_of_commit`), and a link at its link
strength (`certified_of_link`); two certified blocks of one author and round
are one (`eq_of_certified`), a certified block is not directly skipped
(`not_certified_skip`), the row's inequalities between these strengths
(`row_arith`), a direct commit is linked from any eligible anchor
(`certLinked_of_commit`), and the laws of an anchored rule (`sRule_laws`).
-/

namespace LeanDag

namespace KPartialSparse

open KPartialDag Scheme

variable {Validator : Type*} [Fintype Validator] [DecidableEq Validator] [F : Faults Validator]
variable [Cr : Crashes Validator] [Ld : Leaders Validator]
variable {BlockId : Type*} [LinearOrder BlockId] {Payload : Type*} [ClaimFormat BlockId Payload]
variable {U : SRecord Validator BlockId Payload} {p : Params}

omit Cr Ld [LinearOrder BlockId] [ClaimFormat BlockId Payload] in
/-- Among more than `f` authors one is correct. -/
theorem exists_correct_of_lt {X : Finset Validator} (h : F.f < X.card) :
    ∃ w ∈ X, w ∈ (Correct : Finset Validator) := by
  have hsplit := card_le_card_inter_correct_add_byzantine X
  have hb := F.card_byzantine
  obtain ⟨w, hw⟩ : (X ∩ (Correct : Finset Validator)).Nonempty := by
    rw [← Finset.card_pos]; omega
  exact ⟨w, (Finset.mem_inter.mp hw).1, (Finset.mem_inter.mp hw).2⟩

/-! ## Strengths -/

/-- The threshold a direct commit certifies its block at: its votes in a
two-round row, the certificate threshold behind a claim in a three-round
row. -/
abbrev commitStrength (p : Params) : ℕ := if p.voteIsCert then p.commitThreshold else p.certThreshold

/-- The threshold a link certifies its block at. -/
abbrev linkStrength (p : Params) : ℕ := if p.voteIsCert then p.linkSize else p.certThreshold

omit Ld in
/-- **The row's inequalities between strengths**: two commits, a commit and a
skip, a commit and a link, and a link and a skip each exceed `n + f`. -/
theorem row_arith (hrow : Row Validator p) :
    Fintype.card Validator + F.f < commitStrength p + commitStrength p ∧
      Fintype.card Validator + F.f < commitStrength p + p.skipThreshold ∧
      Fintype.card Validator + F.f < commitStrength p + linkStrength p ∧
      Fintype.card Validator + F.f < linkStrength p + p.skipThreshold := by
  have := Cr.card_validators
  rcases hrow with ⟨hv, -, -, h2, h3, -⟩ | ⟨hv, -, h1, h2, h3⟩
  · simp only [commitStrength, linkStrength, hv, Bool.false_eq_true, if_false]; omega
  · simp only [commitStrength, linkStrength, hv, if_true]; omega

/-! ## What a commit and a link certify -/

omit [ClaimFormat BlockId Payload] in
/-- **A certified block has a correct voter**, which references it. -/
theorem exists_correct_voter {t : ℕ} (ht : F.f < t) {A : BlockId} (h : Certified U t A) :
    ∃ z ∈ U.ids, (U.block z).creator ∈ (Correct : Finset Validator) ∧ A ∈ (U.block z).refs := by
  have : F.f < (supporters U A ((U.block A).round + 1)).card := by unfold Certified at h; omega
  obtain ⟨w, hw, hwC⟩ := exists_correct_of_lt this
  obtain ⟨z, hz, -, hAz, rfl⟩ := mem_supporters.mp hw
  exact ⟨z, hz, hwC, hAz⟩

/-- **A direct commit names a certified block**: votes certify it directly,
and among claimers one is correct and claims truthfully. -/
theorem certified_of_commit (hrow : Row Validator p) (ht : Truthful U p.certThreshold)
    {L : BlockId} {r : ℕ}
    (hr : (U.block L).round = r)
    (h : p.commitThreshold ≤ (creatorsOf U.block (certsFor p U L r)).card) :
    Certified U (commitStrength p) L := by
  unfold certsFor at h
  rcases hrow with ⟨hv, -, -, -, -, hq⟩ | ⟨hv, -, -⟩
  · rw [if_neg (by simp [hv])] at h
    simp only [commitStrength, hv, Bool.false_eq_true, if_false]
    have : F.f < (creatorsOf U.block (claimersOf U L (r + 2))).card := by omega
    obtain ⟨w, hw, hwC⟩ := exists_correct_of_lt this
    obtain ⟨C, hC, rfl⟩ := mem_creatorsOf.mp hw
    obtain ⟨hCb, hCL⟩ := Finset.mem_filter.mp hC
    exact ht C (mem_blocksAt.mp hCb).1 hwC L hCL
  · rw [if_pos hv] at h
    simp only [commitStrength, hv, if_true]
    unfold Certified supporters
    rw [hr]; exact h

omit [ClaimFormat BlockId Payload] in
/-- A block of the sub-DAG below a block of the record lies in the record. -/
theorem avail_subset_ids {K : ℕ} {A C : BlockId} (hA : A ∈ U.ids) (hC : C ∈ Avail U K A) :
    C ∈ U.ids := by
  obtain ⟨y, d, hy, hCy⟩ := hC
  exact historyUpto_subset_ids _ (hy.mem hA) hCy

/-- **A link from an anchor names a certified block**: votes in the sub-DAG
certify it directly, and a claim in the sub-DAG was checked by a correct
author. -/
theorem certified_of_link (hrow : Row Validator p) {K : ℕ}
    (hck : Checks U K p.certThreshold) {A L : BlockId}
    (hA : p.voteIsCert = true ∨ Certified U p.certThreshold A) {r : ℕ}
    (hr : (U.block L).round = r) (h : CertLinked p U K A L r) :
    Certified U (linkStrength p) L := by
  obtain ⟨X, hX, hXn⟩ := h
  rcases hrow with ⟨hv, -, h1, h2, -, -⟩ | ⟨hv, -, -⟩
  · simp only [linkStrength, hv, Bool.false_eq_true, if_false]
    obtain ⟨C, hC⟩ : X.Nonempty := by
      rw [← Finset.card_pos]
      exact lt_of_lt_of_le (by omega) (hXn.trans Finset.card_image_le)
    obtain ⟨-, hCa, hCc⟩ := hX C hC
    unfold Certifies at hCc
    rw [if_neg (by simp [hv])] at hCc
    have hAc : Certified U p.certThreshold A := hA.resolve_left (by simp [hv])
    have := F.card_validators
    exact backed hck (exists_correct_voter (by omega) hAc) hCa hCc.2
  · simp only [linkStrength, hv, if_true]
    unfold Certified supporters
    rw [hr]
    refine hXn.trans (Finset.card_le_card (Finset.image_subset_image fun C hC => ?_))
    obtain ⟨hCi, -, hCc⟩ := hX C hC
    unfold Certifies at hCc
    rw [if_pos hv] at hCc
    exact mem_votesFor.mpr ⟨hCi, hCc⟩

/-! ## Uniqueness and exclusion -/

omit [ClaimFormat BlockId Payload] in
/-- **Two certified blocks of one author and round are one**: their voters
share a correct author, whose one block there references one block of each
author. -/
theorem eq_of_certified {t₁ t₂ : ℕ} (h : Fintype.card Validator + F.f < t₁ + t₂)
    {L₁ L₂ : BlockId} (hc : (U.block L₁).creator = (U.block L₂).creator)
    (hr : (U.block L₁).round = (U.block L₂).round)
    (c₁ : Certified U t₁ L₁) (c₂ : Certified U t₂ L₂) : L₁ = L₂ := by
  unfold Certified at c₁ c₂
  rw [← hr] at c₂
  set X := supporters U L₁ ((U.block L₁).round + 1)
  set Y := supporters U L₂ ((U.block L₁).round + 1)
  have hu := Finset.card_union_add_card_inter X Y
  have huniv : (X ∪ Y).card ≤ Fintype.card Validator := Finset.card_le_univ _
  obtain ⟨w, hw, hwC⟩ := exists_correct_of_lt (X := X ∩ Y) (by omega)
  obtain ⟨q₁, hq₁, hq₁r, hL₁q, hq₁w⟩ := mem_supporters.mp (Finset.mem_inter.mp hw).1
  obtain ⟨q₂, hq₂, hq₂r, hL₂q, hq₂w⟩ := mem_supporters.mp (Finset.mem_inter.mp hw).2
  have : q₁ = q₂ := U.no_equivocation q₁ hq₁ q₂ hq₂ (hq₁w ▸ hwC) (hq₁w.trans hq₂w.symm)
    (hq₁r.trans hq₂r.symm)
  subst this
  exact (U.valid q₁ hq₁).distinct L₁ hL₁q L₂ hL₂q hc

omit [ClaimFormat BlockId Payload] in
/-- **A certified block is not directly skipped**: its voters and the blamers
share a correct author, whose one block there would both reference it and
not. -/
theorem not_certified_skip {t s : ℕ} (h : Fintype.card Validator + F.f < t + s) {L : BlockId}
    {r : ℕ} (hr : (U.block L).round = r) (c : Certified U t L)
    (hs : s ≤ (creatorsOf U.block (omissionsOf U L (r + 1))).card) : False := by
  unfold Certified at c
  rw [hr] at c
  set X := supporters U L (r + 1)
  set Y := creatorsOf U.block (omissionsOf U L (r + 1))
  have hu := Finset.card_union_add_card_inter X Y
  have huniv : (X ∪ Y).card ≤ Fintype.card Validator := Finset.card_le_univ _
  obtain ⟨w, hw, hwC⟩ := exists_correct_of_lt (X := X ∩ Y) (by omega)
  obtain ⟨q₁, hq₁, hq₁r, hLq, hq₁w⟩ := mem_supporters.mp (Finset.mem_inter.mp hw).1
  obtain ⟨q₂, hq₂O, hq₂w⟩ := mem_creatorsOf.mp (Finset.mem_inter.mp hw).2
  obtain ⟨hq₂, hq₂r, hLq₂⟩ := mem_omissionsOf.mp hq₂O
  have : q₁ = q₂ := U.no_equivocation q₁ hq₁ q₂ hq₂ (hq₁w ▸ hwC) (hq₁w.trans hq₂w.symm)
    (hq₁r.trans hq₂r.symm)
  exact hLq₂ (this ▸ hLq)

/-! ## Visibility -/

/-- **A direct commit is linked from every leader block above its
certificates**: the sub-DAG holds the certificates of `q + cm − n − f`
authors, which the row makes the link size or more. -/
theorem certLinked_of_commit (hrow : Row Validator p) {K : ℕ} (hdeep : Deep Validator K)
    (hch : Chains U) {A L : BlockId} (hA : A ∈ U.ids)
    (hAl : (U.block A).creator ∈ Ld.leaders (U.block A).round) {r : ℕ}
    (hAr : r + (p.waveLength - 1) + 1 ≤ (U.block A).round)
    (h : p.commitThreshold ≤ (creatorsOf U.block (certsFor p U L r)).card) :
    CertLinked p U K A L r := by
  have hmem : ∀ C ∈ certsFor p U L r, C ∈ U.ids ∧ (U.block C).round = r + (p.waveLength - 1) ∧
      Certifies p U C L r := by
    intro C hC
    unfold certsFor at hC
    unfold Certifies
    rcases hrow with ⟨hv, hw, -⟩ | ⟨hv, hw, -⟩
    · rw [if_neg (by simp [hv])] at hC ⊢
      obtain ⟨hCb, hCL⟩ := Finset.mem_filter.mp hC
      obtain ⟨hCi, hCr⟩ := mem_blocksAt.mp hCb
      exact ⟨hCi, by rw [hw]; omega, hCr, hCL⟩
    · rw [if_pos hv] at hC ⊢
      obtain ⟨hCi, hCr, hLC⟩ := mem_votesFor.mp hC
      exact ⟨hCi, by rw [hw]; omega, hCr, hLC⟩
  obtain ⟨X, hXs, hXa, hXn⟩ := linked_count hdeep hch hA hAl hAr
    (Cl := certsFor p U L r) fun C hC => ⟨(hmem C hC).1, (hmem C hC).2.1⟩
  refine ⟨X, fun C hC => ⟨(hmem C (hXs hC)).1, hXa C hC, (hmem C (hXs hC)).2.2⟩, ?_⟩
  rcases hrow with ⟨-, -, h1, -, -, hq⟩ | ⟨-, -, -, -, h3⟩ <;> omega

/-! ## The laws -/

/-- **The laws of an anchored rule** hold of the commit rule at a row and the
depth the sub-DAG needs, on a disciplined schedule and record. -/
theorem sRule_laws (hrow : Row Validator p) {K : ℕ} (hdeep : Deep Validator K) :
    (sRule (Validator := Validator) (BlockId := BlockId) (Payload := Payload) p K).Laws
      (Disciplined K p.certThreshold) where
  commit_unique := by
    intro S U V₁ V₂ k L₁ L₂ hI hL₁ hL₂ h₁ h₂
    exact eq_of_certified (row_arith hrow).1 (hL₁.2.2.trans hL₂.2.2.symm)
      (hL₁.2.1.trans hL₂.2.1.symm)
      (certified_of_commit hrow hI.2.2.2 hL₁.2.1 h₁.le)
      (certified_of_commit hrow hI.2.2.2 hL₂.2.1 h₂.le)
  commit_skip := by
    intro S U V₁ V₂ k L hI hL h hskip
    exact not_certified_skip (row_arith hrow).2.1 hL.2.1
      (certified_of_commit hrow hI.2.2.2 hL.2.1 h.le)
      (hskip.le.trans (Finset.card_le_card
        (Finset.image_subset_image (slotBlamers_subset_omissionsOf hL))))
  commit_link := by
    intro S U V k j L A hI _ h hA _ helig
    have he := (sRule (Validator := Validator) (BlockId := BlockId) (Payload := Payload)
      p K).eligible_iff.mp helig
    change S.slotRound k + (p.waveLength - 1) + 1 ≤ S.slotRound j at he
    refine ⟨0, Nat.one_pos, ?_⟩
    have hAl : (U.block A).creator ∈ Ld.leaders (U.block A).round := by
      rw [hA.2.2, hA.2.1]; exact hI.1 j
    exact certLinked_of_commit hrow hdeep hI.2.1 hA.1 hAl (by rw [hA.2.1]; exact he) h.le
  commit_link_unique := by
    intro S U V k j i L₁ L₂ A hI hL₁ hL₂ h hA hanc _ _ _ hlink _
    exact eq_of_certified (row_arith hrow).2.2.1 (hL₁.2.2.trans hL₂.2.2.symm)
      (hL₁.2.1.trans hL₂.2.1.symm)
      (certified_of_commit hrow hI.2.2.2 hL₁.2.1 h.le)
      (certified_of_link hrow hI.2.2.1 hanc hL₂.2.1 hlink)
  skip_link := by
    intro S U V k i L A hI hskip hL _ hanc hlink
    exact not_certified_skip (row_arith hrow).2.2.2 hL.2.1
      (certified_of_link hrow hI.2.2.1 hanc hL.2.1 hlink)
      (hskip.le.trans (Finset.card_le_card
        (Finset.image_subset_image (slotBlamers_subset_omissionsOf hL))))
  link_unique := by
    intro S U k j i L₁ L₂ A hI hL₁ hL₂ _ hanc _ _ _ hl₁ hl₂ hm₁ hm₂
    exact le_antisymm (not_lt.mp (hm₁ L₂ hL₂ hl₂)) (not_lt.mp (hm₂ L₁ hL₁ hl₁))
  commit_mono := fun _ hsub h => HoldsAtLeast.mono hsub h
  skip_mono := fun _ hsub h => HoldsAtLeast.mono hsub h
  skip_congr := fun _ hround hk _ h => blameSkip_congr hround hk h
  link_congr := (sRule p K).linkCongr_of_round (fun _ U A L r => CertLinked p U K A L r)
    fun _ _ _ _ _ _ => rfl
  anchor_commit := by
    intro S U V k L hI hL h
    have hc := certified_of_commit hrow hI.2.2.2 hL.2.1 h.le
    cases hv : p.voteIsCert
    · right; simpa [commitStrength, hv] using hc
    · exact Or.inl hv
  anchor_link := by
    intro S U k j i A L hI hA hanc _ hL _ hlink
    have hc := certified_of_link hrow hI.2.2.1 hanc hL.2.1 hlink
    cases hv : p.voteIsCert
    · right; simpa [linkStrength, hv] using hc
    · exact Or.inl hv

end KPartialSparse

end LeanDag
