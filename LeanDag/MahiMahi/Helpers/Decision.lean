import LeanDag.MahiMahi.Model.Decision
import LeanDag.MahiMahi.Helpers.Rules
import LeanDag.Common.Anchored.Bounded
import LeanDag.Mysticeti.Rule
/-!
# Helpers — the decision layer

Generated lemma infrastructure for `Model/Decision.lean`; not part of the
audit surface. View lifting, the direct-versus-indirect agreement lemmas
at wave `w` (the core's M4 and M5 in their slot-indexed forms), the
anchor round bound, and the wave-three correspondences the
conservativity claims consume.
-/

namespace LeanDag

namespace MahiMahi

variable {Validator : Type} [Fintype Validator] [DecidableEq Validator]
variable [F : Faults Validator]
variable {BlockId : Type} [LinearOrder BlockId] {Payload : Type}
variable {U : BlockUniverse Validator BlockId Payload}

/-! ## A view can only under-report -/

theorem directCommit_of_directCommitIn {V : View Validator BlockId Payload U}
    {w : ℕ} {L : BlockId} {r : ℕ} (h : DirectCommitIn U V w L r) : DirectCommit U w L r :=
  le_trans h (Finset.card_le_card (Finset.image_subset_image Finset.inter_subset_left))

theorem directSkip_of_directSkipIn {V : View Validator BlockId Payload U}
    {w : ℕ} {a : Validator} {r : ℕ} (h : DirectSkipIn U V w a r) : DirectSkip U w a r :=
  le_trans h (Finset.card_le_card (Finset.image_subset_image Finset.inter_subset_left))

theorem certificates_nonempty_of_certifiedIn {w : ℕ} {A L : BlockId} {r : ℕ}
    (h : CertifiedIn U w A L r) : (certificates U w L r).Nonempty := by
  obtain ⟨C, hC, -⟩ := h
  exact ⟨C, hC⟩

/-- The commit half of M4: a directly committed candidate is certified in
the cone of every block above its decision round. -/
theorem certifiedIn_of_directCommit {w : ℕ} {L : BlockId} {r : ℕ} (h : DirectCommit U w L r)
    {A : BlockId} (hA : A ∈ U.ids) (hAr : decisionRoundAt w r + 1 ≤ (U.block A).round) :
    CertifiedIn U w A L r :=
  exists_certificate_reaches_of_directCommit h hA hAr

/-- The skip half of M4: a skipped slot's candidates are certified nowhere. -/
theorem not_certifiedIn_of_directSkip {w : ℕ} {a : Validator} {r : ℕ} {L : BlockId}
    (hw : 2 ≤ w) (h : DirectSkip U w a r)
    (hLc : (U.block L).creator = a) (hLr : (U.block L).round = r) {A : BlockId} :
    ¬ CertifiedIn U w A L r := by
  intro hc
  have hne := certificates_nonempty_of_certifiedIn hc
  rw [certificates_eq_empty_of_directSkip hw h hLc hLr] at hne
  exact Finset.not_nonempty_empty hne

section Slots

variable [S : Slots Validator]

omit S in
@[simp] theorem mahiMahiAnchored_wave (w : ℕ) :
    (mahiMahiAnchored Validator BlockId Payload w).wave = w - 1 := rfl
omit S in
@[simp] theorem mahiMahiAnchored_rungs (w : ℕ) :
    (mahiMahiAnchored Validator BlockId Payload w).rungs = 1 := rfl

/-- The relation's decision round is Mahi-Mahi's, at any wave of at
least one round. -/
theorem mahiMahiAnchored_decisionRound {w : ℕ} (hw : 1 ≤ w) (k : ℕ) :
    (mahiMahiAnchored Validator BlockId Payload w).decisionRound k
      = decisionRoundAt w (S.slotRound k) := by
  unfold AnchoredRule.decisionRound decisionRoundAt
  simp only [mahiMahiAnchored_wave]
  omega

/-- Two candidates of one slot with certificates coincide. -/
theorem eq_of_hasCertificate {w k : ℕ} {L₁ L₂ : BlockId} (hw : 2 ≤ w)
    (hL₁ : IsLeaderBlock U k L₁) (hL₂ : IsLeaderBlock U k L₂)
    (h₁ : (certificates U w L₁ (S.slotRound k)).Nonempty)
    (h₂ : (certificates U w L₂ (S.slotRound k)).Nonempty) : L₁ = L₂ :=
  eq_of_certificates_nonempty hw h₁ h₂ (by rw [hL₁.2.2, hL₂.2.2]) (by rw [hL₁.2.1, hL₂.2.1])

theorem eq_of_directCommitIn {w : ℕ} {V₁ V₂ : View Validator BlockId Payload U} {k : ℕ}
    {L₁ L₂ : BlockId} (hw : 2 ≤ w)
    (hL₁ : IsLeaderBlock U k L₁) (hL₂ : IsLeaderBlock U k L₂)
    (h₁ : DirectCommitIn U V₁ w L₁ (S.slotRound k))
    (h₂ : DirectCommitIn U V₂ w L₂ (S.slotRound k)) : L₁ = L₂ :=
  eq_of_hasCertificate hw hL₁ hL₂
    (certificates_nonempty_of_directCommit (directCommit_of_directCommitIn h₁))
    (certificates_nonempty_of_directCommit (directCommit_of_directCommitIn h₂))

/-- A committed candidate's slot is not skipped, across views. -/
theorem not_directSkipIn_of_directCommitIn {w : ℕ} {V₁ V₂ : View Validator BlockId Payload U}
    {k : ℕ} {L : BlockId} (hw : 2 ≤ w) (hL : IsLeaderBlock U k L)
    (h₁ : DirectCommitIn U V₁ w L (S.slotRound k))
    (h₂ : DirectSkipIn U V₂ w (S.leader k) (S.slotRound k)) : False := by
  have hne := certificates_nonempty_of_directCommit (directCommit_of_directCommitIn h₁)
  rw [certificates_eq_empty_of_directSkip hw (directSkip_of_directSkipIn h₂) hL.2.2 hL.2.1] at hne
  exact Finset.not_nonempty_empty hne

/-- A direct commit is seen from any candidate anchor of any eligible
slot. -/
theorem certifiedIn_of_directCommitIn_at_anchor {w : ℕ} (hw : 1 ≤ w)
    {V : View Validator BlockId Payload U} {k j : ℕ} {L A : BlockId}
    (h : DirectCommitIn U V w L (S.slotRound k)) (hA : IsLeaderBlock U j A)
    (helig : (mahiMahiAnchored Validator BlockId Payload w).Eligible k j) :
    CertifiedIn U w A L (S.slotRound k) :=
  certifiedIn_of_directCommit (directCommit_of_directCommitIn h) hA.1 (by
    have := (mahiMahiAnchored Validator BlockId Payload w).anchor_round_le hA helig
    simp only [mahiMahiAnchored_wave] at this
    unfold decisionRoundAt; omega)

omit S in
/-- **Mahi-Mahi's laws** at any wave of at least two rounds: the core's
M6 cases at wave `w`, every commit-against-commit case by certificate
uniqueness. -/
theorem mahiMahiLaws {w : ℕ} (hw : 2 ≤ w) :
    (mahiMahiAnchored Validator BlockId Payload w).Laws where
  commit_unique := fun _ hL₁ hL₂ h₁ h₂ => eq_of_directCommitIn hw hL₁ hL₂ h₁ h₂
  commit_skip := fun _ hL h hskip => not_directSkipIn_of_directCommitIn hw hL h hskip
  commit_link := fun _ _ h hA helig => ⟨0, Nat.one_pos,
    certifiedIn_of_directCommitIn_at_anchor (by omega) h hA helig⟩
  commit_link_unique := by
    intro S U V k j i L₁ L₂ A _ hL₁ hL₂ h _ _ _ _ hlink _
    exact eq_of_hasCertificate hw hL₁ hL₂
      (certificates_nonempty_of_directCommit (directCommit_of_directCommitIn h))
      (certificates_nonempty_of_certifiedIn hlink)
  skip_link := fun _ hskip hL _ =>
    not_certifiedIn_of_directSkip hw (directSkip_of_directSkipIn hskip) hL.2.2 hL.2.1
  link_unique := by
    intro S U k j i L₁ L₂ A _ hL₁ hL₂ _ _ _ _ hl₁ hl₂ _ _
    exact eq_of_hasCertificate hw hL₁ hL₂ (certificates_nonempty_of_certifiedIn hl₁)
      (certificates_nonempty_of_certifiedIn hl₂)
  commit_mono := fun _ hsub h => HoldsAtLeast.mono hsub h
  skip_mono := fun _ hsub h => HoldsAtLeast.mono hsub h
  skip_congr := fun _ hround hk h => by
    show DirectSkipIn _ _ _ _ _
    rw [← hround, ← hk]; exact h
  link_congr := (mahiMahiAnchored Validator BlockId Payload w).linkCongr_of_round
    (fun _ U A L r => MahiMahi.CertifiedIn U w A L r) fun _ _ _ _ _ _ => rfl

/-- No tie: any linked candidate is the rung's choice. -/
theorem exists_least {w : ℕ} {S : Slots Validator} {U : BlockUniverse Validator BlockId Payload}
    {A : BlockId} {i k : ℕ} (_ : i < (mahiMahiAnchored Validator BlockId Payload w).rungs)
    (h : ∃ L, IsLeaderBlock (S := S) U k L ∧
      (mahiMahiAnchored Validator BlockId Payload w).Link i U A L S k) :
    ∃ L, IsLeaderBlock (S := S) U k L ∧
      (mahiMahiAnchored Validator BlockId Payload w).Link i U A L S k ∧
      (mahiMahiAnchored Validator BlockId Payload w).Least (S := S) U A i k L :=
  let ⟨L, hL, hl⟩ := h
  ⟨L, hL, hl, fun _ _ _ h => h⟩

/-! ## Wave three is the core's relation -/

theorem eligible_three_iff {k j : ℕ} :
    (mahiMahiAnchored Validator BlockId Payload 3).Eligible k j ↔
      (coreAnchored Validator BlockId Payload).Eligible k j := by
  simp only [AnchoredRule.Eligible, eligibleAt_iff, mahiMahiAnchored_wave, coreAnchored_wave]

omit S in
theorem certifiedIn_three_iff {A L : BlockId} {r : ℕ} (hLr : (U.block L).round = r) :
    CertifiedIn U 3 A L r ↔ LeanDag.CertifiedIn U A L r := by
  unfold CertifiedIn LeanDag.CertifiedIn
  rw [certificates_eq_of_three hLr]

omit S in
theorem directCommitIn_three_iff {V : View Validator BlockId Payload U} {L : BlockId} {r : ℕ}
    (hLr : (U.block L).round = r) :
    DirectCommitIn U V 3 L r ↔ LeanDag.DirectCommitIn U V L r := by
  unfold DirectCommitIn LeanDag.DirectCommitIn
  rw [certificates_eq_of_three hLr]

omit S in
/-- A blame of the slot in view is a blame of each candidate in view. -/
theorem core_directSkipIn_of_directSkipIn {V : View Validator BlockId Payload U}
    {a : Validator} {r : ℕ} {L : BlockId} (h : DirectSkipIn U V 3 a r)
    (hLc : (U.block L).creator = a) (hLr : (U.block L).round = r) :
    LeanDag.DirectSkipIn U V L r := by
  refine le_trans h (Finset.card_le_card (Finset.image_subset_image ?_))
  intro q hq
  rw [votingRound_three] at hq
  rw [Finset.mem_inter, Finset.mem_filter] at hq
  rw [Finset.mem_inter, omissionsOf, Finset.mem_filter]
  obtain ⟨⟨hqb, hqblame⟩, hqV⟩ := hq
  exact ⟨⟨hqb, not_mem_refs_of_blames (mem_blocksAt.mp hqb).1 hqblame hLc hLr⟩, hqV⟩

/-- **A blame of the slot in view is the core's slot-level blame.** The two
rules agree on what a blame is — no candidate of the slot in the block's
references — so the count transfers verbatim. -/
theorem core_directSkipSlotIn_of_directSkipIn {V : View Validator BlockId Payload U} {k : ℕ}
    (h : DirectSkipIn U V 3 (S.leader k) (S.slotRound k)) :
    LeanDag.DirectSkipSlotIn U V k := by
  refine le_trans h (Finset.card_le_card (Finset.image_subset_image ?_))
  intro q hq
  rw [votingRound_three] at hq
  rw [Finset.mem_inter, Finset.mem_filter] at hq
  rw [Finset.mem_inter, LeanDag.slotBlamers, Finset.mem_filter]
  obtain ⟨⟨hqb, hqblame⟩, hqV⟩ := hq
  refine ⟨⟨hqb, fun j hj hjL => ?_⟩, hqV⟩
  exact not_mem_refs_of_blames (mem_blocksAt.mp hqb).1 hqblame hjL.2.2 hjL.2.1 hj

/-- At wave three every derivation is a derivation of the core's relation. -/
theorem core_decided_of_decided {V : View Validator BlockId Payload U} {k : ℕ}
    {v : Option BlockId} (h : Decided 3 U V k v) : LeanDag.Decided U V k v := by
  induction h with
  | @directCommit k L hL h =>
    exact LeanDag.Decided.directCommit hL ((directCommitIn_three_iff hL.2.1).mp h)
  | @directSkip k hskip =>
    exact LeanDag.Decided.directSkip (core_directSkipSlotIn_of_directSkipIn hskip)
  | @indirectCommit k j A L i hkj helig hj hmid _ _ hL hcert _ ihj ihmid =>
    exact AnchoredRule.Decided.indirectCommit_single rfl (fun _ _ h => h) hkj
      (eligible_three_iff.mp helig) ihj
      (fun i h1 h2 he => ihmid i h1 h2 (eligible_three_iff.mpr he)) hL
      ((certifiedIn_three_iff hL.2.1).mp hcert)
  | @indirectSkip k j A hkj helig hj hmid hnone ihj ihmid =>
    exact AnchoredRule.Decided.indirectSkip_single rfl hkj (eligible_three_iff.mp helig) ihj
      (fun i h1 h2 he => ihmid i h1 h2 (eligible_three_iff.mpr he))
      (fun L hL hc => hnone 0 Nat.one_pos L hL ((certifiedIn_three_iff hL.2.1).mpr hc))

end Slots

end MahiMahi

end LeanDag
