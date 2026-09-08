import LeanDag.Common.Support
import LeanDag.Common.Ledger
import LeanDag.Common.Anchored
import LeanDag.Common.Slots
import LeanDag.Common.History
/-!
# Uncertified DAGs: the Mysticeti commit rules

`spec.md` §4, Phase 2 — Stage A. Where a certified DAG admits a block
only once `2f+1` validators have signed it, Mysticeti drops that round
and rebuilds the authority one round further on: a round-`(r+1)` block
votes for a round-`r` block it references and blames it otherwise; a
round-`(r+2)` block certifies it once `2f+1` distinct validators' votes
are among its own references; `L` is directly committed or skipped when
`2f+1` distinct validators' certificates or blames say so. Everything
here is universe-level, needing neither views nor a leader schedule.
-/

namespace LeanDag

variable {Validator : Type*} [Fintype Validator] [DecidableEq Validator]
variable [F : Faults Validator]
variable {BlockId : Type*} [DecidableEq BlockId] {Payload : Type*}
variable {U : BlockUniverse Validator BlockId Payload}

/-- The references of `C` that vote for `L`: the record's carried votes,
in the plain sense. -/
abbrev votesIn (U : BlockUniverse Validator BlockId Payload) (C L : BlockId) : Finset BlockId :=
  carriedVotes U (IsVote U) C L

/-- A round-`(r+2)` block certifies `L` when its votes for `L` come from a
quorum of distinct validators: the record's certificate at `n − f`. -/
abbrev Certifies (U : BlockUniverse Validator BlockId Payload) (C L : BlockId) : Prop :=
  CarriesVotes U (IsVote U) (quorumCard Validator) C L

/-- The certificates for a round-`r` block `L`: the round-`(r+2)` blocks that
certify it. -/
abbrev certificates (U : BlockUniverse Validator BlockId Payload) (L : BlockId) (r : ℕ) :
    Finset BlockId :=
  certificatesAt U (IsVote U) (quorumCard Validator) L (r + 2)

/-- `L` is directly committed when its certificates come from a quorum of
distinct validators. -/
def DirectCommit (U : BlockUniverse Validator BlockId Payload) (L : BlockId) (r : ℕ) : Prop :=
  quorumCard Validator ≤ (creatorsOf U.block (certificates U L r)).card

/-- `L` is directly skipped when a quorum of distinct validators declined to
vote for it. -/
def DirectSkip (U : BlockUniverse Validator BlockId Payload) (L : BlockId) (r : ℕ) : Prop :=
  quorumCard Validator ≤ (blames U L (r + 1)).card

instance decidableDirectCommit (L : BlockId) (r : ℕ) : Decidable (DirectCommit U L r) :=
  inferInstanceAs (Decidable (quorumCard Validator ≤ (creatorsOf U.block (certificates U L r)).card))

instance decidableDirectSkip (L : BlockId) (r : ℕ) : Decidable (DirectSkip U L r) :=
  inferInstanceAs (Decidable (quorumCard Validator ≤ (blames U L (r + 1)).card))

/-- **M3.** A directly skipped block has no certificate anywhere in the
universe, not merely none in some view: `2f+1` blamers cap the
supporters at `2f`, below what a certificate's `2f+1` voters need. -/
theorem certificates_eq_empty_of_directSkip {L : BlockId} {r : ℕ}
    (h : DirectSkip U L r) : certificates U L r = ∅ := by
  -- A quorum of blamers caps the supporters below a quorum ...
  have hcap := card_supporters_add_card_blames_le U.noEquivOn_honest card_compl_correct_le
    (L := L) (n := r + 1)
  have hb : quorumCard Validator ≤ (blames U L (r + 1)).card := h
  rw [Finset.eq_empty_iff_forall_notMem]
  intro C hC
  rw [mem_certificatesAt] at hC
  obtain ⟨hC_ids, hC_round, hCert⟩ := hC
  unfold CarriesVotes at hCert
  -- ... and every vote a certificate counts is a genuine supporter.
  have hsub : creatorsOf U.block (votesIn U C L) ⊆ supporters U L (r + 1) := by
    intro v hv
    rw [mem_creatorsOf] at hv
    obtain ⟨q, hq, hq_creator⟩ := hv
    obtain ⟨hq_ids, hq_round, hq_ref⟩ := mem_carriedVotes_spec hC_ids hC_round hq
    exact mem_supporters.mpr ⟨q, hq_ids, hq_round, hq_ref, hq_creator⟩
  have := Finset.card_le_card hsub
  simp only [votesIn] at this
  have := F.card_validators
  omega

/-- **M1.** No block is both directly committed and directly skipped,
immediate from M3: a skip leaves no certificates, and a commit needs
`2f+1` of them. -/
theorem not_directCommit_of_directSkip {L : BlockId} {r : ℕ}
    (h : DirectSkip U L r) : ¬ DirectCommit U L r := by
  rw [DirectCommit, certificates_eq_empty_of_directSkip h]
  simp only [creatorsOf, Finset.image_empty, Finset.card_empty]
  have := F.card_validators
  omega

/-- **M2.** Once a block is directly committed, its certificate becomes
unavoidable: every block from round `r+3` on has one in its causal
history. The bound is tight — a round-`(r+2)` block that is not itself a
certificate reaches none — which is why the slot schedule must space
leaders at least three rounds apart. -/
theorem exists_certificate_reaches_of_directCommit {L : BlockId} {r : ℕ}
    (h : DirectCommit U L r)
    {c : BlockId} (hc : c ∈ U.ids) (hcr : r + 3 ≤ (U.block c).round) :
    ∃ C ∈ certificates U L r, Reaches U c C := by
  -- Base case at `r+3`: the certificates' correct authors cannot be dodged.
  have hbase : ∀ c' ∈ U.ids, (U.block c').round = r + 3 →
      ∃ C, C ∈ certificates U L r ∧ Reaches U c' C := by
    intro c' hc' hc'r
    set T := creatorsOf U.block (certificates U L r) ∩ (Correct : Finset Validator) with hT_def
    have hT : ∀ v ∈ T, ∃ q ∈ U.ids,
        (U.block q).round = r + 2 ∧ q ∈ certificates U L r ∧ (U.block q).creator = v := by
      intro v hv
      rw [hT_def, Finset.mem_inter, mem_creatorsOf] at hv
      obtain ⟨⟨q, hq_cert, hq_creator⟩, _⟩ := hv
      obtain ⟨hq_ids, hq_round, -⟩ := mem_certificatesAt.mp hq_cert
      exact ⟨q, hq_ids, hq_round, hq_cert, hq_creator⟩
    have hTc : ∀ v ∈ T, v ∈ (Correct : Finset Validator) :=
      fun _ hv => Finset.mem_of_mem_inter_right hv
    have hcard : F.f + 1 ≤ T.card := card_inter_correct_of_quorum h
    obtain ⟨C, hC_mem, hC_cert⟩ :=
      exists_mem_refs_of_honest_support_of_card
        (Q := fun q => q ∈ certificates U L r) hT hTc (lt_card_add_quorumCard hcard) hc' (by omega)
    exact ⟨C, hC_cert, Reaches.single hC_mem⟩
  exact reaches_pred_of_round_le hbase hc hcr

/-- A direct commit needs `2f+1` distinct certificate authors, so in
particular at least one certificate. -/
theorem certificates_nonempty_of_directCommit {L : BlockId} {r : ℕ}
    (h : DirectCommit U L r) : (certificates U L r).Nonempty := by
  rw [Finset.nonempty_iff_ne_empty]
  rintro hempty
  rw [DirectCommit, hempty] at h
  simp only [creatorsOf, Finset.image_empty, Finset.card_empty] at h
  have := F.card_validators
  omega

/-- **M5′ (certificate uniqueness).** A slot admits at most one
certifiable block: if certificates exist for two round-`r` blocks by the
same author, those blocks coincide. Stronger than M5, and the form the
indirect rule needs, since it commits on a single reachable certificate
rather than a quorum of them. -/
theorem eq_of_certificates_nonempty {L₁ L₂ : BlockId} {r : ℕ}
    (h₁ : (certificates U L₁ r).Nonempty) (h₂ : (certificates U L₂ r).Nonempty)
    (hcreator : (U.block L₁).creator = (U.block L₂).creator) :
    L₁ = L₂ := by
  obtain ⟨C₁, hC₁⟩ := h₁
  obtain ⟨C₂, hC₂⟩ := h₂
  rw [mem_certificatesAt] at hC₁ hC₂
  obtain ⟨hC₁_ids, hC₁_round, hC₁_cert⟩ := hC₁
  obtain ⟨hC₂_ids, hC₂_round, hC₂_cert⟩ := hC₂
  -- The two vote quorums share a block: one round-`(r+1)` block votes for
  -- both candidates.
  obtain ⟨q, hq₁, hq₂⟩ :=
    U.exists_common_mem_of_quorums (n := r + 1)
      (fun _ hq => ⟨(mem_carriedVotes_spec hC₁_ids hC₁_round hq).1,
        (mem_carriedVotes_spec hC₁_ids hC₁_round hq).2.1⟩)
      (fun _ hq => ⟨(mem_carriedVotes_spec hC₂_ids hC₂_round hq).1,
        (mem_carriedVotes_spec hC₂_ids hC₂_round hq).2.1⟩)
      hC₁_cert hC₂_cert
  -- Distinctness forbids it referencing two round-`r` blocks by one author.
  exact (U.valid q (mem_carriedVotes_spec hC₁_ids hC₁_round hq₁).1).distinct_creators
    L₁ (mem_carriedVotes_spec hC₁_ids hC₁_round hq₁).2.2
    L₂ (mem_carriedVotes_spec hC₂_ids hC₂_round hq₂).2.2 hcreator

/-- **M5.** At most one block per slot is directly committed — a
corollary of M5′, since a direct commit implies a certificate exists. -/
theorem eq_of_directCommit_of_creator_eq {L₁ L₂ : BlockId} {r : ℕ}
    (h₁ : DirectCommit U L₁ r) (h₂ : DirectCommit U L₂ r)
    (hcreator : (U.block L₁).creator = (U.block L₂).creator) :
    L₁ = L₂ :=
  eq_of_certificates_nonempty (certificates_nonempty_of_directCommit h₁)
    (certificates_nonempty_of_directCommit h₂) hcreator

/-! ## The indirect rule's test

An undecided slot is settled by looking into the causal history of a later,
directly committed *anchor*: commit if a certificate for the slot lies in
that subgraph, skip otherwise. M4 is the statement that this never
contradicts the direct rule. -/

/-- The indirect rule's test: a certificate for `L` lies in the causal
history of the anchor `A`. -/
abbrev CertifiedIn (U : BlockUniverse Validator BlockId Payload) (A L : BlockId) (r : ℕ) : Prop :=
  certifiedLink IsVote (quorumCard Validator) 2 U A L r

/-- A certificate in reach is, in particular, a certificate that exists. This
is what lets M5′ compare an *indirect* commit against anything else. -/
theorem certificates_nonempty_of_certifiedIn {A L : BlockId} {r : ℕ}
    (h : CertifiedIn U A L r) : (certificates U L r).Nonempty :=
  h.nonempty

/-- **M4, commit half.** A directly committed block is found by every
anchor from round `r+3` on — M2 restated as the indirect rule's test. -/
theorem certifiedIn_of_directCommit {L : BlockId} {r : ℕ} (h : DirectCommit U L r)
    {A : BlockId} (hA : A ∈ U.ids) (hAr : r + 3 ≤ (U.block A).round) :
    CertifiedIn U A L r :=
  exists_certificate_reaches_of_directCommit h hA hAr

/-- **M4, skip half.** A directly skipped block is found by *no* anchor
whatsoever — no round hypothesis needed, because M3 rules out the
certificate universe-wide rather than merely out of reach. -/
theorem not_certifiedIn_of_directSkip {L : BlockId} {r : ℕ} (h : DirectSkip U L r)
    {A : BlockId} : ¬ CertifiedIn U A L r := by
  rintro ⟨C, hC, -⟩
  change C ∈ certificates U L r at hC
  rw [certificates_eq_empty_of_directSkip h] at hC
  exact absurd hC (Finset.notMem_empty C)

/-- **M4.** Where the direct rule decides, the indirect rule agrees:
commit needs the anchor at round `r+3` or beyond, skip needs nothing at
all, since there is no certificate anywhere to reach. -/
theorem indirect_agrees_with_direct {L : BlockId} {r : ℕ}
    {A : BlockId} (hA : A ∈ U.ids) (hAr : r + 3 ≤ (U.block A).round) :
    (DirectCommit U L r → CertifiedIn U A L r) ∧
      (DirectSkip U L r → ¬ CertifiedIn U A L r) :=
  ⟨fun h => certifiedIn_of_directCommit h hA hAr, fun h => not_certifiedIn_of_directSkip h⟩

/-- The indirect test is view-independent: a validator holding the
anchor computes the same verdict from its own local DAG as from the
whole universe (T6a). -/
theorem certifiedIn_iff_of_view {V : View Validator BlockId Payload U} {A L : BlockId} {r : ℕ}
    (hA : A ∈ V.ids) :
    (∃ C, C ∈ V.ids ∧ C ∈ certificates U L r ∧ Reaches U A C) ↔ CertifiedIn U A L r :=
  View.exists_reaches_iff hA

/-! ## Stage C1 — the slot schedule and the decision relation -/


variable [S : Slots Validator]

variable (Validator) in
/-! **Eligibility** is the relation's, at wave two (`EligibleAt 2`): `j`
may anchor `k` when its proposal lies past `k`'s decision round,
`slotRound k + 2`, matching M4's `r + 3` hypothesis. Under a schedule
whose consecutive slots are three rounds apart, every later slot is
eligible (`eligibleAt_of_lt_of_spacing`). -/

/-- Direct commit, as judged from a single view: the view holds
certificates for `L` from a quorum of distinct validators. -/
abbrev DirectCommitIn (U : BlockUniverse Validator BlockId Payload)
    (V : View Validator BlockId Payload U) (L : BlockId) (r : ℕ) : Prop :=
  certCommit IsVote (quorumCard Validator) (quorumCard Validator) 2 U V L r

/-- Direct skip, as judged from a single view: the view holds blocks at
the round above `L` that omit it, from a quorum of distinct validators. -/
abbrev DirectSkipIn (U : BlockUniverse Validator BlockId Payload)
    (V : View Validator BlockId Payload U) (L : BlockId) (r : ℕ) : Prop :=
  HoldsAtLeast U V (quorumCard Validator) (omissionsOf U L (r + 1))

omit S in
/-- **A view can only under-report.** A view-relative direct commit is a
genuine one, which is what lets Stage A's universe-level theorems apply
to a validator's local judgement unchanged. -/
theorem directCommit_of_directCommitIn {V : View Validator BlockId Payload U}
    {L : BlockId} {r : ℕ} (h : DirectCommitIn U V L r) : DirectCommit U L r := h.le

omit S in
theorem directSkip_of_directSkipIn {V : View Validator BlockId Payload U}
    {L : BlockId} {r : ℕ} (h : DirectSkipIn U V L r) : DirectSkip U L r := h.le

/-! ### The slot-level skip

A blame is the absence of any candidate from a voting-round block
(`slotBlamers`). -/

/-- **The slot is directly skipped, as judged from a view**: a quorum of
distinct validators holds a voting-round block, in view, that
references no candidate of the slot. Strictly stronger than the
per-candidate `DirectSkipIn`, which it implies. -/
abbrev DirectSkipSlotIn (U : BlockUniverse Validator BlockId Payload)
    (V : View Validator BlockId Payload U) (k : ℕ) : Prop :=
  blameSkip (quorumCard Validator) U V k

/-- **The slot-level skip implies the per-candidate one.** -/
theorem directSkipIn_of_directSkipSlotIn {V : View Validator BlockId Payload U} {k : ℕ}
    (h : DirectSkipSlotIn U V k) {L : BlockId} (hL : IsLeaderBlock U k L) :
    DirectSkipIn U V L (S.slotRound k) :=
  h.of_subset (slotBlamers_subset_omissionsOf hL)

/-- **A slot with no candidate is blamed by every voting-round block**,
so the skip reduces to a quorum being present at that round. -/
theorem directSkipSlotIn_of_no_candidate {V : View Validator BlockId Payload U} {k : ℕ}
    (hnone : ∀ L, ¬ IsLeaderBlock U k L)
    (hq : HoldsAtLeast U V (quorumCard Validator) (blocksAt U (S.slotRound k + 1))) :
    DirectSkipSlotIn U V k := by
  show HoldsAtLeast U V _ (slotBlamers U k)
  rwa [slotBlamers_of_no_candidate hnone]

/-! ### The decision relation

`Decided U V k v` — a validator holding `V` has settled slot `k`, `v`
naming the committed block or `none` for a skip — is the anchored
relation at the core's data: wavelength two, the certificate-quorum
direct commit, the slot-level direct skip, and one rung of link with no
tie, since two certificates at one slot name the same candidate (M5′). -/

omit S in
/-- **The core as an anchored rule.** -/
def coreAnchored (Validator BlockId Payload : Type*) [Fintype Validator]
    [DecidableEq Validator] [Faults Validator] [DecidableEq BlockId] :
    AnchoredRule Validator BlockId Payload ValidWrt Correct where
  wave := 2
  Commit := fun U V L r => DirectCommitIn U V L r
  decCommit := fun _ _ _ _ => inferInstance
  Skip := fun U V S k => DirectSkipSlotIn (S := S) U V k
  rungs := 1
  Link := fun _ U A L S k => CertifiedIn U A L (S.slotRound k)
  tie := fun _ _ _ => False

omit S in
@[simp] theorem coreAnchored_wave :
    (coreAnchored Validator BlockId Payload).wave = 2 := rfl
omit S in
@[simp] theorem coreAnchored_rungs :
    (coreAnchored Validator BlockId Payload).rungs = 1 := rfl

instance {V : View Validator BlockId Payload U} (L : BlockId) (r : ℕ) :
    Decidable ((coreAnchored Validator BlockId Payload).Commit U V L r) :=
  inferInstanceAs (Decidable (DirectCommitIn U V L r))

instance {V : View Validator BlockId Payload U} (k : ℕ) :
    Decidable ((coreAnchored Validator BlockId Payload).Skip U V S k) :=
  inferInstanceAs (Decidable (DirectSkipSlotIn (S := S) U V k))

/-- **The decision relation**: the anchored relation at the core's data. -/
abbrev Decided (U : BlockUniverse Validator BlockId Payload) (V : View Validator BlockId Payload U) :
    ℕ → Option BlockId → Prop :=
  (coreAnchored Validator BlockId Payload).Decided (S := S) U V

namespace Decided
export AnchoredRule.Decided (directCommit directSkip indirectCommit indirectSkip)
end Decided

/-! ## Stage C2 — the direct rules, lifted to views

Corollaries of Stage A composed with monotonicity: a view can only
under-report, so its verdicts are genuine universe-level ones. -/

/-- Cross-view M1: one validator cannot directly commit what another
directly skips. -/
theorem not_directSkipIn_of_directCommitIn {V₁ V₂ : View Validator BlockId Payload U}
    {L : BlockId} {r : ℕ} (h₁ : DirectCommitIn U V₁ L r) (h₂ : DirectSkipIn U V₂ L r) :
    False :=
  not_directCommit_of_directSkip (directSkip_of_directSkipIn h₂)
    (directCommit_of_directCommitIn h₁)

/-- Cross-view M5: two validators cannot directly commit *different* blocks
for one slot. Both candidates are authored by `leader k`, which is the
same-creator hypothesis M5 needs. -/
theorem eq_of_directCommitIn {V₁ V₂ : View Validator BlockId Payload U}
    {k : ℕ} {L₁ L₂ : BlockId}
    (hL₁ : IsLeaderBlock U k L₁) (hL₂ : IsLeaderBlock U k L₂)
    (h₁ : DirectCommitIn U V₁ L₁ (S.slotRound k))
    (h₂ : DirectCommitIn U V₂ L₂ (S.slotRound k)) :
    L₁ = L₂ :=
  eq_of_directCommit_of_creator_eq (directCommit_of_directCommitIn h₁)
    (directCommit_of_directCommitIn h₂) (by rw [hL₁.2.2, hL₂.2.2])

/-- **The engine of M6.** A direct commit made in any view is visible
from every later eligible slot's leader block, so a validator that
missed it recovers it indirectly. -/
theorem certifiedIn_of_directCommitIn {V : View Validator BlockId Payload U}
    {k j : ℕ} {L A : BlockId}
    (h : DirectCommitIn U V L (S.slotRound k))
    (hA : A ∈ U.ids) (hAr : (U.block A).round = S.slotRound j)
    (helig : EligibleAt (S := S) 2 k j) :
    CertifiedIn U A L (S.slotRound k) := by
  refine certifiedIn_of_directCommit (directCommit_of_directCommitIn h) hA ?_
  rw [eligibleAt_iff] at helig
  omega

omit S in
/-- A direct skip made in any view is invisible from every anchor — no round
hypothesis needed, since M3 rules the certificate out universe-wide. -/
theorem not_certifiedIn_of_directSkipIn {V : View Validator BlockId Payload U}
    {L : BlockId} {r : ℕ} (h : DirectSkipIn U V L r) {A : BlockId} :
    ¬ CertifiedIn U A L r :=
  not_certifiedIn_of_directSkip (directSkip_of_directSkipIn h)

/-- **Direct decisions agree across views.** If one validator directly
commits a slot, no other validator can directly skip it — the argument
here being exactly the premise of `Decided.directSkip`. -/
theorem not_directSkip_of_directCommitIn {V₁ V₂ : View Validator BlockId Payload U}
    {k : ℕ} {L : BlockId} (hL : IsLeaderBlock U k L)
    (h₁ : DirectCommitIn U V₁ L (S.slotRound k))
    (h₂ : DirectSkipSlotIn U V₂ k) :
    False :=
  not_directSkipIn_of_directCommitIn h₁ (directSkipIn_of_directSkipSlotIn h₂ hL)

/-! ### Schedule congruence

The slot-level skip reads the schedule only at its own slot. -/

/-! ## Stage C3 — agreement

M6 is the relation's `decided_unique` at `coreLaws`: every
commit-versus-commit case by M5′, the direct-versus-indirect crossings
by cross-view M1, the visibility lemma and M3, and indirect-versus-indirect
by comparing the two anchors. -/

/-- Two commits for one slot agree, however each was reached. Both routes
yield a certificate, so this is M5′ with the plumbing done. -/
theorem eq_of_hasCertificate {k : ℕ} {L₁ L₂ : BlockId}
    (hL₁ : IsLeaderBlock U k L₁) (hL₂ : IsLeaderBlock U k L₂)
    (h₁ : (certificates U L₁ (S.slotRound k)).Nonempty)
    (h₂ : (certificates U L₂ (S.slotRound k)).Nonempty) :
    L₁ = L₂ :=
  eq_of_certificates_nonempty h₁ h₂ (by rw [hL₁.2.2, hL₂.2.2])

omit S in
/-- **The core's laws.** Every commit-against-commit case is certificate
uniqueness; the crossings are M1, the visibility lemma and M3. -/
theorem coreLaws : (coreAnchored Validator BlockId Payload).Laws where
  commit_unique := fun _ hL₁ hL₂ h₁ h₂ => eq_of_directCommitIn hL₁ hL₂ h₁ h₂
  commit_skip := fun _ hL h hskip => not_directSkip_of_directCommitIn hL h hskip
  commit_link := fun _ _ h hA helig => ⟨0, Nat.one_pos,
    certifiedIn_of_directCommitIn h hA.1 hA.2.1 helig⟩
  commit_link_unique := by
    intro S U V k j i L₁ L₂ A _ hL₁ hL₂ h _ _ _ _ hlink _
    exact eq_of_hasCertificate hL₁ hL₂
      (certificates_nonempty_of_directCommit (directCommit_of_directCommitIn h))
      (certificates_nonempty_of_certifiedIn hlink)
  skip_link := fun _ hskip hL _ =>
    not_certifiedIn_of_directSkipIn (directSkipIn_of_directSkipSlotIn hskip hL)
  link_unique := by
    intro S U k j i L₁ L₂ A _ hL₁ hL₂ _ _ _ _ hl₁ hl₂ _ _
    exact eq_of_hasCertificate hL₁ hL₂ (certificates_nonempty_of_certifiedIn hl₁)
      (certificates_nonempty_of_certifiedIn hl₂)
  commit_mono := fun _ hsub h => HoldsAtLeast.mono hsub h
  skip_mono := fun _ hsub h => HoldsAtLeast.mono hsub h
  skip_congr := fun _ hround hk h => blameSkip_congr hround hk h
  link_congr := (coreAnchored Validator BlockId Payload).linkCongr_of_round
    (fun _ U A L r => CertifiedIn U A L r) fun _ _ _ _ _ _ => rfl

omit S in
/-- No tie: any certified candidate is the rung's choice. -/
theorem exists_least {S : Slots Validator} {U : BlockUniverse Validator BlockId Payload}
    {A : BlockId} {i k : ℕ} (_ : i < (coreAnchored Validator BlockId Payload).rungs)
    (h : ∃ L, IsLeaderBlock (S := S) U k L ∧
      (coreAnchored Validator BlockId Payload).Link i U A L S k) :
    ∃ L, IsLeaderBlock (S := S) U k L ∧
      (coreAnchored Validator BlockId Payload).Link i U A L S k ∧
      (coreAnchored Validator BlockId Payload).Least (S := S) U A i k L :=
  let ⟨L, hL, hl⟩ := h
  ⟨L, hL, hl, fun _ _ _ h => h⟩

/-! M7–M9 (the committed-leader sequence and the ledger) are the
relation's `commitSeq_agree`, `ledgerSet_agree` and `outputAt_agree` at
`coreLaws`. -/

end LeanDag
