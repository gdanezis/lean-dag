import LeanDag.Steelhead.Model.Chain
import LeanDag.MahiMahi.Helpers.Decision
/-!
# Helpers — the decision layer

Generated lemma infrastructure for `Model/Decision.lean`; not part of the
audit surface. Steelhead's laws are Mahi-Mahi's, each applied at the wave
of the slot the law is about: every law of `AnchoredRule.Laws` speaks of
one slot `k` and its anchors, and at slot `k` the rule *is* Mahi-Mahi's
at wave `w (S.kind k)`, eligibility included.
-/

namespace LeanDag

namespace Steelhead

variable {Validator : Type} [Fintype Validator] [DecidableEq Validator]
variable [F : Faults Validator]
variable {BlockId : Type} [LinearOrder BlockId] {Payload : Type}
variable {U : BlockUniverse Validator BlockId Payload}

@[simp] theorem steelheadAnchored_waveAt (w : ℕ → ℕ) (κ : ℕ) :
    (steelheadAnchored Validator BlockId Payload w).waveAt κ = w κ - 1 := rfl

/-- **The two spellings of the paper's pair agree**: the wavelength of the
kind a periodic schedule assigns a round is the paper's wavelength of
that round. -/
theorem wavelength_periodicKind (ws wa p r : ℕ) :
    wavelength ws wa (periodicKind p r) = periodic ws wa p r := by
  unfold wavelength periodicKind periodic
  by_cases h : r % p = 0 <;> simp [h]

/-- A periodic schedule gives kind `1` to exactly the asynchronous
rounds. -/
theorem periodicKind_eq_one_iff {p r : ℕ} : periodicKind p r = 1 ↔ IsAsync p r := by
  unfold periodicKind IsAsync
  by_cases h : r % p = 0 <;> simp [h]

/-- At period one every round is asynchronous, so a periodic schedule
gives every slot kind `1` and the rule reads `wa` everywhere. -/
theorem periodicKind_one : periodicKind 1 = fun _ => 1 := by
  funext r
  simp [periodicKind, Nat.mod_one]

section Slots

variable [S : Slots Validator]

/-- Steelhead's eligibility at a slot is Mahi-Mahi's at the slot's own
wave. -/
theorem eligible_iff_mahiMahi {w : ℕ → ℕ} {k j : ℕ} :
    (steelheadAnchored Validator BlockId Payload w).Eligible k j ↔
      (MahiMahi.mahiMahiAnchored Validator BlockId Payload (w (S.kind k))).Eligible k j :=
  Iff.rfl

/-- A direct commit at slot `k` is certified in the cone of any candidate
anchor of any slot eligible for `k`, at `k`'s wave. -/
theorem certifiedIn_of_commit_at_anchor {w : ℕ → ℕ} (hw : ∀ κ, 1 ≤ w κ)
    {V : View Validator BlockId Payload U} {k j : ℕ} {L A : BlockId}
    (h : (steelheadAnchored Validator BlockId Payload w).Commit U V L (S.slotRound k) (S.kind k))
    (hA : IsLeaderBlock U j A)
    (helig : (steelheadAnchored Validator BlockId Payload w).Eligible k j) :
    MahiMahi.CertifiedIn U (w (S.kind k)) A L (S.slotRound k) :=
  MahiMahi.certifiedIn_of_directCommitIn_at_anchor (hw _) h hA (eligible_iff_mahiMahi.mp helig)

/-- **SH5b.** At a slot of the asynchronous kind the wavelength is `wa`, and at a slot proposed at
its own round and led by the coin the slot's blame is the chain slot's. -/
theorem direct_agrees_with_chain {ws wa r : ℕ} {coin : ℕ → Validator}
    {V : View Validator BlockId Payload U} {L : BlockId} (hid : S.slotRound r = r)
    (hr : S.kind r = 1) (hlead : S.leader r = coin r) :
    ((steelheadAnchored Validator BlockId Payload (wavelength ws wa)).Commit U V L r (S.kind r) ↔
      (MahiMahi.mahiMahiAnchored Validator BlockId Payload wa).Commit U V L r
        ((chainSlots coin).kind r)) ∧
    ((steelheadAnchored Validator BlockId Payload (wavelength ws wa)).Skip U V S r ↔
      (MahiMahi.mahiMahiAnchored Validator BlockId Payload wa).Skip U V (chainSlots coin) r) := by
  have hw : wavelength ws wa (S.kind r) = wa := by rw [hr]; simp [wavelength]
  constructor
  · change MahiMahi.DirectCommitIn U V (wavelength ws wa (S.kind r)) L r ↔
      MahiMahi.DirectCommitIn U V wa L r
    rw [hw]
  · change MahiMahi.DirectSkipIn U V (wavelength ws wa (S.kind r)) (S.leader r)
      (S.slotRound r) ↔ MahiMahi.DirectSkipIn U V wa (coin r) r
    rw [hid, hw, hlead]

/-! ## Wave three is exactly the core's relation -/

/-- **The core's slot-level blame is a blame of the slot at wave three.** A round-`r` block of
the leader in a voting-round block's cone is one of its references, which the core's blamer
excludes; the two rules agree on what a blame is, so the count transfers verbatim, as it does the
other way in MM1d. -/
theorem directSkipIn_of_core_directSkipSlotIn {V : View Validator BlockId Payload U} {k : ℕ}
    (h : LeanDag.DirectSkipSlotIn U V k) :
    MahiMahi.DirectSkipIn U V 3 (S.leader k) (S.slotRound k) := by
  refine le_trans h (Finset.card_le_card (Finset.image_subset_image ?_))
  intro q hq
  rw [Finset.mem_inter, LeanDag.slotBlamers, Finset.mem_filter] at hq
  rw [MahiMahi.votingRound_three, Finset.mem_inter, Finset.mem_filter]
  obtain ⟨⟨hqb, hqblame⟩, hqV⟩ := hq
  refine ⟨⟨hqb, ?_⟩, hqV⟩
  rw [MahiMahi.Blames, Finset.eq_empty_iff_forall_notMem]
  intro b hb
  obtain ⟨hbid, hbr, hbc, hbh⟩ := MahiMahi.mem_candidatesAt.mp hb
  obtain ⟨hqid, hqr⟩ := mem_blocksAt.mp hqb
  exact hqblame b (mem_refs_of_mem_history_of_round_succ hqid hbh (by rw [hbr, hqr]))
    ⟨hbid, hbr, hbc⟩

/-- **SH4, the converse.** At wave three every derivation of the core's relation is one of
Steelhead's: the mirror of MM1d's `core_decided_of_decided`, with the skip case above. -/
theorem decided_of_core_decided {V : View Validator BlockId Payload U} {k : ℕ}
    {v : Option BlockId} (h : LeanDag.Decided U V k v) : Decided (fun _ => 3) U V k v := by
  induction h with
  | @directCommit k L hL h =>
    exact Decided.directCommit hL ((MahiMahi.directCommitIn_three_iff hL.2.1).mpr h)
  | @directSkip k hskip =>
    exact Decided.directSkip (directSkipIn_of_core_directSkipSlotIn hskip)
  | @indirectCommit k j A L i hkj helig hj hmid _ _ hL hcert _ ihj ihmid =>
    exact AnchoredRule.Decided.indirectCommit_single rfl (fun _ _ h => h) hkj
      (MahiMahi.eligible_three_iff.mpr helig) ihj
      (fun i h1 h2 he => ihmid i h1 h2 (MahiMahi.eligible_three_iff.mp he)) hL
      ((MahiMahi.certifiedIn_three_iff hL.2.1).mpr hcert)
  | @indirectSkip k j A hkj helig hj hmid hnone ihj ihmid =>
    exact AnchoredRule.Decided.indirectSkip_single rfl hkj (MahiMahi.eligible_three_iff.mpr helig)
      ihj (fun i h1 h2 he => ihmid i h1 h2 (MahiMahi.eligible_three_iff.mp he))
      (fun L hL hc => hnone 0 Nat.one_pos L hL ((MahiMahi.certifiedIn_three_iff hL.2.1).mp hc))

omit S in
/-- The rung reads the schedule only through the slot's round and kind. -/
theorem linkCongr {w : ℕ → ℕ} : (steelheadAnchored Validator BlockId Payload w).LinkCongr :=
  AnchoredRule.linkCongr_of_round_kind _
    (fun _ U A L r κ => MahiMahi.CertifiedIn U (w κ) A L r) (fun _ _ _ _ _ _ => rfl)

omit S in
/-- **Steelhead's laws** at a wavelength function of at least two rounds
everywhere: Mahi-Mahi's laws, each at the wave of the slot it concerns. -/
theorem steelheadLaws {w : ℕ → ℕ} (hw : ∀ κ, 2 ≤ w κ) :
    (steelheadAnchored Validator BlockId Payload w).Laws where
  commit_unique := by
    intro S U V₁ V₂ k L₁ L₂ _ hL₁ hL₂ h₁ h₂
    exact MahiMahi.eq_of_directCommitIn (hw _) hL₁ hL₂ h₁ h₂
  commit_skip := by
    intro S U V₁ V₂ k L _ hL h hskip
    exact MahiMahi.not_directSkipIn_of_directCommitIn (hw _) hL h hskip
  commit_link := by
    intro S U V k j L A _ _ h hA helig
    exact ⟨0, Nat.one_pos, certifiedIn_of_commit_at_anchor (fun κ => by have := hw κ; omega)
      h hA helig⟩
  commit_link_unique := by
    intro S U V k j i L₁ L₂ A _ hL₁ hL₂ h _ _ _ _ hlink _
    exact MahiMahi.eq_of_hasCertificate (hw _) hL₁ hL₂
      (MahiMahi.certificates_nonempty_of_directCommit (MahiMahi.directCommit_of_directCommitIn h))
      (MahiMahi.certificates_nonempty_of_certifiedIn hlink)
  skip_link := by
    intro S U V k i L A _ hskip hL _
    exact MahiMahi.not_certifiedIn_of_directSkip (hw _) (MahiMahi.directSkip_of_directSkipIn hskip)
      hL.2.2 hL.2.1
  link_unique := by
    intro S U k j i L₁ L₂ A _ hL₁ hL₂ _ _ _ _ hl₁ hl₂ _ _
    exact MahiMahi.eq_of_hasCertificate (hw _) hL₁ hL₂
      (MahiMahi.certificates_nonempty_of_certifiedIn hl₁)
      (MahiMahi.certificates_nonempty_of_certifiedIn hl₂)
  commit_mono := fun _ hsub h => HoldsAtLeast.mono hsub h
  skip_mono := fun _ hsub h => HoldsAtLeast.mono hsub h
  skip_congr := fun _ hround hlead hkind h => by
    change MahiMahi.DirectSkipIn _ _ _ _ _
    rw [← hround, ← hlead, ← hkind]; exact h
  link_congr := linkCongr

omit S in
/-- No tie: any linked candidate is the rung's choice. -/
theorem exists_least {w : ℕ → ℕ} {S : Slots Validator}
    {U : BlockUniverse Validator BlockId Payload} {A : BlockId} {i k : ℕ}
    (_ : i < (steelheadAnchored Validator BlockId Payload w).rungs)
    (h : ∃ L, IsLeaderBlock (S := S) U k L ∧
      (steelheadAnchored Validator BlockId Payload w).Link i U A L S k) :
    ∃ L, IsLeaderBlock (S := S) U k L ∧
      (steelheadAnchored Validator BlockId Payload w).Link i U A L S k ∧
      (steelheadAnchored Validator BlockId Payload w).Least (S := S) U A i k L :=
  let ⟨L, hL, hl⟩ := h
  ⟨L, hL, hl, fun _ _ _ h => h⟩

end Slots

end Steelhead

end LeanDag
