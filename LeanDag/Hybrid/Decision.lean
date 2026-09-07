import LeanDag.Hybrid.Rules
import LeanDag.Common.Anchored.Bounded
/-!
# The hybrid decision relation

The Odontoceti decision layer at the hybrid thresholds: the anchored
relation (`Anchored.lean`) at wavelength one, the view-relative direct
rules at `q`, and one rung of link, `ThickLink` at the indirect
threshold `k`, with the least linked candidate committed — retained
unchanged, since a *Byzantine* leader can still plant two passing
candidates in one anchor's cone, and nothing about the crash class
closes that gap.

The laws hold under `HonestNoEquiv` and an admissible `k`: `hybridLaws`
threads both, and agreement (H6) is the relation's at them. The relation
itself is a definition and carries neither.
-/

namespace LeanDag

namespace Hybrid

variable {Validator : Type} [Fintype Validator] [DecidableEq Validator]
variable [H : HybridFaults Validator]
variable {BlockId : Type} [LinearOrder BlockId] {Payload : Type}
variable {U : BlockUniverse Validator BlockId Payload}
variable [S : Slots Validator]
variable {L A : BlockId} {r k : ℕ}

/-! ## The view-relative direct rules -/

/-- Direct commit, as judged from a single view: the view holds votes for
`L` at the round above it from a hybrid quorum of validators. -/
abbrev DirectCommitIn (U : BlockUniverse Validator BlockId Payload)
    (V : View Validator BlockId Payload U) (L : BlockId) (r : ℕ) : Prop :=
  HoldsAtLeast U V (q Validator) (votesFor U L (r + 1))

/-- Direct skip, as judged from a single view: the view holds blocks at
the round above `L` that omit it, from a hybrid quorum of validators. -/
abbrev DirectSkipIn (U : BlockUniverse Validator BlockId Payload)
    (V : View Validator BlockId Payload U) (L : BlockId) (r : ℕ) : Prop :=
  HoldsAtLeast U V (q Validator) (omissionsOf U L (r + 1))

/-! The voting-round blocks that reference no candidate of the slot are
the core's `slotBlamers`: the same set, over the same `IsLeaderBlock`. -/

/-- **The slot is directly skipped, as judged from a view**: a hybrid
quorum of distinct validators holds a voting-round block, in view, that
references no candidate of the slot.

Strictly stronger than the per-candidate `DirectSkipIn`, which it
implies and which a slot with no candidate satisfies for nothing. The
core and Odontoceti were repaired the same way and for the same reason
(`docs/target-properties.md` §3.2): a rule whose skip quantifies over
the candidates that happen to exist is not invariant under a mechanism
that adds one, so it cannot be `Banded`. -/
abbrev DirectSkipSlotIn (U : BlockUniverse Validator BlockId Payload)
    (V : View Validator BlockId Payload U) (s : ℕ) : Prop :=
  HoldsAtLeast U V (q Validator) (slotBlamers U s)

/-- **The slot-level skip implies the per-candidate one**, so every
theorem stated over `DirectSkipIn` — H3 in particular — applies to it
unchanged. A block referencing no candidate references not `L`. -/
theorem directSkipIn_of_directSkipSlotIn {V : View Validator BlockId Payload U} {s : ℕ}
    (h : DirectSkipSlotIn U V s) {L : BlockId} (hL : IsLeaderBlock U s L) :
    DirectSkipIn U V L (S.slotRound s) :=
  h.of_subset (slotBlamers_subset_omissionsOf hL)

/-- A view can only under-report: its direct commit is genuine. -/
theorem directCommit_of_directCommitIn
    {V : View Validator BlockId Payload U}
    (h : DirectCommitIn U V L r) : DirectCommit U L r :=
  le_trans h (Finset.card_le_card
    (Finset.image_subset_image Finset.inter_subset_left))

/-- A view can only under-report: its direct skip is genuine. -/
theorem directSkip_of_directSkipIn
    {V : View Validator BlockId Payload U}
    (h : DirectSkipIn U V L r) : DirectSkip U L r :=
  le_trans h (Finset.card_le_card
    (Finset.image_subset_image Finset.inter_subset_left))

/-! ## The safety lemmas, lifted to views -/

/-- Cross-view H2: one validator cannot directly commit what another
directly skips. -/
theorem not_directSkipIn_of_directCommitIn (hne : HonestNoEquiv U)
    {V₁ V₂ : View Validator BlockId Payload U}
    (h₁ : DirectCommitIn U V₁ L r) (h₂ : DirectSkipIn U V₂ L r) : False :=
  not_directSkip_of_directCommit hne
    (directCommit_of_directCommitIn h₁) (directSkip_of_directSkipIn h₂)

/-- Cross-view twin uniqueness: two direct commits for one slot agree. -/
theorem eq_of_directCommitIn (hne : HonestNoEquiv U)
    {V₁ V₂ : View Validator BlockId Payload U}
    {k : ℕ} {L₁ L₂ : BlockId}
    (hL₁ : IsLeaderBlock U k L₁) (hL₂ : IsLeaderBlock U k L₂)
    (h₁ : DirectCommitIn U V₁ L₁ r) (h₂ : DirectCommitIn U V₂ L₂ r) :
    L₁ = L₂ :=
  eq_of_directCommit hne (directCommit_of_directCommitIn h₁)
    (directCommit_of_directCommitIn h₂) (by rw [hL₁.2.2, hL₂.2.2])

/-- H4, from a view: a view-level direct commit passes the indirect
test at every block two rounds up. -/
theorem thickLink_of_directCommitIn (hne : HonestNoEquiv U)
    (hkb : k + 3 * H.fb + 2 * H.fc ≤ Fintype.card Validator)
    {V : View Validator BlockId Payload U}
    (h : DirectCommitIn U V L r) (hA : A ∈ U.ids)
    (hround : r + 2 ≤ (U.block A).round) : ThickLink k U A L r :=
  thickLink_of_directCommit hne hkb (directCommit_of_directCommitIn h)
    hA hround

/-- H3, from a view: a view-level direct skip fails the indirect test
everywhere. -/
theorem not_thickLink_of_directSkipIn (hne : HonestNoEquiv U)
    (hka : 2 * H.fb + H.fc + 1 ≤ k)
    {V : View Validator BlockId Payload U}
    (h : DirectSkipIn U V L r) (A : BlockId) : ¬ ThickLink k U A L r :=
  not_thickLink_of_directSkip hne hka (directSkip_of_directSkipIn h) A

/-- H5, from a view: a view-level direct commit is the only same-slot
candidate that can pass the indirect test, at any anchor. -/
theorem eq_of_directCommitIn_of_thickLink (hne : HonestNoEquiv U)
    (hka : 2 * H.fb + H.fc + 1 ≤ k)
    {V : View Validator BlockId Payload U} {j : ℕ} {L₁ L₂ : BlockId}
    (hL₁ : IsLeaderBlock U j L₁) (hL₂ : IsLeaderBlock U j L₂)
    (h₁ : DirectCommitIn U V L₁ r) (ht : ThickLink k U A L₂ r) : L₁ = L₂ :=
  eq_of_directCommit_of_thickLink hne hka
    (directCommit_of_directCommitIn h₁) ht (by rw [hL₁.2.2, hL₂.2.2])

omit S in
/-- The slot-level skip reads the schedule only at its own slot. -/
theorem directSkipSlotIn_congr {S₁ S₂ : Slots Validator}
    {V : View Validator BlockId Payload U} {s : ℕ}
    (hround : S₁.slotRound s = S₂.slotRound s) (hk : S₁.leader s = S₂.leader s)
    (h : DirectSkipSlotIn (S := S₁) U V s) : DirectSkipSlotIn (S := S₂) U V s := by
  show HoldsAtLeast U V _ (slotBlamers (S := S₂) U s)
  rwa [← slotBlamers_congr hround hk]

/-! ## The relation -/

omit S in
/-- **Hybrid as an anchored rule**, one per indirect threshold. -/
def hybridAnchored (Validator BlockId Payload : Type) [Fintype Validator]
    [DecidableEq Validator] [HybridFaults Validator] [LinearOrder BlockId] (k : ℕ) :
    AnchoredRule Validator BlockId Payload ValidWrt Correct where
  wave := 1
  Commit := fun U V L r => Hybrid.DirectCommitIn U V L r
  Skip := fun U V S s => Hybrid.DirectSkipSlotIn (S := S) U V s
  rungs := 1
  Link := fun _ U A L S s => ThickLink k U A L (S.slotRound s)
  tie := fun _ L L' => L < L'

omit S in
@[simp] theorem hybridAnchored_wave (k : ℕ) :
    (hybridAnchored Validator BlockId Payload k).wave = 1 := rfl
omit S in
@[simp] theorem hybridAnchored_rungs (k : ℕ) :
    (hybridAnchored Validator BlockId Payload k).rungs = 1 := rfl

instance {V : View Validator BlockId Payload U} (k : ℕ) (L : BlockId) (r : ℕ) :
    Decidable ((hybridAnchored Validator BlockId Payload k).Commit U V L r) :=
  inferInstanceAs (Decidable (Hybrid.DirectCommitIn U V L r))

instance {V : View Validator BlockId Payload U} (k s : ℕ) :
    Decidable ((hybridAnchored Validator BlockId Payload k).Skip U V S s) :=
  inferInstanceAs (Decidable (Hybrid.DirectSkipSlotIn (S := S) U V s))

instance (k i : ℕ) (A L : BlockId) (S : Slots Validator) (s : ℕ) :
    Decidable ((hybridAnchored Validator BlockId Payload k).Link i U A L S s) :=
  inferInstanceAs (Decidable (ThickLink k U A L (S.slotRound s)))

/-- **The decision relation** at threshold `k`: the anchored relation at
Hybrid's data. -/
abbrev Decided (k : ℕ) (U : BlockUniverse Validator BlockId Payload)
    (V : View Validator BlockId Payload U) : ℕ → Option BlockId → Prop :=
  (hybridAnchored Validator BlockId Payload k).Decided (S := S) U V

namespace Decided
export AnchoredRule.Decided (directCommit directSkip indirectCommit indirectSkip)
end Decided

omit S in
/-- The rung reads the schedule only at its slot's round. -/
theorem linkCongr {k : ℕ} : (hybridAnchored Validator BlockId Payload k).LinkCongr :=
  fun hround _ h => by
    change ThickLink _ _ _ _ _ at h ⊢
    rwa [← hround]

omit S in
/-- **Hybrid's laws**, under `HonestNoEquiv` at an admissible threshold:
the direct/direct cases by H2 and twin uniqueness, the crossings by
H3/H4/H5, and two tie-break choices equal by antisymmetry. -/
theorem hybridLaws {k : ℕ} (hk : Admissible Validator k) :
    (hybridAnchored Validator BlockId Payload k).Laws (fun _ => HonestNoEquiv) where
  commit_unique := fun hne hL₁ hL₂ h₁ h₂ => eq_of_directCommitIn hne hL₁ hL₂ h₁ h₂
  commit_skip := fun hne hL h hskip =>
    not_directSkipIn_of_directCommitIn hne h (directSkipIn_of_directSkipSlotIn hskip hL)
  commit_link := fun hne _ h hA helig => ⟨0, Nat.one_pos,
    thickLink_of_directCommitIn hne hk.2 h hA.1 (by
      have := (hybridAnchored Validator BlockId Payload k).anchor_round_le hA helig
      simp only [hybridAnchored_wave] at this; omega)⟩
  commit_link_unique := by
    intro S U V k j i L₁ L₂ A hne hL₁ hL₂ h _ _ _ _ hlink _
    exact eq_of_directCommitIn_of_thickLink hne hk.1 hL₁ hL₂ h hlink
  skip_link := fun hne hskip hL _ =>
    not_thickLink_of_directSkipIn hne hk.1 (directSkipIn_of_directSkipSlotIn hskip hL) _
  link_unique := by
    intro S U k j i L₁ L₂ A _ hL₁ hL₂ _ _ _ _ hl₁ hl₂ hm₁ hm₂
    exact le_antisymm (not_lt.mp (show ¬ L₂ < L₁ from hm₁ L₂ hL₂ hl₂))
      (not_lt.mp (show ¬ L₁ < L₂ from hm₂ L₁ hL₁ hl₁))
  commit_mono := fun _ hsub h => HoldsAtLeast.mono hsub h
  skip_mono := fun _ hsub h => HoldsAtLeast.mono hsub h
  skip_congr := fun _ hround hk h => directSkipSlotIn_congr hround hk h
  link_congr := linkCongr

omit S in
/-- The rung's tie is the order, so a nonempty rung has a least
candidate. -/
theorem exists_least {S : Slots Validator} {U : BlockUniverse Validator BlockId Payload}
    {A : BlockId} {k i s : ℕ} (_ : i < (hybridAnchored Validator BlockId Payload k).rungs)
    (h : ∃ L, IsLeaderBlock (S := S) U s L ∧
      (hybridAnchored Validator BlockId Payload k).Link i U A L S s) :
    ∃ L, IsLeaderBlock (S := S) U s L ∧
      (hybridAnchored Validator BlockId Payload k).Link i U A L S s ∧
      (hybridAnchored Validator BlockId Payload k).Least (S := S) U A i s L :=
  AnchoredRule.exists_least_of_lt (fun _ _ => Iff.rfl) h

end Hybrid

end LeanDag
