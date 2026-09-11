import LeanDag.Nemo.Rules
import LeanDag.Common.Anchored.Band
import LeanDag.Common.Rules
/-!
# Nemo: the decision relation

Nemo decides as every leader-based rule of this development does: the
anchored relation (`Anchored.lean`) at Nemo's data — wavelength one, the
majority direct commit, no direct skip, and one rung of link, a vote in
the anchor's cone. Agreement, monotonicity, the ledger and the band are
the relation's; what Nemo proves is `nemoLaws`, and every one of its
cases closes by candidate uniqueness, the crash simplification that
retires the Byzantine arcs' twin machinery: universal `no_equivocation`
identifies two blocks sharing a slot's round and leader before any
question of commitment arises.
-/

namespace LeanDag

namespace Nemo

variable {Validator : Type} [Fintype Validator] [DecidableEq Validator]
variable {BlockId : Type} [DecidableEq BlockId] {Payload : Type}
variable {U : Universe Validator BlockId Payload}
variable [S : Slots Validator]

omit [DecidableEq BlockId] in
/-! ## The view-relative direct rule -/

/-- Direct commit, as judged from a single view: the view holds votes for
`L` at the round above it from a majority of validators. -/
abbrev DirectCommitIn (U : Universe Validator BlockId Payload)
    (V : View Validator BlockId Payload U) (L : BlockId) (r : ℕ) : Prop :=
  supportCommit (majority Validator) U V L r

omit S in
/-- A view can only under-report: its direct commit is genuine. -/
theorem directCommit_of_directCommitIn
    {V : View Validator BlockId Payload U} {L : BlockId} {r : ℕ}
    (h : DirectCommitIn U V L r) : DirectCommit U L r := h.le

/-! ## The relation -/

omit S in
/-- **Nemo as an anchored rule.** Wavelength one, the majority direct
commit, no direct skip — the implementation pins its quorum to the full
stake, so skips only ever arrive via an anchor — and one rung, a vote in
the anchor's cone, with no tie to break since a slot has one candidate. -/
def nemoAnchored (Validator BlockId Payload : Type) [Fintype Validator] [DecidableEq Validator]
    [DecidableEq BlockId] : AnchoredRule Validator BlockId Payload ValidWrt Finset.univ where
  waveAt := fun _ => 1
  Commit := fun U V L r => Nemo.DirectCommitIn U V L r
  decCommit := fun _ _ _ _ => inferInstance
  Skip := fun _ _ _ _ => False
  rungs := 1
  Link := fun _ U A L S k => CertifiedIn U A L (S.slotRound k)
  tie := fun _ _ _ => False

omit S in
@[simp] theorem nemoAnchored_waveAt (r : ℕ) :
    (nemoAnchored Validator BlockId Payload).waveAt r = 1 := rfl
omit S in
@[simp] theorem nemoAnchored_rungs : (nemoAnchored Validator BlockId Payload).rungs = 1 := rfl

/-- The rule's direct predicates are decidable, so concrete models can
settle a derivation's premises by `decide`. -/
instance {V : View Validator BlockId Payload U} (L : BlockId) (r : ℕ) :
    Decidable ((nemoAnchored Validator BlockId Payload).Commit U V L r) :=
  inferInstanceAs (Decidable (DirectCommitIn U V L r))

instance {V : View Validator BlockId Payload U} (k : ℕ) :
    Decidable ((nemoAnchored Validator BlockId Payload).Skip U V S k) :=
  inferInstanceAs (Decidable False)

instance (i : ℕ) (A L : BlockId) (S : Slots Validator) (k : ℕ) :
    Decidable ((nemoAnchored Validator BlockId Payload).Link i U A L S k) :=
  inferInstanceAs (Decidable (CertifiedIn U A L (S.slotRound k)))

/-- **The decision relation**: the anchored relation at Nemo's data. -/
abbrev Decided (U : Universe Validator BlockId Payload) (V : View Validator BlockId Payload U) :
    ℕ → Option BlockId → Prop :=
  (nemoAnchored Validator BlockId Payload).Decided (S := S) U V

namespace Decided
export AnchoredRule.Decided (directCommit directSkip indirectCommit indirectSkip)
end Decided

/-- **The visibility lemma.** A view-level direct commit is certified at any
candidate anchor of any eligible slot — the eligibility premise places the
anchor far enough above for link integrity to reach it. -/
theorem certifiedIn_of_directCommitIn_at_anchor
    {V : View Validator BlockId Payload U} {k j : ℕ} {L A : BlockId}
    (h : Nemo.DirectCommitIn U V L (S.slotRound k))
    (hA : IsLeaderBlock U j A) (helig : (nemoAnchored Validator BlockId Payload).Eligible k j) :
    CertifiedIn U A L (S.slotRound k) :=
  certifiedIn_of_directCommit (directCommit_of_directCommitIn h) hA.1
    (by
      have := (nemoAnchored Validator BlockId Payload).anchor_round_le hA helig
      simp only [nemoAnchored_waveAt] at this; omega)

omit S in
/-- **Nemo's laws**, every commit-against-commit case by candidate
uniqueness and the crossings by visibility. -/
theorem nemoLaws : (nemoAnchored Validator BlockId Payload).Laws where
  commit_unique := fun _ hL₁ hL₂ _ _ => isLeaderBlock_unique_of_honest (Finset.mem_univ _) hL₁ hL₂
  commit_skip := fun _ _ _ h => h.elim
  commit_link := fun _ _ h hA helig => ⟨0, Nat.one_pos,
    Nemo.certifiedIn_of_directCommitIn_at_anchor (show Nemo.DirectCommitIn _ _ _ _ from h) hA helig⟩
  commit_link_unique := fun _ hL₁ hL₂ _ _ _ _ _ _ _ => isLeaderBlock_unique_of_honest (Finset.mem_univ _) hL₁ hL₂
  skip_link := fun _ h _ _ => h.elim
  link_unique := fun _ hL₁ hL₂ _ _ _ _ _ _ _ _ => isLeaderBlock_unique_of_honest (Finset.mem_univ _) hL₁ hL₂
  commit_mono := fun _ hsub h => HoldsAtLeast.mono hsub h
  skip_mono := fun _ _ h => h
  skip_congr := fun _ _ _ h => h
  link_congr := (nemoAnchored Validator BlockId Payload).linkCongr_of_round
    (fun _ U A L r => Nemo.CertifiedIn U A L r) fun _ _ _ _ _ _ => rfl

end Nemo

end LeanDag
