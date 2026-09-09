import LeanDag.Integration.BarnacleFrame
import LeanDag.Integration.AdaptiveFrame
/-!
# A run of both mechanisms

`CompRun` carries Barnacle's configuration data and a frame, with one
slot numbering throughout: anchors are global slot indices and `cnt_eq`
is the bridge, a round of configuration `k` being `count k` slots wide.

`anchor_below` is `Params.gap`'s purpose, read at the run's own frame:
the anchor that sets a count lies two epochs below every round that count
governs. `cnt_det` and `anchor_det` are the two determinisms the
composition's safety argument needs — the widths from the configurations,
and the anchor from the verdicts.

What is not here is their assembly into
`Integration.frameRun_agree`'s `hwd`; `docs/adaptive-rounds.md` §6.2
records what that still asks for.

**Trusted core: `CompRun` is a definition.**
-/

namespace LeanDag
namespace Integration
open Barnacle Properties

variable {Validator : Type} [Fintype Validator] [DecidableEq Validator]
variable {BlockId : Type} [DecidableEq BlockId] {Payload : Type}
variable {R : Properties.DagRule Validator BlockId Payload} {P : Params}

/-- **A run of both mechanisms.** Barnacle's configuration data, and the
frame and verdicts of `FrameRun`. `cnt` is the frame's widths and
`cnt_eq` is the bridge: a round of configuration `k` is `count k` slots
wide. Anchors are global slot indices, so there is one numbering
throughout. -/
structure CompRun (W : ℕ) (P : Params)
    (upd : ℕ → ℕ → (U : R.Universe) → R.View U → BlockId → ℕ × ℕ)
    (U : R.Universe) (V : R.View U) (K : ℕ) where
  /-- The round after which configuration `k` is in force. -/
  start : ℕ → ℕ
  /-- Its leader count, back-off, and the global slot of its anchor. -/
  count : ℕ → ℕ
  backoff : ℕ → ℕ
  anchor : ℕ → ℕ
  /-- The schedule's round widths. -/
  F : Frame
  /-- The global verdicts. -/
  vdct : ℕ → Option BlockId
  init : start 0 = 0 ∧ count 0 = 1 ∧ backoff 0 = 0
  count_pos : ∀ k, 0 < count k
  /-- **A round of a configuration is that configuration's count wide.**
  Round `0` precedes every range and is genesis, at one leader. -/
  cnt_zero : F.width 0 = 1
  cnt_eq : ∀ k, k < K → ∀ r, start k < r → r ≤ start (k + 1) → F.width r = count k
  /-- The anchor is committed past the threshold, and least such. -/
  anchor_commits : ∀ k, k < K → (∃ A, vdct (anchor k) = some A) ∧
    start k + P.interval < F.roundOf (anchor k)
  anchor_least : ∀ k, k < K → ∀ g, g < anchor k →
    start k + P.interval < F.roundOf g → vdct g = none
  /-- The next configuration begins `P.gap` rounds after the anchor's. -/
  start_succ : ∀ k, k < K → start (k + 1) = F.roundOf (anchor k) + P.gap
  /-- The next configuration is the rule's, at the anchor's block. -/
  update : ∀ k, k < K → ∀ A, vdct (anchor k) = some A →
    (count (k + 1), backoff (k + 1)) = upd (count k) (backoff k) U V A

namespace CompRun

variable {W : ℕ} {upd : ℕ → ℕ → (U : R.Universe) → R.View U → BlockId → ℕ × ℕ}
variable {U : R.Universe} {V : R.View U} {K : ℕ}

theorem start_lt (Rn : CompRun (R := R) W P upd U V K) (k : ℕ) (hk : k < K) :
    Rn.start k < Rn.start (k + 1) := by
  obtain ⟨-, hthr⟩ := Rn.anchor_commits k hk
  rw [Rn.start_succ k hk]
  have := P.interval_pos
  exact lt_of_lt_of_le (by omega) (Nat.le_add_right _ _)

/-- **The anchor of an earlier configuration is two epochs below.** The
run's own frame, read through `anchor_two_epochs_below`'s counting. -/
theorem anchor_below (Rn : CompRun (R := R) W P upd U V K) (hW : 0 < W)
    (hgap : P.gap = 2 * W) {k : ℕ} (hk : k < K) {r : ℕ} (hr : Rn.start (k + 1) < r) :
    epochOf W (Rn.anchor k) + 2 ≤ epochOf W (Rn.F.cum r) := by
  have hstart : Rn.start (k + 1) = Rn.F.roundOf (Rn.anchor k) + P.gap :=
    Rn.start_succ k hk
  have hglt : Rn.anchor k < Rn.F.cum (Rn.F.roundOf (Rn.anchor k) + 1) :=
    Rn.F.lt_cum_roundOf_succ _
  have hgapr : Rn.F.cum (Rn.F.roundOf (Rn.anchor k) + 1) + P.gap
      ≤ Rn.F.cum (Rn.start (k + 1) + 1) := Rn.F.cum_gap (by omega)
  have hmono : Rn.F.cum (Rn.start (k + 1) + 1) ≤ Rn.F.cum r :=
    Rn.F.cum_mono (by omega)
  exact epochOf_add_two hW (by omega)


/-- Every round a run covers lies in one configuration's range. -/
theorem exists_cfg (Rn : CompRun (R := R) W P upd U V K) {k r : ℕ} (hk : k < K)
    (hr : 0 < r) (hrk : r ≤ Rn.start (k + 1)) :
    ∃ j, j ≤ k ∧ Rn.start j < r ∧ r ≤ Rn.start (j + 1) := by
  induction k with
  | zero => exact ⟨0, le_refl _, by rw [Rn.init.1]; omega, hrk⟩
  | succ i ih =>
      by_cases h : r ≤ Rn.start (i + 1)
      · obtain ⟨j, hj, h1, h2⟩ := ih (by omega) h
        exact ⟨j, by omega, h1, h2⟩
      · exact ⟨i + 1, le_refl _, by omega, hrk⟩

/-- **Agreeing configurations give agreeing widths**, at every round the
runs cover. -/
theorem cnt_det {Rn Rn' : CompRun (R := R) W P upd U V K} {k : ℕ} (hk : k < K)
    (h : ∀ j, j ≤ k + 1 → Rn.start j = Rn'.start j ∧ Rn.count j = Rn'.count j)
    {r : ℕ} (hrk : r ≤ Rn.start (k + 1)) : Rn.F.width r = Rn'.F.width r := by
  rcases Nat.eq_zero_or_pos r with h0 | h0
  · subst h0; rw [Rn.cnt_zero, Rn'.cnt_zero]
  · obtain ⟨j, hj, h1, h2⟩ := Rn.exists_cfg hk h0 hrk
    obtain ⟨hs, hc⟩ := h j (by omega)
    have hs1 : Rn.start (j + 1) = Rn'.start (j + 1) := (h (j + 1) (by omega)).1
    rw [Rn.cnt_eq j (by omega) r h1 h2, Rn'.cnt_eq j (by omega) r (by omega) (by omega), hc]


/-- **The anchor is a function of the verdicts.** Both runs' anchors are
the least committed slot past the same threshold, and a set has one least
element. The widths must agree far enough for the two to mean the same by
"past the threshold", which is what `hcnt` supplies. -/
theorem anchor_det {Rn Rn' : CompRun (R := R) W P upd U V K} {k : ℕ} (hk : k < K)
    (hs : Rn.start k = Rn'.start k)
    (hcnt : ∀ r, r < Rn.start (k + 1) + 1 → Rn'.F.width r = Rn.F.width r)
    (hs1 : Rn.start (k + 1) = Rn'.start (k + 1))
    (hv : ∀ g, Rn.vdct g = Rn'.vdct g) : Rn.anchor k = Rn'.anchor k := by
  obtain ⟨⟨A, hA⟩, hthr⟩ := Rn.anchor_commits k hk
  obtain ⟨⟨A', hA'⟩, hthr'⟩ := Rn'.anchor_commits k hk
  -- the anchors' rounds are below the next configuration's start
  have hr : Rn.F.roundOf (Rn.anchor k) < Rn.start (k + 1) + 1 := by
    have := Rn.start_succ k hk; omega
  have hr' : Rn'.F.roundOf (Rn'.anchor k) < Rn.start (k + 1) + 1 := by
    have := Rn'.start_succ k hk; omega
  rcases Nat.lt_trichotomy (Rn.anchor k) (Rn'.anchor k) with hlt | heq | hgt
  · exfalso
    have hro : Rn'.F.roundOf (Rn.anchor k) = Rn.F.roundOf (Rn.anchor k) :=
      Frame.roundOf_congr (F := Rn.F) (F' := Rn'.F) hcnt hr
    have hno := Rn'.anchor_least k hk (Rn.anchor k) hlt (by rw [hro, ← hs]; exact hthr)
    rw [← hv (Rn.anchor k)] at hno
    exact absurd (hno ▸ hA) (by simp)
  · exact heq
  · exfalso
    have hrg : Rn.F.roundOf (Rn'.anchor k) < Rn.start (k + 1) + 1 :=
      lt_of_le_of_lt (Rn.F.roundOf_mono (le_of_lt hgt)) hr
    have hro : Rn'.F.roundOf (Rn'.anchor k) = Rn.F.roundOf (Rn'.anchor k) :=
      Frame.roundOf_congr (F := Rn.F) (F' := Rn'.F) hcnt hrg
    have hno := Rn.anchor_least k hk (Rn'.anchor k) hgt (by rw [← hro, hs]; exact hthr')
    rw [hv (Rn'.anchor k)] at hno
    exact absurd (hno ▸ hA') (by simp)

end CompRun
end Integration
end LeanDag
