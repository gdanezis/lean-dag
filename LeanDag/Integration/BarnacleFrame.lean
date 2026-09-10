import LeanDag.Barnacle.Helpers.Frame
import LeanDag.Barnacle.Model.Run
import LeanDag.Adaptive.Basic
/-!
# Barnacle's run as a frame

Barnacle indexes its data by configuration and its slots by
configuration; a frame indexes widths by round and slots once. `cfgAt`
and `frameOf` cross between them, and `frameOf_width_eq` is the crossing:
the width of a round of configuration `k` is that configuration's count.

`anchor_two_epochs_below` states what `Params.gap` is for. Barnacle names the
count of configuration `k + 1` from the anchor of configuration `k`,
whose round sits `P.gap` below where the new count takes effect. At
`P.gap = 2 * W` those rounds hold at least `2 * W` slots whatever the
widths are, so the verdict the count reads lies two epochs below the
slots the count is read at — the arithmetic
`Adaptive.frameRun_agree`'s `hwd` asks for.
-/

namespace LeanDag
namespace Integration
open Barnacle

variable {Validator : Type} [Fintype Validator] [DecidableEq Validator]
variable {BlockId : Type} [DecidableEq BlockId] {Payload : Type}
variable {R : BaseRule Validator BlockId Payload} {P : Params}
variable {getLeader : ℕ → Validator} {hk : Keyed getLeader P.maxLeaders}
variable {upd : UpdateRule R} {U : R.Universe} {V : R.View U}
variable {K : ℕ} (Rn : PartialRun R P getLeader hk upd U V K)

/-- **A configuration starts strictly after the one before it**: its
anchor's round is past the threshold, and the threshold is positive. -/
theorem start_lt (k : ℕ) (hk' : k < K) : Rn.start k < Rn.start (k + 1) := by
  obtain ⟨-, hthr⟩ := Rn.anchor_commits k hk'
  rw [Rn.start_succ k hk']
  have := P.interval_pos
  omega

/-- **The anchor that sets a count sits two epochs below every round that
count governs.** Barnacle names the count of configuration `k + 1` from
the anchor of configuration `k`, whose round is `P.gap` below where the
new count takes effect. At `P.gap = 2 * W` those rounds hold at least
`2 * W` slots, whatever the widths are, so the verdict the count reads
lies two epochs below the slots the count is read at — which is what
`Adaptive.frameRun_agree`'s `hwd` asks.

The frame is arbitrary: the claim is about counting rounds into slots and
holds of any schedule with a leader in every round. -/
theorem anchor_two_epochs_below {W : ℕ} (hW : 0 < W) (hgap : P.gap = 2 * W)
    (F : Frame) {k : ℕ} (hk' : k < K)
    {g : ℕ} (hgr : F.roundOf g = Rn.anchor k / Rn.count k)
    {r : ℕ} (hr : Rn.start (k + 1) < r) :
    epochOf W g + 2 ≤ epochOf W (F.cum r) := by
  have hstart : Rn.start (k + 1) = Rn.anchor k / Rn.count k + P.gap :=
    Rn.start_succ k hk'
  -- the anchor's slot lies below the first slot of the round after it
  have hglt : g < F.cum (F.roundOf g + 1) := F.lt_cum_roundOf_succ g
  -- and the gap's rounds hold at least `P.gap` slots
  have hgapr : F.cum (F.roundOf g + 1) + P.gap ≤ F.cum (Rn.start (k + 1) + 1) :=
    F.cum_gap (by rw [hgr]; omega)
  have hmono : F.cum (Rn.start (k + 1) + 1) ≤ F.cum r := F.cum_mono (by omega)
  exact epochOf_add_two hW (by omega)


theorem start_mono {a b : ℕ} (hab : a ≤ b) (hb : b ≤ K) : Rn.start a ≤ Rn.start b := by
  induction b with
  | zero =>
      have ha : a = 0 := by omega
      subst ha; exact le_refl _
  | succ j ih =>
      rcases Nat.eq_or_lt_of_le hab with h | h
      · subst h; exact le_refl _
      · exact le_trans (ih (by omega) (by omega)) (le_of_lt (start_lt Rn j (by omega)))

open Classical in
/-- **The configuration in force at a round**: the last one to have
started at or before it, and the run's last where the run says no more.
Round `0` precedes every configuration's range and takes the first. -/
noncomputable def cfgAt (r : ℕ) : ℕ :=
  Nat.findGreatest (fun k => Rn.start k < r) K

/-- **And it is the configuration whose range holds the round.** -/
theorem cfgAt_eq {k r : ℕ} (hk' : k ≤ K) (hlo : Rn.start k < r)
    (hhi : r ≤ Rn.start (k + 1)) (hk1 : k + 1 ≤ K) : cfgAt Rn r = k := by
  classical
  refine le_antisymm ?_ (Nat.le_findGreatest (P := fun k => Rn.start k < r) hk' hlo)
  by_contra hlt
  push_neg at hlt
  have hspec : Rn.start (cfgAt Rn r) < r :=
    Nat.findGreatest_spec (P := fun k => Rn.start k < r) hk' hlo
  have hle : Rn.start (k + 1) ≤ Rn.start (cfgAt Rn r) :=
    start_mono Rn (by omega) (Nat.findGreatest_le K)
  omega

/-- **The frame a run induces**: every round holds the leaders of the
configuration in force there. -/
noncomputable def frameOf : Frame where
  width := fun r => Rn.count (cfgAt Rn r)
  width_pos := fun r => Rn.count_pos _

@[simp] theorem frameOf_width (r : ℕ) :
    (frameOf Rn).width r = Rn.count (cfgAt Rn r) := rfl

/-- The width of a round of configuration `k` is that configuration's
count — the bridge between Barnacle's per-configuration data and the
frame's per-round widths. -/
theorem frameOf_width_eq {k r : ℕ} (hk' : k ≤ K) (hlo : Rn.start k < r)
    (hhi : r ≤ Rn.start (k + 1)) (hk1 : k + 1 ≤ K) :
    (frameOf Rn).width r = Rn.count k := by
  rw [frameOf_width, cfgAt_eq Rn hk' hlo hhi hk1]

end Integration
end LeanDag
