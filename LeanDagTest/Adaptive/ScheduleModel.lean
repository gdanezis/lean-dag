import LeanDag.Adaptive.ScheduleRun
import LeanDag.Mysticeti.Properties
import LeanDagTest.Integration.VaryingFrame
import LeanDagTest.Mysticeti.Growth
/-!
# A schedule whose epochs and widths both vary

`Schedule.ofFixed` reads no verdict, so its three adaptedness clauses
hold by `rfl` and it may take any epoch lengths and any widths. That is
what this file exhibits: epochs of `3, 4, 5, 3, 4, 5, …` slots over
rounds of `1, 2, 3, 1, 2, 3, …`, neither aligned with the other and
neither constant.

It is the check §12 of `adaptive-schedule.md` asks of steps 3 and 4: the
clauses are satisfiable together at a schedule whose two frames both
move, so `ScheduleRun.agree` is not a theorem about an empty family.
-/

namespace LeanDagTest
namespace ScheduleModel

open LeanDag LeanDag.Adaptive LeanDag.MysticetiProperties LeanDagTest.VaryingFrame

/-- Epochs of `3`, `4`, `5` slots, cycling. -/
def eF : Frame where
  width := fun e => e % 3 + 3
  width_pos := fun _ => by omega

example : eF.width 0 = 3 := rfl
example : eF.width 1 = 4 := rfl
example : eF.width 2 = 5 := rfl

/-- The schedule: `eF`'s epochs over `vF`'s rounds, at `vAsg`. -/
noncomputable def sched : Schedule (mysticetiRule (Validator := Fin 4)
    (BlockId := ℕ) (Payload := Unit)) :=
  Schedule.ofFixed eF vF 3 vF_le vAsg vAsg_keyed

/-- **Both frames move, and they are not aligned.** Round `1` holds two
slots where round `0` holds one, and epoch `1` holds four slots where
epoch `0` holds three. -/
example (v : ℕ → Option ℕ) : sched.widthOf v 0 = 1 := rfl
example (v : ℕ → Option ℕ) : sched.widthOf v 1 = 2 := rfl
example (v : ℕ → Option ℕ) : sched.widthOf v 2 = 3 := rfl
example (v : ℕ → Option ℕ) : sched.len v 0 = 3 := rfl
example (v : ℕ → Option ℕ) : sched.len v 1 = 4 := rfl
example (v : ℕ → Option ℕ) : sched.len v 2 = 5 := rfl

/-- Epoch `0` holds three slots and round `0` holds one, so the epoch
boundary at slot `3` falls inside round `2`, which holds slots `3`, `4`
and `5`. No clause prevents it. -/
example (v : ℕ → Option ℕ) : (sched.frameOf v).cum 2 = 3 := by
  rw [Frame.cum_succ, Frame.cum_succ, Frame.cum_zero]
  rfl
example (v : ℕ → Option ℕ) : (sched.epochFrame v).cum 1 = 3 := by
  rw [Frame.cum_succ, Frame.cum_zero]
  rfl

/-! ## A schedule that reads its verdicts

`sched` above reads nothing, so its clauses hold by `rfl`. `aSched`
reads: both its epoch lengths and its widths depend on whether slot `0`
committed, and the three adaptedness clauses hold because that slot lies
in epoch `0`, two below every epoch either function is consulted for.

It is the smallest schedule that is genuinely adapted in both frames, and
its purpose is to show the clauses do not force the frames to be
constant.
-/

/-- Epochs `0` and `1` hold three slots; later ones hold three or four,
according to whether slot `0` committed. -/
def aLen (v : ℕ → Option ℕ) (e : ℕ) : ℕ :=
  if e < 2 then 3 else if v 0 = none then 3 else 4

/-- Rounds below `6` hold one slot; later ones hold one or two, by the
same reading. -/
def aWid (v : ℕ → Option ℕ) (r : ℕ) : ℕ :=
  if r < 6 then 1 else if v 0 = none then 1 else 2

theorem aLen_pos (v : ℕ → Option ℕ) (e : ℕ) : 0 < aLen v e := by
  unfold aLen; split
  · omega
  · split <;> omega

theorem aWid_pos (v : ℕ → Option ℕ) (r : ℕ) : 0 < aWid v r := by
  unfold aWid; split
  · omega
  · split <;> omega

theorem aWid_le (v : ℕ → Option ℕ) (r : ℕ) : aWid v r ≤ 2 := by
  unfold aWid; split
  · omega
  · split <;> omega

theorem aWid_low {v : ℕ → Option ℕ} {r : ℕ} (h : r < 6) : aWid v r = 1 := if_pos h

/-- The epochs and the rounds the schedule gives at a verdict function. -/
def aE (v : ℕ → Option ℕ) : Frame := ⟨aLen v, aLen_pos v⟩

def aF (v : ℕ → Option ℕ) : Frame := ⟨aWid v, aWid_pos v⟩

@[simp] theorem aE_width (v : ℕ → Option ℕ) (e : ℕ) : (aE v).width e = aLen v e := rfl

@[simp] theorem aF_width (v : ℕ → Option ℕ) (r : ℕ) : (aF v).width r = aWid v r := rfl

theorem aE_cum2 (v : ℕ → Option ℕ) : (aE v).cum 2 = 6 := by
  rw [Frame.cum_succ, Frame.cum_succ, Frame.cum_zero]
  rfl

/-- Slot `0` is in epoch `0`, whatever the verdicts say. -/
theorem aE_roundOf_zero (v : ℕ → Option ℕ) : (aE v).roundOf 0 = 0 :=
  (aE v).roundOf_eq (by simp) (by rw [Frame.cum_succ, Frame.cum_zero]; exact Nat.zero_lt_succ _)

theorem aF_cum_low (v : ℕ → Option ℕ) : ∀ r, r ≤ 6 → (aF v).cum r = r := by
  intro r
  induction r with
  | zero => intro _; simp
  | succ j ih =>
      intro hj
      rw [Frame.cum_succ, ih (by omega), aF_width, aWid_low (show j < 6 by omega)]

/-- A round at or past `6` begins in epoch `2` or later, which is what
the width may read the verdicts of epoch `0` for. -/
theorem aE_two_le (v : ℕ → Option ℕ) {r : ℕ} (h : 6 ≤ r) :
    2 ≤ (aE v).roundOf ((aF v).cum r) := by
  refine (aE v).cum_le_iff_le_roundOf.mp ?_
  rw [aE_cum2]
  have := (aF v).cum_mono h
  rw [aF_cum_low v 6 (le_refl 6)] at this
  omega

/-- **A schedule adapted in both frames.** The leaders are round-robin
over the slots, so `pick_adapted` is `rfl`; the epoch lengths and the
widths read slot `0`'s verdict, and epoch `0` is two below every epoch
either is consulted for. -/
def aSched : Schedule (mysticetiRule (Validator := Fin 4) (BlockId := ℕ) (Payload := Unit)) where
  len := aLen
  len_pos := aLen_pos
  widthOf := aWid
  widthOf_pos := aWid_pos
  maxWidth := 2
  widthOf_le := aWid_le
  pick := fun _ _ _ k => ⟨k % 4, by omega⟩
  keyed := fun _ _ v r i j hi hj h => by
    have hi2 : i < 2 := lt_of_lt_of_le hi (aWid_le v r)
    have hj2 : j < 2 := lt_of_lt_of_le hj (aWid_le v r)
    have := congrArg Fin.val h
    simp only [Frame.index] at this
    omega
  len_adapted := fun v w e h => by
    unfold aLen
    by_cases he : e < 2
    · rw [if_pos he, if_pos he]
    · rw [if_neg he, if_neg he,
        h 0 (show (aE v).roundOf 0 + 2 ≤ e by rw [aE_roundOf_zero]; omega)]
  widthOf_adapted := fun v w r h => by
    unfold aWid
    by_cases hr : r < 6
    · rw [if_pos hr, if_pos hr]
    · rw [if_neg hr, if_neg hr,
        h 0 (show (aE v).roundOf 0 + 2 ≤ (aE v).roundOf ((aF v).cum r) by
          rw [aE_roundOf_zero]; exact aE_two_le v (by omega))]
  pick_adapted := fun _ _ _ _ _ _ _ => rfl

/-- **Both frames move with the verdicts.** -/
example : aSched.len (fun _ => none) 2 = 3 := rfl
example : aSched.len (fun _ => some 0) 2 = 4 := rfl
example : aSched.widthOf (fun _ => none) 6 = 1 := rfl
example : aSched.widthOf (fun _ => some 0) 6 = 2 := rfl

/-- **And the run is inhabited.** At height zero every clause is about an
epoch the run has not closed, so `ScheduleRun` is inhabited outright and
`ScheduleRun.agree` is not a theorem about an empty family. -/
def aRun (U : (mysticetiRule (Validator := Fin 4) (BlockId := ℕ)
      (Payload := Unit)).Universe) (V : View (Fin 4) ℕ Unit U) :
    ScheduleRun aSched U V 0 where
  vdct := fun _ => none
  closed := fun _ _ _ h => absurd h (by omega)

end ScheduleModel

end LeanDagTest
