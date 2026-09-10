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

end ScheduleModel

end LeanDagTest
