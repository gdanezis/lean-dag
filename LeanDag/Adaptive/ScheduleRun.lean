import LeanDag.Adaptive.Schedule
/-!
# A run of a schedule-emitting policy

A `ScheduleRun` carries verdicts and nothing else. Its epochs, its
widths and its leaders are all the schedule's readings of those verdicts,
so `FrameRun`'s `coherent` holds by definition and its two determinisms
are the schedule's own adaptedness clauses.

`agree` is the arc's safety: two runs over one universe, held by
validators with different views of it, have the same verdicts below the
horizon. Nothing is asked of the widths or the epoch lengths beyond that
each is read at the lag, and nothing aligns a width change with an epoch
boundary.

**Trusted core: `ScheduleRun` is a definition.**
-/

namespace LeanDag
namespace Adaptive

open Properties

variable {Validator : Type} [Fintype Validator] [DecidableEq Validator]
variable {BlockId : Type} [DecidableEq BlockId] {Payload : Type}
variable {R : DagRule Validator BlockId Payload}
variable {P : Schedule R} {U : R.Universe} {V : R.View U} {H : ℕ}

/-- **A run of a schedule.** The verdicts, and that every slot of a
closed epoch is decided by the schedule below the round its window ends
at. -/
structure ScheduleRun (P : Schedule R) (U : R.Universe) (V : R.View U) (H : ℕ) where
  /-- The verdicts, by global slot index. -/
  vdct : ℕ → Option BlockId
  closed : ∀ r i, i < (P.frameOf vdct).width r →
    (P.epochFrame vdct).roundOf ((P.frameOf vdct).index r i) < H →
    DecidedFrameBelow R (P.frameOf vdct) (P.asgOf vdct U V)
      ((P.frameOf vdct).roundOf ((P.epochFrame vdct).cum
        ((P.epochFrame vdct).roundOf ((P.frameOf vdct).index r i) + 2)))
      V ((P.frameOf vdct).index r i) (vdct ((P.frameOf vdct).index r i))

namespace ScheduleRun

/-- **A run of a schedule is a run over its own two frames.** `coherent`
is `rfl`: the assignment is the policy's by construction rather than by
a clause. -/
def toFrameRun (Rn : ScheduleRun P U V H) : FrameRun (R := R) P.pick U V H where
  E := P.epochFrame Rn.vdct
  F := P.frameOf Rn.vdct
  asg := P.asgOf Rn.vdct U V
  keyed := P.asgOf_keyed Rn.vdct U V
  vdct := Rn.vdct
  coherent := fun _ _ _ _ => rfl
  closed := Rn.closed

@[simp] theorem toFrameRun_E (Rn : ScheduleRun P U V H) :
    Rn.toFrameRun.E = P.epochFrame Rn.vdct := rfl

@[simp] theorem toFrameRun_F (Rn : ScheduleRun P U V H) :
    Rn.toFrameRun.F = P.frameOf Rn.vdct := rfl

@[simp] theorem toFrameRun_vdct (Rn : ScheduleRun P U V H) :
    Rn.toFrameRun.vdct = Rn.vdct := rfl

/-- **Safety of the adaptive schedule.** Two runs over one universe, held
by validators with different views of it, have the same verdicts below
the horizon.

Each of `frameRun_agree`'s three determinisms is one of the schedule's
clauses read at the runs: the epoch lengths from `len_adapted`, the
widths from `widthOf_adapted`, and the leaders from `pick_adapted`. -/
theorem agree (hR : Agree R) {V' : R.View U}
    (Rn : ScheduleRun P U V H) (Rn' : ScheduleRun P U V' H) :
    ∀ g, (P.epochFrame Rn.vdct).roundOf g < H → Rn.vdct g = Rn'.vdct g :=
  frameRun_agree hR Rn.toFrameRun Rn'.toFrameRun
    (fun k h => P.pick_adapted U V' V Rn.vdct Rn'.vdct k h)
    (fun e _ h => P.len_adapted Rn.vdct Rn'.vdct e (fun j hj => (h j hj).symm))
    (fun r _ h => P.widthOf_adapted Rn.vdct Rn'.vdct r (fun j hj => (h j hj).symm))

end ScheduleRun

end Adaptive

end LeanDag
