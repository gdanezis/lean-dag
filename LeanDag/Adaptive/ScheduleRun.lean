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

/-- **Height zero is free.** Every clause is about an epoch the run has
not closed. -/
def zero (P : Schedule R) (U : R.Universe) (V : R.View U)
    (vdct : ℕ → Option BlockId) : ScheduleRun P U V 0 where
  vdct := vdct
  closed := fun _ _ _ h => absurd h (by omega)

/-- **Progress: one more epoch.** A run extends by an epoch as soon as
that epoch's slots are decided. The verdicts do not move — a
`ScheduleRun` carries nothing else — so extending adds a clause rather
than data, and with it the frames stay exactly where they were. -/
def extend (Rn : ScheduleRun P U V H)
    (h : ∀ r i, i < (P.frameOf Rn.vdct).width r →
      (P.epochFrame Rn.vdct).roundOf ((P.frameOf Rn.vdct).index r i) = H →
      DecidedFrameBelow R (P.frameOf Rn.vdct) (P.asgOf Rn.vdct U V)
        ((P.frameOf Rn.vdct).roundOf ((P.epochFrame Rn.vdct).cum
          ((P.epochFrame Rn.vdct).roundOf ((P.frameOf Rn.vdct).index r i) + 2)))
        V ((P.frameOf Rn.vdct).index r i) (Rn.vdct ((P.frameOf Rn.vdct).index r i))) :
    ScheduleRun P U V (H + 1) where
  vdct := Rn.vdct
  closed := fun r i hi hep => by
    rcases Nat.lt_or_ge ((P.epochFrame Rn.vdct).roundOf
      ((P.frameOf Rn.vdct).index r i)) H with hlt | hge
    · exact Rn.closed r i hi hlt
    · exact h r i hi (by omega)

@[simp] theorem extend_vdct (Rn : ScheduleRun P U V H) (h) :
    (Rn.extend h).vdct = Rn.vdct := rfl

/-- **Every height.** A verdict function whose every slot is decided
below its own window gives a run of every height. -/
def everyHeight (P : Schedule R) (U : R.Universe) (V : R.View U)
    (vdct : ℕ → Option BlockId)
    (h : ∀ r i, i < (P.frameOf vdct).width r →
      DecidedFrameBelow R (P.frameOf vdct) (P.asgOf vdct U V)
        ((P.frameOf vdct).roundOf ((P.epochFrame vdct).cum
          ((P.epochFrame vdct).roundOf ((P.frameOf vdct).index r i) + 2)))
        V ((P.frameOf vdct).index r i) (vdct ((P.frameOf vdct).index r i))) :
    ∀ H, ScheduleRun P U V H := fun _ =>
  { vdct := vdct, closed := fun r i hi _ => h r i hi }

@[simp] theorem everyHeight_vdct (P : Schedule R) (U : R.Universe) (V : R.View U)
    (vdct : ℕ → Option BlockId) (h) (H : ℕ) :
    (everyHeight P U V vdct h H).vdct = vdct := rfl

/-- **What a rule owes for a run to exist**: that it decides every slot
of the schedule, and that it settles each within two epochs.
`closed_of_settles` is the second read at the schedule's own frames, and
`everyHeight` is what it feeds. -/
def ofSettles (P : Schedule R) (U : R.Universe) (V : R.View U)
    (vdct : ℕ → Option BlockId)
    (hs : SettlesInTwoEpochs R (P.epochFrame vdct) (P.frameOf vdct)
      (P.asgOf vdct U V) (P.asgOf_keyed vdct U V) V)
    (hd : ∀ r i, i < (P.frameOf vdct).width r →
      R.Decided ((P.frameOf vdct).toSlots (P.asgOf vdct U V) (P.asgOf_keyed vdct U V)) V
        ((P.frameOf vdct).index r i) (vdct ((P.frameOf vdct).index r i))) :
    ∀ H, ScheduleRun P U V H :=
  everyHeight P U V vdct (fun r i hi =>
    closed_of_settles (H := (P.epochFrame vdct).roundOf ((P.frameOf vdct).index r i) + 1) hs
      (fun r' i' hi' _ => hd r' i' hi') r i hi (by omega))

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

/-- **Two runs of a schedule that share a prefix agree on it**, whatever
heights they have reached and whatever they do above the prefix. The two
runs need not have closed the same epochs: one validator may be behind
the other, and this still holds of every slot the one in front has
settled inside the shared prefix.

`hb` is the whole of what is asked: the slot's window ends inside the
prefix. That is the condition the two-epoch bound is there to give, and
where it fails the statement says nothing — which is what a schedule
computed from verdicts that have not settled amounts to. -/
theorem agree_on_prefix (hR : Agree R) {H' : ℕ}
    (Rn : ScheduleRun P U V H) {V' : R.View U} (Rn' : ScheduleRun P U V' H')
    {B g : ℕ}
    (hw : ∀ r, r < B → (P.frameOf Rn'.vdct).width r = (P.frameOf Rn.vdct).width r)
    (ha : ∀ r i, r < B → i < (P.frameOf Rn.vdct).width r →
      P.asgOf Rn'.vdct U V' r i = P.asgOf Rn.vdct U V r i)
    (hg : (P.epochFrame Rn.vdct).roundOf g < H)
    (hb : (P.frameOf Rn.vdct).roundOf ((P.epochFrame Rn.vdct).cum
      ((P.epochFrame Rn.vdct).roundOf g + 2)) ≤ B)
    (hg' : (P.epochFrame Rn'.vdct).roundOf g < H') :
    Rn.vdct g = Rn'.vdct g :=
  verdict_agree_of_prefix hR hw ha
    ((Rn.toFrameRun.closed_at g hg).mono hb) (Rn'.toFrameRun.decided_self g hg')

end ScheduleRun

end Adaptive

end LeanDag
