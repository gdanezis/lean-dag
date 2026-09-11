import LeanDag.Barnacle.Config
import LeanDag.Properties.Truncate
/-!
# A configuration across a cut

Pruning a universe below round `G` and renumbering from the first slot
of that round leaves a configuration that is the original with its first
`G` rounds dropped. `Config.chop` is that configuration, and
`Config.rebases_chop` is the schedule half of a truncation
(`Properties.Rebases`) at it: the rounds fall by `G`, the leaders are
the same replicas, and the base slot is `C.cum G`.

This is what a joiner needs of an adaptive schedule. Where the fixpoint
arc had `Slots.chop` and `slotsOf` commute definitionally, a `Config`
carries `roundOf` as a `Nat.findGreatest` over its widths, so the
commutation is an argument about `cum` rather than an `rfl` — and it is
the argument that lets a cut be taken at a schedule whose rounds differ
in width.
-/

namespace LeanDag

namespace Barnacle

variable {Validator : Type}

namespace Config

variable (C : Config Validator) (G : ℕ)

/-- **A configuration with its first `G` rounds dropped.** Round `r` of
the result is round `G + r` of the original, with the same width and the
same leaders; the interval is unchanged. -/
def chop : Config Validator where
  slotsAt := fun r => C.slotsAt (G + r)
  slotsAt_pos := fun r => C.slotsAt_pos (G + r)
  lead := fun r i => C.lead (G + r) i
  keyed := fun r i j hi hj h => C.keyed (G + r) i j hi hj h
  interval := C.interval

@[simp] theorem chop_slotsAt (r : ℕ) : (C.chop G).slotsAt r = C.slotsAt (G + r) := rfl

@[simp] theorem chop_interval : (C.chop G).interval = C.interval := rfl

/-- The cut's slot numbering, against the original's: the first slot of
round `G + r` is `C.cum G` slots further on. -/
theorem cum_chop (r : ℕ) : C.cum G + (C.chop G).cum r = C.cum (G + r) := by
  induction r with
  | zero => simp
  | succ j ih =>
      have h1 : (C.chop G).cum (j + 1) = (C.chop G).cum j + C.slotsAt (G + j) :=
        (C.chop G).cum_succ j
      have h2 : C.cum (G + j + 1) = C.cum (G + j) + C.slotsAt (G + j) := C.cum_succ (G + j)
      rw [show G + (j + 1) = G + j + 1 from rfl]
      omega

/-- **The round of a slot falls by the horizon.** -/
theorem roundOf_chop (k : ℕ) : (C.chop G).roundOf k + G = C.roundOf (C.cum G + k) := by
  have hlo := (C.chop G).cum_roundOf_le k
  have hhi := (C.chop G).lt_cum_roundOf_succ k
  have e1 := C.cum_chop G ((C.chop G).roundOf k)
  have e2 := C.cum_chop G ((C.chop G).roundOf k + 1)
  have : C.roundOf (C.cum G + k) = G + (C.chop G).roundOf k := by
    refine C.roundOf_eq ?_ ?_
    · omega
    · rw [show G + (C.chop G).roundOf k + 1 = G + ((C.chop G).roundOf k + 1) from by omega]
      omega
  omega

/-- **Two cuts are one.** Chopping at `G₁` and then at `G₂` drops the
first `G₁ + G₂` rounds, so a validator that has pruned twice holds the
configuration of a validator that pruned once, and the cuts beneath a
configuration compose the way `GC.chop_chop` composes them beneath a
universe. -/
theorem chop_chop (G₁ G₂ : ℕ) : (C.chop G₁).chop G₂ = C.chop (G₁ + G₂) := by
  simp only [chop, Nat.add_assoc]

/-- **Chopping at nothing is doing nothing.** -/
@[simp] theorem chop_zero : C.chop 0 = C := by
  simp only [chop, Nat.zero_add]

/-- **The schedule half of a truncation.** A cut at round `G`, numbered
from the first slot of that round, rebases the configuration's schedule
onto the chopped configuration's. -/
theorem rebases_chop : Properties.Rebases C.sched (C.chop G).sched G (C.cum G) where
  slotRound := fun k => C.roundOf_chop G k
  leader := fun k => by
    have hr := C.roundOf_chop G k
    have hlo := (C.chop G).cum_roundOf_le k
    have e1 := C.cum_chop G ((C.chop G).roundOf k)
    show (C.chop G).lead _ _ = C.lead _ _
    rw [show C.roundOf (C.cum G + k) = G + (C.chop G).roundOf k from by omega]
    show C.lead (G + (C.chop G).roundOf k) _ = C.lead (G + (C.chop G).roundOf k) _
    congr 1
    omega
  base := by
    have := C.roundOf_cum G
    show G ≤ C.roundOf (C.cum G)
    omega

end Config

end Barnacle

end LeanDag
