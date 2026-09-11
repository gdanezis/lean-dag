import LeanDag.GC.ChopDecided
import LeanDag.Adaptive.Helpers.Chop
import LeanDag.Properties.Arcs.GC
import LeanDag.Mysticeti.Record
/-!
# I5 — the joiner and the adaptive schedule, at the core

`Adaptive/Helpers/Chop.lean` at the core's cut. The schedule half is
`Config.rebases_chop` read against `MysticetiProperties.sustains_chop`, which is
where a `Truncates` at a configuration's own schedule comes from; the
verdict half is the generic cross-cut agreement at it.

The claim is the one the arc was built for: **pruning does not split the
ledger, even when the schedule is derived from it.** A joiner that
recomputes its configurations from its own truncated view, under a
horizon-stable score, agrees with the network on every slot both hold.
-/

namespace LeanDag

namespace Integration

open Properties Adaptive Barnacle

variable {Validator : Type} [Fintype Validator] [DecidableEq Validator]
variable [F : Faults Validator]
variable {BlockId : Type} [DecidableEq BlockId] {Payload : Type}
variable {U : BlockUniverse Validator BlockId Payload}
variable {G : ℕ}

/-- **The cut is a truncation at a configuration's own schedule.** The
universe half is the core's; the schedule half is the configuration's,
and no fixed base instance enters — which is what lets the cut be taken
at a schedule whose rounds differ in width. -/
theorem truncates_chop_config (C : Config Validator) :
    Truncates (MysticetiProperties.mysticetiRule (Payload := Payload))
      U (chop U G) C.sched (C.chop G).sched G (C.cum G) :=
  { MysticetiProperties.sustains_chop (U := U) (G := G), C.rebases_chop G with }

/-- **I5's verdict half**, at the core: the joiner and the network agree
on every shared slot, from an arbitrary view of the truncation. -/
theorem joiner_decided_agree (C : Config Validator)
    {W : View Validator BlockId Payload (chop U G)}
    {V : View Validator BlockId Payload U} {k : ℕ} {w v : Option BlockId}
    (hW : Decided (S := (C.chop G).sched) (chop U G) W k w)
    (hV : Decided (S := C.sched) U V (C.cum G + k) v) : w = v :=
  Adaptive.joiner_decided_agree MysticetiProperties.agree MysticetiProperties.banded
    (truncates_chop_config C) MysticetiProperties.viewAgreeAbove_chop hW hV

/-- **I5, whole.** A joiner that recomputed its configuration from its
own truncated view, under a horizon-stable score, derives the network's
verdict at every slot both hold — and runs the network's leaders while
doing it. -/
theorem joiner_run_decided_agree
    {score : (U : BlockUniverse Validator BlockId Payload) →
      View Validator BlockId Payload U → Config Validator → Config Validator}
    (hs : Adaptive.HorizonStable
      (R := MysticetiProperties.mysticetiRule (Payload := Payload)) score G)
    (C : Config Validator)
    {V : View Validator BlockId Payload U}
    {V' : View Validator BlockId Payload (chop U G)}
    (hv : ViewAgreeAbove (MysticetiProperties.mysticetiRule (Payload := Payload)) V V' G)
    {W : View Validator BlockId Payload (chop U G)} {k : ℕ} {w v : Option BlockId}
    (hW : Decided (S := (score (chop U G) V' (C.chop G)).sched) (chop U G) W k w)
    (hV : Decided (S := (score U V C).sched) U V ((score U V C).cum G + k) v) :
    w = v := by
  rw [joiner_config_agree hs hv C] at hW
  exact joiner_decided_agree (score U V C) hW hV

end Integration

end LeanDag
