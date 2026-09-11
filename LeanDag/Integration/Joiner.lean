import LeanDag.Adaptive.Helpers.Mechanisms
import LeanDag.Properties.Arcs.GC
import LeanDag.Mysticeti.Record
/-!
# The adaptive schedule across the core's mechanisms

`Adaptive/Helpers/Mechanisms.lean` composes the segmented arc with the
cut, the fill and re-genesis at **any** carrier on the record, so the
core contributes nothing to those and they are read at the generic names
through `MysticetiProperties.onRecord`. What is stated here is the one
composite the generic file does not reach: the core's fill is
`SkipMsg.skipFill`, its own and not `BlockRecord.copyFill`, so
fill-then-cut at a configuration is assembled here the way `stack_core`
assembles it at a fixed schedule.

The claim the arc was built for — **pruning does not split the ledger,
even when the schedule is derived from it** — is
`Adaptive.joiner_run_decided_agree` at `MysticetiProperties.onRecord`,
and the instantiation below is the exhibit.
-/

namespace LeanDag

namespace Integration

open Properties Adaptive Barnacle
open LeanDag.MysticetiProperties

variable {Validator : Type} [Fintype Validator] [DecidableEq Validator]
variable [F : Faults Validator]
variable {BlockId : Type} [DecidableEq BlockId] {Payload : Type}
variable {U : BlockUniverse Validator BlockId Payload}
variable {G : ℕ}

/-- **The core's recovery and its horizon, under a configuration.** A
validator that filled a crashed peer's gap and then pruned below round
`G` reads one `Rebased` of the configuration's own schedule, so
`Stack.safe_and_live` covers the composite at an adaptive schedule. The
core's fill is `SkipMsg.skipFill`, which is why this is not
`Adaptive.stack_copyFill_chop_config`. -/
theorem stack_core_config (sk : SkipMsg U) (C : Config Validator) :
    Stack (MysticetiProperties.mysticetiRule (Payload := Payload)) U C.sched
      (chop sk.skipFill G) (C.chop G).sched G (max (sk.r + 1) G) (C.cum G) :=
  have st : Stack (MysticetiProperties.mysticetiRule (Payload := Payload)) U C.sched
      (MysticetiProperties.onRecord.chop sk.skipFill G) (C.chop G).sched G
      (max (sk.r + 1) G) (C.cum G) := by
    simpa using Stack.step
      (Rebased.of_sustains (S := C.sched) (sustains_skipFill (Payload := Payload) sk))
      (Adaptive.stack_chop_config MysticetiProperties.onRecord (U := sk.skipFill) (G := G) C)
  st

/-- **I5, whole, at the core**: a joiner that recomputed its
configuration from its own truncated view, under a horizon-stable score,
runs the network's leaders and derives the network's verdict at every
slot both hold. -/
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
    w = v :=
  Adaptive.joiner_run_decided_agree MysticetiProperties.onRecord
    MysticetiProperties.agree MysticetiProperties.banded hs C hv hW hV

end Integration

end LeanDag
