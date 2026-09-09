import LeanDag.Properties.Arcs.Stack
import LeanDag.Properties.Arcs.GC
import LeanDag.Properties.Arcs.SafeSkip
import LeanDag.Nemo.Record
import LeanDag.FinWhale.Record
import LeanDag.Mysticeti.Record
/-!
# Stacks, at the rules

`Properties/Arcs/Stack.lean` proves the composition theorem once, and a
rule contributes nothing to it: the stack assembles from witnesses its
mechanisms already have, and `Stack.safe_and_live` reads it. For a rule
whose fill is the record's, that is `DagRule.OnRecord.stack_copyFill_chop`
and there is nothing per rule to state; Nemo and FinWhale are one call
each. The core is the exception below, and the reason is its fill:
`SkipMsg.skipFill` is Mysticeti's own, not `BlockRecord.copyFill`, so its
sustains witness is `sustains_skipFill` and the stack is assembled here.
A longer stack is one more `Stack.step`. `Properties.Safe` already
quantifies over every stack, so nothing beyond the witnesses is stated.
-/

namespace LeanDag

namespace Integration

open LeanDag.MysticetiProperties
open LeanDag.Properties LeanDag.Properties.Arcs

variable {Validator : Type} [Fintype Validator] [DecidableEq Validator]
variable {BlockId : Type} [DecidableEq BlockId] {Payload : Type}
variable {S : Slots Validator} {G d : ℕ}

/-! ## The core: fill, then cut -/

section Core

variable [Faults Validator] {U : BlockUniverse Validator BlockId Payload}

/-- **The core's fill-then-cut is a stack**, settling at the later of the
gap's top and the horizon, shifted by the horizon, re-indexed from the
base slot. -/
theorem stack_core (sk : SkipMsg U) (hd : G ≤ S.slotRound d) :
    Stack (MysticetiProperties.mysticetiRule (Payload := Payload)) U S
      (chop sk.skipFill G) (S.chop G d hd) G (max (sk.r + 1) G) d := by
  have st := Stack.step (Rebased.of_sustains (S := S) (sustains_skipFill (Payload := Payload) sk))
    (Stack.step (Rebased.of_truncates (MysticetiProperties.truncates_chop (U := sk.skipFill) hd)) Stack.nil)
  simpa using st

end Core

/-! ## Nemo and FinWhale: the record's fill, so the generic cell -/

section OnRecord

/-- **Nemo's fill-then-cut**, at its own record. -/
theorem stack_nemo {U : Nemo.Universe Validator BlockId Payload}
    (sk : SkipData U.ids U.block) (hd : G ≤ S.slotRound d) :
    Stack (NemoProperties.nemoRule (Validator := Validator) (BlockId := BlockId)
      (Payload := Payload)) U S
      (NemoProperties.onRecord.chop (NemoProperties.onRecord.copyFill U sk) G)
      (S.chop G d hd) G (max (sk.r + 1) G) d :=
  NemoProperties.onRecord.stack_copyFill_chop sk hd

/-- **FinWhale's fill-then-cut**, at its own record. -/
theorem stack_finwhale [Faults Validator] [LeanDag.FinWhale.Params Validator]
    {B : Type} [LinearOrder B] {D : LeanDag.FinWhale.Dag Validator B Payload}
    (sk : SkipData D.ids D.block) (hd : G ≤ S.slotRound d) :
    Stack (FinWhaleProperties.finWhaleRule (Validator := Validator) (BlockId := B)
      (Payload := Payload)) D S
      (FinWhaleProperties.onRecord.chop (FinWhaleProperties.onRecord.copyFill D sk) G)
      (S.chop G d hd) G (max (sk.r + 1) G) d :=
  FinWhaleProperties.onRecord.stack_copyFill_chop sk hd

end OnRecord

end Integration

end LeanDag
