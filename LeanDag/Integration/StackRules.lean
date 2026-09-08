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
mechanisms already have (`Rebased.of_sustains`, `Rebased.of_truncates`),
and `Stack.safe_and_live` reads it. Three rules are shown below, fill
then cut; a longer stack is one more `Stack.step`. `Properties.Safe`
already quantifies over every stack, so nothing beyond the witnesses is
stated here.
-/

namespace LeanDag

namespace Integration

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

/-! ## Nemo: its own universe, fill then cut -/

section Nemo

variable {U : Nemo.Universe Validator BlockId Payload}

theorem stack_nemo (sk : SkipData U.ids U.block) (hd : G ≤ S.slotRound d) :
    Stack (NemoProperties.nemoRule (Validator := Validator) (BlockId := BlockId)
      (Payload := Payload)) U S (NemoProperties.onRecord.chop (NemoProperties.onRecord.copyFill U sk) G)
      (S.chop G d hd) G (max (sk.r + 1) G) d := by
  simpa using Stack.step (Rebased.of_sustains (S := S) (NemoProperties.onRecord.sustains_copyFill U sk))
    (Stack.step (Rebased.of_truncates (NemoProperties.onRecord.truncates_chop (NemoProperties.onRecord.copyFill U sk) hd))
      Stack.nil)

end Nemo

/-! ## FinWhale: its own DAG, fill then cut -/

section FinWhale

open LeanDag.FinWhale

variable [Faults Validator] [LeanDag.FinWhale.Params Validator]
variable {B : Type} [LinearOrder B] {D : Dag Validator B Payload}

theorem stack_finwhale (sk : SkipData D.ids D.block) (hd : G ≤ S.slotRound d) :
    Stack (FinWhaleProperties.finWhaleRule (Validator := Validator) (BlockId := B)
      (Payload := Payload)) D S (FinWhaleProperties.onRecord.chop (FinWhaleProperties.onRecord.copyFill D sk) G)
      (S.chop G d hd) G (max (sk.r + 1) G) d := by
  simpa using Stack.step (Rebased.of_sustains (S := S) (FinWhaleProperties.onRecord.sustains_copyFill D sk))
    (Stack.step (Rebased.of_truncates
      (FinWhaleProperties.onRecord.truncates_chop (FinWhaleProperties.onRecord.copyFill D sk) hd)) Stack.nil)

end FinWhale

end Integration

end LeanDag
