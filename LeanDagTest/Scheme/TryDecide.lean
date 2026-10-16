import LeanDag.Scheme.Loop.Proof
import LeanDag.Scheme.Model.LeastSel
import LeanDag.Scheme.Helpers.VotedBlock
import LeanDagTest.MahiMahi.Model
/-!
# The commit loop on Mahi-Mahi's `full4`

The scheme's schedule with one leader per round and pipelining is
`Slots.uniform 1 1`: slot `k` at round `k`, led by `k % 4`. On `full4`
(six rounds, every block referencing the whole round below) the loop at
the Mahi-Mahi row of wave four commits slots `0`, `1` and `2` directly,
as Mahi-Mahi does, and leaves slots `3`–`5` undecided: their decision
rounds lie past round `5`. On Mysticeti's `U7` it commits slot `0`
indirectly. Successive calls, each restarting after the last decision
output, output the same.
-/

namespace LeanDagTest

namespace Scheme

open LeanDag LeanDag.Scheme

section Pipelined

local instance schemeSlots : Slots (Fin 4) :=
  Slots.uniformSingle 1 (by omega) (fun k => ⟨k % 4, by omega⟩)

/-- The least vote on `full4`'s universe. -/
abbrev σL : VoteSel (Fin 4) (Fin 24) Unit ValidWrt Correct := leastSel

/-- The scheme's vote, parents in ascending order. -/
abbrev σV : VoteSel (Fin 4) (Fin 24) Unit ValidWrt Correct :=
  votedBlockSel (fun _ s => (List.finRange 24).filter (· ∈ s))
    (fun _ s x => by simp [List.mem_finRange])

/-- The Mahi-Mahi row at wave four, `n = 4`, `f = 1`. -/
abbrev mm4 : Params := Params.mahiMahi 4 4 1

example : tryDecide mm4 σL full4 (View.full full4) 0 5 = [(0, some 0), (1, some 5), (2, some 10)] := by
  decide

example : tryDecide mm4 σV full4 (View.full full4) 0 5 = [(0, some 0), (1, some 5), (2, some 10)] := by
  decide

/-- Restarting at slot `1` repeats the tail of the output. -/
example : tryDecide mm4 σL full4 (View.full full4) 1 5 = [(1, some 5), (2, some 10)] := by
  decide

/-- Three calls scanning to slots `1`, `3` and `5`, each restarting after the
last decision output: the first outputs slots `0` and `1`, the second slot
`2`, the third nothing. -/
example : consumed mm4 σL full4 0 (fun _ => View.full full4) (fun t => 2 * t + 1) 3 =
    [(0, some 0), (1, some 5), (2, some 10)] := by
  decide

end Pipelined

/-! ## An indirect commit: Mysticeti's `U7`

The schedule is the scheme's without pipelining at wave three,
`Slots.uniformSingle 3`, led by validator `0`. Slot `0` has one
certificate, below the commit threshold, and no direct skip; slot `1`
commits block `12` directly, and block `12` holds the certificate, so the
loop commits slot `0` indirectly, as `Decided` does. -/

/-- The Mysticeti row, `n = 4`, `f = 1`. -/
abbrev myst : Params := Params.mysticeti 4 1

example : tryDirect myst σL U7 V7 0 = none := by decide

example : tryDecide myst σL U7 V7 0 1 = [(0, some 0), (1, some 12)] := by decide

example : tryDecide myst σV U7 V7 0 1 = [(0, some 0), (1, some 12)] := by decide

/-- A call scanning to slot `0` outputs nothing, since slot `0` waits on
slot `1`; the next call, scanning to slot `1`, outputs both. -/
example : consumed myst σL U7 0 (fun _ => V7) (fun t => t) 1 = [] ∧
    consumed myst σL U7 0 (fun _ => V7) (fun t => t) 2 = [(0, some 0), (1, some 12)] := by
  decide

end Scheme

end LeanDagTest
