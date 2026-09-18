import LeanDagTest.Steelhead.Model
import LeanDag.Steelhead.Replay.Proof
/-!
# Steelhead witnesses: the replay on a healthy window

Algorithm 2 run on data (`steelhead.md` §8). The window is the causal history of block `28` of
`sh8`, the eight-round healthy universe of `Model.lean`, at the rounds `7 − 8` and above: rounds
`1` to `7`, round `0` excluded. With the waves `3` and `5`, the canary `7` and the known leader
`(r + 1) mod 4`:

* period `1` scores `18` and period `8` scores `11`: the asynchronous rule pays its two extra
  rounds at every slot, and the window's top stands in for the outcomes the window does not
  resolve;
* **the replay recovers from period `1`** at the deployment's hysteresis `1/10`: the window
  holds no resolvable canary probe, so every synchronous slot is replayed exactly from the
  certificates the healthy universe holds;
* at hysteresis `1/2` the same window keeps period `1`: strong hysteresis blocks an improvement
  the replay sees;
* equal scores keep the current period, and a tie among candidates better than the current one
  goes to the larger.
-/

namespace LeanDagTest

open LeanDag LeanDag.Steelhead.Replay

set_option maxRecDepth 8192

/-- The waves `3` and `5`, the canary `7`, and the known leader `(r + 1) mod 4`. -/
def rpConfig : Config (Fin 4) := ⟨3, 5, some 7, fun r => ⟨(r + 1) % 4, by omega⟩⟩

/-- **The window**: the causal history of block `28` of `sh8`, at round `7`, over seven rounds. -/
def rpWindow : Evidence (Fin 4) := ofAnchor sh8 28 8

/-- The window retains rounds `1` to `7`. -/
theorem rpWindow_bounds : rpWindow.bottom = 1 ∧ rpWindow.top = 7 := by decide +kernel

/-- **Period `1` scores `18`.** -/
theorem rpWindow_score_one : score rpWindow rpConfig 1 = 18 := by decide +kernel

/-- **Period `8` scores `11`.** -/
theorem rpWindow_score_eight : score rpWindow rpConfig 8 = 11 := by decide +kernel

/-- **The replay recovers from period `1`** at hysteresis `1/10`. -/
theorem rpWindow_recovers : update rpWindow rpConfig [1, 2, 4, 8] 1 (1 / 10) = 8 := by
  decide +kernel

/-- **Hysteresis `1/2` keeps period `1`** on the same window. -/
theorem rpWindow_hysteresis_keeps : update rpWindow rpConfig [1, 2, 4, 8] 1 (1 / 2) = 1 := by
  decide +kernel

/-! ## The candidate periods

`candidatesUpto K` is the implementation's `{1, 2, 4, …, maxPeriod}`: the powers of two up to
`K`, and every candidate once `K` is a power of two. -/

example : candidatesUpto 8 = [1, 2, 4, 8] := by decide
example : candidatesUpto 1 = [1] := by decide
-- At a maximum that is no power of two the list stops below it.
example : candidatesUpto 6 = [1, 2, 4] := by decide

/-- Equal scores keep the current period, whatever the candidates' order. -/
theorem select_tie_keeps : select [1, 2, 4, 8] (fun _ => 10) 4 (1 / 10) = 4 := by decide +kernel

/-- When the current period scores worst, a tie among the better candidates goes to the larger. -/
theorem select_tie_larger : select [1, 2, 4, 8] (fun k => if k = 8 then 20 else 10) 8 0 = 4 := by
  decide +kernel

#print axioms rpWindow_recovers
#print axioms rpWindow_hysteresis_keeps

end LeanDagTest
