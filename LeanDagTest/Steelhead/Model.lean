import LeanDagTest.Mysticeti.Model
import LeanDag.Steelhead.Model.Chain
import Mathlib.Tactic.IntervalCases
/-!
# Steelhead witnesses — the rule at a wavelength function on data

Every definition of `LeanDag/Steelhead/Model/` settled by `decide` on a
four-validator universe before anything is proved from it
(`steelhead.md` §8). One universe, `sh8`: eight fully connected rounds
under the period-four wavelength `periodic 3 5 4`, so round `0` and
round `4` are asynchronous slots at wave `5` and the rest synchronous
at wave `3`. On it:

* the wavelength arithmetic and the per-slot eligibility floors;
* the direct rules at each slot's own wave, and the anchor route for
  the asynchronous slot `0` through the synchronous slot `5`, which is
  the first slot at or above round `0 + 5`;
* **the anchor-floor counterexample** of `steelhead.md` §3: with the
  floor read from the synchronous wave instead of the slot's own, the
  relation derives both a commit and a skip of slot `0` from the one
  full view. The synchronous slot `3` is then an eligible anchor, its
  block's history stops at round `3`, and the certificates of round `4`
  are invisible to it. At the slot's own floor slot `3` is not eligible
  and the route through slot `5` commits;
* the chain verdict on data: Mahi-Mahi at wave `5` under a coin map,
  committing round `0` directly.

The committee is the standard witness one, validator `0` Byzantine and
`f = 1` (`LeanDagTest/Mysticeti/Model.lean`), so the quorum is `3`. The
schedule is local to this file, slot `k` at round `k` led by
`(k + 1) % 4`, so that slot `0`'s leader is a correct validator.
-/

namespace LeanDagTest

open LeanDag LeanDag.Steelhead

set_option maxRecDepth 4096

/-- One slot per round, led by `(k + 1) % 4`. -/
local instance shSlots : Slots (Fin 4) :=
  Slots.uniformSingle 1 (by omega) (fun k => ⟨(k + 1) % 4, by omega⟩)

/-- The period-four wavelength of the 3f+1 pair: `5` at rounds
`0, 4, 8, …`, `3` elsewhere. -/
abbrev w4 : ℕ → ℕ := periodic 3 5 4

/-! ## The wavelength function -/

example : w4 0 = 5 := by decide
example : w4 1 = 3 := by decide
example : w4 3 = 3 := by decide
example : w4 4 = 5 := by decide
example : IsAsync 4 8 := by decide
example : ¬ IsAsync 4 6 := by decide
example : periodic 3 5 1 7 = 5 := by decide

/-! ## `sh8` — eight rounds, everyone referencing the whole round below -/

/-- Block `4m + v` is validator `v`'s round-`m` block; every non-genesis
block references all four blocks of the round below. -/
def shBlk : Fin 32 → Block (Fin 4) (Fin 32) Unit := fun i =>
  { round := (i : ℕ) / 4, creator := ⟨(i : ℕ) % 4, by omega⟩,
    refs := if h : (i : ℕ) < 4 then ∅ else
      (Finset.univ.filter (fun j : Fin 32 => (j : ℕ) / 4 + 1 = (i : ℕ) / 4)),
    payload := () }

def sh8 : BlockUniverse (Fin 4) (Fin 32) Unit where
  ids := Finset.univ
  block := shBlk
  complete := by decide
  valid := by decide
  no_equivocation := by decide

/-- The rule at the period-four wavelength on this universe. -/
abbrev sh : AnchoredRule (Fin 4) (Fin 32) Unit ValidWrt Correct :=
  steelheadAnchored (Fin 4) (Fin 32) Unit w4

/-! ### Eligibility at each slot's own floor -/

-- The asynchronous slot `0` anchors at round `5` or above; the synchronous
-- slot `1` at round `4` or above.
example : sh.waveAt 0 = 4 := by decide
example : sh.waveAt 1 = 2 := by decide
example : sh.decisionRound 0 = 4 := by decide
example : sh.decisionRound 1 = 3 := by decide
example : sh.Eligible 0 5 := by decide
example : ¬ sh.Eligible 0 4 := by decide
example : sh.Eligible 1 4 := by decide
example : ¬ sh.Eligible 1 3 := by decide

/-! ### The direct rules at each slot's own wave -/

-- Slot `0`'s candidate is block `1` (round `0`, author `1`); at wave `5`
-- its certificates are the whole of round `4`.
example : IsLeaderBlock sh8 0 1 := by decide
example : MahiMahi.certificates sh8 5 1 0 = {16, 17, 18, 19} := by decide
example : MahiMahi.DirectCommit sh8 5 1 0 := by decide
example : sh.Commit sh8 (View.full sh8) 1 0 := by decide

-- Slot `1`'s candidate is block `6` (round `1`, author `2`); at wave `3`
-- its certificates are the whole of round `3`.
example : IsLeaderBlock sh8 1 6 := by decide
example : MahiMahi.certificates sh8 3 6 1 = {12, 13, 14, 15} := by decide
example : sh.Commit sh8 (View.full sh8) 6 1 := by decide

-- No slot is directly skipped: every voting round votes.
example : ¬ sh.Skip sh8 (View.full sh8) shSlots 0 := by decide
example : ¬ sh.Skip sh8 (View.full sh8) shSlots 1 := by decide

/-! ### The decision relation -/

theorem sh8_slot0 : Steelhead.Decided w4 sh8 (View.full sh8) 0 (some 1) :=
  Decided.directCommit (by decide) (by decide)

theorem sh8_slot1 : Steelhead.Decided w4 sh8 (View.full sh8) 1 (some 6) :=
  Decided.directCommit (by decide) (by decide)

-- Slot `5` (round `5`, author `2`, block `22`) commits directly at wave
-- `3` with the whole of round `7` certifying it.
theorem sh8_slot5 : Steelhead.Decided w4 sh8 (View.full sh8) 5 (some 22) :=
  Decided.directCommit (by decide) (by decide)

/-- **The anchor route for the asynchronous slot**: slot `5` is the
nearest eligible committed slot, nothing eligible lies between, and its
block reaches a round-`4` certificate for block `1`. The same verdict as
the direct route, as SH2 says it must be. -/
theorem sh8_slot0_indirect : Steelhead.Decided w4 sh8 (View.full sh8) 0 (some 1) :=
  AnchoredRule.Decided.indirectCommit_single rfl (fun _ _ h => h) (by omega) (by decide)
    sh8_slot5 (fun m h1 h2 h3 => by interval_cases m <;> exact absurd h3 (by decide))
    (by decide) ⟨16, by decide, Reaches.single (by decide)⟩

/-! ## The anchor-floor counterexample

`lowFloor` is Steelhead with every slot's floor read from the
synchronous wave: an anchor two rounds up, wherever the slot's own
certificates sit. It is the rule the paper's "r + w(anchor)" reading
would give. -/

/-- Steelhead's data at the synchronous floor for every slot. -/
def lowFloor : AnchoredRule (Fin 4) (Fin 32) Unit ValidWrt Correct :=
  { sh with waveAt := fun _ => 2 }

-- Under the low floor, slot `3` is an eligible anchor for slot `0`.
example : lowFloor.Eligible 0 3 := by decide

-- Slot `3` (round `3`, author `0`, block `12`) commits directly at wave
-- `3`, under either floor.
theorem lowFloor_slot3 : lowFloor.Decided sh8 (View.full sh8) 3 (some 12) :=
  AnchoredRule.Decided.directCommit (by decide) (by decide)

-- Block `12`'s history stops at round `3`: it reaches no round-`4`
-- certificate for block `1`.
theorem not_certifiedIn_12 : ¬ MahiMahi.CertifiedIn sh8 5 12 1 0 := by
  rw [MahiMahi.CertifiedIn, linkedVia_iff_history (by decide)]
  decide

/-- **The commit**: the direct route, unchanged. -/
theorem lowFloor_commit : lowFloor.Decided sh8 (View.full sh8) 0 (some 1) :=
  AnchoredRule.Decided.directCommit (by decide) (by decide)

/-- **The skip**: anchored on slot `3`, whose history carries no
certificate for slot `0`'s candidate. Two verdicts for one slot from one
view: the low floor is unsafe, on data. -/
theorem lowFloor_skip : lowFloor.Decided sh8 (View.full sh8) 0 none := by
  refine AnchoredRule.Decided.indirectSkip_single rfl (by omega) (by decide) lowFloor_slot3
    (fun m h1 h2 h3 => by interval_cases m <;> exact absurd h3 (by decide)) ?_
  intro L hL
  have hall : ∀ M : Fin 32, IsLeaderBlock sh8 0 M → M = 1 := by decide
  rw [hall L hL]
  exact not_certifiedIn_12

-- At the slot's own floor the same anchor is not eligible.
example : ¬ sh.Eligible 0 3 := by decide

/-! ## The chain on data -/

/-- A coin map: round `r` elects `(r + 2) % 4`. -/
def shCoin : ℕ → Fin 4 := fun r => ⟨(r + 2) % 4, by omega⟩

-- Round `0`'s coin candidate is block `2`, certified by the whole of
-- round `4` at wave `5`: chain-committed directly.
example : IsLeaderBlock (S := chainSlots shCoin) sh8 0 2 := by decide
theorem sh8_chain0 : ChainDecided 5 shCoin sh8 (View.full sh8) 0 (some 2) :=
  AnchoredRule.Decided.directCommit (S := chainSlots shCoin) (by decide) (by decide)

/-! ## Axioms

Nothing here should ever acquire an axiom beyond the standard three. -/

#print axioms sh8
#print axioms lowFloor_skip
#print axioms sh8_slot0_indirect

end LeanDagTest
