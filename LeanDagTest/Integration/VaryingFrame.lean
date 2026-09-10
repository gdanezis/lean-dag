import LeanDag.Integration.AdaptiveFrame
/-!
# A frame whose rounds differ in width

`Frame.width` is an arbitrary function of the round, so nothing in the
common layer ties one round's width to its neighbour's. This file
exhibits that: `vF` cycles through widths `1`, `2`, `3`, so no two
consecutive rounds are alike, and it is a lawful schedule that satisfies
the spanning clause liveness consumes.

What forbids per-round widths is `CompRun.cnt_eq`, which makes every
round of a configuration's range that configuration's count wide. That is
Barnacle's clause, not the frame's.
-/

namespace LeanDagTest
namespace VaryingFrame

open LeanDag LeanDag.Integration

/-- Widths `1, 2, 3, 1, 2, 3, …`: no two consecutive rounds alike. -/
def vF : Frame where
  width := fun r => r % 3 + 1
  width_pos := fun _ => by omega

example : vF.width 0 = 1 := rfl
example : vF.width 1 = 2 := rfl
example : vF.width 2 = 3 := rfl
example : vF.width 3 = 1 := rfl

theorem vF_le (r : ℕ) : vF.width r ≤ 3 := by
  show r % 3 + 1 ≤ 3
  omega

/-- Position `i` of a round is led by validator `i`. -/
abbrev vAsg : ℕ → ℕ → Fin 4 := fun _ i => ⟨i % 4, by omega⟩

theorem vAsg_keyed : ∀ r i j, i < vF.width r → j < vF.width r →
    vAsg r i = vAsg r j → i = j := by
  intro r i j hi hj h
  have hi' : i < 3 := lt_of_lt_of_le hi (vF_le r)
  have hj' : j < 3 := lt_of_lt_of_le hj (vF_le r)
  have := congrArg Fin.val h
  simp only at this
  omega

/-- The schedule the varying frame gives: slot `g` at round
`vF.roundOf g`, led by its position in that round. -/
noncomputable abbrev vSched : Slots (Fin 4) := vF.toSlots vAsg vAsg_keyed

/-- Its rounds are the frame's, and consecutive slots may share one. -/
example : vSched.slotRound 0 = 0 := by
  show vF.roundOf 0 = 0
  exact vF.roundOf_eq (by simp) (by rw [Frame.cum_succ]; simp [vF])

/-- **A frame whose rounds differ in width still spans a wave.** The
clause `Descends` consumes asks the widths to be bounded, not equal, so
`M = 3` is all it needs of `vF`. -/
theorem vF_spans {wave c : ℕ} (hc : 3 * (wave + 1) ≤ c) :
    SpansEligibleAt (S := vSched) wave c :=
  Frame.spansEligible_toSlots vF_le hc

end VaryingFrame

end LeanDagTest
