import LeanDag.Common.Slots
/-!
# A schedule whose rounds differ in width

`Slots` asks `slotRound` to be monotone and unbounded, `leader` to be a
function, and the pair to be injective. It does *not* ask a round to hold
a fixed number of slots, so a schedule of varying width is a lawful
instance and needs no separate notion of a width.

`vary` is that on data: rounds alternate one slot and two, so slots
`0, 1, 2, 3, 4, 5, …` sit at rounds `0, 1, 1, 2, 3, 3, …`. This is the
check `barnacle-schedules.md` §9 asks for before a configuration is
allowed to emit a schedule.
-/

namespace LeanDagTest
namespace VaryingSchedule

open LeanDag

/-- Round `2j` holds one slot and round `2j + 1` holds two, so slot `k`
sits at round `2 * (k / 3)`, plus one when `k` is not a multiple of
three. -/
def varyRound (k : ℕ) : ℕ := 2 * (k / 3) + (if k % 3 = 0 then 0 else 1)

/-- Within a round the two slots differ in parity, which is what keeps
the round-and-leader pair injective. -/
def varyLeader (k : ℕ) : Fin 2 := ⟨k % 2, Nat.mod_lt _ (by omega)⟩

example : varyRound 0 = 0 := rfl
example : varyRound 1 = 1 := rfl
example : varyRound 2 = 1 := rfl
example : varyRound 3 = 2 := rfl
example : varyRound 4 = 3 := rfl
example : varyRound 5 = 3 := rfl

theorem varyRound_mono : Monotone varyRound := by
  intro a b hab
  unfold varyRound
  have h3 : (0:ℕ) < 3 := by omega
  have ha := Nat.div_add_mod a 3
  have hb := Nat.div_add_mod b 3
  have hda : a / 3 ≤ b / 3 := Nat.div_le_div_right hab
  have hma : a % 3 < 3 := Nat.mod_lt _ h3
  have hmb : b % 3 < 3 := Nat.mod_lt _ h3
  split <;> split <;> omega

/-- **A schedule of varying width.** Rounds alternate one slot and two,
and nothing in `Slots` objects. -/
def vary : Slots (Fin 2) where
  slotRound := varyRound
  leader := varyLeader
  mono := varyRound_mono
  unbounded := fun n => ⟨3 * n, by
    show n ≤ varyRound (3 * n)
    unfold varyRound
    rw [Nat.mul_div_cancel_left _ (by omega), Nat.mul_mod_right]
    omega⟩
  keyed := by
    intro a b hab
    simp only [Prod.mk.injEq] at hab
    obtain ⟨hr, hl⟩ := hab
    have hva : varyRound a = 2 * (a / 3) + (if a % 3 = 0 then 0 else 1) := rfl
    have hvb : varyRound b = 2 * (b / 3) + (if b % 3 = 0 then 0 else 1) := rfl
    have hlv := congrArg Fin.val hl
    simp only [varyLeader] at hlv
    rw [hva, hvb] at hr
    have hda := Nat.div_add_mod a 3
    have hdb := Nat.div_add_mod b 3
    have hma : a % 3 < 3 := Nat.mod_lt _ (by omega)
    have hmb : b % 3 < 3 := Nat.mod_lt _ (by omega)
    split at hr <;> split at hr <;> omega

/-- Round `1` holds two slots and round `0` holds one, so the width is
not constant. -/
example : vary.slotRound 1 = vary.slotRound 2 := rfl
example : vary.slotRound 0 ≠ vary.slotRound 1 := by decide
example : vary.leader 1 ≠ vary.leader 2 := by decide

/-- **The bound liveness reads, on this schedule**: no round holds more
than two slots, stated without naming a width — two slots `n` apart
cannot share a round once `n` is the bound. -/
theorem vary_width_le (k : ℕ) : vary.slotRound k < vary.slotRound (k + 2) := by
  show varyRound k < varyRound (k + 2)
  unfold varyRound
  have hd := Nat.div_add_mod k 3
  have hm : k % 3 < 3 := Nat.mod_lt _ (by omega)
  have hd2 := Nat.div_add_mod (k + 2) 3
  have hm2 : (k + 2) % 3 < 3 := Nat.mod_lt _ (by omega)
  split <;> split <;> omega

end VaryingSchedule

end LeanDagTest
