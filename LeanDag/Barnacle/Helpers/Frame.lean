import LeanDag.Barnacle.Model.Schedule
import LeanDag.Properties.Derived.Frame
/-!
# Barnacle's schedule as a frame

`Sched getLeader hk m` is the constant frame: every round holds `m`
slots and position `i` of round `r` is led by `getLeader (r + i)`.
`sched_frame_local` is what that buys — a configuration's verdicts are
settled within its own rounds, so the count may change above them.
-/

namespace LeanDag

namespace Barnacle

variable {Validator : Type} [Fintype Validator] [DecidableEq Validator]

/-- **A count's leaders are distinct within a round**, in the frame's own
coordinates: `Keyed` read at the slots of one round. -/
theorem keyed_frame {getLeader : ℕ → Validator} {w : ℕ} (hk : Keyed getLeader w)
    {m : ℕ} (hm : 0 < m) (hmax : m ≤ w) :
    ∀ r i j, i < (constFrame m hm).width r → j < (constFrame m hm).width r →
      getLeader (r + i) = getLeader (r + j) → i = j := by
  intro r i j hi' hj' he
  have hi : i < m := hi'
  have hj : j < m := hj'
  have hd₁ : (m * r + i) / m = r := by rw [Nat.mul_add_div hm, Nat.div_eq_of_lt hi]; omega
  have hd₂ : (m * r + j) / m = r := by rw [Nat.mul_add_div hm, Nat.div_eq_of_lt hj]; omega
  have hm₁ : (m * r + i) % m = i := by
    rw [Nat.mul_add_mod, Nat.mod_eq_of_lt hi]
  have hm₂ : (m * r + j) % m = j := by
    rw [Nat.mul_add_mod, Nat.mod_eq_of_lt hj]
  have := hk m hm hmax (m * r + i) (m * r + j) (by rw [hd₁, hd₂])
    (by rw [hd₁, hd₂, hm₁, hm₂]; exact he)
  omega

/-- **Barnacle's schedule is the constant frame.** At count `m` every
round holds `m` slots and position `i` of round `r` is led by
`getLeader (r + i)`. -/
theorem Sched_eq_frame (getLeader : ℕ → Validator) {w : ℕ} (hk : Keyed getLeader w)
    (m : ℕ) (hm : 0 < m) (hmax : m ≤ w) :
    Sched getLeader hk m hm hmax
      = (constFrame m hm).toSlots (fun r i => getLeader (r + i)) (keyed_frame hk hm hmax) := by
  refine Slots.ext' ?_ ?_
  · funext g
    show 1 * (g / m) = (constFrame m hm).roundOf g
    rw [constFrame_roundOf, Nat.one_mul]
  · funext g
    show getLeader (g / m + g % m)
      = getLeader ((constFrame m hm).roundOf g
          + (g - (constFrame m hm).cum ((constFrame m hm).roundOf g)))
    rw [constFrame_roundOf, constFrame_cum]
    congr 1
    have h := Nat.div_add_mod g m
    have e : g / m * m = m * (g / m) := Nat.mul_comm _ _
    omega


/-- **A configuration's verdicts do not depend on what the count becomes
later.** Every slot decided under the schedule of count `m` has a round
bound below which that count and its rotation settle it; above the bound
the widths may be anything, so in particular they may be the count the
next configuration installs.

This is the assumption Barnacle's runs have been making. `PartialRun`
records a configuration's verdicts as decided against
`Sched getLeader hk (count k)`, the uniform schedule at that count
extended to every round, which is not the schedule that runs once the
count changes. What makes that sound is that a configuration's verdicts
are settled within its own rounds, and this is that statement. -/
theorem sched_frame_local {BlockId : Type} [DecidableEq BlockId] {Payload : Type}
    {R : Properties.DagRule Validator BlockId Payload} (hb : Properties.Banded R)
    {getLeader : ℕ → Validator} {w : ℕ} {hk : Keyed getLeader w}
    {m : ℕ} {hm : 0 < m} {hmax : m ≤ w}
    {U : R.Universe} {V : R.View U} {g : ℕ} {v : Option BlockId}
    (hd : R.Decided (Sched getLeader hk m hm hmax) V g v) :
    ∃ B, g / m < B ∧
      ∀ (F' : Frame) (asg' : ℕ → ℕ → Validator) (hk'),
        (∀ r, r < B → F'.width r = m) →
        (∀ r i, r < B → i < m → asg' r i = getLeader (r + i)) →
        R.Decided (F'.toSlots asg' hk') V g v := by
  rw [Sched_eq_frame getLeader hk m hm hmax] at hd
  obtain ⟨B, hB, ht⟩ := Properties.decided_of_frame_agree hb hd
  rw [constFrame_roundOf] at hB
  exact ⟨B, hB, fun F' asg' hk' hw ha => ht F' asg' hk' hw ha⟩

end Barnacle
end LeanDag
