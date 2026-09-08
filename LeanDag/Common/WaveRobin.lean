import LeanDag.Common.Schedule
import LeanDag.Mysticeti.Liveness
/-!
# The wave-aligned rotation — fairness as a theorem

`FairRunOn` and `SpansEligible` are stated hypotheses, since
`Slots.leader` is arbitrary; what can be a theorem is that some
schedule satisfies them, at every `n` and fault configuration. The
trick is to sidestep the per-slot pigeonhole: `waveRobin` rotates by
**waves**, the leader holding three consecutive slots before advancing,
so one correct leader's wave is a full correct 3-run by itself and
`FairRunOn Correct 3` needs nothing but `Correct.Nonempty`. One fair
schedule suffices, since the liveness theorems quantify over every
`Slots` instance.
-/

namespace LeanDag

variable {Validator : Type*} [Fintype Validator] [DecidableEq Validator]
variable [F : Faults Validator]

/-- The correct pool is nonempty, at least `2 F.f + 1 ≥ 1` members — all
wave-aligned fairness needs, since one correct validator is one
recurring correct wave. -/
theorem correct_nonempty : (Correct : Finset Validator).Nonempty :=
  Finset.card_pos.mp (by
    have := two_f_add_one_le_card_correct (Validator := Validator)
    omega)

/-- **A fair schedule exists — wave-aligned rotation, unconditionally.**
The witness for slot `k` is a correct validator `v`'s wave in the `k`-th
rotation cycle: slot `3 * (v + n * k)` opens a wave led by `v`, past `k`,
with all three slots `v`-led. -/
theorem waveRobin_fairRun (n : ℕ) (hn : 0 < n) [F : Faults (Fin n)] :
    FairRunOn (S := waveRobin n hn) (Correct : Finset (Fin n)) 3 := by
  intro k
  obtain ⟨v, hv⟩ := correct_nonempty (Validator := Fin n)
  refine ⟨3 * (v.val + n * k), ?_, ?_⟩
  · have hk : k ≤ n * k := Nat.le_mul_of_pos_left k hn
    omega
  · intro i hi
    have hleader : (waveRobin n hn).leader (3 * (v.val + n * k) + i) = v := by
      apply Fin.ext
      rw [waveRobin_leader_val, Nat.mul_add_div (by omega), Nat.div_eq_of_lt hi,
        Nat.add_zero, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt v.isLt]
    rw [hleader]
    exact hv

/-- **`SpansEligibleAt 2 3`, the core's pipelined shape, at every `n`.**
A run of three consecutive slots reaches three rounds past everything
below it. -/
theorem waveRobin_spansEligible (n : ℕ) (hn : 0 < n) :
    SpansEligibleAt (S := waveRobin n hn) 2 3 := by
  intro b i hi
  simp only [eligibleAt_iff, waveRobin_slotRound]
  omega

/-- The wave-aligned rotation is fair in the single-slot sense too, so L6 and
the `ViewPace` results apply to it unchanged. -/
theorem waveRobin_fairSchedule (n : ℕ) (hn : 0 < n) [F : Faults (Fin n)] :
    FairScheduleOn (S := waveRobin n hn) (Correct : Finset (Fin n)) :=
  FairRunOn.fairScheduleOn (S := waveRobin n hn) (by omega) (waveRobin_fairRun n hn)

end LeanDag
