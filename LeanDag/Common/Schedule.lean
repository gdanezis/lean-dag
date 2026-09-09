import LeanDag.Common.Anchored
import LeanDag.Common.Slots
import Mathlib.Data.Finset.Prod

/-!
# Leader schedules

Every deployed schedule is **uniform**: `m` leaders in every `p`-th
round, with the closed form `slotRound k = p * (k / m)`, so
`Slots.uniform` proves the three class fields once.

| | `p` | `m` | `slotRound k` |
|---|---|---|---|
| the original single-leader schedule | 3 | 1 | `3k` |
| pipelined, one leader per round | 1 | 1 | `k` |
| pipelined, `m` leaders per round | 1 | `m` | `k / m` |

The first row is the conservativity check: `uniformSingle 3` satisfies
the old three-round spacing condition, so the generalised `Decided`
loses no derivation the three-round schedule had.
-/

namespace LeanDag

namespace Slots

variable {Validator : Type*}

/-! ### Conservativity

`uniformSingle 3` is the schedule the development had before
pipelining; the results below are what "the generalisation loses
nothing" means concretely. -/

variable (elect : ℕ → Validator)

/-- **The old `spacing` field, recovered.** Consecutive slots of
`uniformSingle 3` really are three rounds apart, so the schedule the
development used before pipelining is an instance of the weakened class. -/
theorem uniformSingle_spacing (k : ℕ) :
    (uniformSingle 3 (by omega) elect).slotRound k + 3 ≤
      (uniformSingle 3 (by omega) elect).slotRound (k + 1) := by
  simp only [uniformSingle_slotRound]
  omega

/-- The other half of conservativity: under this schedule every later
slot may anchor an earlier one, so the generalised `Decided` offers
exactly the old constructors. Stated for an instance, how callers meet
the schedule. -/
example [S : Slots Validator] (hsp : ∀ k, S.slotRound k = 3 * k) {k j : ℕ} (h : k < j) :
    EligibleAt (S := S) 2 k j :=
  eligibleAt_of_lt_of_spacing (fun k => by simp [hsp]; omega) h

/-- **Slot indices do not outrun rounds.** `keyed` and `mono` inject the
slots at round `N` or below into `range (N + 1) ×ˢ univ`, bounding their
indices below `(N + 1) * card Validator` — the horizon a reverse pass
needs, since a round bound on blocks says nothing about slot indices
alone. -/
theorem slot_lt_of_slotRound_le {Validator : Type*} [Fintype Validator]
    [S : Slots Validator] {N k : ℕ} (h : S.slotRound k ≤ N) :
    k < (N + 1) * Fintype.card Validator := by
  classical
  have hsub : ∀ j ∈ Finset.range (k + 1),
      (S.slotRound j, S.leader j) ∈
        (Finset.range (N + 1)) ×ˢ (Finset.univ : Finset Validator) := by
    intro j hj
    have hjk : j ≤ k := by simpa [Nat.lt_succ_iff] using Finset.mem_range.1 hj
    have := S.mono hjk
    simp only [Finset.mem_product, Finset.mem_range, Finset.mem_univ, and_true]
    omega
  have hinj : Set.InjOn (fun j => (S.slotRound j, S.leader j)) (Finset.range (k + 1)) :=
    fun _ _ _ _ hab => S.keyed hab
  have := Finset.card_le_card_of_injOn _ hsub hinj
  simpa [Finset.card_product, Nat.lt_iff_add_one_le] using this

end Slots

end LeanDag
