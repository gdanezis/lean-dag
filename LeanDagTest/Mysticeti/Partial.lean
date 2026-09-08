import LeanDagTest.Mysticeti.Growth
import LeanDag.Network.Quorum
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Ring
/-!
# Partial views — the non-degenerate witnesses

`liveness.md` §8 Q5. `Ugrow` and `ugrowTiming` show the liveness definitions
are *satisfiable*, but they satisfy them in the easiest possible way:

- `ugrowDelivery` sets `held v n` to **every** round-`n` block, so the
  delivery hop added by S2 never meets a genuinely partial view;
- `ugrowTiming` has `delay = 0` and zero drift, so S6's two-case induction
  only ever takes the **timeout-limited** branch.

Partial views are the normal case, not the exception, and a branch no witness
reaches is a branch where a mistake would hide. This file supplies both
missing cases over the same `Ugrow N` universe.
-/

namespace LeanDagTest

open LeanDag

/-! ## Rounds above the horizon are empty

Needed to discharge `DeliversQuorum`'s hypothesis, which is stated for every
`n` while `Ugrow N` only reaches `N`. -/

theorem ugrow_blocksAt_eq_empty {N n : ℕ} (h : N < n) : blocksAt (Ugrow N) n = ∅ := by
  rw [Finset.eq_empty_iff_forall_notMem]
  intro i hi
  rw [mem_blocksAt] at hi
  obtain ⟨him, hir⟩ := hi
  simp only [ugrow_ids, Finset.mem_range] at him
  simp only [ugrow_block, rrBlock_round] at hir
  omega

theorem ugrow_le_of_authorsAt {N n : ℕ} (h : 0 < (authorsAt (Ugrow N) n).card) :
    n ≤ N := by
  by_contra hc
  rw [authorsAt, ugrow_blocksAt_eq_empty (by omega)] at h
  simp [creatorsOf] at h

/-! ## A genuinely partial view

The Byzantine validator (`0`) withholds, so correct validators hold only the
three correct blocks of each round — a strict subset, and exactly the quorum.

This is the case §3(b) and S5 are about: withholding is free for the
adversary, so no argument may count on Byzantine-authored blocks arriving. -/

/-- What a correct validator holds when validator `0` publishes nothing. -/
def ugrowHonest (N : ℕ) : Delivery (Ugrow N) where
  held _ n := (blocksAt (Ugrow N) n).filter (fun i => ¬ (4 ∣ i))
  held_spec _ _ i hi := mem_blocksAt.mp (Finset.mem_filter.mp hi).1
  accepted _ n := (blocksAt (Ugrow N) n).filter (fun i => ¬ (4 ∣ i))
  accepted_sub _ _ := Finset.Subset.rfl
  accepted_inj := by
    intro _ n i hi j hj hij
    rw [Finset.mem_filter, mem_blocksAt] at hi hj
    have hv : (i % 4) = (j % 4) := by
      have := congrArg (fun (v : Fin 4) => (v : ℕ)) hij
      simpa using this
    simp only [ugrow_block, rrBlock_round] at hi hj
    omega
  accepts_correct _ _ _ _ h _ := h
  includes := by
    intro _ _ n b _ _ hbr i hi
    obtain ⟨hi, _⟩ := Finset.mem_filter.mp hi
    rw [mem_blocksAt] at hi
    simp only [ugrow_block, rrBlock_round] at hbr hi
    simp only [ugrow_block, mem_growBlock_refs]
    omega

/-- **The view really is partial.** Validator `0`'s round-`n` block exists in
the universe but is held by nobody. -/
theorem ugrowHonest_partial (N n : ℕ) (hn : n ≤ N) (v : Fin 4) :
    4 * n ∈ blocksAt (Ugrow N) n ∧ 4 * n ∉ (ugrowHonest N).held v n := by
  constructor
  · rw [mem_blocksAt]
    simp only [ugrow_ids, Finset.mem_range, ugrow_block, rrBlock_round]
    omega
  · intro h
    obtain ⟨_, hdvd⟩ := Finset.mem_filter.mp h
    exact hdvd ⟨n, by ring⟩

/-- Membership in `T` pins the validator index, which is what the arithmetic
of the timed witnesses needs. -/
theorem mem_T_bounds {v : Fin 4} (hv : v ∈ ({1, 2, 3} : Finset (Fin 4))) :
    1 ≤ (v : ℕ) ∧ (v : ℕ) ≤ 3 := by fin_cases hv <;> exact ⟨by decide, by decide⟩

#print axioms ugrowHonest_partial

end LeanDagTest
