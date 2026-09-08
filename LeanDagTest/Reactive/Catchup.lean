import LeanDagTest.Reactive.Model
import LeanDagTest.Mysticeti.ViewPace
import Mathlib.Algebra.Group.Action.Defs
/-!
# The collapse bound is tight

Two facts about the collapsed spread `Δ + proc`, both on data.

The bound is *attained and kept*: `ugrowSkew_spread_constant` shows the
running witness carrying a spread of exactly `Δ + proc = 2` at every
round, for ever — the collapse contracts any larger spread down to the
bound (`Collapse.lean` exhibits that), but nothing contracts past it,
so `drift_collapse`'s constant cannot be improved.

And the wait bound runs at it: `ugrowCatchPace` is a `ViewPace` at
spacing `5`, `delay 2`, `proc 1`, and `decided_of_wait` commits a slot
at timeout `5 = 2Δ + proc` with **no start-spread hypothesis anywhere**
— the threshold is a constant of the network and the implementation,
met here with equality.
-/

namespace LeanDagTest

open LeanDag

attribute [local instance 2000] rrSlots

/-- **Drift does not contract past the collapse bound.** The skewed
witness satisfies every clause — catch-up included, at `proc = 0` — and
its spread is exactly `Δ + proc = 2` at every round, for ever:
`drift_collapse`'s constant is met with equality and cannot be
improved. -/
theorem ugrowSkew_spread_constant (N n : ℕ) :
    (ugrowSkewPace N).built 3 n = (ugrowSkewPace N).built 1 n + 2 := by
  change (3 : ℕ) + 4 * n = ((1 : ℕ) + 4 * n) + 2
  omega

/-- What `v` holds at time `t` on the `5`-spaced schedule: block `b`
(built at `b % 4 + 5 * (b / 4)`) has arrived once `delay = 2` has
passed, and one's own block is in hand at once. -/
def catchHolds (N : ℕ) (v : Fin 4) (t : ℕ) : Finset ℕ :=
  (Finset.range (4 * (N + 1))).filter fun b =>
    b % 4 + 5 * (b / 4) + 2 ≤ t ∨ (b % 4 = (v : ℕ) ∧ b % 4 + 5 * (b / 4) ≤ t)

/-! ## The witness -/
def ugrowCatchPace (N : ℕ) : ViewPace (Ugrow N) {1, 2, 3} N where
  top _ := N
  built v n := (v : ℕ) + 5 * n
  timeout _ := 5
  gst := 0
  delay := 2
  proc := 1
  rounds_le b hb := by
    simp only [ugrow_ids, Finset.mem_range] at hb
    simp only [ugrow_block, rrBlock_round]; omega
  built_of_le_top v hv n hn := rrUniverse_populatedOn _ _ _ _ _ _ hn v hv
  le_top_of_built _ _ b hb _ := by
    simp only [ugrow_ids, Finset.mem_range] at hb
    simp only [ugrow_block, rrBlock_round]; omega
  waits _ _ _ _ := by omega
  timeout_pos _ := by omega
  latest n := 3 + 5 * n
  built_le_latest v _ _ _ := by have := v.isLt; omega
  refs_held v hv n b hb hbc hbr := by
    obtain ⟨h1, h3⟩ := mem_T_bounds hv
    intro j hj
    simp only [ugrow_ids, Finset.mem_range] at hb
    simp only [ugrow_block, rrBlock_round] at hbr
    simp only [ugrow_block, mem_growBlock_refs] at hj
    simp only [catchHolds, Finset.mem_filter, Finset.mem_range]
    exact ⟨by omega, Or.inl (by omega)⟩
  holds := catchHolds N
  holds_sub _ _ := by
    simp only [catchHolds, ugrow_ids]; exact Finset.filter_subset _ _
  holds_closed v hv t b hb j hj := by
    obtain ⟨h1, h3⟩ := mem_T_bounds hv
    simp only [catchHolds, Finset.mem_filter, Finset.mem_range] at hb ⊢
    simp only [ugrow_block, mem_growBlock_refs] at hj
    have hjd : j / 4 + 1 = b / 4 := by omega
    refine ⟨by omega, Or.inl ?_⟩
    rcases hb.2 with h | ⟨_, h⟩ <;> omega
  holds_own v hv n _ b hb hbc hbr := by
    obtain ⟨h1, h3⟩ := mem_T_bounds hv
    simp only [ugrow_ids, Finset.mem_range] at hb
    simp only [ugrow_block, rrBlock_round] at hbr
    have hb4 : b % 4 = (v : ℕ) := by
      have := congrArg (fun (x : Fin 4) => (x : ℕ)) hbc
      simpa [ugrow_block] using this
    simp only [catchHolds, Finset.mem_filter, Finset.mem_range]
    exact ⟨hb, Or.inr ⟨hb4, by omega⟩⟩
  holds_mono v s t hst := by
    intro b hb
    simp only [catchHolds, Finset.mem_filter, Finset.mem_range] at hb ⊢
    exact ⟨hb.1, by omega⟩
  converges v _ w _ t _ := by
    intro b hb
    simp only [catchHolds, Finset.mem_filter, Finset.mem_range] at hb ⊢
    refine ⟨hb.1, Or.inl ?_⟩
    rcases hb.2 with h | h
    · omega
    · omega
  references v hv n hn c hc hcc hcr a ha har := by
    obtain ⟨h1, h3⟩ := mem_T_bounds hv
    simp only [catchHolds, Finset.mem_filter, Finset.mem_range] at ha
    simp only [ugrow_block, rrBlock_round] at har hcr
    simp only [ugrow_block, mem_growBlock_refs]
    omega
  advances _ _ _ hn _ _ := hn
  catchup v hv n hn b hb hbT hbr t _ hheld := by
    obtain ⟨hv1, hv3⟩ := mem_T_bounds hv
    simp only [ugrow_ids, Finset.mem_range] at hb
    simp only [ugrow_block, rrBlock_round] at hbr
    simp only [catchHolds, Finset.mem_filter, Finset.mem_range] at hheld
    refine ⟨hn, ?_⟩
    change (v : ℕ) + 5 * n ≤ t + 1
    have hv4 := v.isLt
    rcases hheld.2 with h | ⟨_, h⟩
    · omega
    · omega

/-- **The commit at `2Δ + proc`, production derived, no start spread.**
Nothing in the structure asserts a block above round `0`. -/
theorem ugrowCatchPace_decided (N : ℕ) (hN : rrSlots.slotRound 1 + 2 ≤ N) :
    ∃ L, IsLeaderBlock (S := rrSlots) (Ugrow N) 1 L ∧
      Decided (S := rrSlots) (Ugrow N) (View.full (Ugrow N)) 1 (some L) :=
  (ugrowCatchPace N).decided_of_wait (R := 0) (by decide)
    (le_refl 0) (fun n _ => by change 2 * 2 + 1 ≤ 5; omega)
    (Nat.zero_le _) hN (by decide)

/-! ## The rush bound, on data

The honest floor of `exists_honest_floor` (CU5) is met with equality on
the running witness: at constant timeout `4`, the accumulated floor for
round `n` is `built u 0 + 4n`, which is exactly `built u n` — a valid
block of round `n + 1` certifies a reliable validator that paid the full
bill, and on this schedule the bill is the whole build time. -/

example (N n : ℕ) :
    (ugrowSkewPace N).built 1 0 + (∑ i ∈ Finset.range n, (ugrowSkewPace N).timeout i)
      = (ugrowSkewPace N).built 1 n := by
  show (1 : ℕ) + 4 * 0 + (∑ _i ∈ Finset.range n, 4) = 1 + 4 * n
  rw [Finset.sum_const, Finset.card_range, smul_eq_mul]
  omega

#print axioms ugrowCatchPace_decided
#print axioms LeanDag.PaceCore.drift_collapse
#print axioms LeanDag.ViewPace.decided_of_wait
#print axioms ugrowSkew_spread_constant
#print axioms LeanDag.exists_reliable_parent
#print axioms LeanDag.PaceCore.round_le_top_succ
#print axioms LeanDag.ViewPace.exists_honest_floor

end LeanDagTest
