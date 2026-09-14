import LeanDagTest.Mysticeti.Unbounded
import LeanDag.Steelhead.Helpers.Coin
import LeanDag.Steelhead.Model.Decision
import LeanDag.Common.Ledger
/-!
# Steelhead witness: no deterministic bound on the output's delay at period one

Theorem 2 of the paper says every honest block is ordered within `O(wa + b)` rounds of its
creation, `b` the number of Byzantine validators. At period `1` every slot is the coin's, and a
coin is uniform: it may name the one absent validator at `N + 1` rounds in a row, with
probability `n^-(N + 1) > 0` for every horizon `N`. On the DAG in which the three reliable
validators reference one another at every round and validator `0` never proposes, no slot below
the horizon then commits, so no settled prefix outputs a block, although every reliable round is
populated and synchronised from round `0` and the reliable round-`1` block exists at every
nontrivial horizon (`steelhead.md` §7, finding 6). The bound holds in expectation, or with
probability tending to one (SH15), not for every coin sequence.

The DAG is the family `Uomit 0 N` of `LeanDagTest/Mysticeti/Unbounded.lean` with the absent
validator's blocks removed.
-/

namespace LeanDagTest

namespace SteelheadCoinDelay

open LeanDag LeanDag.Steelhead
open scoped ENNReal

/-- The reliable validators' blocks of `Uomit 0 N`: those not authored by validator `0`. -/
def honestView (N : ℕ) : View (Fin 4) ℕ Unit (Uomit 0 N) where
  ids := (Uomit 0 N).ids.filter fun b => b % 4 ≠ 0
  subset_ids := Finset.filter_subset _ _
  complete := by
    intro i hi q hq
    simp only [Finset.mem_filter, uomit_ids, Finset.mem_range] at hi ⊢
    change q ∈ omitRefs 0 i at hq
    rw [mem_omitRefs] at hq
    simp only [Fin.val_zero] at hq
    omega

/-- **The DAG**: a reliable quorum at every round through `N`, validator `0` absent. -/
def dag (N : ℕ) : BlockUniverse (Fin 4) ℕ Unit := (honestView N).toRecord

/-- No block of the DAG is validator `0`'s. -/
theorem absent_zero (N b : ℕ) (hb : b ∈ (dag N).ids) : ((dag N).block b).creator ≠ 0 := by
  change b ∈ (Finset.range (4 * (N + 1))).filter (fun b => b % 4 ≠ 0) at hb
  intro hc
  have hv := congrArg Fin.val hc
  change b % 4 = 0 at hv
  exact (Finset.mem_filter.mp hb).2 hv

/-- Every reliable validator has a block at every round through the horizon. -/
theorem populated (N r : ℕ) (hr : r ≤ N) : PopulatedOn (dag N) Correct r := by
  intro v hv
  have hv0 : v ≠ (0 : Fin 4) := (by decide : ∀ v : Fin 4, v ∈ Correct → v ≠ 0) v hv
  have hvpos : 0 < v.val := by
    have : v.val ≠ 0 := fun h => hv0 (Fin.ext h)
    omega
  refine ⟨4 * r + v.val, ?_, ?_, ?_⟩
  · change 4 * r + v.val ∈ (Finset.range (4 * (N + 1))).filter (fun b => b % 4 ≠ 0)
    simp only [Finset.mem_filter, Finset.mem_range]
    have := v.isLt
    omega
  · apply Fin.ext
    change (4 * r + v.val) % 4 = v.val
    omega
  · change (4 * r + v.val) / 4 = r
    omega

/-- Every reliable block references every reliable block of the round below: synchronised from
round `0`. -/
theorem synchronised (N : ℕ) : SynchronisedOn (dag N) Correct 0 := by
  intro r _ b hb hbr _ a ha har _
  have ha0 := absent_zero N a ha
  have ha0' : a % 4 ≠ 0 := by
    intro h
    exact ha0 (Fin.ext h)
  change b / 4 = r + 1 at hbr
  change a / 4 = r at har
  change a ∈ omitRefs 0 b
  rw [mem_omitRefs]
  simp only [Fin.val_zero]
  omega

/-- A slot the coin hands to the absent validator commits nothing, by any route: a committed
verdict names a block of its leader. -/
theorem no_commit {N r : ℕ} {coin : ℕ → Fin 4} (hc : coin r = 0)
    (V : View (Fin 4) ℕ Unit (dag N)) (L : ℕ) :
    ¬ Decided (S := chainSlots coin) (fun _ => 5) (dag N) V r (some L) := by
  intro hd
  have hL := AnchoredRule.isLeaderBlock_of_decided (S := chainSlots coin) hd
  exact absent_zero N L hL.1 (hL.2.2.trans hc)

/-- Every block of the DAG lies at or below the horizon. -/
theorem round_le (N b : ℕ) (hb : b ∈ (dag N).ids) : ((dag N).block b).round ≤ N := by
  change b ∈ (Finset.range (4 * (N + 1))).filter (fun b => b % 4 ≠ 0) at hb
  have := Finset.mem_range.mp (Finset.mem_filter.mp hb).1
  change b / 4 ≤ N
  omega

/-- With the coin naming validator `0` through the horizon, no slot at all commits: a slot above
the horizon has no candidate, a slot below has an absent leader. -/
theorem no_commit_in_horizon {N : ℕ} {coin : ℕ → Fin 4} (hc : ∀ r, r ≤ N → coin r = 0)
    (V : View (Fin 4) ℕ Unit (dag N)) (r L : ℕ) :
    ¬ Decided (S := chainSlots coin) (fun _ => 5) (dag N) V r (some L) := by
  intro hd
  have hL := AnchoredRule.isLeaderBlock_of_decided (S := chainSlots coin) hd
  have hr := round_le N L hL.1
  rw [hL.2.1] at hr
  exact no_commit (hc r hr) V L hd

/-- **No settled prefix outputs a block** while the coin names validator `0` through the
horizon, whatever the view and however long the prefix. -/
theorem no_output_by_horizon {N : ℕ} {coin : ℕ → Fin 4} (hc : ∀ r, r ≤ N → coin r = 0)
    (V : View (Fin 4) ℕ Unit (dag N)) (g : ℕ → Option ℕ) (n : ℕ)
    (hg : ∀ r, r < n → Decided (S := chainSlots coin) (fun _ => 5) (dag N) V r (g r)) :
    ledgerSet (dag N) g n = ∅ := by
  ext b
  constructor
  · rintro ⟨r, hr, L, hL, _⟩
    have hd := hg r hr
    rw [hL] at hd
    exact (no_commit_in_horizon hc V r L hd).elim
  · simp

/-- The reliable round-`1` block of validator `1` exists at every nontrivial horizon: the honest
block Theorem 2's bound is about. -/
theorem honest_block_exists (N : ℕ) (hN : 1 ≤ N) :
    5 ∈ (dag N).ids ∧ ((dag N).block 5).round = 1 ∧ ((dag N).block 5).creator ∈ Correct := by
  refine ⟨?_, rfl, ?_⟩
  · change 5 ∈ (Finset.range (4 * (N + 1))).filter (fun b => b % 4 ≠ 0)
    simp only [Finset.mem_filter, Finset.mem_range]
    omega
  · change (1 : Fin 4) ∈ Correct
    decide

/-- The coins of the `N + 1` rounds, extended past the horizon by validator `1`. -/
def sampleCoin (N : ℕ) (coins : Fin (N + 1) → Fin 4) (r : ℕ) : Fin 4 :=
  if h : r < N + 1 then coins ⟨r, h⟩ else 1

/-- **The no-output event has positive probability at every horizon**: the coins that name
validator `0` at every round through `N` are one map among `4^(N + 1)`, and under them no
settled prefix of any view outputs a block. -/
theorem positive_no_output (N : ℕ) :
    0 < (PMF.uniformOfFintype (Fin (N + 1) → Fin 4)).toOuterMeasure
      {coins | ∀ (V : View (Fin 4) ℕ Unit (dag N)) (g : ℕ → Option ℕ) (n : ℕ),
        (∀ r, r < n → Decided (S := chainSlots (sampleCoin N coins))
          (fun _ => 5) (dag N) V r (g r)) → ledgerSet (dag N) g n = ∅} := by
  apply lt_of_lt_of_le (constant_coin_probability_pos (0 : Fin 4) (N + 1))
  apply MeasureTheory.measure_mono
  intro coins hc V g n hg
  apply no_output_by_horizon (V := V) (g := g) (n := n) ?_ hg
  intro r hr
  simp only [sampleCoin, dif_pos (show r < N + 1 by omega)]
  exact hc _

/-! ## Axioms -/

#print axioms positive_no_output
#print axioms populated
#print axioms synchronised

end SteelheadCoinDelay

end LeanDagTest
