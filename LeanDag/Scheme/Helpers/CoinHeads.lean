import LeanDag.Scheme.Model.Schedules
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import LeanDag.Scheme.Model.NoFaults
import LeanDag.Steelhead.Helpers.Coin
/-!
# The coin's heads

`coinHead` reads the head of round `ρ` off block `ρ / w` of a draw at
position `ρ mod w` (`coinHead_eq`). If every window of `M` blocks holds a
block of safe heads, then from every round a wave of safe heads lies within
two windows (`safeHeadRuns_of_windows`). A uniform draw leaves some window
without such a block with probability at most `J · badBlockBoundAt c w ^ M`
(`windowsFail_le`).
-/

namespace LeanDag

namespace Scheme

variable {Validator : Type} [Fintype Validator] [DecidableEq Validator]
variable {BlockId : Type} [LinearOrder BlockId] {Payload : Type}
variable {P : Validity Validator BlockId Payload} {honest : Finset Validator}

/-- Block `m` of window `j` is block `j · M + m` of the draw. -/
theorem blk_lt {J M j m : ℕ} (hj : j < J) (hm : m < M) : j * M + m < J * M :=
  calc j * M + m < j * M + M := by omega
    _ = (j + 1) * M := by ring
    _ ≤ J * M := Nat.mul_le_mul_right M hj

omit [Fintype Validator] [DecidableEq Validator] in
/-- **The head of round `k · w + i` is the draw's coin `i` of block `k`.** -/
theorem coinHead_eq {J M w : ℕ} (dflt : Validator) (g : Fin (J * M) → Fin w → Validator)
    {k i : ℕ} (hk : k < J * M) (hi : i < w) :
    coinHead dflt g (k * w + i) = g ⟨k, hk⟩ ⟨i, hi⟩ := by
  have hw0 : 0 < w := by omega
  have hdiv : (k * w + i) / w = k := by
    rw [Nat.add_comm, Nat.add_mul_div_right _ _ hw0, Nat.div_eq_of_lt hi, Nat.zero_add]
  have hmod : (k * w + i) % w = i := by
    rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hi]
  unfold coinHead
  rw [dif_pos ⟨by rw [hdiv]; exact hk, hw0⟩]
  congr 1
  · exact Fin.ext hdiv
  · exact Fin.ext hmod

omit [Fintype Validator] in
/-- **Windows of good blocks give runs of safe heads**: the draw's coins
range over `X`, each read as a leader by `φ`; if each of `J` windows of `M`
blocks holds a block whose `w` coins lie in sets `Sr` that `φ` maps into the
safe sets, and the rounds up to `N` fill the windows, then from every round
a wave of safe heads lies within `2 · M · w` rounds. -/
theorem safeHeadRuns_of_windows {X : Type} (p : Params)
    (U : BlockRecord Validator BlockId Payload P honest) {J M w : ℕ}
    (hw : p.waveLength - 1 + 1 = w) (dflt : X) (φ : X → Validator) (Sr : ℕ → Finset X)
    (hφ : ∀ r x, x ∈ Sr r → φ x ∈ safeAt p U r)
    (g : Fin (J * M) → Fin w → X) {N : ℕ} (hNJ : N + 1 ≤ J * (M * w))
    (hgood : ∀ j : Fin J, ∃ m : Fin M, ∀ i : Fin w,
      g ⟨j * M + m, blk_lt j.isLt m.isLt⟩ i ∈ Sr ((j * M + m) * w + i)) :
    SafeHeadRuns p U (fun ρ => φ (coinHead dflt g ρ)) (2 * (M * w)) 0 N := by
  have hw0 : 0 < w := by omega
  intro r _ hr
  rw [hw] at hr ⊢
  have hLpos : 0 < M * w := by
    rcases Nat.eq_zero_or_pos (M * w) with h | h
    · rw [h] at hNJ; simp at hNJ
    · exact h
  have har : r / (M * w) * (M * w) ≤ r := Nat.div_mul_le_self r (M * w)
  have har2 : r < r / (M * w) * (M * w) + M * w := Nat.lt_div_mul_add hLpos
  have hjJ : r / (M * w) + 1 < J := by
    have h1 : (r / (M * w) + 2) * (M * w) ≤ J * (M * w) := by
      have : (r / (M * w) + 2) * (M * w) = r / (M * w) * (M * w) + 2 * (M * w) := by ring
      rw [this]
      omega
    have := Nat.le_of_mul_le_mul_right h1 hLpos
    omega
  obtain ⟨m, hm⟩ := hgood ⟨r / (M * w) + 1, hjJ⟩
  have e1 : ((r / (M * w) + 1) * M + m) * w =
      r / (M * w) * (M * w) + M * w + (m : ℕ) * w := by ring
  have e2 : (m : ℕ) * w + w ≤ M * w := by
    have := Nat.mul_le_mul_right w (show (m : ℕ) + 1 ≤ M from m.isLt)
    linarith [Nat.add_mul (m : ℕ) 1 w]
  refine ⟨((r / (M * w) + 1) * M + m) * w, ?_, ?_, fun i hi => ?_⟩
  · have := e1; omega
  · have := e1; omega
  · have hi' : i < w := by omega
    show φ (coinHead dflt g (((r / (M * w) + 1) * M + m) * w + i)) ∈ _
    rw [coinHead_eq dflt g (blk_lt hjJ m.isLt) hi']
    exact hφ _ _ (hm ⟨i, hi'⟩)

omit [LinearOrder BlockId] in
/-- **A supporting table hits every large set**: a table supporting `k`
validators with weight `e` has at least `e · (k + s − n)` entries in any set
of `s` validators, since the support meets the set in `k + s − n` of them. -/
theorem card_hits_ge {m k e s : ℕ} {tbl : Fin m → Validator} (htbl : Supports tbl k e)
    {S : Finset Validator} (hS : s ≤ S.card) :
    e * (k + s - Fintype.card Validator) ≤ (Finset.univ.filter fun j => tbl j ∈ S).card := by
  obtain ⟨D, hD, hfib⟩ := htbl
  have hinter : k + s - Fintype.card Validator ≤ (D ∩ S).card := by
    have := Finset.card_inter_add_card_union D S
    have := Finset.card_le_univ (D ∪ S)
    omega
  have hsum : (Finset.univ.filter fun j => tbl j ∈ D ∩ S).card =
      ∑ v ∈ D ∩ S, ((Finset.univ.filter fun j => tbl j ∈ D ∩ S).filter fun j => tbl j = v).card :=
    Finset.card_eq_sum_card_fiberwise fun j hj => (Finset.mem_filter.mp hj).2
  have hge : (D ∩ S).card * e ≤ (Finset.univ.filter fun j => tbl j ∈ D ∩ S).card := by
    rw [hsum]
    refine le_trans ?_ (Finset.card_nsmul_le_sum _ _ e fun v hv => ?_)
    · simp
    · have heq : ((Finset.univ.filter fun j => tbl j ∈ D ∩ S).filter fun j => tbl j = v) =
          Finset.univ.filter fun j => tbl j = v := by
        ext j; simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        exact ⟨fun h => h.2, fun h => ⟨h ▸ hv, h⟩⟩
      rw [heq]
      exact hfib v (Finset.mem_inter.mp hv).1
  have hsub : (Finset.univ.filter fun j => tbl j ∈ D ∩ S) ⊆
      Finset.univ.filter fun j => tbl j ∈ S := fun j hj => by
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_inter] at hj ⊢
    exact hj.2
  calc e * (k + s - Fintype.card Validator) ≤ e * (D ∩ S).card := Nat.mul_le_mul_left e hinter
    _ = (D ∩ S).card * e := Nat.mul_comm _ _
    _ ≤ _ := le_trans hge (Finset.card_le_card hsub)

open scoped ENNReal in
attribute [local instance] noFaults in
/-- **Some window lacks a block of good coins** with probability at most
`J · badBlockBoundAt c w ^ M`, when every safe set of the windows' rounds
holds at least `c` validators: a union bound over the windows, each failing
with probability at most `badBlockBoundAt c w ^ M`. -/
theorem windowsFail_le {X : Type} [Fintype X] [DecidableEq X] [Nonempty X]
    (Sr : ℕ → Finset X) {J M w c : ℕ}
    (hfloor : ∀ r, r < J * (M * w) → c ≤ (Sr r).card) :
    (PMF.uniformOfFintype (Fin (J * M) → Fin w → X)).toOuterMeasure
        {g | ¬ ∀ j : Fin J, ∃ m : Fin M, ∀ i : Fin w,
          g ⟨j * M + m, blk_lt j.isLt m.isLt⟩ i ∈ Sr ((j * M + m) * w + i)} ≤
      (J : ℝ≥0∞) * Steelhead.Coin.badBlockBoundAt X c w ^ M := by
  let H : Fin J → Finset (Fin (J * M)) := fun j =>
    (Finset.univ : Finset (Fin M)).map
      ⟨fun (m : Fin M) => (⟨j * M + m, blk_lt j.isLt m.isLt⟩ : Fin (J * M)),
        fun a b h => Fin.ext (by have := congrArg Fin.val h; simpa using this)⟩
  let G : Fin (J * M) → Fin w → Finset X := fun k i => Sr (k * w + i)
  have hG : ∀ k i, c ≤ (G k i).card := fun k i => hfloor _ (by
    have h1 := Nat.mul_le_mul_right w (show (k : ℕ) + 1 ≤ J * M from k.isLt)
    have h2 := i.isLt
    have : (J * M) * w = J * (M * w) := by ring
    nlinarith)
  have hsub : {g : Fin (J * M) → Fin w → X | ¬ ∀ j : Fin J, ∃ m : Fin M, ∀ i : Fin w,
        g ⟨j * M + m, blk_lt j.isLt m.isLt⟩ i ∈ Sr ((j * M + m) * w + i)} ⊆
      ⋃ j, {g | ∀ k ∈ H j, ∃ i, g k i ∉ G k i} := by
    intro g hg
    simp only [Set.mem_setOf_eq, not_forall, not_exists] at hg
    obtain ⟨j, hj⟩ := hg
    refine Set.mem_iUnion.mpr ⟨j, fun k hk => ?_⟩
    obtain ⟨m, -, rfl⟩ := Finset.mem_map.mp hk
    obtain ⟨i, hi⟩ := hj m
    exact ⟨i, hi⟩
  refine le_trans (MeasureTheory.measure_mono hsub)
    (le_trans (MeasureTheory.measure_iUnion_fintype_le _ _) ?_)
  calc ∑ j : Fin J, (PMF.uniformOfFintype _).toOuterMeasure
          {g : Fin (J * M) → Fin w → X | ∀ k ∈ H j, ∃ i, g k i ∉ G k i}
        ≤ ∑ _j : Fin J, Steelhead.Coin.badBlockBoundAt X c w ^ M := by
          refine Finset.sum_le_sum fun j _ => ?_
          have := Steelhead.no_good_block_prob_le (H j) G hG
          rw [Finset.card_map, Finset.card_univ] at this
          simpa only [Fintype.card_fin, Steelhead.Coin.badBlockBoundAt] using this
      _ = (J : ℝ≥0∞) * Steelhead.Coin.badBlockBoundAt X c w ^ M := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]

end Scheme

end LeanDag
