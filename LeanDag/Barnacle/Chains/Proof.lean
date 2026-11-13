import LeanDag.Barnacle.Chains.Statement
import LeanDag.Barnacle.Helpers.Chains
import LeanDag.Barnacle.Helpers.Shuffle
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
/-!
# Bounded anchor chains from random assignments — proof

If each of `J` windows of `M` blocks holds a block opening with `w` heads
from `T`, the scan from every round under the horizon ends at such a block
within two windows (`chainEnds_of_windows`, by `chainEnds_of_heads`). A
window holds no such block with probability at most `ε^M`, the blocks being
independent (`window_le`, by `Measure.pi_pi`); a union over the windows
and over the sets `T` gives `2ⁿ · J · ε^M`.
-/

namespace LeanDag

namespace Barnacle

namespace Chains

open MeasureTheory
open scoped ENNReal

variable {Validator : Type} [Fintype Validator] [DecidableEq Validator]

/-- Block `m` of window `j` is block `j · M + m`. -/
theorem win_lt {J M j m : ℕ} (hj : j < J) (hm : m < M) : j * M + m < J * M :=
  calc j * M + m < j * M + M := by omega
    _ = (j + 1) * M := by ring
    _ ≤ J * M := Nat.mul_le_mul_right M hj

omit [Fintype Validator] [DecidableEq Validator] in
/-- **The head of round `k · L + i` is entry `i` of block `k`.** -/
theorem blockHead_eq {J M L : ℕ} (dflt : Validator) (g : Fin (J * M) → Fin L → Validator)
    {k i : ℕ} (hk : k < J * M) (hi : i < L) :
    blockHead dflt g (k * L + i) = g ⟨k, hk⟩ ⟨i, hi⟩ := by
  have hL : 0 < L := by omega
  have hdiv : (k * L + i) / L = k := by
    rw [Nat.add_comm, Nat.add_mul_div_right _ _ hL, Nat.div_eq_of_lt hi, Nat.zero_add]
  have hmod : (k * L + i) % L = i := by
    rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hi]
  unfold blockHead
  rw [dif_pos ⟨by rw [hdiv]; exact hk, hL⟩]
  congr 1
  · exact Fin.ext hdiv
  · exact Fin.ext hmod

/-- **Windows of good blocks end every scan**: if each window of `M` blocks
holds a block opening with `w` heads from `T`, the scan from the first slot
of every round `x` with `x + 2ML + w ≤ Nmax ≤ J·M·L` ends by `x + 2ML`. -/
theorem chainEnds_of_windows {J M L w Nmax : ℕ} (dflt : Validator)
    (g : Fin (J * M) → Fin L → Validator) {T D : Finset Validator} (hw : 0 < w) (hwL : w ≤ L)
    (hN : Nmax ≤ J * (M * L))
    (hgood : ∀ j : Fin J, ∃ m : Fin M, g ⟨j * M + m, win_lt j.isLt m.isLt⟩ ∈ PrefixIn T w)
    (C : Config Validator) (hC : ∀ ρ, C.head ρ = blockHead dflt g ρ) {x : ℕ}
    (hx : x + 2 * (M * L) + w ≤ Nmax) :
    C.ChainEnds T D w (x + 2 * (M * L)) (C.cum x) := by
  have hML : 0 < M * L := by
    rcases Nat.eq_zero_or_pos (M * L) with h | h
    · rw [h, Nat.mul_zero] at hN; omega
    · exact h
  have har : x / (M * L) * (M * L) ≤ x := Nat.div_mul_le_self x (M * L)
  have har2 : x < x / (M * L) * (M * L) + M * L := Nat.lt_div_mul_add hML
  have hjJ : x / (M * L) + 1 < J := by
    have h1 : (x / (M * L) + 2) * (M * L) ≤ J * (M * L) := by
      have : (x / (M * L) + 2) * (M * L) = x / (M * L) * (M * L) + 2 * (M * L) := by ring
      rw [this]; omega
    have := Nat.le_of_mul_le_mul_right h1 hML
    omega
  obtain ⟨m, hm⟩ := hgood ⟨x / (M * L) + 1, hjJ⟩
  have hL : 0 < L := by omega
  have e1 : ((x / (M * L) + 1) * M + m) * L = x / (M * L) * (M * L) + M * L + (m : ℕ) * L := by
    ring
  have e2 : (m : ℕ) * L + L ≤ M * L := by
    have := Nat.mul_le_mul_right L (show (m : ℕ) + 1 ≤ M from m.isLt)
    linarith [Nat.add_mul (m : ℕ) 1 L]
  refine chainEnds_of_heads C hw (ρ := ((x / (M * L) + 1) * M + m) * L) (by omega) (by omega)
    fun i hi => ?_
  rw [hC, blockHead_eq dflt g (win_lt hjJ m.isLt) (by omega)]
  exact hm ⟨i, by omega⟩ hi

/-- **A window lacks a good block with probability at most `ε^M`**: its `M`
blocks are independent, each bad with probability at most `ε`. -/
theorem window_le {X : Type} [MeasurableSpace X] (μ : Measure X) [IsProbabilityMeasure μ]
    (B : Set X) {ε : ℝ≥0∞} (hε : μ Bᶜ ≤ ε) {J M : ℕ} (j : Fin J) :
    (Measure.pi fun _ : Fin (J * M) => μ)
        {g | ∀ m : Fin M, g ⟨j * M + m, win_lt j.isLt m.isLt⟩ ∉ B} ≤ ε ^ M := by
  classical
  let e : Fin M ↪ Fin (J * M) :=
    ⟨fun m => ⟨j * M + m, win_lt j.isLt m.isLt⟩, fun a b h => Fin.ext (by
      have := congrArg Fin.val h; simpa using this)⟩
  let W : Finset (Fin (J * M)) := Finset.univ.map e
  let s : Fin (J * M) → Set X := fun k => if k ∈ W then Bᶜ else Set.univ
  have hset : {g : Fin (J * M) → X | ∀ m : Fin M, g ⟨j * M + m, win_lt j.isLt m.isLt⟩ ∉ B} =
      Set.pi Set.univ s := by
    ext g
    simp only [Set.mem_setOf_eq, Set.mem_pi, Set.mem_univ, true_implies, s]
    constructor
    · intro h k
      split
      · rename_i hk
        obtain ⟨m, -, rfl⟩ := Finset.mem_map.mp hk
        exact h m
      · trivial
    · intro h m
      have := h (e m)
      rw [if_pos (Finset.mem_map_of_mem e (Finset.mem_univ m))] at this
      exact this
  rw [hset, Measure.pi_pi]
  rw [← Finset.prod_mul_prod_compl W]
  have h1 : ∏ k ∈ W, μ (s k) = μ Bᶜ ^ M := by
    rw [Finset.prod_map]
    have : ∀ x : Fin M, μ (s (e x)) = μ Bᶜ := fun x => by
      show μ (if e x ∈ W then Bᶜ else Set.univ) = μ Bᶜ
      rw [if_pos (Finset.mem_map_of_mem e (Finset.mem_univ x))]
    simp only [this, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  have h2 : ∏ k ∈ Wᶜ, μ (s k) = 1 := by
    refine Finset.prod_eq_one fun k hk => ?_
    simp only [s, if_neg (Finset.mem_compl.mp hk), measure_univ]
  rw [h1, h2, mul_one]
  exact pow_le_pow_left' hε M

theorem randomChains : RandomChains := by
  intro Validator _ _ _ _ L w J M slack fb dflt μ _ ε hw hwL hε Nmax hN
  classical
  let Ts : Finset (Finset Validator) :=
    Finset.univ.filter fun T => Fintype.card Validator ≤ T.card + slack
  have hsub : {g : Fin (J * M) → Fin L → Validator | ¬ ∀ C : Config Validator,
        (∀ ρ, C.head ρ = blockHead dflt g ρ) →
        C.BoundedChainsUpto slack fb w (2 * (M * L)) Nmax} ⊆
      ⋃ T ∈ Ts, ⋃ j : Fin J,
        {g | ∀ m : Fin M, g ⟨j * M + m, win_lt j.isLt m.isLt⟩ ∉ PrefixIn T w} := by
    intro g hg
    by_contra hno
    simp only [Set.mem_iUnion, Set.mem_setOf_eq, not_exists, not_forall, not_not] at hno
    apply hg
    intro C hC T D _ hT _ x hx
    exact chainEnds_of_windows dflt g hw hwL hN
      (fun j => hno T (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hT⟩) j) C hC hx
  refine le_trans (measure_mono hsub) (le_trans (measure_biUnion_finset_le _ _) ?_)
  calc ∑ T ∈ Ts, (Measure.pi fun _ : Fin (J * M) => μ)
          (⋃ j : Fin J, {g | ∀ m : Fin M, g ⟨j * M + m, win_lt j.isLt m.isLt⟩ ∉ PrefixIn T w})
        ≤ ∑ _T ∈ Ts, (J : ℝ≥0∞) * ε ^ M := by
          refine Finset.sum_le_sum fun T hT => le_trans (measure_iUnion_fintype_le _ _) ?_
          calc ∑ j : Fin J, (Measure.pi fun _ : Fin (J * M) => μ)
                  {g | ∀ m : Fin M, g ⟨j * M + m, win_lt j.isLt m.isLt⟩ ∉ PrefixIn T w}
                ≤ ∑ _j : Fin J, ε ^ M := Finset.sum_le_sum fun j _ =>
                  window_le μ _ (hε T (Finset.mem_filter.mp hT).2) j
            _ = (J : ℝ≥0∞) * ε ^ M := by
                  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      _ = (Ts.card : ℝ≥0∞) * ((J : ℝ≥0∞) * ε ^ M) := by rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ 2 ^ Fintype.card Validator * ((J : ℝ≥0∞) * ε ^ M) := by
          gcongr
          have : Ts.card ≤ 2 ^ Fintype.card Validator := by
            have := Finset.card_le_univ Ts
            rwa [Fintype.card_finset] at this
          exact_mod_cast this

/-- **A random ordering opens with `w` validators of `T`** with probability
`|T|^(w) / n^(w)`, so outside it with probability at most
`1 − (n − slack)^(w) / n^(w)` when `T` misses at most `slack` validators. -/
theorem shuffle_compl_le [MeasurableSpace Validator] [MeasurableSingletonClass Validator]
    {w slack : ℕ} (hw : w ≤ Fintype.card Validator) (T : Finset Validator)
    (hT : Fintype.card Validator ≤ T.card + slack) :
    (shuffle Validator).toMeasure (PrefixIn T w)ᶜ ≤
      1 - ((Fintype.card Validator - slack).descFactorial w : ℝ≥0∞) /
        (Fintype.card Validator).descFactorial w := by
  classical
  haveI : Nonempty (Fin (Fintype.card Validator) ≃ Validator) :=
    ⟨(Fintype.equivFin Validator).symm⟩
  rw [prob_compl_eq_one_sub (Set.toFinite _).measurableSet]
  refine tsub_le_tsub_left ?_ 1
  set n := Fintype.card Validator
  set A := (Finset.univ.filter fun e : Fin n ≃ Validator =>
    ∀ i : Fin n, (i : ℕ) < w → e i ∈ T).card
  set P := Fintype.card (Fin n ≃ Validator)
  set D := n.descFactorial w
  set t := T.card.descFactorial w
  have hP : (P : ℝ≥0∞) ≠ 0 := by simp [P, Fintype.card_ne_zero]
  have hD : (D : ℝ≥0∞) ≠ 0 := by
    have : 0 < D := Nat.descFactorial_pos.mpr hw
    exact_mod_cast this.ne'
  have hmul : A * D = t * P := card_prefixIn_mul hw T
  have hμ : (shuffle Validator).toMeasure (PrefixIn T w) = (A : ℝ≥0∞) / P := by
    rw [PMF.toMeasure_apply_eq_toOuterMeasure, shuffle, PMF.toOuterMeasure_map_apply,
      PMF.toOuterMeasure_uniformOfFintype_apply]
    congr 2
    rw [Fintype.card_subtype]
    simp only [A]
    congr 1
    ext e
    simp [PrefixIn]
    rfl
  have heq : (A : ℝ≥0∞) / P = (t : ℝ≥0∞) / D := by
    rw [← ENNReal.mul_div_mul_right (A : ℝ≥0∞) P hD (ENNReal.natCast_ne_top _),
      ← ENNReal.mul_div_mul_right (t : ℝ≥0∞) D hP (ENNReal.natCast_ne_top _)]
    congr 1
    · exact_mod_cast hmul
    · ring
  rw [hμ, heq]
  gcongr
  exact Nat.descFactorial_le w (by omega)

theorem shuffleChains : ShuffleChains := by
  intro Validator _ _ _ _ w J M slack fb dflt hw hwn Nmax hN
  exact randomChains Validator (Fintype.card Validator) w J M slack fb dflt _ _ hw hwn
    (fun T hT => shuffle_compl_le hwn T hT) Nmax hN

theorem holds : Statement := ⟨randomChains, shuffleChains⟩

end Chains

end Barnacle

end LeanDag
