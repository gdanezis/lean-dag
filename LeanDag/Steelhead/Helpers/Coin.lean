import LeanDag.Steelhead.Coin.Statement
import LeanDag.MahiMahi.Helpers.Counting
import LeanDag.MahiMahi.Properties
/-!
# Helpers — the coin

Generated lemma infrastructure for `Coin/Statement.lean`; not part of
the audit surface. A uniform draw lands in a set with the set's density;
MM2 (`goodCard`) bounds the committed set's size; a good coin's block is
directly committed, which a caught-up view sees; and the leader maps
that miss every round's committed set are counted.
-/

namespace LeanDag

namespace Steelhead

open Filter Topology
open scoped ENNReal

variable {Validator : Type} [Fintype Validator] [DecidableEq Validator]
variable [F : Faults Validator]
variable {BlockId : Type} [LinearOrder BlockId] {Payload : Type}

/-! ## One coin -/

/-- A uniform draw lands in `G` with probability `|G| / |α|`. -/
theorem uniform_prob_mem {α : Type} [Fintype α] [Nonempty α] (G : Finset α) :
    (PMF.uniformOfFintype α).toOuterMeasure ↑G = (G.card : ℝ≥0∞) / Fintype.card α := by
  rw [PMF.toOuterMeasure_apply_finset]
  simp [PMF.uniformOfFintype_apply, Finset.sum_const, div_eq_mul_inv]

/-- The coin of round `r` names a committed leader with probability `|goodAt U wa r| / n`. -/
theorem commitProb_eq (U : BlockUniverse Validator BlockId Payload) (wa r : ℕ) :
    commitProb U wa r = ((MahiMahi.goodAt U wa r).card : ℝ≥0∞) / Fintype.card Validator :=
  uniform_prob_mem _

/-- **MM2 as a count**: at least `n − f − b` validators are committed at round `r`. -/
theorem card_goodAt_of_populated {U : BlockUniverse Validator BlockId Payload} {wa : ℕ}
    (hwa : 5 ≤ wa) {T : Finset Validator} (hcard : quorumCard Validator ≤ T.card) {r : ℕ}
    (hpop₃ : PopulatedOn U T (r + 3)) (hpopd : PopulatedOn U T (MahiMahi.decisionRoundAt wa r)) :
    Fintype.card Validator - F.f - F.byzantine.card ≤ (MahiMahi.goodAt U wa r).card := by
  have h := MahiMahi.goodCard hwa hcard hpop₃ hpopd
  have := Finset.card_le_card (Finset.inter_subset_left (s₁ := MahiMahi.goodAt U wa r)
    (s₂ := (Correct : Finset Validator)))
  change Fintype.card Validator - F.f ≤ _ at h
  omega

/-- **SH11a, first half.** -/
theorem ratio_le_commitProb {U : BlockUniverse Validator BlockId Payload} {wa : ℕ}
    (hwa : 5 ≤ wa) {T : Finset Validator} (hcard : quorumCard Validator ≤ T.card) {r : ℕ}
    (hpop₃ : PopulatedOn U T (r + 3)) (hpopd : PopulatedOn U T (MahiMahi.decisionRoundAt wa r)) :
    ((Fintype.card Validator - F.f - F.byzantine.card : ℕ) : ℝ≥0∞) / Fintype.card Validator ≤
      commitProb U wa r := by
  rw [commitProb_eq]
  exact ENNReal.div_le_div_right (Nat.cast_le.mpr (card_goodAt_of_populated hwa hcard hpop₃ hpopd))
    _

/-- `(n − f − b) / n ≥ 1/3` at `n ≥ 3f + 1` and `b ≤ f`. -/
theorem third_le_ratio :
    (3 : ℝ≥0∞)⁻¹ ≤
      ((Fintype.card Validator - F.f - F.byzantine.card : ℕ) : ℝ≥0∞) / Fintype.card Validator := by
  have hn : (Fintype.card Validator : ℝ≥0∞) ≠ 0 := by
    have := F.card_validators
    exact_mod_cast (by omega : Fintype.card Validator ≠ 0)
  rw [ENNReal.le_div_iff_mul_le (Or.inl hn) (Or.inl (ENNReal.natCast_ne_top _))]
  rw [← ENNReal.div_eq_inv_mul, ENNReal.div_le_iff (by norm_num) (by norm_num)]
  have := F.card_validators
  have := F.card_byzantine
  exact_mod_cast (by omega : Fintype.card Validator ≤
    (Fintype.card Validator - F.f - F.byzantine.card) * 3)

/-- **SH11a, second half.** -/
theorem third_le_commitProb {U : BlockUniverse Validator BlockId Payload} {wa : ℕ}
    (hwa : 5 ≤ wa) {T : Finset Validator} (hcard : quorumCard Validator ≤ T.card) {r : ℕ}
    (hpop₃ : PopulatedOn U T (r + 3)) (hpopd : PopulatedOn U T (MahiMahi.decisionRoundAt wa r)) :
    (3 : ℝ≥0∞)⁻¹ ≤ commitProb U wa r :=
  le_trans third_le_ratio (ratio_le_commitProb hwa hcard hpop₃ hpopd)

/-- **SH11e.** MM2's wave-four form names one committed correct candidate, so `1 ≤ |goodAt|`. -/
theorem inv_card_le_commitProb {U : BlockUniverse Validator BlockId Payload} {wa : ℕ}
    (hwa : 4 ≤ wa) {T : Finset Validator} (hcard : quorumCard Validator ≤ T.card) {r : ℕ}
    (hpop₂ : PopulatedOn U T (r + 2)) (hpopd : PopulatedOn U T (MahiMahi.decisionRoundAt wa r)) :
    (Fintype.card Validator : ℝ≥0∞)⁻¹ ≤ commitProb U wa r := by
  rw [commitProb_eq, ← one_div]
  have h : 1 ≤ (MahiMahi.goodAt U wa r).card :=
    Finset.card_pos.mpr
      ((MahiMahi.goodNonempty hwa hcard hpop₂ hpopd).mono Finset.inter_subset_left)
  exact ENNReal.div_le_div_right (by exact_mod_cast h) _

/-! ## The coin and the chain -/

/-- **SH11b.** A good coin's block is directly committed, and a view holding the decision round
holds its certificates. -/
theorem chainCommit_of_mem_goodAt {U : BlockUniverse Validator BlockId Payload} {wa : ℕ}
    {coin : ℕ → Validator} {V : View Validator BlockId Payload U} {r : ℕ}
    (h : coin r ∈ MahiMahi.goodAt U wa r) (hV : V.CoversUpto (MahiMahi.decisionRoundAt wa r)) :
    ∃ L, IsLeaderBlock (S := chainSlots coin) U r L ∧ ChainDecided wa coin U V r (some L) := by
  obtain ⟨L, hL, hLr, hLc, hdc⟩ := MahiMahi.mem_goodAt.mp h
  exact ⟨L, ⟨hL, hLr, hLc⟩, MahiMahi.Decided.directCommit (S := chainSlots coin) ⟨hL, hLr, hLc⟩
    (MahiMahiProperties.directCommitIn_of_coversUpto hdc hV)⟩

/-! ## Many coins -/

/-- **No coin among `m` hits its target.** If every `G i` has at least `c` members, the uniform
leader map misses all of them with probability at most `((n − c) / n)^m`. -/
theorem no_hit_prob_le {m c : ℕ} (G : Fin m → Finset Validator) (hc : ∀ i, c ≤ (G i).card) :
    (PMF.uniformOfFintype (Fin m → Validator)).toOuterMeasure {f | ∀ i, f i ∉ G i} ≤
      (((Fintype.card Validator - c : ℕ) : ℝ≥0∞) / Fintype.card Validator) ^ m := by
  have hset : ({f | ∀ i, f i ∉ G i} : Set (Fin m → Validator)) =
      ↑(Fintype.piFinset fun i => (G i)ᶜ) := by
    ext f
    simp
  rw [hset, uniform_prob_mem, Fintype.card_piFinset, Fintype.card_fun, Fintype.card_fin,
    Nat.cast_pow, div_eq_mul_inv, div_eq_mul_inv, mul_pow, ← ENNReal.inv_pow]
  gcongr
  rw [← Nat.cast_pow, Nat.cast_le]
  refine le_trans (Finset.prod_le_pow_card _ _ (Fintype.card Validator - c) fun i _ => ?_) ?_
  · rw [Finset.card_compl]
    exact Nat.sub_le_sub_left (hc i) _
  · simp

/-- **SH11c.** -/
theorem noCommitProb_le {U : BlockUniverse Validator BlockId Payload} {wa : ℕ} (hwa : 5 ≤ wa)
    {T : Finset Validator} (hcard : quorumCard Validator ≤ T.card) {r₀ m : ℕ}
    (hpop : ∀ i : Fin m, PopulatedOn U T (r₀ + i + 3) ∧
      PopulatedOn U T (MahiMahi.decisionRoundAt wa (r₀ + i))) :
    noCommitProb U wa r₀ m ≤
      (((F.f + F.byzantine.card : ℕ) : ℝ≥0∞) / Fintype.card Validator) ^ m := by
  have h := no_hit_prob_le (fun i : Fin m => MahiMahi.goodAt U wa (r₀ + i)) fun i =>
    card_goodAt_of_populated hwa hcard (hpop i).1 (hpop i).2
  have := F.card_validators
  have := F.card_byzantine
  rwa [show Fintype.card Validator - (Fintype.card Validator - F.f - F.byzantine.card) =
    F.f + F.byzantine.card by omega] at h

/-- `((n − c) / n)^m` tends to `0` when `0 < c ≤ n`. -/
theorem no_hit_prob_tendsto_zero {n c : ℕ} (hc : 0 < c) (hcn : c ≤ n) :
    Tendsto (fun m : ℕ => (((n - c : ℕ) : ℝ≥0∞) / n) ^ m) atTop (𝓝 0) := by
  refine ENNReal.tendsto_pow_atTop_nhds_zero_of_lt_one ?_
  have hn : (n : ℝ≥0∞) ≠ 0 := by exact_mod_cast (by omega : n ≠ 0)
  rw [ENNReal.div_lt_iff (Or.inl hn) (Or.inl (ENNReal.natCast_ne_top _)), one_mul]
  exact_mod_cast (by omega : n - c < n)

/-- **SH11d.** `f + b ≤ 2f < n`. -/
theorem tail_tendsto_zero :
    Tendsto (fun m : ℕ => (((F.f + F.byzantine.card : ℕ) : ℝ≥0∞) / Fintype.card Validator) ^ m)
      atTop (𝓝 0) := by
  have := F.card_validators
  have := F.card_byzantine
  have h := no_hit_prob_tendsto_zero (n := Fintype.card Validator)
    (c := Fintype.card Validator - F.f - F.byzantine.card) (by omega) (by omega)
  rwa [show Fintype.card Validator - (Fintype.card Validator - F.f - F.byzantine.card) =
    F.f + F.byzantine.card by omega] at h

end Steelhead

end LeanDag
