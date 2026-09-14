import LeanDag.Steelhead.Coin.Statement
import LeanDag.Steelhead.Helpers.Period
import LeanDag.MahiMahi.Helpers.Counting
import LeanDag.MahiMahi.Properties
/-!
# Helpers — the coin

Generated lemma infrastructure for `Coin/Statement.lean`; not part of
the audit surface. A uniform draw lands in a set with the set's density;
MM2 (`goodCard`) bounds the committed set's size; a good coin's block is
directly committed, which a caught-up view sees; the leader maps that
miss every round's committed set are counted; and so are the block maps
under which every block of a set holds a bad coin, which with SH14c
bounds the probability that a slot stays undecided.
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

/-! ## Blocks of coins -/

omit [Fintype Validator] [DecidableEq Validator] F in
/-- The block map reads its own coins back: at `K ≤ I` the blocks are disjoint. -/
theorem coinOfBlocks_blockRound {M K I j₀ : ℕ} (hKI : K ≤ I) (g : Fin M → Fin K → Validator)
    (d : Validator) (j : Fin M) (i : Fin K) :
    coinOfBlocks I j₀ g d (blockRound I j₀ j i) = g j i := by
  have hI : 0 < I := by have := i.isLt; omega
  have hmul : (j₀ + 1 + j) * I = (j₀ + 1) * I + I * j := by
    rw [Nat.add_mul, Nat.mul_comm (j : ℕ) I]
  have hsub : blockRound I j₀ j i - ((j₀ + 1) * I + 1) = I * j + i := by
    unfold blockRound
    omega
  have hdiv : (I * j + i) / I = j := by
    rw [Nat.mul_add_div hI, Nat.div_eq_of_lt (by have := i.isLt; omega), Nat.add_zero]
  have hmod : (I * j + i) % I = i := by
    rw [Nat.mul_add_mod, Nat.mod_eq_of_lt (by have := i.isLt; omega)]
  unfold coinOfBlocks
  rw [dif_pos ⟨by unfold blockRound; omega, by rw [hsub, hdiv]; exact j.isLt,
    by rw [hsub, hmod]; exact i.isLt⟩]
  congr 1 <;> ext <;> simp only [hsub, hdiv, hmod]

/-- **Every block of a set holds a bad coin**, with probability at most the block bound to the
size of the set: the uniform block map is a product, and each block of the set misses its all-good
maps, of which there are at least `c^K` out of `n^K`. -/
theorem no_good_block_prob_le {M K c : ℕ} (H : Finset (Fin M))
    (G : Fin M → Fin K → Finset Validator) (hc : ∀ j i, c ≤ (G j i).card) :
    (PMF.uniformOfFintype (Fin M → Fin K → Validator)).toOuterMeasure
        {g | ∀ j ∈ H, ∃ i, g j i ∉ G j i} ≤
      ((((Fintype.card Validator ^ K - c ^ K : ℕ) : ℝ≥0∞) / (Fintype.card Validator : ℝ≥0∞) ^ K)
        ^ H.card) := by
  classical
  have hn : (Fintype.card Validator : ℝ≥0∞) ^ K ≠ 0 := by
    have := F.card_validators
    exact pow_ne_zero _ (by exact_mod_cast (by omega : Fintype.card Validator ≠ 0))
  have hnt : (Fintype.card Validator : ℝ≥0∞) ^ K ≠ ⊤ :=
    ENNReal.pow_ne_top (ENNReal.natCast_ne_top _)
  -- the event is a box
  have hset : ({g | ∀ j ∈ H, ∃ i, g j i ∉ G j i} : Set (Fin M → Fin K → Validator)) =
      ↑(Fintype.piFinset fun j => if j ∈ H then (Fintype.piFinset (G j))ᶜ else Finset.univ) := by
    ext g
    simp only [Set.mem_setOf_eq, Finset.mem_coe, Fintype.mem_piFinset]
    constructor
    · intro h j
      by_cases hj : j ∈ H
      · rw [if_pos hj, Finset.mem_compl, Fintype.mem_piFinset]
        obtain ⟨i, hi⟩ := h j hj
        exact fun hall => hi (hall i)
      · rw [if_neg hj]; exact Finset.mem_univ _
    · intro h j hj
      have := h j
      rw [if_pos hj, Finset.mem_compl, Fintype.mem_piFinset] at this
      exact not_forall.mp this
  -- its probability is the product of the blocks' densities
  rw [hset, uniform_prob_mem, Fintype.card_piFinset, Fintype.card_fun, Fintype.card_fun,
    Fintype.card_fin, Fintype.card_fin, Nat.cast_prod, Nat.cast_pow, Nat.cast_pow,
    show ((Fintype.card Validator : ℝ≥0∞) ^ K) ^ M =
      ∏ _j : Fin M, (Fintype.card Validator : ℝ≥0∞) ^ K by
        rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin],
    ← ENNReal.prod_div_distrib_of_ne_top (fun _ _ => hnt)]
  -- each block of the set contributes at most the bound, the others at most one
  calc ∏ j : Fin M, ((if j ∈ H then (Fintype.piFinset (G j))ᶜ else Finset.univ).card : ℝ≥0∞) /
        (Fintype.card Validator : ℝ≥0∞) ^ K
      ≤ ∏ j : Fin M, (if j ∈ H then
          (((Fintype.card Validator ^ K - c ^ K : ℕ) : ℝ≥0∞) / (Fintype.card Validator : ℝ≥0∞) ^ K)
          else 1) := by
        refine Finset.prod_le_prod (fun _ _ => zero_le) fun j _ => ?_
        by_cases hj : j ∈ H
        · rw [if_pos hj, if_pos hj]
          refine ENNReal.div_le_div_right ?_ _
          rw [Finset.card_compl, Fintype.card_piFinset, Fintype.card_fun, Fintype.card_fin]
          have h := Finset.pow_card_le_prod Finset.univ (fun i => (G j i).card) c fun i _ => hc j i
          rw [Finset.card_univ, Fintype.card_fin] at h
          exact Nat.cast_le.mpr (Nat.sub_le_sub_left h _)
        · rw [if_neg hj, if_neg hj, Finset.card_univ, Fintype.card_fun, Fintype.card_fin,
            Nat.cast_pow, ENNReal.div_self hn hnt]
    _ = _ := by rw [Finset.prod_ite_mem, Finset.univ_inter, Finset.prod_const]

/-- The block bound is at most one. -/
theorem badBlockBound_le_one (K : ℕ) : Coin.badBlockBound Validator K ≤ 1 := by
  unfold Coin.badBlockBound
  have hn : (Fintype.card Validator : ℝ≥0∞) ^ K ≠ 0 := by
    have := F.card_validators
    exact pow_ne_zero _ (by exact_mod_cast (by omega : Fintype.card Validator ≠ 0))
  rw [ENNReal.div_le_iff hn (ENNReal.pow_ne_top (ENNReal.natCast_ne_top _)), one_mul,
    ← Nat.cast_pow, Nat.cast_le]
  exact Nat.sub_le _ _

/-- A good block in each half decides the slot: the earlier one anchors its interval, the later one
is the run above it (SH14c). -/
theorem decided_of_good_blocks {U : BlockUniverse Validator BlockId Payload} {ws wa I K : ℕ}
    (hws : 2 ≤ ws) (hle : ws ≤ wa) (hwa : 3 ≤ wa) (hwaK : wa ≤ K) (hKI : K ≤ I)
    {upd : UpdateRule BlockId} {k₀ : ℕ} (h₀ : 1 ≤ k₀) (hK : k₀ ≤ K)
    (hupd : ∀ j A k, 1 ≤ k → k ≤ K → 1 ≤ upd j A k ∧ upd j A k ≤ K) {known : ℕ → Validator}
    {d : Validator} {s M : ℕ} {g : Fin M → Fin K → Validator} {j₁ j₂ : Fin M} (hj : j₁ < j₂)
    (hg₁ : ∀ i : Fin K, g j₁ i ∈ MahiMahi.goodAt U wa (blockRound I (intervalOf I s) j₁ i))
    (hg₂ : ∀ i : Fin K, g j₂ i ∈ MahiMahi.goodAt U wa (blockRound I (intervalOf I s) j₂ i))
    (V : View Validator BlockId Payload U) (per : ℕ → ℕ)
    (hreset : ResetsOnNoOutput
      (S := adaptiveSlots (coinOfBlocks I (intervalOf I s) g d) known I per) U
      (adaptiveWave ws wa I per) I upd)
    (hV : V.CoversUpto (blocksHorizon I wa (intervalOf I s) M))
    (hper : ∀ j, j ≤ intervalOf I (blocksHorizon I wa (intervalOf I s) M) →
      PeriodAt I wa (coinOfBlocks I (intervalOf I s) g d) upd k₀ U V j (per j)) :
    ∃ v, Decided (S := adaptiveSlots (coinOfBlocks I (intervalOf I s) g d) known I per)
      (adaptiveWave ws wa I per) U V s v := by
  have hI : 0 < I := by omega
  have h1 : (intervalOf I s + 1 + j₂) * I ≤ (intervalOf I s + M) * I :=
    Nat.mul_le_mul_right I (by have := j₂.isLt; omega)
  have hb0 : blockRound I (intervalOf I s) j₂ 0 + wa - 1 ≤
      blocksHorizon I wa (intervalOf I s) M := by
    unfold blockRound blocksHorizon MahiMahi.decisionRoundAt
    omega
  have hb : MahiMahi.decisionRoundAt wa (blockRound I (intervalOf I s) j₂ 0 + wa - 1) ≤
      blocksHorizon I wa (intervalOf I s) M := by
    unfold blockRound blocksHorizon MahiMahi.decisionRoundAt
    omega
  refine output_liveness_of_runs
    (S := adaptiveSlots (coinOfBlocks I (intervalOf I s) g d) known I per)
    hws hle hwa (fun _ => rfl) hI (fun r h => if_pos h) h₀ hK hupd hKI hreset
    (b := blockRound I (intervalOf I s) j₂ 0)
    (fun j' hj' => hper j' (le_trans hj' (intervalOf_mono hb0)))
    (j := intervalOf I s + 1 + j₁) (by omega) (fun i hi => ?_) ?_ (fun i hi => ?_) (hV.mono hb)
  · have := coinOfBlocks_blockRound (j₀ := intervalOf I s) hKI g d j₁ ⟨i, hi⟩
    simp only [blockRound] at this
    rw [this]
    exact hg₁ ⟨i, hi⟩
  · unfold blockRound
    have : (intervalOf I s + 1 + j₁ + 1) * I ≤ (intervalOf I s + 1 + j₂) * I :=
      Nat.mul_le_mul_right I (by omega)
    omega
  · have := coinOfBlocks_blockRound (j₀ := intervalOf I s) hKI g d j₂ ⟨i, by omega⟩
    simp only [blockRound] at this
    rw [show blockRound I (intervalOf I s) j₂ 0 + i = (intervalOf I s + 1 + j₂) * I + 1 + i by
      unfold blockRound; omega, this]
    exact hg₂ ⟨i, by omega⟩

/-- **SH15a.** The failure set lies in the union of the two halves' no-good-block sets, each of
which the counting bounds. -/
theorem undecidedProb_le {U : BlockUniverse Validator BlockId Payload} {ws wa I K : ℕ}
    (hws : 2 ≤ ws) (hle : ws ≤ wa) (hwa : 5 ≤ wa) (hwaK : wa ≤ K) (hKI : K ≤ I)
    {T : Finset Validator} (hcard : quorumCard Validator ≤ T.card) {upd : UpdateRule BlockId}
    {k₀ : ℕ} (h₀ : 1 ≤ k₀) (hK : k₀ ≤ K)
    (hupd : ∀ j A k, 1 ≤ k → k ≤ K → 1 ≤ upd j A k ∧ upd j A k ≤ K) {known : ℕ → Validator}
    {d : Validator} {s M : ℕ}
    (hpop : ∀ (j : Fin M) (i : Fin K), PopulatedOn U T (blockRound I (intervalOf I s) j i + 3) ∧
      PopulatedOn U T (MahiMahi.decisionRoundAt wa (blockRound I (intervalOf I s) j i))) :
    undecidedProb U ws wa I K upd k₀ known d s M ≤
      2 * Coin.badBlockBound Validator K ^ (M / 2) := by
  classical
  set G : Fin M → Fin K → Finset Validator :=
    fun j i => MahiMahi.goodAt U wa (blockRound I (intervalOf I s) j i) with hG
  have hc : ∀ j i, Fintype.card Validator - F.f - F.byzantine.card ≤ (G j i).card :=
    fun j i => card_goodAt_of_populated hwa hcard (hpop j i).1 (hpop j i).2
  set H₁ : Finset (Fin M) := Finset.univ.filter fun j => (j : ℕ) < M / 2 with hH₁
  set H₂ : Finset (Fin M) := Finset.univ.filter fun j => M / 2 ≤ (j : ℕ) with hH₂
  -- a good block in each half decides the slot, so failing needs a bad half
  have hsub : {g : Fin M → Fin K → Validator | ¬ ∀ (V : View Validator BlockId Payload U)
        (per : ℕ → ℕ),
        ResetsOnNoOutput (S := adaptiveSlots (coinOfBlocks I (intervalOf I s) g d) known I per) U
          (adaptiveWave ws wa I per) I upd →
        V.CoversUpto (blocksHorizon I wa (intervalOf I s) M) →
        (∀ j, j ≤ intervalOf I (blocksHorizon I wa (intervalOf I s) M) →
          PeriodAt I wa (coinOfBlocks I (intervalOf I s) g d) upd k₀ U V j (per j)) →
        ∃ v, Decided (S := adaptiveSlots (coinOfBlocks I (intervalOf I s) g d) known I per)
          (adaptiveWave ws wa I per) U V s v} ⊆
      {g | ∀ j ∈ H₁, ∃ i, g j i ∉ G j i} ∪ {g | ∀ j ∈ H₂, ∃ i, g j i ∉ G j i} := by
    intro g hg
    by_contra hcon
    obtain ⟨h₁, h₂⟩ := not_or.mp hcon
    have good : ∀ H : Finset (Fin M),
        g ∉ {g : Fin M → Fin K → Validator | ∀ j ∈ H, ∃ i, g j i ∉ G j i} →
        ∃ j ∈ H, ∀ i, g j i ∈ G j i := by
      intro H hH
      by_contra hne
      exact hH fun j hj => by
        by_contra hall
        exact hne ⟨j, hj, fun i => by by_contra hi; exact hall ⟨i, hi⟩⟩
    obtain ⟨j₁, hj₁, hg₁⟩ := good H₁ h₁
    obtain ⟨j₂, hj₂, hg₂⟩ := good H₂ h₂
    rw [hH₁, Finset.mem_filter] at hj₁
    rw [hH₂, Finset.mem_filter] at hj₂
    have hlt : j₁ < j₂ := Fin.lt_def.mpr (by omega)
    exact hg fun V per hreset hV hper => decided_of_good_blocks hws hle (by omega) hwaK hKI h₀ hK
      hupd hlt hg₁ hg₂ V per hreset hV hper
  -- each half holds at least M / 2 blocks
  have hcard₁ : M / 2 ≤ H₁.card := by
    rw [← Finset.card_range (M / 2), ← Finset.card_image_of_injective H₁ Fin.val_injective]
    refine Finset.card_le_card fun n hn => ?_
    rw [Finset.mem_range] at hn
    refine Finset.mem_image.mpr ⟨⟨n, by omega⟩, ?_, rfl⟩
    rw [hH₁, Finset.mem_filter]
    exact ⟨Finset.mem_univ _, hn⟩
  have hcard₂ : M / 2 ≤ H₂.card := by
    rw [← Finset.card_image_of_injective H₂ Fin.val_injective]
    refine le_trans (by rw [Nat.card_Ico]; omega) (Finset.card_le_card (s := Finset.Ico (M / 2) M)
      fun n hn => ?_)
    rw [Finset.mem_Ico] at hn
    refine Finset.mem_image.mpr ⟨⟨n, hn.2⟩, ?_, rfl⟩
    rw [hH₂, Finset.mem_filter]
    exact ⟨Finset.mem_univ _, hn.1⟩
  calc undecidedProb U ws wa I K upd k₀ known d s M
      ≤ (PMF.uniformOfFintype (Fin M → Fin K → Validator)).toOuterMeasure
          ({g | ∀ j ∈ H₁, ∃ i, g j i ∉ G j i} ∪ {g | ∀ j ∈ H₂, ∃ i, g j i ∉ G j i}) :=
        MeasureTheory.measure_mono hsub
    _ ≤ (PMF.uniformOfFintype (Fin M → Fin K → Validator)).toOuterMeasure
          {g | ∀ j ∈ H₁, ∃ i, g j i ∉ G j i} +
        (PMF.uniformOfFintype (Fin M → Fin K → Validator)).toOuterMeasure
          {g | ∀ j ∈ H₂, ∃ i, g j i ∉ G j i} := MeasureTheory.measure_union_le _ _
    _ ≤ Coin.badBlockBound Validator K ^ H₁.card + Coin.badBlockBound Validator K ^ H₂.card :=
        add_le_add (no_good_block_prob_le H₁ G hc) (no_good_block_prob_le H₂ G hc)
    _ ≤ Coin.badBlockBound Validator K ^ (M / 2) + Coin.badBlockBound Validator K ^ (M / 2) :=
        add_le_add (pow_le_pow_of_le_one zero_le (badBlockBound_le_one K) hcard₁)
          (pow_le_pow_of_le_one zero_le (badBlockBound_le_one K) hcard₂)
    _ = 2 * Coin.badBlockBound Validator K ^ (M / 2) := (two_mul _).symm

/-- **SH15b.** `n^K − (n − f − b)^K < n^K`, since `n − f − b ≥ 1`, so the bound is below one and
its powers vanish; halving the exponent and doubling the value change nothing. -/
theorem undecided_tail_tendsto_zero {K : ℕ} :
    Tendsto (fun M : ℕ => 2 * Coin.badBlockBound Validator K ^ (M / 2)) atTop (𝓝 0) := by
  have hlt : Coin.badBlockBound Validator K < 1 := by
    unfold Coin.badBlockBound
    have := F.card_validators
    have := F.card_byzantine
    have hn : (Fintype.card Validator : ℝ≥0∞) ^ K ≠ 0 :=
      pow_ne_zero _ (by exact_mod_cast (by omega : Fintype.card Validator ≠ 0))
    rw [ENNReal.div_lt_iff (Or.inl hn) (Or.inl (ENNReal.pow_ne_top (ENNReal.natCast_ne_top _))),
      one_mul, ← Nat.cast_pow, Nat.cast_lt]
    have hc : 1 ≤ (Fintype.card Validator - F.f - F.byzantine.card) ^ K :=
      Nat.one_le_pow _ _ (by omega)
    have hcn : (Fintype.card Validator - F.f - F.byzantine.card) ^ K ≤ Fintype.card Validator ^ K :=
      Nat.pow_le_pow_left (by omega) _
    omega
  have h := (ENNReal.tendsto_pow_atTop_nhds_zero_of_lt_one hlt).comp
    (Nat.tendsto_div_const_atTop (by norm_num : (2 : ℕ) ≠ 0))
  simpa using ENNReal.Tendsto.const_mul h (Or.inr (by norm_num))

end Steelhead

end LeanDag
