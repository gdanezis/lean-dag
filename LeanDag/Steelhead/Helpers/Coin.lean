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

/-! ## The adaptive count

What the box argument below cannot reach: a family of bad sets that reads the draws already made.
Peeling the last block, whose bad set the earlier blocks fix, gives the same bound as the fixed
family, and the whole argument is a count over a finite type, with no conditioning to state. -/

/-- **The adaptive block bound, as a count.** With every block's bad set of at most `q` maps and
fixed by the blocks below it, at most `q ^ m` maps have every block bad. -/
theorem card_all_bad_le {α : Type} [Fintype α] [DecidableEq α] :
    ∀ (m : ℕ) (q : Fin m → ℕ) (B : (Fin m → α) → Fin m → Finset α),
      (∀ g g' (j : Fin m), (∀ j' : Fin m, j' < j → g j' = g' j') → B g j = B g' j) →
      (∀ g j, (B g j).card ≤ q j) →
      (Finset.univ.filter fun g : Fin m → α => ∀ j, g j ∈ B g j).card ≤ ∏ j, q j := by
  intro m
  induction m with
  | zero =>
    intro q B _ _
    rw [Fin.prod_univ_zero]
    exact le_trans (Finset.card_filter_le _ _) (by simp)
  | succ m ih =>
    intro q B hna hq
    classical
    rcases isEmpty_or_nonempty α with hα | hα
    · have : (Finset.univ.filter fun g : Fin (m + 1) → α => ∀ j, g j ∈ B g j) = ∅ := by
        refine Finset.eq_empty_of_forall_notMem fun g _ => ?_
        exact (hα.false (g 0)).elim
      rw [this]
      exact Nat.zero_le _
    · obtain ⟨a₀⟩ := hα
      -- the bad set of a block below the last reads only the blocks below it, so it is the
      -- earlier blocks' own family
      set B' : (Fin m → α) → Fin m → Finset α := fun p j => B (Fin.snoc p a₀) j.castSucc with hB'
      have hcast : ∀ (p : Fin m → α) (a : α) (j' : Fin (m + 1)) (hj' : j'.val < m),
          (Fin.snoc p a : Fin (m + 1) → α) j' = p ⟨j'.val, hj'⟩ := by
        intro p a j'
        induction j' using Fin.lastCases with
        | last => intro h; exact absurd h (by simp)
        | cast i =>
          intro _
          have h : (Fin.snoc p a : Fin (m + 1) → α) (Fin.castSucc i) = p i := by simp
          exact h
      have hna' : ∀ p p' (j : Fin m), (∀ j' : Fin m, j' < j → p j' = p' j') → B' p j = B' p' j := by
        intro p p' j hagree
        refine hna _ _ _ fun j' hj' => ?_
        have hlt : j'.val < m := by
          have : j'.val < (Fin.castSucc j).val := hj'
          simp only [Fin.val_castSucc] at this
          omega
        rw [hcast p a₀ j' hlt, hcast p' a₀ j' hlt]
        exact hagree ⟨j'.val, hlt⟩ (by simpa [Fin.lt_def] using hj')
      have hsub : (Finset.univ.filter fun g : Fin (m + 1) → α => ∀ j, g j ∈ B g j) ⊆
          (Finset.univ.filter fun p : Fin m → α => ∀ j, p j ∈ B' p j).biUnion
            fun p => (B (Fin.snoc p a₀) (Fin.last m)).image fun a => Fin.snoc p a := by
        intro g hg
        have hgb : ∀ j, g j ∈ B g j := (Finset.mem_filter.mp hg).2
        -- the blocks below the last agree with the map that fills the last slot with `a₀`
        have hagree : ∀ (j' : Fin (m + 1)), j'.val < m →
            g j' = (Fin.snoc (Fin.init g) a₀ : Fin (m + 1) → α) j' := by
          intro j' hj'
          rw [hcast _ a₀ j' hj']
          rfl
        refine Finset.mem_biUnion.mpr ⟨Fin.init g, Finset.mem_filter.mpr ⟨Finset.mem_univ _,
          fun j => ?_⟩, Finset.mem_image.mpr ⟨g (Fin.last m), ?_, Fin.snoc_init_self g⟩⟩
        · have hB : B' (Fin.init g) j = B g (Fin.castSucc j) := by
            refine hna _ _ _ fun j' hj' => ?_
            have hlt : j'.val < m := by
              have : j'.val < (Fin.castSucc j).val := hj'
              simp only [Fin.val_castSucc] at this
              omega
            exact (hagree j' hlt).symm
          rw [hB]
          exact hgb (Fin.castSucc j)
        · have hB : B (Fin.snoc (Fin.init g) a₀) (Fin.last m) = B g (Fin.last m) := by
            refine hna _ _ _ fun j' hj' => ?_
            have hlt : j'.val < m := by
              have : j'.val < (Fin.last m).val := hj'
              simpa using this
            exact (hagree j' hlt).symm
          rw [hB]
          exact hgb (Fin.last m)
      calc (Finset.univ.filter fun g : Fin (m + 1) → α => ∀ j, g j ∈ B g j).card
          ≤ _ := Finset.card_le_card hsub
        _ ≤ ∑ _p ∈ Finset.univ.filter fun p : Fin m → α => ∀ j, p j ∈ B' p j, q (Fin.last m) :=
            le_trans Finset.card_biUnion_le
              (Finset.sum_le_sum fun p _ => le_trans Finset.card_image_le (hq _ _))
        _ = (Finset.univ.filter fun p : Fin m → α => ∀ j, p j ∈ B' p j).card * q (Fin.last m) := by
            rw [Finset.sum_const, smul_eq_mul]
        _ ≤ (∏ j : Fin m, q j.castSucc) * q (Fin.last m) :=
            Nat.mul_le_mul_right _ (ih (fun j => q j.castSucc) B' hna' fun p j => hq _ _)
        _ = ∏ j, q j := (Fin.prod_univ_castSucc q).symm

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

/-! ## One validator, many coins -/

/-- **One validator leads `m` coins in a row** with probability `n^-m`: the constant map is one
leader map among `n^m`. -/
theorem constant_coin_probability (v : Validator) (m : ℕ) :
    (PMF.uniformOfFintype (Fin m → Validator)).toOuterMeasure {coins | ∀ i, coins i = v} =
      ((Fintype.card Validator : ℝ≥0∞) ^ m)⁻¹ := by
  classical
  have hset : ({coins | ∀ i, coins i = v} : Set (Fin m → Validator)) =
      ↑({fun _ => v} : Finset (Fin m → Validator)) := by
    ext coins
    simp only [Finset.coe_singleton, Set.mem_setOf_eq, Set.mem_singleton_iff]
    exact ⟨fun h => funext h, fun h i => congrFun h i⟩
  rw [hset, uniform_prob_mem]
  simp [Fintype.card_fin]

/-- So no bound on the rounds a validator leads holds for every coin sequence: the streak has
positive probability at every finite length, however small. -/
theorem constant_coin_probability_pos (v : Validator) (m : ℕ) :
    0 < (PMF.uniformOfFintype (Fin m → Validator)).toOuterMeasure {coins | ∀ i, coins i = v} := by
  rw [constant_coin_probability]
  exact ENNReal.inv_pos.mpr (ENNReal.pow_ne_top (by simp))

/-! ## Blocks of coins -/

omit [Fintype Validator] [DecidableEq Validator] F in
/-- The block map reads its own coins back: at `K ≤ I` the blocks are disjoint. -/
theorem coinOfBlocks_blockRound {M K I j₀ : ℕ} (hKI : K ≤ I) (g : Fin M → Fin K → Validator)
    (d : Validator) (j : Fin M) (i : Fin K) :
    coinOfBlocks I j₀ g d (blockRound I j₀ j i) = g j i := by
  have hI : 0 < I := by have := i.isLt; omega
  have hmul : (j₀ + 2 + j) * I = (j₀ + 2) * I + I * j := by
    rw [Nat.add_mul, Nat.mul_comm (j : ℕ) I]
  have hsub : blockRound I j₀ j i - ((j₀ + 2) * I + 1) = I * j + i := by
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

/-- **SH11f, the adaptive block bound.** The bound the fixed family gets, for bad sets that read
the blocks below their own: the count is the peeling count, and the densities multiply as before.
An adversary that shapes the DAG from the coins already drawn gains nothing. -/
theorem no_good_block_prob_le_adaptive {M K c : ℕ} (H : Finset (Fin M))
    (G : (Fin M → Fin K → Validator) → Fin M → Fin K → Finset Validator)
    (hna : ∀ g g' (j : Fin M), (∀ j' : Fin M, j' < j → g j' = g' j') → ∀ i, G g j i = G g' j i)
    (hc : ∀ g j i, c ≤ (G g j i).card) :
    (PMF.uniformOfFintype (Fin M → Fin K → Validator)).toOuterMeasure
        {g | ∀ j ∈ H, ∃ i, g j i ∉ G g j i} ≤
      ((((Fintype.card Validator ^ K - c ^ K : ℕ) : ℝ≥0∞) / (Fintype.card Validator : ℝ≥0∞) ^ K)
        ^ H.card) := by
  classical
  have hn : (Fintype.card Validator : ℝ≥0∞) ^ K ≠ 0 := by
    have := F.card_validators
    exact pow_ne_zero _ (by exact_mod_cast (by omega : Fintype.card Validator ≠ 0))
  have hnt : (Fintype.card Validator : ℝ≥0∞) ^ K ≠ ⊤ :=
    ENNReal.pow_ne_top (ENNReal.natCast_ne_top _)
  set B : (Fin M → Fin K → Validator) → Fin M → Finset (Fin K → Validator) :=
    fun g j => if j ∈ H then (Fintype.piFinset (G g j))ᶜ else Finset.univ with hB
  set q : Fin M → ℕ := fun j =>
    if j ∈ H then Fintype.card Validator ^ K - c ^ K else Fintype.card Validator ^ K with hq
  -- the event is the one the peeling count reads
  have hset : ({g | ∀ j ∈ H, ∃ i, g j i ∉ G g j i} : Set (Fin M → Fin K → Validator)) =
      ↑(Finset.univ.filter fun g => ∀ j, g j ∈ B g j) := by
    ext g
    rw [Finset.mem_coe, Finset.mem_filter]
    constructor
    · refine fun h => ⟨Finset.mem_univ _, fun j => ?_⟩
      by_cases hj : j ∈ H
      · rw [hB]
        dsimp only
        rw [if_pos hj, Finset.mem_compl, Fintype.mem_piFinset]
        obtain ⟨i, hi⟩ := h j hj
        exact fun hall => hi (hall i)
      · rw [hB]
        dsimp only
        rw [if_neg hj]
        exact Finset.mem_univ _
    · intro h j hj
      have hjB := h.2 j
      rw [hB] at hjB
      dsimp only at hjB
      rw [if_pos hj, Finset.mem_compl, Fintype.mem_piFinset] at hjB
      exact not_forall.mp hjB
  -- the bad sets read the blocks below their own, and each is small
  have hnaB : ∀ g g' (j : Fin M), (∀ j' : Fin M, j' < j → g j' = g' j') → B g j = B g' j := by
    intro g g' j hagree
    rw [hB]
    dsimp only
    by_cases hj : j ∈ H
    · rw [if_pos hj, if_pos hj]
      have hG : G g j = G g' j := funext fun i => hna g g' j hagree i
      rw [hG]
    · rw [if_neg hj, if_neg hj]
  have hqB : ∀ g j, (B g j).card ≤ q j := by
    intro g j
    rw [hB, hq]
    dsimp only
    by_cases hj : j ∈ H
    · rw [if_pos hj, if_pos hj, Finset.card_compl, Fintype.card_piFinset, Fintype.card_fun,
        Fintype.card_fin]
      have h := Finset.pow_card_le_prod Finset.univ (fun i => (G g j i).card) c fun i _ => hc g j i
      rw [Finset.card_univ, Fintype.card_fin] at h
      omega
    · rw [if_neg hj, if_neg hj, Finset.card_univ, Fintype.card_fun, Fintype.card_fin]
  have hcount := card_all_bad_le (α := Fin K → Validator) M q B hnaB hqB
  rw [hset, uniform_prob_mem, Fintype.card_fun, Fintype.card_fun, Fintype.card_fin,
    Fintype.card_fin, Nat.cast_pow, Nat.cast_pow]
  calc ((Finset.univ.filter fun g : Fin M → Fin K → Validator => ∀ j, g j ∈ B g j).card : ℝ≥0∞) /
        ((Fintype.card Validator : ℝ≥0∞) ^ K) ^ M
      ≤ ((∏ j, q j : ℕ) : ℝ≥0∞) / ((Fintype.card Validator : ℝ≥0∞) ^ K) ^ M :=
        ENNReal.div_le_div_right (Nat.cast_le.mpr hcount) _
    _ = ∏ j, ((q j : ℝ≥0∞) / (Fintype.card Validator : ℝ≥0∞) ^ K) := by
        rw [Nat.cast_prod,
          show ((Fintype.card Validator : ℝ≥0∞) ^ K) ^ M =
            ∏ _j : Fin M, (Fintype.card Validator : ℝ≥0∞) ^ K by
              rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin],
          ← ENNReal.prod_div_distrib_of_ne_top (fun _ _ => hnt)]
    _ ≤ ∏ j, (if j ∈ H then
          (((Fintype.card Validator ^ K - c ^ K : ℕ) : ℝ≥0∞) /
            (Fintype.card Validator : ℝ≥0∞) ^ K) else 1) := by
        refine Finset.prod_le_prod (fun _ _ => zero_le) fun j _ => ?_
        by_cases hj : j ∈ H
        · rw [if_pos hj, hq]
          dsimp only
          rw [if_pos hj]
        · rw [if_neg hj, hq]
          dsimp only
          rw [if_neg hj, ← Nat.cast_pow, Nat.cast_pow, ENNReal.div_self hn hnt]
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

/-- A good block in each half settles every chain verdict up to the later one, so the states are
derived that far, and decides the slot: the earlier block's first coin anchors its interval, the
later block is the run above it (SH14c). Stated for any coin map whose values on the two blocks
are good. -/
theorem decided_of_good_blocks {U : BlockUniverse Validator BlockId Payload} {ws wa I K : ℕ}
    (hws : 2 ≤ ws) (hle : ws ≤ wa) (hwa : 3 ≤ wa) (hwaK : wa ≤ K) (hKI : K ≤ I)
    {upd : UpdateRule BlockId} {k₀ : ℕ} {known coin : ℕ → Validator}
    {s M : ℕ} (h₁ : 1 ≤ s) {j₁ j₂ : Fin M} (hj : j₁ < j₂)
    (hg₁ : ∀ i : Fin K, coin (blockRound I (intervalOf I s) j₁ i) ∈
      MahiMahi.goodAt U wa (blockRound I (intervalOf I s) j₁ i))
    (hg₂ : ∀ i : Fin K, coin (blockRound I (intervalOf I s) j₂ i) ∈
      MahiMahi.goodAt U wa (blockRound I (intervalOf I s) j₂ i))
    (V : View Validator BlockId Payload U) (per : ℕ → ℕ)
    (hV : V.CoversUpto (blocksHorizon I wa (intervalOf I s) M))
    (hmatch : Matches I wa coin known upd k₀ ws U V per) :
    Settles I wa coin known upd k₀ ws U V per s := by
  have hI : 0 < I := by omega
  have h1 : (intervalOf I s + 2 + j₂) * I ≤ (intervalOf I s + 1 + M) * I :=
    Nat.mul_le_mul_right I (by have := j₂.isLt; omega)
  have hb : MahiMahi.decisionRoundAt wa (blockRound I (intervalOf I s) j₂ 0 + wa - 1) ≤
      blocksHorizon I wa (intervalOf I s) M := by
    unfold blockRound blocksHorizon MahiMahi.decisionRoundAt
    omega
  -- the later block's coins
  have hgoodb : ∀ i, i < wa → coin (blockRound I (intervalOf I s) j₂ 0 + i) ∈
      MahiMahi.goodAt U wa (blockRound I (intervalOf I s) j₂ 0 + i) := by
    intro i hi
    have := hg₂ ⟨i, by omega⟩
    simp only [blockRound] at this
    rw [show blockRound I (intervalOf I s) j₂ 0 + i = (intervalOf I s + 2 + j₂) * I + 1 + i by
      unfold blockRound; omega]
    exact this
  -- its run settles every chain verdict below it, so the states are derived up to its interval
  have hall := chainAllDecidedBelowOfRun (by omega) hgoodb (hV.mono hb)
  have hint : intervalOf I (blockRound I (intervalOf I s) j₂ 0 + wa - 1) =
      intervalOf I s + 2 + j₂ := by
    have hmul : (intervalOf I s + 2 + j₂ + 1) * I = (intervalOf I s + 2 + j₂) * I + I := by
      rw [Nat.add_mul, Nat.one_mul]
    exact intervalOf_eq_of_mul_lt_le (by unfold blockRound; omega) (by unfold blockRound; omega)
  have hw2 : ∀ r, 2 ≤ adaptiveWave ws wa I per r :=
    adaptiveWave_two_le (I := I) (per := per) hws (by omega)
  have hper : ∀ j', j' ≤ intervalOf I (blockRound I (intervalOf I s) j₂ 0 + wa - 1) → ∃ st,
      PeriodAt (S := adaptiveSlots coin known I per) I wa coin upd k₀ U V
        (adaptiveWave ws wa I per) j' st ∧ per j' = st.period := by
    intro j' hj'
    rw [hint] at hj'
    have hex : ∀ j, j ≤ intervalOf I s + 1 + j₂ + 1 →
        ∃ st, PeriodAt (S := adaptiveSlots coin known I per) I wa coin upd k₀ U V
          (adaptiveWave ws wa I per) j st :=
      exists_periodAt_of_settled (S := adaptiveSlots coin known I per) hw2 fun r hr => hall r (by
        have := le_of_intervalOf hI (rfl : intervalOf I r = intervalOf I r)
        have := Nat.mul_le_mul_right I (show intervalOf I r + 1 ≤ intervalOf I s + 2 + j₂ by omega)
        unfold blockRound
        omega)
    obtain ⟨st, hst⟩ := hex j' (by omega)
    exact ⟨st, hst, hmatch j' st hst⟩
  unfold Settles
  refine ⟨(hper _ (by rw [hint]; omega)).imp fun st h => h.1, ?_⟩
  refine output_liveness_of_runs (S := adaptiveSlots coin known I per)
    hws hle hwa (fun _ => rfl) hI (fun r h => if_pos h)
    (b := blockRound I (intervalOf I s) j₂ 0) hper h₁
    (j := intervalOf I s + 2 + j₁) (by omega) ?_ ?_ hgoodb (hV.mono hb)
  · have := hg₁ ⟨0, by omega⟩
    simp only [blockRound, Nat.add_zero] at this
    exact this
  · unfold blockRound
    have : (intervalOf I s + 2 + j₁ + 1) * I ≤ (intervalOf I s + 2 + j₂) * I :=
      Nat.mul_le_mul_right I (by omega)
    omega

/-- The lower half of `M` blocks. -/
def lowerHalf (M : ℕ) : Finset (Fin M) := Finset.univ.filter fun j => (j : ℕ) < M / 2

/-- The upper half of `M` blocks. -/
def upperHalf (M : ℕ) : Finset (Fin M) := Finset.univ.filter fun j => M / 2 ≤ (j : ℕ)

omit [Fintype Validator] [DecidableEq Validator] F in
/-- A block map outside both halves' no-good-block sets holds a good block in each half, the
lower one first. -/
theorem exists_good_blocks_of_not {M K : ℕ} {G : Fin M → Fin K → Finset Validator}
    {g : Fin M → Fin K → Validator}
    (h₁ : ¬ ∀ j ∈ lowerHalf M, ∃ i, g j i ∉ G j i)
    (h₂ : ¬ ∀ j ∈ upperHalf M, ∃ i, g j i ∉ G j i) :
    ∃ j₁ j₂ : Fin M, j₁ < j₂ ∧ (∀ i, g j₁ i ∈ G j₁ i) ∧ ∀ i, g j₂ i ∈ G j₂ i := by
  have good : ∀ H : Finset (Fin M), (¬ ∀ j ∈ H, ∃ i, g j i ∉ G j i) →
      ∃ j ∈ H, ∀ i, g j i ∈ G j i := by
    intro H hH
    by_contra hne
    exact hH fun j hj => by
      by_contra hall
      exact hne ⟨j, hj, fun i => by by_contra hi; exact hall ⟨i, hi⟩⟩
  obtain ⟨j₁, hj₁, hg₁⟩ := good _ h₁
  obtain ⟨j₂, hj₂, hg₂⟩ := good _ h₂
  rw [lowerHalf, Finset.mem_filter] at hj₁
  rw [upperHalf, Finset.mem_filter] at hj₂
  exact ⟨j₁, j₂, Fin.lt_def.mpr (by omega), hg₁, hg₂⟩

omit [Fintype Validator] [DecidableEq Validator] F in
/-- The same, read off a block map outside the union of the two halves' no-good-block sets. -/
theorem exists_good_blocks {M K : ℕ} {G : Fin M → Fin K → Finset Validator}
    {g : Fin M → Fin K → Validator}
    (hg : g ∉ {g | ∀ j ∈ lowerHalf M, ∃ i, g j i ∉ G j i} ∪
      {g | ∀ j ∈ upperHalf M, ∃ i, g j i ∉ G j i}) :
    ∃ j₁ j₂ : Fin M, j₁ < j₂ ∧ (∀ i, g j₁ i ∈ G j₁ i) ∧ ∀ i, g j₂ i ∈ G j₂ i :=
  exists_good_blocks_of_not (fun h => hg (Or.inl h)) fun h => hg (Or.inr h)

/-- The lower half holds at least `M / 2` blocks. -/
theorem card_lowerHalf (M : ℕ) : M / 2 ≤ (lowerHalf M).card := by
  classical
  rw [← Finset.card_range (M / 2),
    ← Finset.card_image_of_injective (lowerHalf M) Fin.val_injective]
  refine Finset.card_le_card fun n hn => ?_
  rw [Finset.mem_range] at hn
  refine Finset.mem_image.mpr ⟨⟨n, by omega⟩, ?_, rfl⟩
  rw [lowerHalf, Finset.mem_filter]
  exact ⟨Finset.mem_univ _, hn⟩

/-- The upper half holds at least `M / 2` blocks. -/
theorem card_upperHalf (M : ℕ) : M / 2 ≤ (upperHalf M).card := by
  classical
  rw [← Finset.card_image_of_injective (upperHalf M) Fin.val_injective]
  refine le_trans (by rw [Nat.card_Ico]; omega) (Finset.card_le_card (s := Finset.Ico (M / 2) M)
    fun n hn => ?_)
  rw [Finset.mem_Ico] at hn
  refine Finset.mem_image.mpr ⟨⟨n, hn.2⟩, ?_, rfl⟩
  rw [upperHalf, Finset.mem_filter]
  exact ⟨Finset.mem_univ _, hn.1⟩

/-- **Both halves hold a bad coin** with probability at most twice the block bound to the power
`M / 2`. -/
theorem bad_halves_prob_le {M K : ℕ} (G : Fin M → Fin K → Finset Validator)
    (hc : ∀ j i, Fintype.card Validator - F.f - F.byzantine.card ≤ (G j i).card) :
    (PMF.uniformOfFintype (Fin M → Fin K → Validator)).toOuterMeasure
        ({g | ∀ j ∈ lowerHalf M, ∃ i, g j i ∉ G j i} ∪
          {g | ∀ j ∈ upperHalf M, ∃ i, g j i ∉ G j i}) ≤
      2 * Coin.badBlockBound Validator K ^ (M / 2) := by
  classical
  have hcard₁ : M / 2 ≤ (lowerHalf M).card := card_lowerHalf M
  have hcard₂ : M / 2 ≤ (upperHalf M).card := card_upperHalf M
  calc (PMF.uniformOfFintype (Fin M → Fin K → Validator)).toOuterMeasure
        ({g | ∀ j ∈ lowerHalf M, ∃ i, g j i ∉ G j i} ∪
          {g | ∀ j ∈ upperHalf M, ∃ i, g j i ∉ G j i})
      ≤ (PMF.uniformOfFintype (Fin M → Fin K → Validator)).toOuterMeasure
          {g | ∀ j ∈ lowerHalf M, ∃ i, g j i ∉ G j i} +
        (PMF.uniformOfFintype (Fin M → Fin K → Validator)).toOuterMeasure
          {g | ∀ j ∈ upperHalf M, ∃ i, g j i ∉ G j i} := MeasureTheory.measure_union_le _ _
    _ ≤ Coin.badBlockBound Validator K ^ (lowerHalf M).card +
        Coin.badBlockBound Validator K ^ (upperHalf M).card :=
        add_le_add (no_good_block_prob_le _ G hc) (no_good_block_prob_le _ G hc)
    _ ≤ Coin.badBlockBound Validator K ^ (M / 2) + Coin.badBlockBound Validator K ^ (M / 2) :=
        add_le_add (pow_le_pow_of_le_one zero_le (badBlockBound_le_one K) hcard₁)
          (pow_le_pow_of_le_one zero_le (badBlockBound_le_one K) hcard₂)
    _ = 2 * Coin.badBlockBound Validator K ^ (M / 2) := (two_mul _).symm

/-- **Both halves hold a bad coin against a strategy**, at the same bound: SH11f at each half. -/
theorem bad_halves_prob_le_adaptive {M K : ℕ}
    (G : (Fin M → Fin K → Validator) → Fin M → Fin K → Finset Validator)
    (hna : ∀ g g' (j : Fin M), (∀ j' : Fin M, j' < j → g j' = g' j') → ∀ i, G g j i = G g' j i)
    (hc : ∀ g j i, Fintype.card Validator - F.f - F.byzantine.card ≤ (G g j i).card) :
    (PMF.uniformOfFintype (Fin M → Fin K → Validator)).toOuterMeasure
        ({g | ∀ j ∈ lowerHalf M, ∃ i, g j i ∉ G g j i} ∪
          {g | ∀ j ∈ upperHalf M, ∃ i, g j i ∉ G g j i}) ≤
      2 * Coin.badBlockBound Validator K ^ (M / 2) := by
  classical
  calc (PMF.uniformOfFintype (Fin M → Fin K → Validator)).toOuterMeasure
        ({g | ∀ j ∈ lowerHalf M, ∃ i, g j i ∉ G g j i} ∪
          {g | ∀ j ∈ upperHalf M, ∃ i, g j i ∉ G g j i})
      ≤ (PMF.uniformOfFintype (Fin M → Fin K → Validator)).toOuterMeasure
          {g | ∀ j ∈ lowerHalf M, ∃ i, g j i ∉ G g j i} +
        (PMF.uniformOfFintype (Fin M → Fin K → Validator)).toOuterMeasure
          {g | ∀ j ∈ upperHalf M, ∃ i, g j i ∉ G g j i} := MeasureTheory.measure_union_le _ _
    _ ≤ Coin.badBlockBound Validator K ^ (lowerHalf M).card +
        Coin.badBlockBound Validator K ^ (upperHalf M).card :=
        add_le_add (no_good_block_prob_le_adaptive _ G hna hc)
          (no_good_block_prob_le_adaptive _ G hna hc)
    _ ≤ Coin.badBlockBound Validator K ^ (M / 2) + Coin.badBlockBound Validator K ^ (M / 2) :=
        add_le_add (pow_le_pow_of_le_one zero_le (badBlockBound_le_one K) (card_lowerHalf M))
          (pow_le_pow_of_le_one zero_le (badBlockBound_le_one K) (card_upperHalf M))
    _ = 2 * Coin.badBlockBound Validator K ^ (M / 2) := (two_mul _).symm

/-- A block map with a good block in each half settles the slot against a strategy, so the
failure set lies in the union of the two halves' no-good-block sets. -/
theorem failure_subset_halves_adaptive {ws wa I K : ℕ} (hws : 2 ≤ ws) (hle : ws ≤ wa)
    (hwa : 3 ≤ wa) (hwaK : wa ≤ K) (hKI : K ≤ I) {upd : UpdateRule BlockId} {k₀ : ℕ}
    {known : ℕ → Validator} {d : Validator} {s M : ℕ}
    {σ : (Fin M → Fin K → Validator) → BlockUniverse Validator BlockId Payload} (h₁ : 1 ≤ s) :
    {g : Fin M → Fin K → Validator | ¬ ∀ (V : View Validator BlockId Payload (σ g))
        (per : ℕ → ℕ),
        V.CoversUpto (blocksHorizon I wa (intervalOf I s) M) →
        Matches I wa (coinOfBlocks I (intervalOf I s) g d) known upd k₀ ws (σ g) V per →
        Settles I wa (coinOfBlocks I (intervalOf I s) g d) known upd k₀ ws (σ g) V per s} ⊆
      {g | ∀ j ∈ lowerHalf M, ∃ i : Fin K,
          g j i ∉ MahiMahi.goodAt (σ g) wa (blockRound I (intervalOf I s) j i)} ∪
        {g | ∀ j ∈ upperHalf M, ∃ i : Fin K,
          g j i ∉ MahiMahi.goodAt (σ g) wa (blockRound I (intervalOf I s) j i)} := by
  intro g hg
  by_contra hcon
  obtain ⟨j₁, j₂, hlt, hg₁, hg₂⟩ :=
    exists_good_blocks_of_not (G := fun j i => MahiMahi.goodAt (σ g) wa
        (blockRound I (intervalOf I s) j i))
      (fun h => hcon (Or.inl h)) fun h => hcon (Or.inr h)
  exact hg fun V per hV hmatch => decided_of_good_blocks hws hle hwa hwaK hKI h₁ hlt
    (fun i => by rw [coinOfBlocks_blockRound hKI]; exact hg₁ i)
    (fun i => by rw [coinOfBlocks_blockRound hKI]; exact hg₂ i) V per hV hmatch

/-- **SH15d.** The failure set against a strategy lies in the union of the two halves'
no-good-block sets, which SH11f bounds for a strategy that reads only the draws already made:
the blocks' committed sets move with the record, and the argument of SH15a is unchanged. -/
theorem undecidedProb_le_adaptive {ws wa I K : ℕ} (hws : 2 ≤ ws) (hle : ws ≤ wa) (hwa : 5 ≤ wa)
    (hwaK : wa ≤ K) (hKI : K ≤ I) {T : Finset Validator}
    (hcard : quorumCard Validator ≤ T.card) {upd : UpdateRule BlockId} {k₀ : ℕ}
    {known : ℕ → Validator} {d : Validator} {s M : ℕ}
    {σ : (Fin M → Fin K → Validator) → BlockUniverse Validator BlockId Payload} (h₁ : 1 ≤ s)
    (hσ : NonAnticipating σ wa I (intervalOf I s))
    (hpop : ∀ g (j : Fin M) (i : Fin K),
      PopulatedOn (σ g) T (blockRound I (intervalOf I s) j i + 3) ∧
      PopulatedOn (σ g) T (MahiMahi.decisionRoundAt wa (blockRound I (intervalOf I s) j i))) :
    undecidedProbAgainst σ ws wa I upd k₀ known d s ≤
      2 * Coin.badBlockBound Validator K ^ (M / 2) :=
  le_trans
    (MeasureTheory.measure_mono
      (failure_subset_halves_adaptive hws hle (by omega) hwaK hKI h₁))
    (bad_halves_prob_le_adaptive
      (fun g j i => MahiMahi.goodAt (σ g) wa (blockRound I (intervalOf I s) j i)) hσ
      fun g j i => card_goodAt_of_populated hwa hcard (hpop g j i).1 (hpop g j i).2)

/-- **SH15a.** The failure set lies in the union of the two halves' no-good-block sets, each of
which the counting bounds. -/
theorem undecidedProb_le {U : BlockUniverse Validator BlockId Payload} {ws wa I K : ℕ}
    (hws : 2 ≤ ws) (hle : ws ≤ wa) (hwa : 5 ≤ wa) (hwaK : wa ≤ K) (hKI : K ≤ I)
    {T : Finset Validator} (hcard : quorumCard Validator ≤ T.card) {upd : UpdateRule BlockId}
    {k₀ : ℕ} {known : ℕ → Validator} {d : Validator} {s M : ℕ} (h₁ : 1 ≤ s)
    (hpop : ∀ (j : Fin M) (i : Fin K), PopulatedOn U T (blockRound I (intervalOf I s) j i + 3) ∧
      PopulatedOn U T (MahiMahi.decisionRoundAt wa (blockRound I (intervalOf I s) j i))) :
    undecidedProb U ws wa I K upd k₀ known d s M ≤
      2 * Coin.badBlockBound Validator K ^ (M / 2) := by
  classical
  set G : Fin M → Fin K → Finset Validator :=
    fun j i => MahiMahi.goodAt U wa (blockRound I (intervalOf I s) j i) with hG
  have hc : ∀ j i, Fintype.card Validator - F.f - F.byzantine.card ≤ (G j i).card :=
    fun j i => card_goodAt_of_populated hwa hcard (hpop j i).1 (hpop j i).2
  -- a good block in each half decides the slot, so failing needs a bad half
  have hsub : {g : Fin M → Fin K → Validator | ¬ ∀ (V : View Validator BlockId Payload U)
        (per : ℕ → ℕ),
        V.CoversUpto (blocksHorizon I wa (intervalOf I s) M) →
        Matches I wa (coinOfBlocks I (intervalOf I s) g d) known upd k₀ ws U V per →
        Settles I wa (coinOfBlocks I (intervalOf I s) g d) known upd k₀ ws U V per s} ⊆
      {g | ∀ j ∈ lowerHalf M, ∃ i, g j i ∉ G j i} ∪
        {g | ∀ j ∈ upperHalf M, ∃ i, g j i ∉ G j i} := by
    intro g hg
    by_contra hcon
    obtain ⟨j₁, j₂, hlt, hg₁, hg₂⟩ := exists_good_blocks hcon
    exact hg fun V per hV hmatch => decided_of_good_blocks hws hle (by omega) hwaK hKI h₁ hlt
      (fun i => by rw [coinOfBlocks_blockRound hKI]; exact hg₁ i)
      (fun i => by rw [coinOfBlocks_blockRound hKI]; exact hg₂ i) V per hV hmatch
  exact le_trans (MeasureTheory.measure_mono hsub) (bad_halves_prob_le G hc)

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

/-! ## The coin as a process -/

omit [Fintype Validator] [DecidableEq Validator] F in
/-- The block map is injective at `K ≤ I`: the block index is the quotient and the round index
the remainder, by `I`, of the offset from the first block's first round. -/
theorem blockRound_injective {I j₀ K M : ℕ} (hKI : K ≤ I) {j j' : Fin M} {i i' : Fin K}
    (h : blockRound I j₀ j i = blockRound I j₀ j' i') : j = j' ∧ i = i' := by
  have hI : 0 < I := by have := i.isLt; omega
  have key : ∀ (j : Fin M) (i : Fin K),
      (blockRound I j₀ j i - ((j₀ + 2) * I + 1)) / I = j ∧
        (blockRound I j₀ j i - ((j₀ + 2) * I + 1)) % I = i := by
    intro j i
    have hmul : (j₀ + 2 + j) * I = (j₀ + 2) * I + I * j := by
      rw [Nat.add_mul, Nat.mul_comm (j : ℕ) I]
    have hsub : blockRound I j₀ j i - ((j₀ + 2) * I + 1) = I * j + i := by
      unfold blockRound; omega
    rw [hsub, Nat.mul_add_div hI, Nat.div_eq_of_lt (by have := i.isLt; omega), Nat.add_zero,
      Nat.mul_add_mod, Nat.mod_eq_of_lt (by have := i.isLt; omega)]
    exact ⟨rfl, rfl⟩
  obtain ⟨hj, hi⟩ := key j i
  obtain ⟨hj', hi'⟩ := key j' i'
  rw [h] at hj hi
  exact ⟨Fin.ext (hj.symm.trans hj'), Fin.ext (hi.symm.trans hi')⟩

/-- **The process on the blocks is the uniform block map**: the coins of `M` blocks of `K`
rounds, read from the process, land in a set of block maps with the probability the uniform
distribution over the block maps gives it. One block map is a box on the blocks' rounds, of
measure `n^(−MK)`, and a set of maps is the disjoint union of its members' boxes. -/
theorem coinMeasure_blockCoins_mem [MeasurableSpace Validator] [MeasurableSingletonClass Validator]
    {I j₀ K M : ℕ} (hKI : K ≤ I) (S : Set (Fin M → Fin K → Validator)) :
    coinMeasure Validator {coin | blockCoins I j₀ M K coin ∈ S} =
      (PMF.uniformOfFintype (Fin M → Fin K → Validator)).toOuterMeasure S := by
  classical
  -- the blocks' rounds
  set B : Finset ℕ := Finset.univ.image fun p : Fin M × Fin K => blockRound I j₀ p.1 p.2 with hB
  have hBcard : B.card = M * K := by
    rw [hB, Finset.card_image_of_injective _ fun p q hpq => ?_, Finset.card_univ,
      Fintype.card_prod, Fintype.card_fin, Fintype.card_fin]
    obtain ⟨h1, h2⟩ := blockRound_injective hKI hpq
    exact Prod.ext h1 h2
  -- the coordinate set of one block map at a block's round is the map's value there
  have hsingle : ∀ (g : Fin M → Fin K → Validator) (j : Fin M) (i : Fin K),
      {v | ∀ (j' : Fin M) (i' : Fin K), blockRound I j₀ j' i' = blockRound I j₀ j i →
        v = g j' i'} = {g j i} := by
    intro g j i
    ext v
    simp only [Set.mem_setOf_eq, Set.mem_singleton_iff]
    constructor
    · intro h
      exact h j i rfl
    · rintro rfl j' i' h
      obtain ⟨rfl, rfl⟩ := blockRound_injective hKI h
      rfl
  have hmt : ∀ (g : Fin M → Fin K → Validator), ∀ r ∈ B,
      MeasurableSet {v | ∀ (j : Fin M) (i : Fin K), blockRound I j₀ j i = r → v = g j i} := by
    intro g r hr
    obtain ⟨p, -, rfl⟩ := Finset.mem_image.mp hr
    rw [hsingle]
    exact measurableSet_singleton _
  -- one block map is a box on the blocks' rounds
  have hbox : ∀ g : Fin M → Fin K → Validator,
      {coin | blockCoins I j₀ M K coin = g} =
        Set.pi (↑B) fun r =>
          {v | ∀ (j : Fin M) (i : Fin K), blockRound I j₀ j i = r → v = g j i} := by
    intro g
    ext coin
    simp only [Set.mem_setOf_eq, Set.mem_pi, Finset.mem_coe]
    constructor
    · intro hg r _ j i hji
      subst hji
      exact congrFun (congrFun hg j) i
    · intro h
      funext j i
      exact h (blockRound I j₀ j i)
        (by rw [hB]; exact Finset.mem_image.mpr ⟨(j, i), Finset.mem_univ _, rfl⟩) j i rfl
  -- of measure n^(−MK)
  have hone : ∀ g : Fin M → Fin K → Validator,
      coinMeasure Validator {coin | blockCoins I j₀ M K coin = g} =
        (Fintype.card Validator : ℝ≥0∞)⁻¹ ^ (M * K) := by
    intro g
    rw [hbox, coinMeasure, MeasureTheory.Measure.infinitePi_pi _ (hmt g), ← hBcard,
      ← Finset.prod_const]
    refine Finset.prod_congr rfl fun r hr => ?_
    obtain ⟨p, -, rfl⟩ := Finset.mem_image.mp hr
    rw [hsingle, PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton _),
      PMF.uniformOfFintype_apply]
  -- a set of block maps is the disjoint union of its members' boxes
  have hunion : {coin | blockCoins I j₀ M K coin ∈ S} =
      ⋃ g ∈ S.toFinset, {coin | blockCoins I j₀ M K coin = g} := by
    ext coin
    simp only [Set.mem_setOf_eq, Set.mem_iUnion, Set.mem_toFinset, exists_prop, exists_eq_right']
  rw [hunion, MeasureTheory.measure_biUnion_finset]
  · simp only [hone, Finset.sum_const, nsmul_eq_mul]
    conv_rhs => rw [← Set.coe_toFinset S]
    rw [uniform_prob_mem, Fintype.card_fun, Fintype.card_fun, Fintype.card_fin, Fintype.card_fin,
      ← pow_mul, Nat.cast_pow, div_eq_mul_inv, ENNReal.inv_pow, Nat.mul_comm K M]
  · intro g _ g' _ hne
    rw [Function.onFun, Set.disjoint_left]
    intro coin h1 h2
    exact hne (h1.symm.trans h2)
  · intro g _
    rw [hbox]
    exact MeasurableSet.pi B.countable_toSet (hmt g)

/-- **The failure set of one record under the process**: the coins under which some view holding
the record's horizon, at some period sequence matching what it derives under the handover, has not
derived the slot's period or leaves the slot undecided have measure at most SH15a's bound, by the
same inclusion read through the process. -/
theorem undecided_coin_le [MeasurableSpace Validator] [MeasurableSingletonClass Validator]
    {U : BlockUniverse Validator BlockId Payload} {ws wa I K : ℕ}
    (hws : 2 ≤ ws) (hle : ws ≤ wa) (hwa : 5 ≤ wa) (hwaK : wa ≤ K) (hKI : K ≤ I)
    {T : Finset Validator} (hcard : quorumCard Validator ≤ T.card) {upd : UpdateRule BlockId}
    {k₀ : ℕ} {known : ℕ → Validator} {s M : ℕ} (h₁ : 1 ≤ s)
    (hpop : ∀ (j : Fin M) (i : Fin K), PopulatedOn U T (blockRound I (intervalOf I s) j i + 3) ∧
      PopulatedOn U T (MahiMahi.decisionRoundAt wa (blockRound I (intervalOf I s) j i))) :
    coinMeasure Validator {coin | ¬ ∀ (V : View Validator BlockId Payload U) (per : ℕ → ℕ),
        V.CoversUpto (blocksHorizon I wa (intervalOf I s) M) →
        Matches I wa coin known upd k₀ ws U V per → Settles I wa coin known upd k₀ ws U V per s} ≤
      2 * Coin.badBlockBound Validator K ^ (M / 2) := by
  classical
  set G : Fin M → Fin K → Finset Validator :=
    fun j i => MahiMahi.goodAt U wa (blockRound I (intervalOf I s) j i) with hG
  have hc : ∀ j i, Fintype.card Validator - F.f - F.byzantine.card ≤ (G j i).card :=
    fun j i => card_goodAt_of_populated hwa hcard (hpop j i).1 (hpop j i).2
  -- a good block in each half decides the slot, so failing needs a bad half
  have hsub : {coin : ℕ → Validator | ¬ ∀ (V : View Validator BlockId Payload U) (per : ℕ → ℕ),
        V.CoversUpto (blocksHorizon I wa (intervalOf I s) M) →
        Matches I wa coin known upd k₀ ws U V per → Settles I wa coin known upd k₀ ws U V per s} ⊆
      {coin | blockCoins I (intervalOf I s) M K coin ∈
        {g | ∀ j ∈ lowerHalf M, ∃ i, g j i ∉ G j i} ∪
          {g | ∀ j ∈ upperHalf M, ∃ i, g j i ∉ G j i}} := by
    intro coin hcoin
    by_contra hcon
    obtain ⟨j₁, j₂, hlt, hg₁, hg₂⟩ := exists_good_blocks hcon
    exact hcoin fun V per hV hmatch => decided_of_good_blocks hws hle (by omega) hwaK hKI
      h₁ hlt hg₁ hg₂ V per hV hmatch
  exact le_trans (MeasureTheory.measure_mono hsub)
    (le_of_eq_of_le (coinMeasure_blockCoins_mem hKI _) (bad_halves_prob_le G hc))

/-- **The failure set of a strategy under the process**: the same inclusion as SH15a's, read
through the coins of the blocks, with the record the strategy builds from them. -/
theorem undecided_coin_le_adaptive [MeasurableSpace Validator]
    [MeasurableSingletonClass Validator] {ws wa I K : ℕ} (hws : 2 ≤ ws) (hle : ws ≤ wa)
    (hwa : 5 ≤ wa) (hwaK : wa ≤ K) (hKI : K ≤ I) {T : Finset Validator}
    (hcard : quorumCard Validator ≤ T.card) {upd : UpdateRule BlockId} {k₀ : ℕ}
    {known : ℕ → Validator} {s M : ℕ}
    {σ : (Fin M → Fin K → Validator) → BlockUniverse Validator BlockId Payload} (h₁ : 1 ≤ s)
    (hσ : NonAnticipating σ wa I (intervalOf I s))
    (hpop : ∀ (g : Fin M → Fin K → Validator) (j : Fin M) (i : Fin K),
      PopulatedOn (σ g) T (blockRound I (intervalOf I s) j i + 3) ∧
      PopulatedOn (σ g) T (MahiMahi.decisionRoundAt wa (blockRound I (intervalOf I s) j i))) :
    coinMeasure Validator {coin |
        ¬ ∀ (V : View Validator BlockId Payload (σ (blockCoins I (intervalOf I s) M K coin)))
          (per : ℕ → ℕ),
        V.CoversUpto (blocksHorizon I wa (intervalOf I s) M) →
        Matches I wa coin known upd k₀ ws (σ (blockCoins I (intervalOf I s) M K coin)) V per →
        Settles I wa coin known upd k₀ ws (σ (blockCoins I (intervalOf I s) M K coin)) V per s} ≤
      2 * Coin.badBlockBound Validator K ^ (M / 2) := by
  have hsub : {coin : ℕ → Validator |
        ¬ ∀ (V : View Validator BlockId Payload (σ (blockCoins I (intervalOf I s) M K coin)))
          (per : ℕ → ℕ),
        V.CoversUpto (blocksHorizon I wa (intervalOf I s) M) →
        Matches I wa coin known upd k₀ ws (σ (blockCoins I (intervalOf I s) M K coin)) V per →
        Settles I wa coin known upd k₀ ws (σ (blockCoins I (intervalOf I s) M K coin)) V per s} ⊆
      {coin | blockCoins I (intervalOf I s) M K coin ∈
        ({g | ∀ j ∈ lowerHalf M, ∃ i : Fin K,
            g j i ∉ MahiMahi.goodAt (σ g) wa (blockRound I (intervalOf I s) j i)} ∪
          {g | ∀ j ∈ upperHalf M, ∃ i : Fin K,
            g j i ∉ MahiMahi.goodAt (σ g) wa (blockRound I (intervalOf I s) j i)})} := by
    intro coin hcoin
    by_contra hcon
    obtain ⟨j₁, j₂, hlt, hg₁, hg₂⟩ :=
      exists_good_blocks_of_not (G := fun j i => MahiMahi.goodAt
          (σ (blockCoins I (intervalOf I s) M K coin)) wa (blockRound I (intervalOf I s) j i))
        (fun h => hcon (Or.inl h)) fun h => hcon (Or.inr h)
    exact hcoin fun V per hV hmatch => decided_of_good_blocks hws hle (by omega) hwaK hKI
      h₁ hlt hg₁ hg₂ V per hV hmatch
  exact le_trans (MeasureTheory.measure_mono hsub)
    (le_of_eq_of_le (coinMeasure_blockCoins_mem hKI _)
      (bad_halves_prob_le_adaptive
        (fun g j i => MahiMahi.goodAt (σ g) wa (blockRound I (intervalOf I s) j i)) hσ
        fun g j i => card_goodAt_of_populated hwa hcard (hpop g j i).1 (hpop g j i).2))

/-- **SH15e.** The almost-sure claim against an adversary that answers the draws already made:
the records of the sequence are the strategies' answers to the coins of their own blocks, and the
argument of SH15c is unchanged, since the failure set of each record is SH15d's. -/
theorem decidedAlmostSurely_adaptive [MeasurableSpace Validator]
    [MeasurableSingletonClass Validator] {ws wa I K : ℕ} (hws : 2 ≤ ws) (hle : ws ≤ wa)
    (hwa : 5 ≤ wa) (hwaK : wa ≤ K) (hKI : K ≤ I)
    {σ : ∀ m : ℕ, (Fin m → Fin K → Validator) → BlockUniverse Validator BlockId Payload}
    {T : Finset Validator} (hcard : quorumCard Validator ≤ T.card) {upd : ℕ → UpdateRule BlockId}
    {k₀ : ℕ} {known : ℕ → Validator} {s : ℕ} (h₁ : 1 ≤ s)
    (hσ : ∀ m, NonAnticipating (σ m) wa I (intervalOf I s))
    (hpop : ∀ (m : ℕ) (g : Fin m → Fin K → Validator) (j : Fin m) (i : Fin K),
      PopulatedOn (σ m g) T (blockRound I (intervalOf I s) j i + 3) ∧
      PopulatedOn (σ m g) T (MahiMahi.decisionRoundAt wa (blockRound I (intervalOf I s) j i))) :
    ∀ᵐ coin ∂(coinMeasure Validator), ∃ m,
      ∀ (V : View Validator BlockId Payload (σ m (blockCoins I (intervalOf I s) m K coin)))
        (per : ℕ → ℕ),
        V.CoversUpto (blocksHorizon I wa (intervalOf I s) m) →
        Matches I wa coin known (upd m) k₀ ws (σ m (blockCoins I (intervalOf I s) m K coin))
          V per →
        Settles I wa coin known (upd m) k₀ ws (σ m (blockCoins I (intervalOf I s) m K coin))
          V per s := by
  rw [MeasureTheory.ae_iff]
  refine le_antisymm
    (ge_of_tendsto' (undecided_tail_tendsto_zero (Validator := Validator) (K := K)) fun m => ?_)
    zero_le
  refine le_trans (MeasureTheory.measure_mono fun coin h => ?_)
    (undecided_coin_le_adaptive hws hle hwa hwaK hKI hcard (upd := upd m) (k₀ := k₀)
      (known := known) h₁ (hσ m) (hpop m))
  simp only [Set.mem_setOf_eq, not_exists] at h ⊢
  exact h m

/-- **SH15c.** The coins under which no record decides the slot lie, for every `m`, among those
under which the `m`-th leaves it undecided, a set of vanishing measure. -/
theorem decidedAlmostSurely [MeasurableSpace Validator] [MeasurableSingletonClass Validator]
    {ws wa I K : ℕ} (hws : 2 ≤ ws) (hle : ws ≤ wa) (hwa : 5 ≤ wa) (hwaK : wa ≤ K) (hKI : K ≤ I)
    {U : ℕ → BlockUniverse Validator BlockId Payload} {T : Finset Validator}
    (hcard : quorumCard Validator ≤ T.card) {upd : ℕ → UpdateRule BlockId} {k₀ : ℕ}
    {known : ℕ → Validator} {s : ℕ} (h₁ : 1 ≤ s)
    (hpop : ∀ (m : ℕ) (j : Fin m) (i : Fin K),
      PopulatedOn (U m) T (blockRound I (intervalOf I s) j i + 3) ∧
      PopulatedOn (U m) T (MahiMahi.decisionRoundAt wa (blockRound I (intervalOf I s) j i))) :
    ∀ᵐ coin ∂(coinMeasure Validator), ∃ m,
      ∀ (V : View Validator BlockId Payload (U m)) (per : ℕ → ℕ),
        V.CoversUpto (blocksHorizon I wa (intervalOf I s) m) →
        Matches I wa coin known (upd m) k₀ ws (U m) V per →
        Settles I wa coin known (upd m) k₀ ws (U m) V per s := by
  rw [MeasureTheory.ae_iff]
  refine le_antisymm
    (ge_of_tendsto' (undecided_tail_tendsto_zero (Validator := Validator) (K := K)) fun m => ?_)
    zero_le
  refine le_trans (MeasureTheory.measure_mono fun coin h => ?_)
    (undecided_coin_le hws hle hwa hwaK hKI hcard (upd := upd m) (k₀ := k₀) (known := known) h₁
      (hpop m))
  simp only [Set.mem_setOf_eq, not_exists] at h ⊢
  exact h m

end Steelhead

end LeanDag
