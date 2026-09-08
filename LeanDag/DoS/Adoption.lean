import LeanDag.DoS.SelfParent
import LeanDag.DoS.Counting
import Mathlib.Data.Finset.Max

/-!
# The adoption collapse, and the main bound

`dos-equivocation-and-growth.md` §5. With self-parents, an author's blocks
in a history organise into chains, and counting reduces to how many
chains one author can hold: every block lies below a top
(`exists_top_of_mem_history`), a top other than `b` is named by another
author's block, and one namer names only one chain's top
(`top_eq_of_mem_namer_history`, the adoption collapse). When every other
author is unexposed, tops are bounded by the `3f` other authors, giving
`|H(b)| ≤ (6f+1)(r+1)` (`card_history_le_of_unique_equivocator`), which
settles C1′ unconditionally at `f = 1`.
-/

namespace LeanDag

variable {Validator : Type*} [Fintype Validator] [DecidableEq Validator]
variable [F : Faults Validator]
variable {BlockId : Type*} [DecidableEq BlockId] {Payload : Type*}
variable {U : BlockUniverse Validator BlockId Payload}

/-- The pointwise form of D11's counting: two blocks by an author unexposed
in a history, at one round of it, are equal. -/
theorem eq_of_not_exposedIn {c i j : BlockId} {X : Validator} (h : ¬ ExposedIn U c X)
    (hi : i ∈ history U c) (hj : j ∈ history U c)
    (hic : (U.block i).creator = X) (hjc : (U.block j).creator = X)
    (hround : (U.block i).round = (U.block j).round) : i = j := by
  by_contra hne
  exact h ⟨i, hi, j, hj, hne, hic, hjc, hround⟩

/-- Everything in a history except the block itself is referenced from
within the history. -/
theorem exists_referencer {b i : BlockId} (hb : b ∈ U.ids) (hi : i ∈ history U b)
    (hne : i ≠ b) : ∃ j ∈ history U b, i ∈ (U.block j).refs := by
  rcases ((mem_history_iff hb).mp hi).cases_tail with heq | ⟨c, hc, hstep⟩
  · exact absurd heq hne
  · exact ⟨c, (mem_history_iff hb).mpr hc, hstep⟩

/-- **Unexposed means one chain.** Two same-author blocks of a history, the
author unexposed there, are chain-related: the lower lies in the higher
one's history. -/
theorem mem_history_of_creator_eq_of_not_exposedIn {b i j : BlockId} {X : Validator}
    (hb : b ∈ U.ids) (hX : ¬ ExposedIn U b X)
    (hi : i ∈ history U b) (hj : j ∈ history U b)
    (hic : (U.block i).creator = X) (hjc : (U.block j).creator = X)
    (hround : (U.block i).round ≤ (U.block j).round) : i ∈ history U j := by
  have hj_ids : j ∈ U.ids := history_subset_ids hb hj
  obtain ⟨q, hq, hqc, hqr⟩ := exists_self_ancestor hj_ids (t := (U.block i).round) hround
  have hsub : history U j ⊆ history U b :=
    history_subset_of_reaches hb ((mem_history_iff hb).mp hj)
  have hqi : q = i := eq_of_not_exposedIn hX (hsub hq) hi (hqc.trans hjc) hic hqr
  exact hqi ▸ hq

/-- The chain tops of author `X` in `b`'s history: `X`-blocks with no
`X`-authored child there. Chains being priced exactly (D22/D23), tops are
what remains to count. -/
def topsOf (U : BlockUniverse Validator BlockId Payload) (b : BlockId) (X : Validator) :
    Finset BlockId :=
  (history U b).filter fun t => (U.block t).creator = X ∧
    ∀ c ∈ history U b, (U.block c).creator = X → t ∉ (U.block c).refs

/-- Membership in `topsOf`, unfolded: a top is a block of `X` in the history with no later block of `X` reachable above it. -/
theorem mem_topsOf {b t : BlockId} {X : Validator} :
    t ∈ topsOf U b X ↔ t ∈ history U b ∧ (U.block t).creator = X ∧
      ∀ c ∈ history U b, (U.block c).creator = X → t ∉ (U.block c).refs := by
  simp [topsOf, and_assoc]

/-- Every `X`-block of a history lies in some top's history: walk up
`X`-children as far as they go. -/
theorem exists_top_of_mem_history {b i : BlockId} {X : Validator} (hb : b ∈ U.ids)
    (hi : i ∈ history U b) (hic : (U.block i).creator = X) :
    ∃ t ∈ topsOf U b X, i ∈ history U t := by
  classical
  set K := (history U b).filter (fun t => (U.block t).creator = X ∧ i ∈ history U t)
    with hK
  have hKne : K.Nonempty :=
    ⟨i, by rw [hK, Finset.mem_filter]; exact ⟨hi, hic, mem_history_self⟩⟩
  obtain ⟨t, htK, hmax⟩ := K.exists_max_image (fun t => (U.block t).round) hKne
  rw [hK, Finset.mem_filter] at htK
  obtain ⟨htb, htc, hti⟩ := htK
  refine ⟨t, mem_topsOf.mpr ⟨htb, htc, ?_⟩, hti⟩
  intro c hc hcc htref
  have hc_ids : c ∈ U.ids := history_subset_ids hb hc
  have hround := U.round_of_mem_refs hc_ids htref
  have hcK : c ∈ K := by
    rw [hK, Finset.mem_filter]
    exact ⟨hc, hcc, history_subset_of_reaches hc_ids (Reaches.single htref) hti⟩
  have := hmax c hcK
  omega

/-- An author's whole content is at most one block per (top, round) pair:
each block sits on the chain of some top, and a top's own history holds one
`X`-block per round (D21 applied to the top itself). -/
theorem card_filter_creator_le_card_topsOf (hdos : DoSValid U) {b : BlockId}
    (hb : b ∈ U.ids) (X : Validator) :
    ((history U b).filter fun i => (U.block i).creator = X).card
      ≤ (topsOf U b X).card * ((U.block b).round + 1) := by
  classical
  rw [← Finset.card_range ((U.block b).round + 1), ← Finset.card_product]
  refine Finset.card_le_card_of_injOn
    (fun i => (if h : ∃ t ∈ topsOf U b X, i ∈ history U t then h.choose else i,
      (U.block i).round)) ?_ ?_
  · intro i hi
    simp only [Finset.mem_coe, Finset.mem_filter] at hi
    have hex : ∃ t ∈ topsOf U b X, i ∈ history U t :=
      exists_top_of_mem_history hb hi.1 hi.2
    refine Finset.mem_coe.mpr (Finset.mem_product.mpr ⟨?_, ?_⟩)
    · show (if h : ∃ t ∈ topsOf U b X, i ∈ history U t then h.choose else i) ∈ topsOf U b X
      rw [dif_pos hex]
      exact hex.choose_spec.1
    · show (U.block i).round ∈ Finset.range ((U.block b).round + 1)
      rw [Finset.mem_range]
      have := round_le_of_mem_history hb hi.1
      omega
  · intro i₁ h₁ i₂ h₂ heq
    simp only [Finset.mem_coe, Finset.mem_filter] at h₁ h₂
    have hex₁ : ∃ t ∈ topsOf U b X, i₁ ∈ history U t :=
      exists_top_of_mem_history hb h₁.1 h₁.2
    have hex₂ : ∃ t ∈ topsOf U b X, i₂ ∈ history U t :=
      exists_top_of_mem_history hb h₂.1 h₂.2
    simp only [dif_pos hex₁, dif_pos hex₂, Prod.mk.injEq] at heq
    obtain ⟨htop, hrnd⟩ := heq
    obtain ⟨htmem, hi₁t⟩ := hex₁.choose_spec
    have hi₂t : i₂ ∈ history U hex₁.choose := htop ▸ hex₂.choose_spec.2
    obtain ⟨htb, htc, -⟩ := mem_topsOf.mp htmem
    have ht_ids : hex₁.choose ∈ U.ids := history_subset_ids hb htb
    exact eq_of_not_exposedIn (not_exposedIn_self_creator hdos ht_ids) hi₁t hi₂t
      (h₁.2.trans htc.symm) (h₂.2.trans htc.symm) hrnd

/-- **The adoption collapse.** Two tops, one lying inside the history of a
block that references the other, coincide. -/
theorem top_eq_of_mem_namer_history (hdos : DoSValid U) {b : BlockId} (hb : b ∈ U.ids)
    {X : Validator} {t₁ t₂ j : BlockId}
    (ht₁ : t₁ ∈ topsOf U b X) (ht₂ : t₂ ∈ topsOf U b X)
    (hj : j ∈ history U b) (hjref : t₂ ∈ (U.block j).refs)
    (h₁j : t₁ ∈ history U j) : t₁ = t₂ := by
  obtain ⟨ht₁b, ht₁c, ht₁top⟩ := mem_topsOf.mp ht₁
  obtain ⟨ht₂b, ht₂c, ht₂top⟩ := mem_topsOf.mp ht₂
  have hj_ids : j ∈ U.ids := history_subset_ids hb hj
  have hjc : (U.block j).creator ≠ X := fun h => ht₂top j hj h hjref
  have hXexp : ¬ ExposedIn U j X := ht₂c ▸ hdos j hj_ids t₂ hjref
  have h₂j : t₂ ∈ history U j := mem_history_of_mem_refs hj_ids hjref
  have ht₂r := U.round_of_mem_refs hj_ids hjref
  have h₁ne : t₁ ≠ j := fun h => hjc (h ▸ ht₁c)
  have h₁r : (U.block t₁).round < (U.block j).round := by
    have hle := round_le_of_mem_history hj_ids h₁j
    rcases Nat.lt_or_ge (U.block t₁).round (U.block j).round with h | h
    · exact h
    · exact absurd (eq_of_mem_history_of_round_eq hj_ids h₁j (by omega)) h₁ne
  rcases Nat.lt_or_ge (U.block t₁).round (U.block t₂).round with hlt | hge
  · -- t₁ strictly below t₂: t₂'s chain hands t₁ an X-child — no top after all
    exfalso
    have h₁₂ : t₁ ∈ history U t₂ :=
      mem_history_of_creator_eq_of_not_exposedIn hj_ids hXexp h₁j h₂j ht₁c ht₂c
        (by omega)
    have ht₂_ids : t₂ ∈ U.ids := history_subset_ids hb ht₂b
    obtain ⟨q, hq, hqc, hqr⟩ := exists_self_ancestor ht₂_ids
      (t := (U.block t₁).round + 1) (by omega)
    have hq_ids : q ∈ U.ids := history_subset_ids ht₂_ids hq
    obtain ⟨p, hp, hpc⟩ := (U.valid q hq_ids).self_parent (by omega)
    have hqsub : history U q ⊆ history U t₂ :=
      history_subset_of_reaches ht₂_ids ((mem_history_iff ht₂_ids).mp hq)
    have hpr := U.round_of_mem_refs hq_ids hp
    have ht₂X : ¬ ExposedIn U t₂ X := ht₂c ▸ not_exposedIn_self_creator hdos ht₂_ids
    have hpt₁ : p = t₁ :=
      eq_of_not_exposedIn ht₂X (hqsub (mem_history_of_mem_refs hq_ids hp)) h₁₂
        (hpc.trans (hqc.trans ht₂c)) ht₁c (by omega)
    have hqb : q ∈ history U b :=
      history_subset_of_reaches hb ((mem_history_iff hb).mp ht₂b) hq
    exact ht₁top q hqb (hqc.trans ht₂c) (hpt₁ ▸ hp)
  · exact eq_of_not_exposedIn hXexp h₁j h₂j ht₁c ht₂c (by omega)

/-- **Tops are as scarce as authors.** When every author other than `X` is
unexposed — its blocks a single chain — distinct tops need distinct namer
authors, of which there are at most `3f`. -/
theorem card_topsOf_le (hdos : DoSValid U) {b : BlockId} (hb : b ∈ U.ids) {X : Validator}
    (hXb : X ≠ (U.block b).creator)
    (hother : ∀ W, W ≠ X → ¬ ExposedIn U b W) :
    (topsOf U b X).card ≤ (Fintype.card Validator - 1) := by
  classical
  have hmap : ∀ t ∈ topsOf U b X, ∃ j ∈ history U b, t ∈ (U.block j).refs := by
    intro t ht
    obtain ⟨htb, htc, -⟩ := mem_topsOf.mp ht
    exact exists_referencer hb htb (fun h => hXb ((h ▸ htc).symm))
  have hbound : (topsOf U b X).card ≤ (Finset.univ.erase X).card := by
    refine Finset.card_le_card_of_injOn
      (fun t => if h : ∃ j ∈ history U b, t ∈ (U.block j).refs
        then (U.block h.choose).creator else X) ?_ ?_
    · intro t ht
      have hex := hmap t ht
      obtain ⟨-, -, httop⟩ := mem_topsOf.mp ht

      obtain ⟨hjb, hjref⟩ := hex.choose_spec
      simp only [dif_pos hex]
      exact Finset.mem_erase.mpr ⟨fun h => httop hex.choose hjb h hjref, Finset.mem_univ _⟩
    · intro t₁ h₁ t₂ h₂ heq
      rw [Finset.mem_coe] at h₁ h₂
      have hex₁ := hmap t₁ h₁
      have hex₂ := hmap t₂ h₂
      simp only [dif_pos hex₁, dif_pos hex₂] at heq
      obtain ⟨hj₁b, hj₁ref⟩ := hex₁.choose_spec
      obtain ⟨hj₂b, hj₂ref⟩ := hex₂.choose_spec
      obtain ⟨-, ht₁c, ht₁top⟩ := mem_topsOf.mp h₁
      have hW : (U.block hex₁.choose).creator ≠ X :=
        fun h => ht₁top hex₁.choose hj₁b h hj₁ref
      have hWexp : ¬ ExposedIn U b (U.block hex₁.choose).creator :=
        hother _ hW
      have hj₁_ids : hex₁.choose ∈ U.ids := history_subset_ids hb hj₁b
      have hj₂_ids : hex₂.choose ∈ U.ids := history_subset_ids hb hj₂b
      rcases le_total (U.block hex₁.choose).round (U.block hex₂.choose).round with
        hle | hle
      · have hchain : hex₁.choose ∈ history U hex₂.choose :=
          mem_history_of_creator_eq_of_not_exposedIn hb hWexp hj₁b hj₂b rfl heq.symm hle
        exact top_eq_of_mem_namer_history hdos hb h₁ h₂ hj₂b hj₂ref
          (history_subset_of_reaches hj₂_ids ((mem_history_iff hj₂_ids).mp hchain)
            (mem_history_of_mem_refs hj₁_ids hj₁ref))
      · have hchain : hex₂.choose ∈ history U hex₁.choose :=
          mem_history_of_creator_eq_of_not_exposedIn hb (heq ▸ hWexp) hj₂b hj₁b rfl heq hle
        exact (top_eq_of_mem_namer_history hdos hb h₂ h₁ hj₁b hj₁ref
          (history_subset_of_reaches hj₁_ids ((mem_history_iff hj₁_ids).mp hchain)
            (mem_history_of_mem_refs hj₂_ids hj₂ref))).symm
  have hcard : (Finset.univ.erase X).card = (Fintype.card Validator - 1) := by
    rw [Finset.card_erase_of_mem (Finset.mem_univ X), Finset.card_univ]
  omega

/-- **The main bound, unique-equivocator regime.** If at most one author is
exposed in `b`'s history, `|H(b)| ≤ (6f+1)(r+1)`. -/
theorem card_history_le_of_unique_equivocator (hdos : DoSValid U) {b : BlockId}
    (hb : b ∈ U.ids) {X : Validator} (hother : ∀ W, W ≠ X → ¬ ExposedIn U b W) :
    (history U b).card ≤ ((2 * Fintype.card Validator - 1)) * ((U.block b).round + 1) := by
  classical
  have hfib : (history U b).card = ∑ W ∈ Finset.univ,
      ((history U b).filter fun i => (U.block i).creator = W).card :=
    Finset.card_eq_sum_card_fiberwise (fun i _ => Finset.mem_univ _)
  have hXfiber : ((history U b).filter fun i => (U.block i).creator = X).card
      ≤ (Fintype.card Validator) * ((U.block b).round + 1) := by
    by_cases hXexp : ExposedIn U b X
    · have hXb : X ≠ (U.block b).creator := fun h =>
        not_exposedIn_self_creator hdos hb (h ▸ hXexp)
      calc ((history U b).filter fun i => (U.block i).creator = X).card
          ≤ (topsOf U b X).card * ((U.block b).round + 1) :=
            card_filter_creator_le_card_topsOf hdos hb X
        _ ≤ ((Fintype.card Validator - 1)) * ((U.block b).round + 1) :=
            Nat.mul_le_mul_right _ (card_topsOf_le hdos hb hXb hother)
        _ ≤ (Fintype.card Validator) * ((U.block b).round + 1) :=
            Nat.mul_le_mul_right _ (by omega)
    · calc ((history U b).filter fun i => (U.block i).creator = X).card
          ≤ (U.block b).round + 1 := card_filter_creator_le hb hXexp
        _ = 1 * ((U.block b).round + 1) := (one_mul _).symm
        _ ≤ (Fintype.card Validator) * ((U.block b).round + 1) :=
            Nat.mul_le_mul_right _ (by have := F.card_validators; omega)
  have herase : (Finset.univ.erase X).card = (Fintype.card Validator - 1) := by
    rw [Finset.card_erase_of_mem (Finset.mem_univ X), Finset.card_univ]
  calc (history U b).card
      = ∑ W ∈ Finset.univ,
          ((history U b).filter fun i => (U.block i).creator = W).card := hfib
    _ = ((history U b).filter fun i => (U.block i).creator = X).card
        + ∑ W ∈ Finset.univ.erase X,
            ((history U b).filter fun i => (U.block i).creator = W).card :=
          (Finset.add_sum_erase _ _ (Finset.mem_univ X)).symm
    _ ≤ (Fintype.card Validator) * ((U.block b).round + 1)
        + ∑ W ∈ Finset.univ.erase X, ((U.block b).round + 1) := by
          refine Nat.add_le_add hXfiber (Finset.sum_le_sum ?_)
          intro W hW
          exact card_filter_creator_le hb (hother W (Finset.mem_erase.mp hW).1)
    _ = (Fintype.card Validator) * ((U.block b).round + 1)
        + ((Fintype.card Validator - 1)) * ((U.block b).round + 1) := by
          rw [Finset.sum_const_nat (m := (U.block b).round + 1) (fun _ _ => rfl), herase]
    _ = ((2 * Fintype.card Validator - 1)) * ((U.block b).round + 1) := by
          rw [← Nat.add_mul]
          congr 1
          omega

/-- The same bound with the hypothesis in counted form: at most one author
caught in the whole history. -/
theorem card_history_le_of_card_exposedTo_le_one (hdos : DoSValid U) {b : BlockId}
    (hb : b ∈ U.ids) (hexp : (exposedTo U b).card ≤ 1) :
    (history U b).card ≤ ((2 * Fintype.card Validator - 1)) * ((U.block b).round + 1) := by
  classical
  by_cases hex : ∃ X, ExposedIn U b X
  · obtain ⟨X, hX⟩ := hex
    refine card_history_le_of_unique_equivocator hdos hb (X := X) ?_
    intro W hW hWexp
    have : 1 < (exposedTo U b).card :=
      Finset.one_lt_card.mpr
        ⟨W, mem_exposedTo.mpr hWexp, X, mem_exposedTo.mpr hX, hW⟩
    omega
  · push_neg at hex
    have hne : Nonempty Validator := by
      have := F.card_validators
      exact Fintype.card_pos_iff.mp (by omega)
    obtain ⟨X⟩ := hne
    exact card_history_le_of_unique_equivocator hdos hb (X := X) (fun W _ => hex W)

/-- **C1′ at `f ≤ 1`, unconditionally.** Exposure is Byzantine (D15) and the
Byzantine set has at most one member, so every DoS-valid history is linear:
at `f = 1`, `|H(b)| ≤ 7(r+1)`. -/
theorem card_history_le_of_f_le_one (hdos : DoSValid U) {b : BlockId} (hb : b ∈ U.ids)
    (hf : F.f ≤ 1) :
    (history U b).card ≤ ((2 * Fintype.card Validator - 1)) * ((U.block b).round + 1) :=
  card_history_le_of_card_exposedTo_le_one hdos hb (le_trans (card_exposedTo_le hb) hf)

end LeanDag
