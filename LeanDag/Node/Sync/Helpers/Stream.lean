import LeanDag.Node.Sync.Model.Stream
/-!
# Sync by causal streams — one sync

`docs/sync.md` §4. The frontier is sound: below it the requester holds a
block of the author at every round (`frontier_sound`). A stream in order
of round, each of whose blocks has its references held or streamed, is
taken in whole (`absorb_all`). So a block the stream leaves unready has a
reference neither held nor streamed (`exists_unstreamed`), which lies
below its author's frontier and so is a twin of a held block; the next
pass asks for it by name and the pass after detects its author
(`detects_next`). Each failing pass thus adds an equivocator to the
detected authors within two passes (`card_ge_of_fails`).
-/

namespace LeanDag

namespace Node

namespace Sync

variable {Validator BlockId Payload : Type} [DecidableEq Validator] [LinearOrder BlockId]
variable {blk : BlockId → Block Validator BlockId Payload}

omit [LinearOrder BlockId] in
/-- Below the result of `gapFrom`, from `k` up, `S` holds a block of `a`
at every round. -/
theorem gapFrom_sound {S : Finset BlockId} {a : Validator} :
    ∀ (fuel k j : ℕ), k ≤ j → j < gapFrom blk S a fuel k → HoldsAt blk S a j
  | 0, k, j, hk, hj => by simp only [gapFrom] at hj; omega
  | fuel + 1, k, j, hk, hj => by
    simp only [gapFrom] at hj
    split_ifs at hj with h
    · rcases Nat.eq_or_lt_of_le hk with rfl | hlt
      · exact h
      · exact gapFrom_sound fuel (k + 1) j hlt hj
    · omega

omit [LinearOrder BlockId] in
/-- **The frontier is sound.** -/
theorem frontier_sound {S : Finset BlockId} {a : Validator} {j : ℕ} (hj : j < frontier blk S a) :
    HoldsAt blk S a j :=
  gapFrom_sound _ 0 j (Nat.zero_le j) hj

omit [LinearOrder BlockId] in
/-- The frontier a request carries is sound, and `0` for a detected
author. -/
theorem frontierOf_sound {S : Finset BlockId} {D : Finset Validator} {a : Validator} {j : ℕ}
    (hj : j < frontierOf blk S D a) : a ∉ D ∧ HoldsAt blk S a j := by
  unfold frontierOf at hj
  split_ifs at hj with h
  · omega
  · exact ⟨h, frontier_sound hj⟩

omit [DecidableEq Validator] in
theorem absorb_mono : ∀ (S : Finset BlockId) (L : List BlockId), S ⊆ absorb blk S L
  | _, [] => Finset.Subset.refl _
  | S, i :: L => by
    refine Finset.Subset.trans ?_ (absorb_mono _ L)
    split_ifs
    · exact Finset.subset_insert _ _
    · exact Finset.Subset.refl _

omit [DecidableEq Validator] in
theorem absorb_sub : ∀ (S : Finset BlockId) (L : List BlockId),
    absorb blk S L ⊆ S ∪ L.toFinset
  | S, [] => by simp [absorb]
  | S, i :: L => by
    refine Finset.Subset.trans (absorb_sub _ L) ?_
    intro x hx
    simp only [Finset.mem_union, List.mem_toFinset, List.mem_cons] at hx ⊢
    split_ifs at hx
    · rcases hx with hx | hx
      · rcases Finset.mem_insert.mp hx with rfl | hx
        · exact Or.inr (Or.inl rfl)
        · exact Or.inl hx
      · exact Or.inr (Or.inr hx)
    · rcases hx with hx | hx
      · exact Or.inl hx
      · exact Or.inr (Or.inr hx)

omit [DecidableEq Validator] in
/-- **A stream in order of round, each of whose blocks has its references
held or streamed, one round below it, is taken in whole.** -/
theorem absorb_all :
    ∀ (S : Finset BlockId) (L : List BlockId),
      L.Pairwise (fun i j => (blk i).round ≤ (blk j).round) →
      (∀ i ∈ L, ∀ y ∈ (blk i).refs, y ∈ S ∨ y ∈ L) →
      (∀ i ∈ L, ∀ y ∈ (blk i).refs, (blk y).round + 1 = (blk i).round) →
      ∀ i ∈ L, i ∈ absorb blk S L
  | _, [], _, _, _ => fun _ h => absurd h List.not_mem_nil
  | S, i :: L, hsort, hrefs, hpred => by
    rw [List.pairwise_cons] at hsort
    have hready : Ready blk S i := by
      refine ⟨fun y hy => ?_, hpred i List.mem_cons_self⟩
      have hr := hpred i List.mem_cons_self y hy
      rcases hrefs i List.mem_cons_self y hy with h | h
      · exact h
      · rcases List.mem_cons.mp h with rfl | h
        · omega
        · have := hsort.1 y h
          omega
    have hS : absorb blk S (i :: L) = absorb blk (insert i S) L := by
      simp only [absorb, if_pos hready]
    rw [hS]
    have ih := absorb_all (insert i S) L hsort.2
      (fun j hj y hy => by
        rcases hrefs j (List.mem_cons_of_mem _ hj) y hy with h | h
        · exact Or.inl (Finset.mem_insert_of_mem h)
        · rcases List.mem_cons.mp h with rfl | h
          · exact Or.inl (Finset.mem_insert_self _ _)
          · exact Or.inr h)
      (fun j hj => hpred j (List.mem_cons_of_mem _ hj))
    intro j hj
    rcases List.mem_cons.mp hj with rfl | hj
    · exact absorb_mono _ L (Finset.mem_insert_self _ _)
    · exact ih j hj

omit [DecidableEq Validator] in
theorem mem_stream {R : Finset BlockId} {t : BlockId} {fr : Validator → ℕ} {X : Finset BlockId}
    {i : BlockId} : i ∈ stream blk R t fr X ↔ i ∈ streamed blk R t fr X := by
  unfold stream
  rw [List.mem_mergeSort, Finset.mem_sort]

omit [DecidableEq Validator] in
theorem stream_sorted (R : Finset BlockId) (t : BlockId) (fr : Validator → ℕ)
    (X : Finset BlockId) :
    (stream blk R t fr X).Pairwise (fun i j => (blk i).round ≤ (blk j).round) := by
  unfold stream
  have := List.pairwise_mergeSort (le := fun i j => decide ((blk i).round ≤ (blk j).round))
    (fun a b c hab hbc => by simp only [decide_eq_true_eq] at *; omega)
    (fun a b => by simp only [Bool.or_eq_true, decide_eq_true_eq]; omega)
    ((streamed blk R t fr X).sort (· ≤ ·))
  exact this.imp fun h => by simpa using h

omit [DecidableEq Validator] in
theorem mem_streamed {R : Finset BlockId} {t : BlockId} {fr : Validator → ℕ}
    {X : Finset BlockId} {i : BlockId} :
    i ∈ streamed blk R t fr X ↔
      i ∈ R ∧ ReachesFrom blk t i ∧ (i = t ∨ i ∈ X ∨ fr (blk i).creator ≤ (blk i).round) := by
  classical
  unfold streamed
  exact Finset.mem_filter

omit [DecidableEq Validator] in
/-- **A stream that leaves its target unready has a reference neither held
nor streamed.** -/
theorem exists_unstreamed {R S : Finset BlockId} {t : BlockId} {fr : Validator → ℕ}
    {X : Finset BlockId} (hR : CausalStructure blk R) (ht : t ∈ R)
    (hnot : t ∉ absorb blk S (stream blk R t fr X)) :
    ∃ g ∈ stream blk R t fr X, ∃ y ∈ (blk g).refs,
      y ∉ S ∧ y ∉ stream blk R t fr X := by
  by_contra hno
  push Not at hno
  have htL : t ∈ stream blk R t fr X :=
    mem_stream.mpr (mem_streamed.mpr ⟨ht, ReachesFrom.refl, Or.inl rfl⟩)
  refine hnot (absorb_all S _ (stream_sorted R t fr X) (fun i hi y hy => ?_)
    (fun i hi y hy => ?_) t htL)
  · by_cases hyS : y ∈ S
    · exact Or.inl hyS
    · exact Or.inr (hno i hi y hy hyS)
  · exact hR.refs_round i (mem_streamed.mp (mem_stream.mp hi)).1 y hy

/-- **The pass after a failing pass asks for an unstreamed reference by
name, and the pass after that detects its author**, an equivocator of
`R` against the blocks held, not detected before. -/
theorem detects_next {R S₀ : Finset BlockId} {t : BlockId} {s : Pass Validator BlockId}
    (hR : CausalStructure blk R) (ht : t ∈ R) (hsub : s.held ⊆ R ∪ S₀)
    (hnot : t ∉ (pass blk R t s).held) :
    ∃ a ∈ equivocators blk R S₀, a ∉ s.detected ∧
      a ∈ (pass blk R t (pass blk R t s)).detected := by
  set L := stream blk R t (frontierOf blk s.held s.detected) s.asked with hL
  have hheld : (pass blk R t s).held = absorb blk s.held L := rfl
  rw [hheld] at hnot
  obtain ⟨g, hg, y, hy, hyS, hyL⟩ := exists_unstreamed hR ht hnot
  obtain ⟨hgR, hgt, -⟩ := mem_streamed.mp (mem_stream.mp hg)
  have hyR : y ∈ R := hR.complete g hgR y hy
  have hyt : ReachesFrom blk t y := hgt.trans (ReachesFrom.single hy)
  -- `y` lies below its author's frontier, so a twin of it is held
  have hfr : (blk y).round < frontierOf blk s.held s.detected (blk y).creator := by
    by_contra h
    exact hyL (mem_stream.mpr (mem_streamed.mpr ⟨hyR, hyt, Or.inr (Or.inr (by omega))⟩))
  obtain ⟨hyD, j, hj, hjc, hjr⟩ := frontierOf_sound hfr
  have hyj : Twins blk y j := ⟨fun e => hyS (e ▸ hj), hjc.symm, hjr.symm⟩
  -- the next pass asks for `y` by name, and the one after streams it
  have hyS₁ : y ∉ (pass blk R t s).held := by
    intro h
    rcases Finset.mem_union.mp (absorb_sub _ _ h) with h | h
    · exact hyS h
    · exact hyL (List.mem_toFinset.mp h)
  have hyX : y ∈ (pass blk R t s).asked := by
    refine Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨?_, hyS₁⟩)
    exact Finset.mem_biUnion.mpr ⟨g, List.mem_toFinset.mpr hg, hy⟩
  have hjS₁ : j ∈ (pass blk R t s).held := absorb_mono _ _ hj
  refine ⟨(blk y).creator, ?_, hyD, ?_⟩
  · refine Finset.mem_image.mpr ⟨(y, j), Finset.mem_filter.mpr ⟨?_, hyj⟩, rfl⟩
    exact Finset.mem_product.mpr ⟨hyR, hsub hj⟩
  · refine Finset.mem_union_right _ (List.mem_toFinset.mpr (List.mem_map.mpr ⟨y, ?_, rfl⟩))
    refine List.mem_filter.mpr ⟨?_, ?_⟩
    · exact mem_stream.mpr (mem_streamed.mpr ⟨hyR, hyt, Or.inr (Or.inl hyX)⟩)
    · exact decide_eq_true ⟨hyS₁, j, hjS₁, hyj⟩

theorem pass_held_mono (R : Finset BlockId) (t : BlockId) (s : Pass Validator BlockId) :
    s.held ⊆ (pass blk R t s).held :=
  absorb_mono _ _

theorem pass_detected_mono (R : Finset BlockId) (t : BlockId) (s : Pass Validator BlockId) :
    s.detected ⊆ (pass blk R t s).detected :=
  Finset.subset_union_left

theorem pass_held_sub {R S₀ : Finset BlockId} (t : BlockId) {s : Pass Validator BlockId}
    (hsub : s.held ⊆ R ∪ S₀) : (pass blk R t s).held ⊆ R ∪ S₀ := by
  intro x hx
  rcases Finset.mem_union.mp (absorb_sub _ _ hx) with h | h
  · exact hsub h
  · exact Finset.mem_union_left _
      (mem_streamed.mp (mem_stream.mp (List.mem_toFinset.mp h))).1

theorem iterate_held_sub {R : Finset BlockId} (t : BlockId) (s : Pass Validator BlockId) :
    ∀ k, ((pass blk R t)^[k] s).held ⊆ R ∪ s.held
  | 0 => Finset.subset_union_right
  | k + 1 => by
    rw [Function.iterate_succ_apply']
    exact pass_held_sub t (iterate_held_sub t s k)

theorem iterate_held_mono (R : Finset BlockId) (t : BlockId) (s : Pass Validator BlockId)
    {k l : ℕ} (h : k ≤ l) : ((pass blk R t)^[k] s).held ⊆ ((pass blk R t)^[l] s).held := by
  induction l with
  | zero => obtain rfl : k = 0 := by omega
            exact Finset.Subset.refl _
  | succ l ih =>
    rcases Nat.eq_or_lt_of_le h with rfl | hlt
    · exact Finset.Subset.refl _
    · rw [Function.iterate_succ_apply']
      exact (ih (by omega)).trans (pass_held_mono R t _)

theorem iterate_detected_mono (R : Finset BlockId) (t : BlockId) (s : Pass Validator BlockId)
    {k l : ℕ} (h : k ≤ l) :
    ((pass blk R t)^[k] s).detected ⊆ ((pass blk R t)^[l] s).detected := by
  induction l with
  | zero => obtain rfl : k = 0 := by omega
            exact Finset.Subset.refl _
  | succ l ih =>
    rcases Nat.eq_or_lt_of_le h with rfl | hlt
    · exact Finset.Subset.refl _
    · rw [Function.iterate_succ_apply']
      exact (ih (by omega)).trans (pass_detected_mono R t _)

/-- **A failing pass raises the detected equivocators within two
passes.** -/
theorem card_lt_of_fails {R : Finset BlockId} {t : BlockId} {s : Pass Validator BlockId}
    (hR : CausalStructure blk R) (ht : t ∈ R) {k : ℕ}
    (hnot : t ∉ ((pass blk R t)^[k + 1] s).held) :
    (((pass blk R t)^[k] s).detected ∩ equivocators blk R s.held).card <
      (((pass blk R t)^[k + 2] s).detected ∩ equivocators blk R s.held).card := by
  rw [Function.iterate_succ_apply'] at hnot
  obtain ⟨a, haE, haD, haD₂⟩ := detects_next hR ht (iterate_held_sub t s k) hnot
  refine Finset.card_lt_card ⟨Finset.inter_subset_inter_right
    (iterate_detected_mono R t s (by omega)), fun hsub => ?_⟩
  rw [Function.iterate_succ_apply', Function.iterate_succ_apply'] at hsub
  exact haD (Finset.mem_inter.mp (hsub (Finset.mem_inter.mpr ⟨haD₂, haE⟩))).1

theorem card_ge_of_fails {R : Finset BlockId} {t : BlockId} {s : Pass Validator BlockId}
    (hR : CausalStructure blk R) (ht : t ∈ R) :
    ∀ m, t ∉ ((pass blk R t)^[2 * m + 1] s).held →
      m + 1 ≤ (((pass blk R t)^[2 * m + 2] s).detected ∩ equivocators blk R s.held).card
  | 0, hnot => Nat.succ_le_of_lt (lt_of_le_of_lt (Nat.zero_le _)
      (card_lt_of_fails hR ht (k := 0) hnot))
  | m + 1, hnot => by
    have hprev : t ∉ ((pass blk R t)^[2 * m + 1] s).held :=
      fun h => hnot (iterate_held_mono R t s (by omega) h)
    have ih := card_ge_of_fails hR ht m hprev
    have := card_lt_of_fails hR ht (k := 2 * m + 2) (by
      have : 2 * (m + 1) + 1 = 2 * m + 2 + 1 := by omega
      rwa [this] at hnot)
    have e : 2 * (m + 1) + 2 = 2 * m + 2 + 2 := by omega
    rw [e]
    omega

end Sync

end Node

end LeanDag
