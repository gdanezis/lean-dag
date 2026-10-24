import LeanDag.Node.Helpers.Flush
/-!
# The walks of a sync

The stream for a request holds, with each of its blocks, each reference of
it that the store holds and the stream carries (`streamOf_closed`), and the
requested block itself (`mem_streamOf_self`); its blocks are the store's
(`mem_streamOf`). The walk through a stream piece from a block meets, with
each block, each reference of it that the piece holds (`found_closed`),
and the block itself when the piece holds it (`found_self`); a piece of a
block map's blocks gives each block its references (`pieceRefs_of_map`).
A block valid under a block map is ready on a store reading as it that
holds its references (`ready_of_refs`), and a stream piece taken in
without gaining a block was taken in block by block with each held or not
ready (`foldl_stuck`).
-/

namespace LeanDag

namespace Node

variable {Validator BlockId Payload : Type} [Fintype Validator] [DecidableEq Validator]
variable [LinearOrder BlockId]
variable {cfg : Config Validator BlockId Payload}

section Stream

variable (st : Store Validator BlockId Payload) (carries : BlockId → Bool) (t : BlockId)

/-- The stream's walk after `k` levels. -/
def streamAt (k : ℕ) : List BlockId × List BlockId :=
  (streamLevel st carries)^[k] ([t], [])

omit [Fintype Validator] [DecidableEq Validator] in
theorem streamAt_succ (k : ℕ) :
    streamAt st carries t (k + 1) = streamLevel st carries (streamAt st carries t k) := by
  unfold streamAt
  rw [Function.iterate_succ_apply']

omit [Fintype Validator] [DecidableEq Validator] in
/-- **The walk's front**, past the first level, is the references of
blocks it met, and what it met is on the store and carried. -/
theorem streamAt_spec : ∀ k : ℕ,
    (∀ x ∈ (streamAt st carries t k).2, x ∈ st.ids ∧ carries x = true) ∧
    (∀ x ∈ (streamAt st carries t k).2, ∀ y ∈ (st.blk x).refs, y ∈ st.ids → carries y = true →
      y ∈ (streamAt st carries t k).2 ∨ y ∈ (streamAt st carries t k).1) ∧
    (∀ x ∈ (streamAt st carries t k).1, x ∈ st.ids →
      (st.blk x).round + k = (st.blk t).round)
  | 0 => ⟨fun _ h => absurd h List.not_mem_nil, fun _ h => absurd h List.not_mem_nil,
      fun x hx _ => by
        simp only [streamAt, Function.iterate_zero, id, List.mem_singleton] at hx
        subst hx; rfl⟩
  | k + 1 => by
    obtain ⟨h₁, h₂, h₃⟩ := streamAt_spec k
    rw [streamAt_succ]
    set w := streamAt st carries t k
    unfold streamLevel
    dsimp only
    set front := (w.1.filter fun x => decide (x ∈ st.ids) && carries x && decide (x ∉ w.2)).dedup
    have hfront : ∀ x ∈ front, x ∈ w.1 ∧ x ∈ st.ids ∧ carries x = true ∧ x ∉ w.2 := by
      intro x hx
      have := List.mem_filter.mp (List.mem_dedup.mp hx)
      simp only [Bool.and_eq_true, decide_eq_true_eq] at this
      exact ⟨this.1, this.2.1.1, this.2.1.2, this.2.2⟩
    refine ⟨fun x hx => ?_, fun x hx y hy hyst hyc => ?_, fun x hx hxst => ?_⟩
    · rcases List.mem_append.mp hx with hx | hx
      · exact h₁ x hx
      · exact ⟨(hfront x hx).2.1, (hfront x hx).2.2.1⟩
    · rcases List.mem_append.mp hx with hx | hx
      · rcases h₂ x hx y hy hyst hyc with h | h
        · exact Or.inl (List.mem_append_left _ h)
        · by_cases hyw : y ∈ w.2
          · exact Or.inl (List.mem_append_left _ hyw)
          · refine Or.inl (List.mem_append_right _ (List.mem_dedup.mpr (List.mem_filter.mpr
              ⟨h, ?_⟩)))
            simp [hyst, hyc, hyw]
      · exact Or.inr (List.mem_flatMap.mpr ⟨x, hx, (Finset.mem_sort _).mpr hy⟩)
    · obtain ⟨p, hp, hxp⟩ := List.mem_flatMap.mp hx
      rw [Finset.mem_sort] at hxp
      obtain ⟨hpw, hpst, -, -⟩ := hfront p hp
      have hr : (st.blk p).round + k = (st.blk t).round := h₃ p hpw hpst
      have hpr : (st.blk x).round + 1 = (st.blk p).round := st.pred p hpst x hxp
      omega

omit [Fintype Validator] [DecidableEq Validator] in
/-- **The stream's identifiers** are what the walk met. -/
theorem mem_streamOf_iff {fr : Validator → ℕ} {ids : List BlockId} {x : BlockId} :
    x ∈ (streamOf st t fr ids).map Prod.fst ↔ x ∈ (streamAt st (fun i =>
      decide (i = t ∨ i ∈ ids ∨ fr (st.blk i).creator ≤ (st.blk i).round)) t
        ((st.blk t).round + 1)).2 := by
  unfold streamOf streamAt
  constructor
  · intro hx
    obtain ⟨e, he, rfl⟩ := List.mem_map.mp hx
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp (List.mem_mergeSort.mp he)
    exact hi
  · intro hx
    exact List.mem_map.mpr ⟨(x, st.blk x), List.mem_mergeSort.mpr (List.mem_map.mpr ⟨x, hx, rfl⟩),
      rfl⟩

omit [Fintype Validator] [DecidableEq Validator] in
/-- **The stream is closed under carried references on the store.** -/
theorem streamOf_closed {fr : Validator → ℕ} {ids : List BlockId} {x y : BlockId}
    (hx : x ∈ (streamOf st t fr ids).map Prod.fst) (hy : y ∈ (st.blk x).refs) (hyst : y ∈ st.ids)
    (hyc : y = t ∨ y ∈ ids ∨ fr (st.blk y).creator ≤ (st.blk y).round) :
    y ∈ (streamOf st t fr ids).map Prod.fst := by
  rw [mem_streamOf_iff] at hx ⊢
  obtain ⟨-, h₂, h₃⟩ := streamAt_spec st (fun i =>
    decide (i = t ∨ i ∈ ids ∨ fr (st.blk i).creator ≤ (st.blk i).round)) t ((st.blk t).round + 1)
  rcases h₂ x hx y hy hyst (by simpa using hyc) with h | h
  · exact h
  · have := h₃ y h hyst; omega

omit [Fintype Validator] [DecidableEq Validator] in
/-- What the walk met it keeps. -/
theorem streamAt_mono {k k' : ℕ} (h : k ≤ k') :
    (streamAt st carries t k).2 ⊆ (streamAt st carries t k').2 := by
  induction k', h using Nat.le_induction with
  | base => exact List.Subset.refl _
  | succ k' _ ih =>
    intro x hx
    rw [streamAt_succ]
    exact List.mem_append_left _ (ih hx)

omit [Fintype Validator] [DecidableEq Validator] in
/-- **The stream holds the requested block**, when the store does. -/
theorem mem_streamOf_self {fr : Validator → ℕ} {ids : List BlockId} (ht : t ∈ st.ids) :
    t ∈ (streamOf st t fr ids).map Prod.fst := by
  rw [mem_streamOf_iff]
  refine streamAt_mono st _ t (show 1 ≤ (st.blk t).round + 1 by omega) ?_
  rw [streamAt_succ]
  simp [streamAt, streamLevel, ht]

omit [Fintype Validator] [DecidableEq Validator] in
/-- **The stream's blocks are the store's.** -/
theorem mem_streamOf {fr : Validator → ℕ} {ids : List BlockId}
    {e : BlockId × Block Validator BlockId Payload} (he : e ∈ streamOf st t fr ids) :
    e.1 ∈ st.ids ∧ e.2 = st.blk e.1 := by
  unfold streamOf at he
  obtain ⟨i, hi, rfl⟩ := List.mem_map.mp (List.mem_mergeSort.mp he)
  exact ⟨((streamAt_spec st _ t _).1 i hi).1, rfl⟩

end Stream

section Piece

variable (L : List (BlockId × Block Validator BlockId Payload)) (t : BlockId)

/-- The references the piece gives an identifier: those of its first block
under it. -/
def pieceRefs (x : BlockId) : List BlockId :=
  ((L.find? fun e => decide (e.1 = x)).map fun e => e.2.refs.sort (· ≤ ·)).getD []

/-- The piece's walk after `k` levels. -/
def pieceAt (k : ℕ) : List BlockId × List BlockId :=
  (pieceLevel L)^[k] ([t], [])

omit [Fintype Validator] [DecidableEq Validator] in
theorem pieceAt_succ (k : ℕ) : pieceAt L t (k + 1) = pieceLevel L (pieceAt L t k) := by
  unfold pieceAt
  rw [Function.iterate_succ_apply']

omit [Fintype Validator] [DecidableEq Validator] in
/-- **The piece's walk**: what it met is in the piece, once each; the
references the piece gives what it met are met or in the front; and the
front holds an identifier of the piece not met only after as many levels
as it met. -/
theorem pieceAt_spec : ∀ k : ℕ,
    (∀ x ∈ (pieceAt L t k).2, x ∈ L.map Prod.fst) ∧ (pieceAt L t k).2.Nodup ∧
    (∀ x ∈ (pieceAt L t k).2, ∀ y ∈ pieceRefs L x, y ∈ L.map Prod.fst →
      y ∈ (pieceAt L t k).2 ∨ y ∈ (pieceAt L t k).1) ∧
    ((∃ y ∈ (pieceAt L t k).1, y ∈ L.map Prod.fst ∧ y ∉ (pieceAt L t k).2) →
      k ≤ (pieceAt L t k).2.length)
  | 0 => ⟨fun _ h => absurd h List.not_mem_nil, List.nodup_nil,
      fun _ h => absurd h List.not_mem_nil, fun _ => Nat.zero_le _⟩
  | k + 1 => by
    obtain ⟨h₁, h₂, h₃, h₄⟩ := pieceAt_spec k
    rw [pieceAt_succ]
    set w := pieceAt L t k
    unfold pieceLevel
    dsimp only
    set front := (w.1.filter fun x => decide (x ∈ L.map Prod.fst) && decide (x ∉ w.2)).dedup
    have hfront : ∀ x ∈ front, x ∈ w.1 ∧ x ∈ L.map Prod.fst ∧ x ∉ w.2 := by
      intro x hx
      have := List.mem_filter.mp (List.mem_dedup.mp hx)
      simp only [Bool.and_eq_true, decide_eq_true_eq] at this
      exact ⟨this.1, this.2.1, this.2.2⟩
    have hnd : front.Nodup := List.nodup_dedup _
    refine ⟨fun x hx => ?_, ?_, fun x hx y hy hyL => ?_, fun ⟨y, hy, hyL, hyn⟩ => ?_⟩
    · rcases List.mem_append.mp hx with hx | hx
      · exact h₁ x hx
      · exact (hfront x hx).2.1
    · exact List.Nodup.append h₂ hnd fun x hx hx' => (hfront x hx').2.2 hx
    · rcases List.mem_append.mp hx with hx | hx
      · rcases h₃ x hx y hy hyL with h | h
        · exact Or.inl (List.mem_append_left _ h)
        · by_cases hyw : y ∈ w.2
          · exact Or.inl (List.mem_append_left _ hyw)
          · refine Or.inl (List.mem_append_right _ (List.mem_dedup.mpr (List.mem_filter.mpr
              ⟨h, ?_⟩)))
            simp [hyL, hyw]
      · exact Or.inr (List.mem_flatMap.mpr ⟨x, hx, hy⟩)
    · -- the front was not empty, so the walk met a new identifier at this level
      obtain ⟨p, hp, -⟩ := List.mem_flatMap.mp hy
      obtain ⟨hpw, hpL, hpn⟩ := hfront p hp
      have hk := h₄ ⟨p, hpw, hpL, hpn⟩
      rw [List.length_append]
      have : 0 < front.length := List.length_pos_of_mem hp
      omega

omit [Fintype Validator] [DecidableEq Validator] in
/-- **The part of a piece in a block's history is closed** under the
references the piece gives, among the piece's identifiers. -/
theorem found_closed {x y : BlockId} (hx : x ∈ (pieceAt L t (L.length + 1)).2)
    (hy : y ∈ pieceRefs L x) (hyL : y ∈ L.map Prod.fst) : y ∈ (pieceAt L t (L.length + 1)).2 := by
  obtain ⟨h₁, h₂, h₃, h₄⟩ := pieceAt_spec L t (L.length + 1)
  rcases h₃ x hx y hy hyL with h | h
  · exact h
  · by_contra hyn
    have hk := h₄ ⟨y, h, hyL, hyn⟩
    have hle : (pieceAt L t (L.length + 1)).2.length ≤ (L.map Prod.fst).length :=
      (List.Nodup.subperm h₂ h₁).length_le
    rw [List.length_map] at hle
    omega

omit [Fintype Validator] [DecidableEq Validator] in
/-- What the piece's walk met it keeps. -/
theorem pieceAt_mono {k k' : ℕ} (h : k ≤ k') :
    (pieceAt L t k).2 ⊆ (pieceAt L t k').2 := by
  induction k', h using Nat.le_induction with
  | base => exact List.Subset.refl _
  | succ k' _ ih =>
    intro x hx
    rw [pieceAt_succ]
    exact List.mem_append_left _ (ih hx)

omit [Fintype Validator] [DecidableEq Validator] in
/-- **The block itself is met**, when the piece holds it. -/
theorem found_self (ht : t ∈ L.map Prod.fst) : t ∈ (pieceAt L t (L.length + 1)).2 := by
  refine pieceAt_mono L t (show 1 ≤ L.length + 1 by omega) ?_
  rw [pieceAt_succ]
  simp [pieceAt, pieceLevel, ht]

omit [Fintype Validator] in
/-- **Membership of the part of a piece in a block's history.** -/
theorem mem_inHistory {b : BlockId × Block Validator BlockId Payload}
    {e : BlockId × Block Validator BlockId Payload} :
    e ∈ inHistory cfg b L ↔ e ∈ L ∧ e.1 = cfg.idOf e.2 ∧ e.2.creator ≠ cfg.me ∧
      e.1 ∈ (pieceAt L b.1 (L.length + 1)).2 := by
  unfold inHistory
  rw [List.mem_mergeSort, List.mem_filter]
  simp only [Bool.and_eq_true, decide_eq_true_eq]
  constructor
  · rintro ⟨h, ⟨h₁, h₂⟩, h₃⟩; exact ⟨h, h₁, h₂, h₃⟩
  · rintro ⟨h, h₁, h₂, h₃⟩; exact ⟨h, ⟨h₁, h₂⟩, h₃⟩

omit [Fintype Validator] [DecidableEq Validator] in
/-- **A piece of a block map's blocks** gives each identifier it holds the
references of its block. -/
theorem pieceRefs_of_map {g : BlockId → Block Validator BlockId Payload}
    (hL : ∀ e ∈ L, e.2 = g e.1) {x : BlockId} (hx : x ∈ L.map Prod.fst) {y : BlockId} :
    y ∈ pieceRefs L x ↔ y ∈ (g x).refs := by
  have : ∃ e, (L.find? fun e' => decide (e'.1 = x)) = some e := by
    obtain ⟨e, heL, rfl⟩ := List.mem_map.mp hx
    exact Option.isSome_iff_exists.mp
      ((List.find?_isSome (p := fun e' => decide (e'.1 = e.1))).mpr ⟨e, heL, by simp⟩)
  obtain ⟨e, hf⟩ := this
  have hex : e.1 = x := by simpa using List.find?_some hf
  have heg := hL e (List.mem_of_find?_eq_some hf)
  simp [pieceRefs, hf, Finset.mem_sort, heg, hex]

end Piece

section Ready

omit [Fintype Validator] in
/-- **A block valid under a block map is ready** on a store reading as it
that holds its references. -/
theorem ready_of_refs {g : BlockId → Block Validator BlockId Payload}
    {y : BlockId × Block Validator BlockId Payload}
    (hv : (∀ j ∈ y.2.refs, (g j).round + 1 = y.2.round) ∧ rowValid cfg.q cfg.xp g y.2)
    {st : Store Validator BlockId Payload} (hst : ReadsAs g st) (hrefs : y.2.refs ⊆ st.ids)
    (hnin : y.1 ∉ st.ids) : readyOn cfg st y = true := by
  have hag : ∀ j ∈ y.2.refs, st.blk j = g j := fun j hj => hst j (hrefs hj)
  simp only [readyOn, Store.Checks, decide_eq_true_eq]
  refine ⟨hrefs, fun j hj => by rw [hag j hj]; exact hv.1 j hj,
    rowValid_congr (fun j hj => ?_) hv.2⟩
  have hj' : j ≠ y.1 := fun e => hnin (e ▸ hrefs hj)
  rw [Function.update_of_ne hj', hag j hj]; exact ⟨rfl, rfl, rfl⟩

omit [Fintype Validator] in
/-- **Blocks taken in whole**: blocks in order of round, valid under a
block map they agree with, each of whose references the store or the
blocks hold, are all held after they are taken in. -/
theorem foldl_all {g : BlockId → Block Validator BlockId Payload} :
    ∀ (l : List (BlockId × Block Validator BlockId Payload)) (st : Store Validator BlockId Payload),
    l.Pairwise (fun x y => x.2.round ≤ y.2.round) → ReadsAs g st → (∀ e ∈ l, g e.1 = e.2) →
    (∀ e ∈ l, (∀ j ∈ e.2.refs, (g j).round + 1 = e.2.round) ∧ rowValid cfg.q cfg.xp g e.2) →
    (∀ e ∈ l, ∀ y ∈ e.2.refs, y ∈ st.ids ∨ y ∈ l.map Prod.fst) →
    ∀ e ∈ l, e.1 ∈ (l.foldl (fun s e => acceptOn cfg s e.1 e.2) st).ids
  | [], _, _, _, _, _, _, _, he => absurd he List.not_mem_nil
  | x :: l, st, hp, hst, hg, hv, hcl, e, he => by
    rw [List.foldl_cons]
    have hx : x.1 ∈ (acceptOn cfg st x.1 x.2).ids := by
      by_cases hin : x.1 ∈ st.ids
      · exact (Grows.accept (cfg := cfg) st x.1 x.2).1 hin
      · have hrefs : x.2.refs ⊆ st.ids := fun y hy => by
          rcases hcl x List.mem_cons_self y hy with h | h
          · exact h
          · exfalso
            obtain ⟨e', he', rfl⟩ := List.mem_map.mp h
            have hr := (hv x List.mem_cons_self).1 _ hy
            rw [hg e' he'] at hr
            rcases List.mem_cons.mp he' with rfl | he'
            · omega
            · have := List.rel_of_pairwise_cons hp he'
              omega
        have hr := ready_of_refs (hv x List.mem_cons_self) hst hrefs hin
        have hc : x.1 ∉ st.ids ∧ st.Checks cfg.q cfg.xp x.1 x.2 :=
          ⟨hin, by simpa [readyOn] using hr⟩
        unfold acceptOn
        rw [dif_pos hc, Store.insert_ids]
        exact Finset.mem_insert_self _ _
    rcases List.mem_cons.mp he with rfl | he
    · exact (Grows.foldl (cfg := cfg) l _).1 hx
    · refine foldl_all l _ (List.Pairwise.of_cons hp) (hst.accept (hg x List.mem_cons_self))
        (fun e he => hg e (List.mem_cons_of_mem _ he))
        (fun e he => hv e (List.mem_cons_of_mem _ he)) (fun e' he' y hy => ?_) e he
      rcases hcl e' (List.mem_cons_of_mem _ he') y hy with h | h
      · exact Or.inl ((Grows.accept (cfg := cfg) st x.1 x.2).1 h)
      · rcases List.mem_cons.mp h with h | h
        · exact Or.inl (h ▸ hx)
        · exact Or.inr h

end Ready

end Node

end LeanDag
