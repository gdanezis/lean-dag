import LeanDag.Node.Helpers.Grow
/-!
# What flushing leaves

With more passes than pending blocks, a flush leaves no pending block
ready (`flush_no_ready`): each pass that finds a ready block removes it.
And on stores at horizon `0` reading as a block map `g`, a pending block
that `accept` takes whenever it is ready (`Fits`), which every block
valid under `g` is (`fits_of_valid`), is still pending or accepted
afterwards (`flush_keeps`).
-/

namespace LeanDag

namespace Node

variable {Validator BlockId Payload : Type} [Fintype Validator] [DecidableEq Validator]
variable [LinearOrder BlockId]
variable {cfg : Config Validator BlockId Payload}

omit [Fintype Validator] in
/-- **No pending block is left ready** by a flush with more passes than
pending blocks. -/
theorem flush_no_ready : ∀ (fuel : ℕ) (st : Store Validator BlockId Payload)
    (pend : List (BlockId × Block Validator BlockId Payload)), pend.length < fuel →
    ∀ e ∈ (flush cfg fuel st pend).2, ready cfg (flush cfg fuel st pend).1 e = false
  | 0, _, _, h => absurd h (Nat.not_lt_zero _)
  | fuel + 1, st, pend, h => by
    unfold flush
    dsimp only
    split
    · rename_i hE
      intro e he
      rw [List.isEmpty_iff, List.partition_eq_filter_filter, List.filter_eq_nil_iff] at hE
      simpa using hE e he
    · rename_i hE
      apply flush_no_ready
      rw [List.partition_eq_filter_filter] at hE ⊢
      have hl := List.length_eq_length_filter_add (fun e => ready cfg st e) (l := pend)
      have : 0 < (pend.filter fun e => ready cfg st e).length := by
        rw [List.isEmpty_iff] at hE
        exact List.length_pos_of_ne_nil hE
      simp only [Function.comp_def] at hl ⊢
      omega

variable (g : BlockId → Block Validator BlockId Payload)

/-- **A store at horizon `0` reading as `g`.** -/
def ReadsAs (st : Store Validator BlockId Payload) : Prop :=
  st.base = 0 ∧ ∀ j ∈ st.ids, st.blk j = g j

variable {g}

omit [Fintype Validator] in
theorem ReadsAs.accept {st : Store Validator BlockId Payload} (h : ReadsAs g st) {id : BlockId}
    {b : Block Validator BlockId Payload} (hb : g id = atBase 0 b) :
    ReadsAs g (Node.accept cfg st id b) := by
  unfold Node.accept
  split
  · rename_i hc
    refine ⟨h.1, fun j hj => ?_⟩
    change j ∈ Insert.insert id st.ids at hj
    by_cases hj' : j = id
    · subst hj'
      simp only [Store.blk, lookup, Store.insert, Std.TreeMap.getD_insert_self, h.1]
      exact hb.symm
    · have := Grows.blk (Grows.insert st (hnew := hc.1) (hab := hc.2.1) (hrefs := hc.2.2.1)
        (hpred := hc.2.2.2.1)) rfl ((Finset.mem_insert.mp hj).resolve_left hj')
      rw [this]
      exact h.2 j ((Finset.mem_insert.mp hj).resolve_left hj')
  · exact h

omit [Fintype Validator] in
theorem ReadsAs.foldl : ∀ (l : List (BlockId × Block Validator BlockId Payload))
    {st : Store Validator BlockId Payload}, ReadsAs g st → (∀ e ∈ l, g e.1 = atBase 0 e.2) →
    ReadsAs g (l.foldl (fun s e => Node.accept cfg s e.1 e.2) st)
  | [], _, h, _ => h
  | e :: l, _, h, hl =>
    ReadsAs.foldl l (h.accept (hl e List.mem_cons_self))
      fun x hx => hl x (List.mem_cons_of_mem _ hx)

omit [Fintype Validator] in
theorem ReadsAs.flush : ∀ (fuel : ℕ) {st : Store Validator BlockId Payload}
    {pend : List (BlockId × Block Validator BlockId Payload)}, ReadsAs g st →
    (∀ e ∈ pend, g e.1 = atBase 0 e.2) →
    ReadsAs g (Node.flush cfg fuel st pend).1 ∧ ∀ e ∈ (Node.flush cfg fuel st pend).2,
      g e.1 = atBase 0 e.2
  | 0, _, _, h, hp => ⟨h, hp⟩
  | fuel + 1, st, pend, h, hp => by
    unfold Node.flush
    dsimp only
    split
    · exact ⟨h, hp⟩
    · rw [List.partition_eq_filter_filter]
      exact ReadsAs.flush fuel (h.foldl _ fun e he => hp e (List.mem_filter.mp he).1)
        fun e he => hp e (List.mem_filter.mp he).1

variable (cfg g) in
/-- **`accept` takes the block whenever it is ready**, on a store reading
as `g`. -/
def Fits (y : BlockId × Block Validator BlockId Payload) : Prop :=
  ∀ st : Store Validator BlockId Payload, ReadsAs g st → ready cfg st y = true →
    y.1 ∈ (Node.accept cfg st y.1 y.2).ids

omit [Fintype Validator] in
/-- **A block valid under `g` fits.** -/
theorem fits_of_valid {y : BlockId × Block Validator BlockId Payload}
    (hv : 0 < y.2.round → (∀ j ∈ y.2.refs, (g j).round + 1 = y.2.round) ∧
      rowValid cfg.q g y.2) : Fits cfg g y := by
  intro st hst hr
  unfold Node.accept
  by_cases hin : y.1 ∈ st.ids
  · split
    · exact Finset.mem_insert_self _ _
    · exact hin
  · have hrefs : st.base < y.2.round → y.2.refs ⊆ st.ids := by
      intro hlt
      simp only [ready, Bool.or_eq_true, decide_eq_true_eq] at hr
      rcases hr with hr | hr
      · omega
      · exact hr.1
    have hag : ∀ j ∈ y.2.refs, st.base < y.2.round → st.blk j = g j :=
      fun j hj hlt => hst.2 j (hrefs hlt hj)
    rw [dif_pos ⟨hin, by rw [hst.1]; exact Nat.zero_le _, hrefs, fun hlt j hj => by
        rw [hag j hj hlt]; exact (hv (by omega)).1 j hj,
      fun hlt => rowValid_congr (fun j hj => by
        have hj' : j ≠ y.1 := fun e => hin (e ▸ hrefs hlt hj)
        rw [Function.update_of_ne hj', hag j hj hlt]; exact ⟨rfl, rfl⟩)
        (hv (by omega)).2⟩]
    exact Finset.mem_insert_self _ _

omit [Fintype Validator] in
theorem ready_mono {st st' : Store Validator BlockId Payload} (hg : Grows st st')
    (hb : st'.base = st.base) {e : BlockId × Block Validator BlockId Payload}
    (h : ready cfg st e = true) : ready cfg st' e = true := by
  simp only [ready, Bool.or_eq_true, decide_eq_true_eq] at h ⊢
  obtain ⟨hsub, -, hm⟩ := hg.2 hb
  have hblk : ∀ j ∈ st.ids, st'.blk j = st.blk j := fun j hj => by
    unfold Store.blk lookup; rw [hm j hj, hb]
  rcases h with h | ⟨h₁, h₂, h₃⟩
  · exact Or.inl (hb ▸ h)
  · refine Or.inr ⟨h₁.trans hsub, fun j hj => by rw [hblk j (h₁ hj)]; exact h₂ j hj,
      rowValid_congr (fun j hj => ?_) h₃⟩
    by_cases hje : j = e.1
    · subst hje; simp
    · rw [Function.update_of_ne hje, Function.update_of_ne hje, hblk j (h₁ hj)]
      exact ⟨rfl, rfl⟩

omit [Fintype Validator] in
theorem foldl_takes : ∀ (l : List (BlockId × Block Validator BlockId Payload))
    {st : Store Validator BlockId Payload} {y : BlockId × Block Validator BlockId Payload},
    ReadsAs g st → (∀ e ∈ l, g e.1 = atBase 0 e.2) → Fits cfg g y → y ∈ l →
    ready cfg st y = true → y.1 ∈ (l.foldl (fun s e => Node.accept cfg s e.1 e.2) st).ids
  | [], _, _, _, _, _, hy, _ => absurd hy (List.not_mem_nil)
  | e :: l, st, y, h, hl, hf, hy, hr => by
    rw [List.foldl_cons]
    have hst₁ := h.accept (cfg := cfg) (hl e List.mem_cons_self)
    have hg := Grows.foldl (cfg := cfg) l (Node.accept cfg st e.1 e.2)
    have hb : (l.foldl (fun s e => Node.accept cfg s e.1 e.2) (Node.accept cfg st e.1 e.2)).base =
        (Node.accept cfg st e.1 e.2).base := by
      rw [(ReadsAs.foldl l hst₁ fun x hx => hl x (List.mem_cons_of_mem _ hx)).1, hst₁.1]
    rcases List.mem_cons.mp hy with rfl | hy
    · exact (hg.2 hb).1 (hf st h hr)
    · refine foldl_takes l hst₁ (fun x hx => hl x (List.mem_cons_of_mem _ hx)) hf hy ?_
      exact ready_mono (Grows.accept (cfg := cfg) st e.1 e.2) (by rw [hst₁.1, h.1]) hr

omit [Fintype Validator] in
/-- **A fitting pending block is still pending or accepted after a flush.** -/
theorem flush_keeps : ∀ (fuel : ℕ) {st : Store Validator BlockId Payload}
    {pend : List (BlockId × Block Validator BlockId Payload)}
    {y : BlockId × Block Validator BlockId Payload},
    ReadsAs g st → (∀ e ∈ pend, g e.1 = atBase 0 e.2) → Fits cfg g y → y ∈ pend →
    y ∈ (Node.flush cfg fuel st pend).2 ∨ y.1 ∈ (Node.flush cfg fuel st pend).1.ids
  | 0, _, _, _, _, _, _, hy => Or.inl hy
  | fuel + 1, st, pend, y, h, hp, hf, hy => by
    unfold Node.flush
    dsimp only
    split
    · exact Or.inl hy
    · rw [List.partition_eq_filter_filter]
      have hst₁ := h.foldl (cfg := cfg) (pend.filter fun e => ready cfg st e)
        fun e he => hp e (List.mem_filter.mp he).1
      by_cases hr : ready cfg st y = true
      · right
        have hin := foldl_takes (pend.filter fun e => ready cfg st e) h
          (fun e he => hp e (List.mem_filter.mp he).1) hf
          (List.mem_filter.mpr ⟨hy, hr⟩) hr
        have hg := Grows.flush (cfg := cfg) fuel
          ((pend.filter fun e => ready cfg st e).foldl (fun s e => Node.accept cfg s e.1 e.2) st)
          (pend.filter fun e => !ready cfg st e)
        have hb := (ReadsAs.flush (cfg := cfg) fuel hst₁
          (pend := pend.filter fun e => !ready cfg st e)
          fun e he => hp e (List.mem_filter.mp he).1).1.1
        simp only [Function.comp_def]
        exact (hg.2 (hb.trans hst₁.1.symm)).1 hin
      · simp only [Function.comp_def]
        exact flush_keeps fuel hst₁ (fun e he => hp e (List.mem_filter.mp he).1) hf
          (List.mem_filter.mpr ⟨hy, by simpa using hr⟩)

omit [Fintype Validator] in
theorem accept_in {K : Set (BlockId × Block Validator BlockId Payload)}
    {st : Store Validator BlockId Payload} (hK : ∀ j ∈ st.ids, (j, st.map.getD j st.junk) ∈ K)
    {id : BlockId} {b : Block Validator BlockId Payload} (hb : (id, b) ∈ K) :
    ∀ j ∈ (accept cfg st id b).ids,
      (j, (accept cfg st id b).map.getD j (accept cfg st id b).junk) ∈ K := by
  unfold accept
  split
  · exact known_insert hK hb
  · exact hK

omit [Fintype Validator] in
theorem foldl_in {K : Set (BlockId × Block Validator BlockId Payload)} :
    ∀ (l : List (BlockId × Block Validator BlockId Payload)) {st : Store Validator BlockId Payload},
    (∀ j ∈ st.ids, (j, st.map.getD j st.junk) ∈ K) → (∀ e ∈ l, e ∈ K) →
    let st' := l.foldl (fun s e => accept cfg s e.1 e.2) st
    ∀ j ∈ st'.ids, (j, st'.map.getD j st'.junk) ∈ K
  | [], _, hK, _ => hK
  | e :: l, _, hK, hl =>
    foldl_in l (accept_in hK (hl e List.mem_cons_self)) fun x hx => hl x (List.mem_cons_of_mem _ hx)

omit [Fintype Validator] in
/-- **A flush holds only what it was given**: the store's blocks and the
pending ones. -/
theorem flush_in {K : Set (BlockId × Block Validator BlockId Payload)} :
    ∀ (fuel : ℕ) {st : Store Validator BlockId Payload}
      {pend : List (BlockId × Block Validator BlockId Payload)},
    (∀ j ∈ st.ids, (j, st.map.getD j st.junk) ∈ K) → (∀ e ∈ pend, e ∈ K) →
    let r := flush cfg fuel st pend
    (∀ j ∈ r.1.ids, (j, r.1.map.getD j r.1.junk) ∈ K) ∧ ∀ e ∈ r.2, e ∈ K
  | 0, _, _, hK, hp => ⟨hK, hp⟩
  | fuel + 1, st, pend, hK, hp => by
    unfold flush
    dsimp only
    split
    · exact ⟨hK, hp⟩
    · rw [List.partition_eq_filter_filter]
      exact flush_in fuel (foldl_in _ hK fun e he => hp e (List.mem_filter.mp he).1)
        fun e he => hp e (List.mem_filter.mp he).1

end Node

end LeanDag
