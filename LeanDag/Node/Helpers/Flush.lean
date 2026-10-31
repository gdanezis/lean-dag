import LeanDag.Node.Helpers.Grow
/-!
# Accepting blocks on a store

On stores reading as a block map `g`, accepting blocks of `g` keeps the
store reading as `g` (`ReadsAs.foldl`). A block that `accept` takes
whenever it is ready (`Fits`), which every block valid under `g` is
(`fits_of_valid`), is taken by accepting a list holding it once it is
ready (`foldl_takes`). Accepting known blocks keeps the store known
(`foldl_in`).
-/

namespace LeanDag

namespace Node

variable {Validator BlockId Payload : Type} [Fintype Validator] [DecidableEq Validator]
variable [LinearOrder BlockId]
variable {cfg : Config Validator BlockId Payload}

variable (g : BlockId → Block Validator BlockId Payload)

/-- **A store reading as `g`.** -/
def ReadsAs (st : Store Validator BlockId Payload) : Prop :=
  ∀ j ∈ st.ids, st.blk j = g j

variable {g}

omit [Fintype Validator] in
theorem ReadsAs.accept {st : Store Validator BlockId Payload} (h : ReadsAs g st) {id : BlockId}
    {b : Block Validator BlockId Payload} (hb : g id = b) :
    ReadsAs g (acceptOn cfg st id b) := by
  unfold acceptOn
  split
  · rename_i hc
    intro j hj
    rw [Store.insert_ids] at hj
    by_cases hj' : j = id
    · subst hj'
      simp only [Store.blk, Store.insert, Std.TreeMap.getD_insert_self]
      exact hb.symm
    · have := Grows.blk (Grows.insert st (hnew := hc.1) (hrefs := hc.2.1)
        (hpred := hc.2.2.1)) ((Finset.mem_insert.mp hj).resolve_left hj')
      rw [this]
      exact h j ((Finset.mem_insert.mp hj).resolve_left hj')
  · exact h

omit [Fintype Validator] in
theorem ReadsAs.foldl : ∀ (l : List (BlockId × Block Validator BlockId Payload))
    {st : Store Validator BlockId Payload}, ReadsAs g st → (∀ e ∈ l, g e.1 = e.2) →
    ReadsAs g (l.foldl (fun s e => acceptOn cfg s e.1 e.2) st)
  | [], _, h, _ => h
  | e :: l, _, h, hl =>
    ReadsAs.foldl l (h.accept (hl e List.mem_cons_self))
      fun x hx => hl x (List.mem_cons_of_mem _ hx)

variable (cfg g) in
/-- **`accept` takes the block whenever it is ready**, on a store reading
as `g`. -/
def Fits (y : BlockId × Block Validator BlockId Payload) : Prop :=
  ∀ st : Store Validator BlockId Payload, ReadsAs g st → readyOn cfg st y = true →
    y.1 ∈ (acceptOn cfg st y.1 y.2).ids

omit [Fintype Validator] in
/-- **A block valid under `g` fits.** -/
theorem fits_of_valid {y : BlockId × Block Validator BlockId Payload}
    (hv : (∀ j ∈ y.2.refs, (g j).round + 1 = y.2.round) ∧ rowValid cfg.q cfg.xp g y.2) :
    Fits cfg g y := by
  intro st hst hr
  unfold acceptOn
  by_cases hin : y.1 ∈ st.ids
  · split
    · exact Store.mem_insert_self
    · exact hin
  · have hrefs : y.2.refs ⊆ st.ids := by
      simp only [readyOn, Store.Checks, decide_eq_true_eq] at hr
      exact hr.1
    have hag : ∀ j ∈ y.2.refs, st.blk j = g j := fun j hj => hst j (hrefs hj)
    rw [dif_pos ⟨hin, hrefs, fun j hj => by rw [hag j hj]; exact hv.1 j hj,
      rowValid_congr (fun j hj => by
        have hj' : j ≠ y.1 := fun e => hin (e ▸ hrefs hj)
        rw [Function.update_of_ne hj', hag j hj]; exact ⟨rfl, rfl, rfl⟩) hv.2⟩]
    exact Store.mem_insert_self

omit [Fintype Validator] in
theorem ready_mono {st st' : Store Validator BlockId Payload} (hg : Grows st st')
    {e : BlockId × Block Validator BlockId Payload}
    (h : readyOn cfg st e = true) : readyOn cfg st' e = true := by
  simp only [readyOn, Store.Checks, decide_eq_true_eq] at h ⊢
  obtain ⟨h₁, h₂, h₃⟩ := h
  refine ⟨h₁.trans hg.1, fun j hj => by rw [hg.blk (h₁ hj)]; exact h₂ j hj,
    rowValid_congr (fun j hj => ?_) h₃⟩
  by_cases hje : j = e.1
  · subst hje; simp
  · rw [Function.update_of_ne hje, Function.update_of_ne hje, hg.blk (h₁ hj)]
    exact ⟨rfl, rfl, rfl⟩

omit [Fintype Validator] in
theorem foldl_takes : ∀ (l : List (BlockId × Block Validator BlockId Payload))
    {st : Store Validator BlockId Payload} {y : BlockId × Block Validator BlockId Payload},
    ReadsAs g st → (∀ e ∈ l, g e.1 = e.2) → Fits cfg g y → y ∈ l →
    readyOn cfg st y = true → y.1 ∈ (l.foldl (fun s e => acceptOn cfg s e.1 e.2) st).ids
  | [], _, _, _, _, _, hy, _ => absurd hy (List.not_mem_nil)
  | e :: l, st, y, h, hl, hf, hy, hr => by
    rw [List.foldl_cons]
    have hst₁ := h.accept (cfg := cfg) (hl e List.mem_cons_self)
    have hg := Grows.foldl (cfg := cfg) l (acceptOn cfg st e.1 e.2)
    rcases List.mem_cons.mp hy with rfl | hy
    · exact hg.1 (hf st h hr)
    · refine foldl_takes l hst₁ (fun x hx => hl x (List.mem_cons_of_mem _ hx)) hf hy ?_
      exact ready_mono (Grows.accept (cfg := cfg) st e.1 e.2) hr

omit [Fintype Validator] in
theorem accept_in {K : Set (BlockId × Block Validator BlockId Payload)}
    {st : Store Validator BlockId Payload} (hK : ∀ j ∈ st.ids, (j, st.blk j) ∈ K)
    {id : BlockId} {b : Block Validator BlockId Payload} (hb : (id, b) ∈ K) :
    ∀ j ∈ (acceptOn cfg st id b).ids, (j, (acceptOn cfg st id b).blk j) ∈ K := by
  unfold acceptOn
  split
  · exact known_insert hK hb
  · exact hK

omit [Fintype Validator] in
theorem foldl_in {K : Set (BlockId × Block Validator BlockId Payload)} :
    ∀ (l : List (BlockId × Block Validator BlockId Payload)) {st : Store Validator BlockId Payload},
    (∀ j ∈ st.ids, (j, st.blk j) ∈ K) → (∀ e ∈ l, e ∈ K) →
    let st' := l.foldl (fun s e => acceptOn cfg s e.1 e.2) st
    ∀ j ∈ st'.ids, (j, st'.blk j) ∈ K
  | [], _, hK, _ => hK
  | e :: l, _, hK, hl =>
    foldl_in l (accept_in hK (hl e List.mem_cons_self)) fun x hx => hl x (List.mem_cons_of_mem _ hx)

end Node

end LeanDag
