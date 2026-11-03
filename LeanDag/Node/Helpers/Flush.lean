import LeanDag.Node.Helpers.Grow
/-!
# Accepting blocks on a store

On stores reading as a block map `g`, accepting blocks of `g` keeps the
store reading as `g` (`ReadsAs.foldl`). Accepting known blocks keeps the
store known (`foldl_in`).
-/

namespace LeanDag

namespace Node

variable {Validator BlockId Payload : Type} [Fintype Validator] [DecidableEq Validator]
variable [LinearOrder BlockId]
variable {cfg : Config Validator BlockId Payload}

variable (g : BlockId → Block Validator BlockId Payload)

/-- **A store reading as `g`**: its blocks as accepted are those of `g`. -/
def ReadsAs (st : Store Validator BlockId Payload) : Prop :=
  ∀ j ∈ st.ids, st.full j = g j

variable {g}

omit [Fintype Validator] in
theorem ReadsAs.accept {F : ℕ} {st : Store Validator BlockId Payload} (h : ReadsAs g st)
    {id : BlockId} {b : Block Validator BlockId Payload} (hb : g id = b) :
    ReadsAs g (acceptOn cfg F st id b) := by
  unfold acceptOn
  split
  · rename_i hc
    intro j hj
    rw [Store.insert_ids] at hj
    rw [Store.full_insert]
    by_cases hj' : j = id
    · subst hj'
      rw [if_pos rfl]
      exact hb.symm
    · rw [if_neg hj']
      exact h j ((Finset.mem_insert.mp hj).resolve_left hj')
  · split
    · intro j hj
      rw [Store.base_ids] at hj
      rw [Store.full_base]
      by_cases hj' : j = id
      · subst hj'
        rw [if_pos rfl]
        exact hb.symm
      · rw [if_neg hj']
        exact h j ((Finset.mem_insert.mp hj).resolve_left hj')
    · exact h

omit [Fintype Validator] in
theorem ReadsAs.foldl {F : ℕ} : ∀ (l : List (BlockId × Block Validator BlockId Payload))
    {st : Store Validator BlockId Payload}, ReadsAs g st → (∀ e ∈ l, g e.1 = e.2) →
    ReadsAs g (l.foldl (fun s e => acceptOn cfg F s e.1 e.2) st)
  | [], _, h, _ => h
  | e :: l, _, h, hl =>
    ReadsAs.foldl l (h.accept (hl e List.mem_cons_self))
      fun x hx => hl x (List.mem_cons_of_mem _ hx)

omit [Fintype Validator] in
theorem ready_mono {F : ℕ} {st st' : Store Validator BlockId Payload} (hg : Grows st st')
    {e : BlockId × Block Validator BlockId Payload}
    (h : readyOn cfg F st e = true) : readyOn cfg F st' e = true := by
  simp only [readyOn, Store.Checks, Bool.or_eq_true, decide_eq_true_eq, Bool.and_eq_true] at h ⊢
  rcases h with ⟨h₁, h₂, h₃⟩ | h
  swap
  · exact Or.inr h
  refine Or.inl ⟨h₁.trans hg.1, fun j hj => by rw [(hg.fields (h₁ hj)).1]; exact h₂ j hj,
    rowValid_congr (fun j hj => ?_) h₃⟩
  by_cases hje : j = e.1
  · subst hje; simp
  · rw [Function.update_of_ne hje, Function.update_of_ne hje]
    have := hg.fields (h₁ hj)
    exact ⟨this.1.symm, this.2.1.symm, this.2.2.symm⟩

omit [Fintype Validator] in
theorem accept_in {K : Set (BlockId × Block Validator BlockId Payload)} {F : ℕ}
    {st : Store Validator BlockId Payload} (hK : ∀ j ∈ st.ids, (j, st.full j) ∈ K)
    {id : BlockId} {b : Block Validator BlockId Payload} (hb : (id, b) ∈ K) :
    ∀ j ∈ (acceptOn cfg F st id b).ids, (j, (acceptOn cfg F st id b).full j) ∈ K := by
  unfold acceptOn
  split
  · exact known_insert hK hb
  · split
    · intro j hj
      rw [Store.base_ids] at hj
      rw [Store.full_base]
      split
      · rename_i hje; subst hje; exact hb
      · rename_i hje; exact hK j ((Finset.mem_insert.mp hj).resolve_left hje)
    · exact hK

omit [Fintype Validator] in
theorem foldl_in {K : Set (BlockId × Block Validator BlockId Payload)} {F : ℕ} :
    ∀ (l : List (BlockId × Block Validator BlockId Payload)) {st : Store Validator BlockId Payload},
    (∀ j ∈ st.ids, (j, st.full j) ∈ K) → (∀ e ∈ l, e ∈ K) →
    let st' := l.foldl (fun s e => acceptOn cfg F s e.1 e.2) st
    ∀ j ∈ st'.ids, (j, st'.full j) ∈ K
  | [], _, hK, _ => hK
  | e :: l, _, hK, hl =>
    foldl_in l (accept_in hK (hl e List.mem_cons_self)) fun x hx => hl x (List.mem_cons_of_mem _ hx)

end Node

end LeanDag
