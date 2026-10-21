import LeanDag.Node.Helpers.Local
/-!
# A node's store grows until its horizon rises

Across a step the horizon never falls, and while it stays put the store
only gains blocks (`Grows`): inserting adds a block, flushing and
building insert, deciding leaves the store alone, and collecting either
raises the horizon or leaves the store alone.
-/

namespace LeanDag

namespace Node

variable {Validator BlockId Payload : Type} [Fintype Validator] [DecidableEq Validator]
variable [LinearOrder BlockId]
variable {cfg : Config Validator BlockId Payload}

/-- **The store grows**: its horizon does not fall, and while it stays
put no block is lost and none changes. -/
def Grows (st st' : Store Validator BlockId Payload) : Prop :=
  st.base ≤ st'.base ∧ (st'.base = st.base → st.ids ⊆ st'.ids ∧ st'.junk = st.junk ∧
    ∀ j ∈ st.ids, st'.map.getD j st'.junk = st.map.getD j st.junk)

omit [Fintype Validator] [DecidableEq Validator] in
theorem Grows.refl (st : Store Validator BlockId Payload) : Grows st st :=
  ⟨le_rfl, fun _ => ⟨subset_rfl, rfl, fun _ _ => rfl⟩⟩

omit [Fintype Validator] [DecidableEq Validator] in
theorem Grows.trans {a b c : Store Validator BlockId Payload} (h₁ : Grows a b) (h₂ : Grows b c) :
    Grows a c :=
  ⟨h₁.1.trans h₂.1, fun h => by
    have hb : b.base = a.base := le_antisymm (h ▸ h₂.1) h₁.1
    obtain ⟨s₁, j₁, m₁⟩ := h₁.2 hb
    obtain ⟨s₂, j₂, m₂⟩ := h₂.2 (h.trans hb.symm)
    exact ⟨s₁.trans s₂, j₂.trans j₁, fun j hj => (m₂ j (s₁ hj)).trans (m₁ j hj)⟩⟩

omit [Fintype Validator] [DecidableEq Validator] in
/-- While the horizon stays put, a grown store reads its old blocks alike. -/
theorem Grows.blk {st st' : Store Validator BlockId Payload} (h : Grows st st')
    (hb : st'.base = st.base) {j : BlockId} (hj : j ∈ st.ids) : st'.blk j = st.blk j := by
  obtain ⟨-, hjk, hm⟩ := h.2 hb
  simp only [Store.blk, lookup, hb, hm j hj]

omit [Fintype Validator] [DecidableEq Validator] in
theorem Grows.insert (st : Store Validator BlockId Payload) {id : BlockId}
    {b : Block Validator BlockId Payload} {hnew hab hrefs hpred} :
    Grows st (st.insert id b hnew hab hrefs hpred) :=
  ⟨le_rfl, fun _ => ⟨Finset.subset_insert _ _, rfl, fun _ hj =>
    treeMap_getD_insert_ne (fun e => hnew (e ▸ hj))⟩⟩

omit [Fintype Validator] in
theorem Grows.accept (st : Store Validator BlockId Payload) (id : BlockId)
    (b : Block Validator BlockId Payload) : Grows st (Node.accept cfg st id b) := by
  unfold Node.accept
  split
  · exact Grows.insert st
  · exact Grows.refl st

omit [Fintype Validator] in
theorem Grows.foldl : ∀ (l : List (BlockId × Block Validator BlockId Payload))
    (st : Store Validator BlockId Payload),
    Grows st (l.foldl (fun s e => Node.accept cfg s e.1 e.2) st)
  | [], st => Grows.refl st
  | e :: l, st => (Grows.accept st e.1 e.2).trans (Grows.foldl l _)

omit [Fintype Validator] in
theorem Grows.flush : ∀ (fuel : ℕ) (st : Store Validator BlockId Payload)
    (pend : List (BlockId × Block Validator BlockId Payload)),
    Grows st (Node.flush cfg fuel st pend).1
  | 0, st, _ => Grows.refl st
  | fuel + 1, st, pend => by
    unfold Node.flush
    dsimp only
    split
    · exact Grows.refl st
    · exact (Grows.foldl _ st).trans (Grows.flush fuel _ _)

omit [Fintype Validator] in
theorem Grows.progress : ∀ (fuel : ℕ) (s : State Validator BlockId Payload),
    Grows s.store (Node.progress cfg fuel s).1.store ∧ (Node.progress cfg fuel s).1.lo = s.lo
  | 0, s => ⟨Grows.refl _, rfl⟩
  | fuel + 1, s => by
    unfold Node.progress
    split
    · rename_i s₁ out h
      obtain ⟨r, id, b, hnew, hab, hrefs, hpred, -, -, -, -, -, hst, -, -, hlo, -⟩ :=
        tryBuild_some h
      have ih := Grows.progress fuel s₁
      have hg : Grows s.store s₁.store := hst ▸ Grows.insert s.store
      exact ⟨hg.trans ih.1, ih.2.trans hlo⟩
    · exact ⟨Grows.refl _, rfl⟩

omit [Fintype Validator] in
/-- **Collecting raises the horizon or leaves the state's store and next
slot alone.** -/
theorem collect_cases (s : State Validator BlockId Payload) :
    s.store.base < (Node.collect cfg s).1.store.base ∨
      ((Node.collect cfg s).1.store = s.store ∧ (Node.collect cfg s).1.lo = s.lo ∧
        (Node.collect cfg s).2 = []) := by
  unfold Node.collect
  split
  · dsimp only
    split
    · rename_i hG
      exact Or.inl hG
    · exact Or.inr ⟨rfl, rfl, rfl⟩
  · exact Or.inr ⟨rfl, rfl, rfl⟩

omit [Fintype Validator] in
theorem decideStep_store (s : State Validator BlockId Payload) :
    (Node.decideStep cfg s).1.store = s.store := by
  unfold Node.decideStep
  dsimp only
  split
  · exact (proposeAt_keeps _).1
  · exact (proposeAt_keeps _).1

omit [Fintype Validator] in
theorem Grows.collect (s : State Validator BlockId Payload) :
    Grows s.store (Node.collect cfg s).1.store := by
  rcases collect_cases (cfg := cfg) s with h | ⟨h, -, -⟩
  · exact ⟨h.le, fun e => absurd e (by omega)⟩
  · rw [h]; exact Grows.refl _

omit [Fintype Validator] in
theorem Grows.advance (s : State Validator BlockId Payload) :
    Grows s.store (Node.advance cfg s).1.store := by
  simp only [Node.advance]
  refine (Grows.progress (cfg := cfg) (s.store.topRound + 2) s).1.trans ?_
  have hc := Grows.collect (cfg := cfg)
    (Node.decideStep cfg (Node.progress cfg (s.store.topRound + 2) s).1).1
  rw [decideStep_store] at hc
  exact hc.trans (Grows.flush _ _ _)

omit [Fintype Validator] in
theorem Grows.quiesce (n : ℕ) (s : State Validator BlockId Payload) :
    Grows s.store (Node.quiesce cfg n s).1.store :=
  (quiesce_rel (P := fun _ => True) (R := fun a _ b => Grows a.store b.store)
    (fun s => Grows.refl _) (fun _ _ _ _ _ h₁ h₂ => h₁.trans h₂)
    (fun s _ => ⟨Grows.advance s, trivial⟩) n s trivial).1

omit [Fintype Validator] in
theorem Grows.settle (s : State Validator BlockId Payload) :
    Grows s.store (Node.settle cfg s).1.store := by
  rcases settle_cases (cfg := cfg) s with h | ⟨s₁, hj, h⟩ <;> rw [h]
  · exact Grows.quiesce _ s
  · obtain ⟨-, -, -, -, -, hst, -⟩ := tryResume_some hj
    exact hst ▸ Grows.quiesce _ s₁

omit [Fintype Validator] in
theorem Grows.settle_of {st : Store Validator BlockId Payload} (s : State Validator BlockId Payload)
    (h : s.store = st) : Grows st (Node.settle cfg s).1.store :=
  h ▸ Grows.settle s

/-- **Across a step the store grows.** -/
theorem Grows.step (s : State Validator BlockId Payload) (i : Input Validator BlockId Payload) :
    Grows s.store (Node.step cfg s i).1.store := by
  cases i with
  | start =>
    simp only [Node.step]
    split
    · split
      · rename_i h₂
        dsimp only
        refine (Grows.insert s.store (hnew := h₂.1) (hab := h₂.2.1)
          (hrefs := fun _ => Finset.empty_subset _)
          (hpred := fun _ j hj => absurd hj (Finset.notMem_empty j))).trans ?_
        exact Grows.settle_of _ rfl
      · exact Grows.refl _
    · exact Grows.refl _
  | deliver id b =>
    simp only [Node.step]
    split
    · dsimp only
      refine (Grows.flush (cfg := cfg) (s.pending.length + 1) s.store
        ((id, b) :: s.pending)).trans ?_
      exact Grows.settle_of _ rfl
    · split <;> exact Grows.refl s.store
  | timer r => exact Grows.settle_of _ rfl
  | restart => exact Grows.settle_of _ rfl
  | baseOffer peer G =>
    dsimp only [Node.step]
    split
    · exact Grows.settle_of _ rfl
    · exact Grows.refl _
  | certOffer peer c ds =>
    dsimp only [Node.step]
    split
    · rw [adopt_eq]; exact Grows.settle_of _ rfl
    · split
      · exact Grows.settle_of _ rfl
      · exact Grows.refl _
  | announced peer c =>
    simp only [Node.step]
    split
    · exact Grows.refl _
    · split
      · exact Grows.settle_of _ rfl
      · split <;> exact Grows.refl _
  | proposal peer k kh =>
    simp only [Node.step]
    split
    · exact Grows.settle_of _ (by rfl)
    · exact Grows.refl _
  | _ => exact Grows.refl _

/-- **Across a run the store grows.** -/
theorem Grows.run : ∀ (is : List (Input Validator BlockId Payload))
    (s : State Validator BlockId Payload), Grows s.store (Node.run cfg s is).1.store
  | [], _ => Grows.refl _
  | i :: is, s => (Grows.step s i).trans (Grows.run is _)

end Node

end LeanDag
