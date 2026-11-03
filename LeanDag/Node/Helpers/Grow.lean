import LeanDag.Node.Helpers.Local
/-!
# A node's disk grows

Deciding keeps the disk's blocks, as accepted, but those it drops
(`decideStep_shrinks`), and keeps the node's own block
(`decideStep_own_mem`). At a node that does not drop, the disk only gains
blocks across a step (`Grows`, `Helpers/Local.lean`): building and taking
blocks in insert, and deciding keeps the disk's blocks, those below the new
floor perhaps without their references (`decideStep_disk`).
-/

namespace LeanDag

namespace Node

variable {Validator BlockId Payload : Type} [Fintype Validator] [DecidableEq Validator]
variable [LinearOrder BlockId]
variable {cfg : Config Validator BlockId Payload}

omit [Fintype Validator] in
theorem Grows.progress : ∀ (fuel : ℕ) (s : State Validator BlockId Payload),
    Grows s.disk (Node.progress cfg fuel s).1.disk ∧ (Node.progress cfg fuel s).1.lo = s.lo
  | 0, s => ⟨Grows.refl _, rfl⟩
  | fuel + 1, s => by
    unfold Node.progress
    split
    · rename_i s₁ out h
      obtain ⟨r, id, b, hnew, hrefs, hpred, -, -, -, -, -, hst, -, -, hlo, -⟩ := tryBuild_some h
      have ih := Grows.progress fuel s₁
      have hg : Grows s.disk s₁.disk := (Grows.insert s.disk).trans (Grows.of_restrips hst)
      exact ⟨hg.trans ih.1, ih.2.trans hlo⟩
    · exact ⟨Grows.refl _, rfl⟩

omit [Fintype Validator] in
/-- **Deciding keeps the disk's blocks but those it drops**, as accepted. -/
theorem decideStep_shrinks (s : State Validator BlockId Payload) :
    Store.Shrinks s.disk (Node.decideStep cfg s).1.disk := by
  unfold Node.decideStep
  dsimp only
  split
  · have h : ∀ t : State Validator BlockId Payload, t.disk = s.disk →
        Store.Shrinks s.disk (drop cfg (release cfg t)).disk := fun t ht =>
      ht ▸ (release_disk (cfg := cfg) t).shrinks.trans (drop_disk _)
    exact h _ rfl
  · exact (Store.Restrips.refl _ 0).shrinks

omit [Fintype Validator] in
theorem decideStep_own (s : State Validator BlockId Payload) :
    (Node.decideStep cfg s).1.own = s.own := by
  unfold Node.decideStep
  dsimp only
  split <;> simp only [drop_own, release_own]

omit [Fintype Validator] in
/-- **Deciding keeps the node's own block.** -/
theorem decideStep_own_mem {s : State Validator BlockId Payload} {j : BlockId}
    (hj : s.own = some j) (hm : j ∈ s.disk.ids) : j ∈ (Node.decideStep cfg s).1.disk.ids := by
  unfold Node.decideStep
  dsimp only
  split
  · refine drop_own_mem _ ?_ ?_
    · rw [release_own]; exact hj
    · rw [release_ids]; exact hm
  · exact hm

omit [Fintype Validator] in
/-- **Deciding without dropping keeps the disk's blocks**, those below the
new floor perhaps without their references. -/
theorem decideStep_disk (s : State Validator BlockId Payload) (hd : cfg.drops = false) :
    Store.Restrips (Node.decideStep cfg s).1.floor s.disk (Node.decideStep cfg s).1.disk := by
  unfold Node.decideStep
  dsimp only
  split
  · rw [drop_of_false _ hd]; exact release_disk _
  · exact Store.Restrips.refl _ _

omit [Fintype Validator] in
theorem Grows.absorb (s : State Validator BlockId Payload)
    (L : List (BlockId × Block Validator BlockId Payload)) :
    Grows s.disk (Node.absorb cfg s L).disk := by
  rw [absorb_disk]; exact Grows.foldl _ _

omit [Fintype Validator] in
theorem Grows.advance (s : State Validator BlockId Payload) (hd : cfg.drops = false) :
    Grows s.disk (Node.advance cfg s).1.disk := by
  rw [advance_disk]
  simp only [Node.pass]
  refine (Grows.progress (cfg := cfg) (s.disk.topRound + 2) s).1.trans ?_
  refine (Grows.of_restrips
    (decideStep_disk (cfg := cfg) (Node.progress cfg (s.disk.topRound + 2) s).1 hd)).trans ?_
  obtain ⟨L, -, hL⟩ := (flushSyncs_eq (cfg := cfg) _ _).1
  rw [hL]
  exact Grows.foldl _ _

omit [Fintype Validator] in
theorem Grows.quiesce (n : ℕ) (s : State Validator BlockId Payload) (hd : cfg.drops = false) :
    Grows s.disk (Node.quiesce cfg n s).1.disk :=
  (quiesce_rel (P := fun _ => True) (R := fun a _ b => Grows a.disk b.disk)
    (fun s => Grows.refl _) (fun _ _ _ _ _ h₁ h₂ => h₁.trans h₂)
    (fun s _ => ⟨Grows.advance s hd, trivial⟩) n s trivial).1

omit [Fintype Validator] in
theorem Grows.settle (s : State Validator BlockId Payload) (hd : cfg.drops = false) :
    Grows s.disk (Node.settle cfg s).1.disk :=
  Grows.quiesce _ s hd

omit [Fintype Validator] in
theorem Grows.settle_of {st : Store Validator BlockId Payload} (s : State Validator BlockId Payload)
    (h : s.disk = st) (hd : cfg.drops = false) : Grows st (Node.settle cfg s).1.disk :=
  h ▸ Grows.settle s hd

omit [Fintype Validator] in
theorem Grows.takeIn (s : State Validator BlockId Payload)
    (t : BlockId × Block Validator BlockId Payload)
    (L : List (BlockId × Block Validator BlockId Payload)) :
    Grows s.disk (Node.takeIn cfg s t L).disk := by
  unfold Node.takeIn
  split
  · exact Grows.absorb s L
  · exact Grows.refl _

/-- **Across a step the disk grows**, when the node does not drop. -/
theorem Grows.step (s : State Validator BlockId Payload) (i : Input Validator BlockId Payload)
    (hd : cfg.drops = false) : Grows s.disk (Node.step cfg s i).1.disk := by
  cases i with
  | start =>
    simp only [Node.step]
    split
    · split
      · rename_i h₂
        dsimp only
        refine (Grows.insert s.disk (id := cfg.idOf cfg.genesis) (b := cfg.genesis) (hnew := h₂.1)
          (hrefs := fun _ hj => absurd hj (Finset.notMem_empty _))
          (hpred := fun j hj => absurd hj (Finset.notMem_empty j))).trans ?_
        exact Grows.settle_of _ rfl hd
      · exact Grows.refl _
    · exact Grows.refl _
  | deliver u id b =>
    simp only [Node.step]
    split
    · split
      · exact (Grows.absorb (cfg := cfg) s [(id, b)]).trans (Grows.settle_of _ rfl hd)
      · split
        · exact Grows.settle_of _ rfl hd
        · exact Grows.refl _
    · exact Grows.refl s.disk
  | stream u L =>
    simp only [Node.step]
    split
    · exact Grows.refl _
    · split
      · exact (Grows.takeIn (cfg := cfg) s _ _).trans (Grows.settle_of _ rfl hd)
      · exact (Grows.takeIn (cfg := cfg) s _ _).trans (Grows.settle_of _ rfl hd)
  | timer r => rw [step_timer_fst]; exact Grows.settle_of _ rfl hd
  | syncRequest peer t fr ids => exact Grows.refl _
  | ask peer r => exact Grows.refl _
  | restart => exact Grows.settle_of { s with recovering := true } rfl hd

/-! ## The blocks as accepted stay closed under references -/

omit [Fintype Validator] in
theorem closed_accept {st : Store Validator BlockId Payload} (h : st.FullClosed) (id : BlockId)
    (b : Block Validator BlockId Payload) : (acceptOn cfg st id b).FullClosed := by
  unfold acceptOn
  split
  · exact h.insert
  · exact h

omit [Fintype Validator] in
theorem closed_foldl : ∀ (l : List (BlockId × Block Validator BlockId Payload))
    (st : Store Validator BlockId Payload), st.FullClosed →
    (l.foldl (fun s e => acceptOn cfg s e.1 e.2) st).FullClosed
  | [], _, h => h
  | e :: l, _, h => closed_foldl l _ (closed_accept h e.1 e.2)

omit [Fintype Validator] in
theorem closed_progress : ∀ (fuel : ℕ) (s : State Validator BlockId Payload),
    s.disk.FullClosed → (Node.progress cfg fuel s).1.disk.FullClosed
  | 0, _, h => h
  | fuel + 1, s, h => by
    unfold Node.progress
    split
    · rename_i s₁ out hb
      obtain ⟨r, id, b, hnew, hrefs, hpred, -, -, -, -, -, hst, -⟩ := tryBuild_some hb
      exact closed_progress fuel s₁ (hst.fullClosed h.insert)
    · exact h

omit [Fintype Validator] in
theorem closed_absorb (s : State Validator BlockId Payload)
    (L : List (BlockId × Block Validator BlockId Payload)) (h : s.disk.FullClosed) :
    (Node.absorb cfg s L).disk.FullClosed := by
  rw [absorb_disk]; exact closed_foldl _ _ h

omit [Fintype Validator] in
theorem closed_advance (s : State Validator BlockId Payload) (hd : cfg.drops = false)
    (h : s.disk.FullClosed) :
    (Node.advance cfg s).1.disk.FullClosed := by
  rw [advance_disk]
  simp only [Node.pass]
  have h₁ := closed_progress (cfg := cfg) (s.disk.topRound + 2) s h
  have h₂ := (decideStep_disk (cfg := cfg)
    (Node.progress cfg (s.disk.topRound + 2) s).1 hd).fullClosed h₁
  obtain ⟨L, -, hL⟩ := (flushSyncs_eq (cfg := cfg) _ _).1
  rw [hL]
  exact closed_foldl _ _ h₂

omit [Fintype Validator] in
theorem closed_settle (s : State Validator BlockId Payload) (hd : cfg.drops = false)
    (h : s.disk.FullClosed) : (Node.settle cfg s).1.disk.FullClosed :=
  quiesce_ind (fun s h => closed_advance s hd h) _ s h

omit [Fintype Validator] in
theorem closed_takeIn (s : State Validator BlockId Payload)
    (t : BlockId × Block Validator BlockId Payload)
    (L : List (BlockId × Block Validator BlockId Payload)) (h : s.disk.FullClosed) :
    (Node.takeIn cfg s t L).disk.FullClosed := by
  unfold Node.takeIn
  split
  · exact closed_absorb s L h
  · exact h

/-- **Across a step the blocks as accepted stay closed under references**,
when the node does not drop. -/
theorem closed_step (s : State Validator BlockId Payload) (i : Input Validator BlockId Payload)
    (hd : cfg.drops = false) (h : s.disk.FullClosed) : (Node.step cfg s i).1.disk.FullClosed := by
  cases i with
  | start =>
    simp only [Node.step]
    split
    · split
      · rename_i h₂
        exact closed_settle _ hd (h.insert (id := cfg.idOf cfg.genesis) (b := cfg.genesis)
          (hnew := h₂.1) (hrefs := fun _ hj => absurd hj (Finset.notMem_empty _))
          (hpred := fun j hj => absurd hj (Finset.notMem_empty j)))
      · exact h
    · exact h
  | deliver u id b =>
    simp only [Node.step]
    split
    · split
      · exact closed_settle _ hd (closed_absorb (cfg := cfg) s [(id, b)] h)
      · split
        · exact closed_settle _ hd h
        · exact h
    · exact h
  | stream u L =>
    simp only [Node.step]
    split
    · exact h
    · split
      · exact closed_settle _ hd (closed_takeIn (cfg := cfg) s _ _ h)
      · exact closed_settle _ hd (closed_takeIn (cfg := cfg) s _ _ h)
  | timer r => rw [step_timer_fst]; exact closed_settle _ hd h
  | syncRequest peer t fr ids => exact h
  | ask peer r => exact h
  | restart => exact closed_settle { s with recovering := true } hd h

end Node

end LeanDag
