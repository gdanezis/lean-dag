import LeanDag.Node.Helpers.Local
/-!
# A node's disk grows

Across a step the disk only gains blocks (`Grows`, `Helpers/Local.lean`):
building and taking blocks in insert, and deciding leaves the disk alone.
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
      have hg : Grows s.disk s₁.disk := hst ▸ Grows.insert s.disk
      exact ⟨hg.trans ih.1, ih.2.trans hlo⟩
    · exact ⟨Grows.refl _, rfl⟩

omit [Fintype Validator] in
theorem decideStep_disk (s : State Validator BlockId Payload) :
    (Node.decideStep cfg s).1.disk = s.disk := by
  unfold Node.decideStep
  dsimp only
  split
  · exact release_disk _
  · rfl

omit [Fintype Validator] in
theorem Grows.absorb (s : State Validator BlockId Payload)
    (L : List (BlockId × Block Validator BlockId Payload)) :
    Grows s.disk (Node.absorb cfg s L).disk := by
  rw [absorb_disk]; exact Grows.foldl _ _

omit [Fintype Validator] in
theorem Grows.advance (s : State Validator BlockId Payload) :
    Grows s.disk (Node.advance cfg s).1.disk := by
  rw [advance_disk]
  simp only [Node.pass]
  refine (Grows.progress (cfg := cfg) (s.disk.topRound + 2) s).1.trans ?_
  rw [← decideStep_disk (cfg := cfg) (Node.progress cfg (s.disk.topRound + 2) s).1]
  obtain ⟨L, -, hL⟩ := (flushSyncs_eq (cfg := cfg) _ _).1
  rw [hL]
  exact Grows.foldl _ _

omit [Fintype Validator] in
theorem Grows.quiesce (n : ℕ) (s : State Validator BlockId Payload) :
    Grows s.disk (Node.quiesce cfg n s).1.disk :=
  (quiesce_rel (P := fun _ => True) (R := fun a _ b => Grows a.disk b.disk)
    (fun s => Grows.refl _) (fun _ _ _ _ _ h₁ h₂ => h₁.trans h₂)
    (fun s _ => ⟨Grows.advance s, trivial⟩) n s trivial).1

omit [Fintype Validator] in
theorem Grows.settle (s : State Validator BlockId Payload) :
    Grows s.disk (Node.settle cfg s).1.disk :=
  Grows.quiesce _ s

omit [Fintype Validator] in
theorem Grows.settle_of {st : Store Validator BlockId Payload} (s : State Validator BlockId Payload)
    (h : s.disk = st) : Grows st (Node.settle cfg s).1.disk :=
  h ▸ Grows.settle s

omit [Fintype Validator] in
theorem Grows.takeIn (s : State Validator BlockId Payload)
    (t : BlockId × Block Validator BlockId Payload)
    (L : List (BlockId × Block Validator BlockId Payload)) :
    Grows s.disk (Node.takeIn cfg s t L).disk := by
  unfold Node.takeIn
  split
  · exact Grows.absorb s L
  · exact Grows.refl _

/-- **Across a step the disk grows.** -/
theorem Grows.step (s : State Validator BlockId Payload) (i : Input Validator BlockId Payload) :
    Grows s.disk (Node.step cfg s i).1.disk := by
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
        exact Grows.settle_of _ rfl
      · exact Grows.refl _
    · exact Grows.refl _
  | deliver u id b =>
    simp only [Node.step]
    split
    · split
      · exact (Grows.absorb (cfg := cfg) s [(id, b)]).trans (Grows.settle_of _ rfl)
      · split
        · exact Grows.settle_of _ rfl
        · exact Grows.refl _
    · exact Grows.refl s.disk
  | stream u L =>
    simp only [Node.step]
    split
    · exact Grows.refl _
    · split
      · exact (Grows.takeIn (cfg := cfg) s _ _).trans (Grows.settle_of _ rfl)
      · exact (Grows.takeIn (cfg := cfg) s _ _).trans (Grows.settle_of _ rfl)
  | timer r => rw [step_timer_fst]; exact Grows.settle_of _ rfl
  | syncRequest peer t fr ids => exact Grows.refl _
  | ask peer r => exact Grows.refl _
  | restart => exact Grows.settle_of { s with recovering := true } rfl

end Node

end LeanDag
