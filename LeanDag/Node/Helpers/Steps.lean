import LeanDag.Node.Helpers.Flush
/-!
# What one step does to the pending blocks and the disk

On disks reading as a block map `g`, a step keeps every block that fits
pending or on disk (`step_keeps`). A block becomes pending only on account
of a delivery the node acts on (`Admits`, `step_sub`). Every block of the
node's own that a step outputs is on the disk after it
(`step_persist`), and after every step no pending block is ready
(`noReady_step`).
-/

namespace LeanDag

namespace Node

variable {Validator BlockId Payload : Type} [Fintype Validator] [DecidableEq Validator]
variable [LinearOrder BlockId]
variable {cfg : Config Validator BlockId Payload} {g : BlockId → Block Validator BlockId Payload}

omit [Fintype Validator] in
/-- A build keeps the pending blocks. -/
theorem tryBuild_pending {s s' : State Validator BlockId Payload}
    {out : List (Output Validator BlockId Payload)} (h : tryBuild cfg s = some (s', out)) :
    s'.pending = s.pending := by
  obtain ⟨_, _, _, -, h, -⟩ := tryBuild_cases h
  unfold buildAbove at h
  dsimp only at h
  split at h
  · split at h
    · rw [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, -⟩ := h
      exact release_pending _
    · exact absurd h (by simp)
  · exact absurd h (by simp)

omit [Fintype Validator] in
/-- Building keeps the pending blocks. -/
theorem progress_pending : ∀ (fuel : ℕ) (s : State Validator BlockId Payload),
    (Node.progress cfg fuel s).1.pending = s.pending
  | 0, _ => rfl
  | fuel + 1, s => by
    unfold Node.progress
    split
    · rename_i s₁ out h
      exact (progress_pending fuel s₁).trans (tryBuild_pending h)
    · rfl

omit [Fintype Validator] in
/-- Deciding keeps the pending blocks. -/
theorem decideStep_pending (s : State Validator BlockId Payload) :
    (Node.decideStep cfg s).1.pending = s.pending := by
  unfold Node.decideStep
  dsimp only
  split <;> simp only [release_disk, release_pending, release_top, release_own,
    release_fired, release_lo, release_decided, release_armed]

omit [Fintype Validator] [DecidableEq Validator] in
/-- A store that grows into one reading as `g` reads as `g`. -/
theorem ReadsAs.of_grows {st st' : Store Validator BlockId Payload} (h : ReadsAs g st')
    (hg : Grows st st') : ReadsAs g st :=
  fun j hj => by rw [← hg.blk hj]; exact h j (hg.1 hj)

omit [Fintype Validator] in
/-- **A block that fits stays pending or on disk across a pass.** -/
theorem advance_keeps {s : State Validator BlockId Payload}
    (hR : ReadsAs g (Node.advance cfg s).1.disk)
    (hp : ∀ e ∈ s.pending, g e.1 = e.2) {y : BlockId × Block Validator BlockId Payload}
    (hf : Fits cfg g y) (hy : y ∈ s.pending ∨ y.1 ∈ s.disk.ids) :
    y ∈ (Node.advance cfg s).1.pending ∨ y.1 ∈ (Node.advance cfg s).1.disk.ids := by
  have hg₁ := (Grows.progress (cfg := cfg) (s.disk.topRound + 2) s).1
  have hp₁ := progress_pending (cfg := cfg) (s.disk.topRound + 2) s
  rw [advance_disk] at hR
  rw [advance_pending, advance_disk]
  simp only [Node.pass, flush_disk, flush_pending] at hR ⊢
  generalize Node.progress cfg (s.disk.topRound + 2) s = r at hg₁ hp₁ hR ⊢
  have hd := decideStep_disk (cfg := cfg) r.1
  have hdp := decideStep_pending (cfg := cfg) r.1
  generalize Node.decideStep cfg r.1 = d at hd hdp hR ⊢
  have hgf := Grows.flush (cfg := cfg) (d.1.pending.length + 1) d.1.disk d.1.pending
  have hRd : ReadsAs g d.1.disk := hR.of_grows hgf
  have hpd : ∀ e ∈ d.1.pending, g e.1 = e.2 := by rw [hdp, hp₁]; exact hp
  have hy' : y ∈ d.1.pending ∨ y.1 ∈ d.1.disk.ids := by
    rw [hdp, hp₁, hd]
    rcases hy with hy | hy
    · exact Or.inl hy
    · exact Or.inr (hg₁.1 hy)
  rcases hy' with hy' | hy'
  · exact flush_keeps _ hRd hpd hf hy'
  · exact Or.inr (hgf.1 hy')

omit [Fintype Validator] in
/-- A flush leaves only blocks that were pending. -/
theorem flush_pending_sub : ∀ (fuel : ℕ) (st : Store Validator BlockId Payload)
    (pend : List (BlockId × Block Validator BlockId Payload)),
    ∀ e ∈ (flushOn cfg fuel st pend).2, e ∈ pend
  | 0, _, _, _, he => he
  | fuel + 1, st, pend, e, he => by
    unfold flushOn at he
    dsimp only at he
    split at he
    · exact he
    · rw [List.partition_eq_filter_filter] at he
      exact (List.mem_filter.mp (flush_pending_sub fuel _ _ e he)).1

omit [Fintype Validator] in
/-- A pass adds no pending block. -/
theorem advance_sub (s : State Validator BlockId Payload) :
    ∀ e ∈ (Node.advance cfg s).1.pending, e ∈ s.pending := by
  have hp := progress_pending (cfg := cfg) (s.disk.topRound + 2) s
  have hd := decideStep_pending (cfg := cfg) (Node.progress cfg (s.disk.topRound + 2) s).1
  intro e he
  rw [advance_pending] at he
  simp only [Node.pass, flush_pending] at he
  have := flush_pending_sub (cfg := cfg) _ _ _ e he
  rwa [hd, hp] at this

omit [Fintype Validator] in
/-- **A block that fits stays pending or on disk across the passes.** -/
theorem quiesce_keeps : ∀ (n : ℕ) {s : State Validator BlockId Payload},
    ReadsAs g (quiesce cfg n s).1.disk →
    (∀ e ∈ s.pending, g e.1 = e.2) → ∀ {y : BlockId × Block Validator BlockId Payload},
    Fits cfg g y → (y ∈ s.pending ∨ y.1 ∈ s.disk.ids) →
    y ∈ (quiesce cfg n s).1.pending ∨ y.1 ∈ (quiesce cfg n s).1.disk.ids
  | 0, s, _, _, _, _, hy => hy
  | n + 1, s, hR, hp, y, hf, hy => by
    rcases quiesce_succ_cases (cfg := cfg) n s with he | he <;> rw [he] at hR ⊢
    · exact advance_keeps hR hp hf hy
    · set a := (Node.advance cfg s).1
      have hga := Grows.quiesce (cfg := cfg) n a
      have hRa : ReadsAs g a.disk := hR.of_grows hga
      exact quiesce_keeps n hR
        (fun e he => hp e (advance_sub (cfg := cfg) s e he)) hf
        (advance_keeps hRa hp hf hy)

omit [Fintype Validator] in
/-- **A block that fits stays pending or on disk across a settle.** -/
theorem settle_keeps {s : State Validator BlockId Payload}
    (hR : ReadsAs g (Node.settle cfg s).1.disk)
    (hp : ∀ e ∈ s.pending, g e.1 = e.2) {y : BlockId × Block Validator BlockId Payload}
    (hf : Fits cfg g y) (hy : y ∈ s.pending ∨ y.1 ∈ s.disk.ids) :
    y ∈ (Node.settle cfg s).1.pending ∨ y.1 ∈ (Node.settle cfg s).1.disk.ids :=
  quiesce_keeps _ hR hp hf hy

omit [Fintype Validator] in
/-- The passes add no pending block. -/
theorem quiesce_sub (n : ℕ) (s : State Validator BlockId Payload) :
    ∀ e ∈ (quiesce cfg n s).1.pending, e ∈ s.pending :=
  (quiesce_rel (P := fun _ => True)
    (R := fun a _ b => ∀ e ∈ b.pending, e ∈ a.pending)
    (fun _ _ h => h)
    (fun _ _ _ _ _ h₁ h₂ e he => h₁ e (h₂ e he))
    (fun s _ => ⟨advance_sub s, trivial⟩) n s trivial).1

omit [Fintype Validator] in
/-- **A settle adds no pending block.** -/
theorem settle_sub (s : State Validator BlockId Payload) :
    ∀ e ∈ (Node.settle cfg s).1.pending, e ∈ s.pending :=
  quiesce_sub _ s

variable (cfg) in
/-- **A delivery the node acts on**: identified by its hash, not the
node's own, and new. -/
def Admits (s : State Validator BlockId Payload) (id : BlockId)
    (b : Block Validator BlockId Payload) : Prop :=
  id = cfg.idOf b ∧ b.creator ≠ cfg.me ∧ id ∉ s.disk.ids ∧ id ∉ s.pending.map Prod.fst

/-- The state after a delivery the node acts on is flushed: the pending
blocks, the delivered one among them, after a flush. -/
def afterFlush (s : State Validator BlockId Payload) (id : BlockId)
    (b : Block Validator BlockId Payload) : State Validator BlockId Payload :=
  flush cfg (s.pending.length + 1) { s with pending := (id, b) :: s.pending }

section AfterFlush

variable (s : State Validator BlockId Payload) (id : BlockId) (b : Block Validator BlockId Payload)

omit [Fintype Validator] in
@[simp] theorem afterFlush_disk : (afterFlush (cfg := cfg) s id b).disk =
    (flushOn cfg (s.pending.length + 1) s.disk ((id, b) :: s.pending)).1 :=
  flush_disk _ _

omit [Fintype Validator] in
@[simp] theorem afterFlush_pending : (afterFlush (cfg := cfg) s id b).pending =
    (flushOn cfg (s.pending.length + 1) s.disk ((id, b) :: s.pending)).2 :=
  flush_pending _ _

omit [Fintype Validator] in
@[simp] theorem afterFlush_floor : (afterFlush (cfg := cfg) s id b).floor = s.floor :=
  flush_floor _ _

omit [Fintype Validator] in
@[simp] theorem afterFlush_top : (afterFlush (cfg := cfg) s id b).top = s.top := flush_top _ _

omit [Fintype Validator] in
@[simp] theorem afterFlush_own : (afterFlush (cfg := cfg) s id b).own = s.own := flush_own _ _

omit [Fintype Validator] in
@[simp] theorem afterFlush_fired : (afterFlush (cfg := cfg) s id b).fired = s.fired :=
  flush_fired _ _

omit [Fintype Validator] in
@[simp] theorem afterFlush_lo : (afterFlush (cfg := cfg) s id b).lo = s.lo := flush_lo _ _

end AfterFlush

/-- **A delivery the node acts on**: it flushes, asks for the missing
blocks, and settles. -/
theorem step_deliver {s : State Validator BlockId Payload} {id : BlockId}
    {b : Block Validator BlockId Payload} (h : Admits cfg s id b) :
    let s₁ := afterFlush (cfg := cfg) s id b
    let miss := missing s₁ b
    Node.step cfg s (.deliver id b) =
      ((Node.settle cfg s₁).1,
        (if miss.isEmpty then [] else [.fetch b.creator (s.top.getD 0) miss]) ++ (Node.settle cfg s₁).2) := by
  have h' : id = cfg.idOf b ∧ b.creator ≠ cfg.me ∧ id ∉ s.disk.ids ∧
      id ∉ s.pending.map Prod.fst := h
  simp only [Node.step]
  rw [if_pos h']
  rfl

/-- **A delivery the node does not act on changes nothing.** -/
theorem step_deliver_not {s : State Validator BlockId Payload} {id : BlockId}
    {b : Block Validator BlockId Payload} (h : ¬ Admits cfg s id b) :
    Node.step cfg s (.deliver id b) = (s, []) := by
  have h' : ¬ (id = cfg.idOf b ∧ b.creator ≠ cfg.me ∧ id ∉ s.disk.ids ∧
      id ∉ s.pending.map Prod.fst) := h
  simp only [Node.step]
  rw [if_neg h']

/-- **Across a step a fitting block stays pending or on disk**, on disks
reading as `g`. -/
theorem step_keeps {s : State Validator BlockId Payload} {inp : Input Validator BlockId Payload}
    (hR : ReadsAs g (Node.step cfg s inp).1.disk)
    (hp : ∀ e ∈ s.pending, g e.1 = e.2)
    (hd : ∀ id b, inp = .deliver id b → id = cfg.idOf b → g id = b)
    {y : BlockId × Block Validator BlockId Payload} (hf : Fits cfg g y)
    (hy : y ∈ s.pending ∨ y.1 ∈ s.disk.ids) :
    y ∈ (Node.step cfg s inp).1.pending ∨ y.1 ∈ (Node.step cfg s inp).1.disk.ids := by
  have hRs : ReadsAs g s.disk := hR.of_grows (Grows.step (cfg := cfg) s inp)
  -- a step that settles `s₀`, whose pending blocks read as `g` and which keeps `y`
  have hset : ∀ s₀ : State Validator BlockId Payload,
      Node.step cfg s inp = ((Node.settle cfg s₀).1, (Node.step cfg s inp).2) →
      (∀ e ∈ s₀.pending, g e.1 = e.2) → (y ∈ s₀.pending ∨ y.1 ∈ s₀.disk.ids) →
      y ∈ (Node.step cfg s inp).1.pending ∨ y.1 ∈ (Node.step cfg s inp).1.disk.ids := by
    intro s₀ he hp₀ hy₀
    rw [he] at hR ⊢
    exact settle_keeps hR hp₀ hf hy₀
  cases inp with
  | start =>
    by_cases h₁ : s.top = none ∧ cfg.Admissible
    · by_cases h₂ : cfg.idOf cfg.genesis ∉ s.disk.ids ∧
          rowValid cfg.q (Function.update s.disk.blk (cfg.idOf cfg.genesis) cfg.genesis)
            cfg.genesis
      · let st := s.disk.insert (cfg.idOf cfg.genesis) cfg.genesis h₂.1
          (fun _ hj => absurd hj (Finset.notMem_empty _))
          (fun j hj => absurd hj (Finset.notMem_empty j))
        let s₀ := { keep s (cfg.idOf cfg.genesis) cfg.genesis h₂.1
            (fun _ hj => absurd hj (Finset.notMem_empty _))
            (fun j hj => absurd hj (Finset.notMem_empty j)) with
            top := some 0, own := some (cfg.idOf cfg.genesis), recovering := false }
        refine hset s₀ ?_ hp ?_
        · simp only [Node.step, dif_pos h₂, if_pos h₁]
          try rfl
        · rcases hy with hy | hy
          · exact Or.inl hy
          · exact Or.inr (show y.1 ∈ st.ids from Store.mem_insert_of_mem hy)
      · simp only [Node.step, dif_neg h₂, if_pos h₁]; exact hy
    · simp only [Node.step, if_neg h₁]; exact hy
  | deliver id b =>
    by_cases hc : Admits cfg s id b
    · have hstep := step_deliver (cfg := cfg) hc
      let s₁ := afterFlush (cfg := cfg) s id b
      have hpb : ∀ e ∈ (id, b) :: s.pending, g e.1 = e.2 := by
        intro e he
        rcases List.mem_cons.mp he with rfl | he
        · exact hd _ _ rfl hc.1
        · exact hp e he
      have hfl := ReadsAs.flush (cfg := cfg) (s.pending.length + 1) hRs hpb
      refine hset s₁ (by rw [hstep]) (by rw [afterFlush_pending]; exact hfl.2) ?_
      rw [afterFlush_pending, afterFlush_disk]
      rcases hy with hy | hy
      · exact flush_keeps _ hRs hpb hf (List.mem_cons_of_mem _ hy)
      · exact Or.inr ((Grows.flush (cfg := cfg) (s.pending.length + 1) s.disk
          ((id, b) :: s.pending)).1 hy)
    · rw [step_deliver_not hc]; exact hy
  | timer r =>
    exact hset { s with fired := fire s r, recovering := false } (step_timer_eq s r) hp hy
  | fetchRequest peer r ids => exact hy
  | restart => exact hset { s with recovering := true } rfl hp hy

/-- **A block becomes pending only by being delivered**, and only when the
node acts on the delivery. -/
theorem step_sub (s : State Validator BlockId Payload) (inp : Input Validator BlockId Payload) :
    ∀ e ∈ (Node.step cfg s inp).1.pending, e ∈ s.pending ∨
      (inp = .deliver e.1 e.2 ∧ Admits cfg s e.1 e.2) := by
  cases inp with
  | start =>
    by_cases h₁ : s.top = none ∧ cfg.Admissible
    · by_cases h₂ : cfg.idOf cfg.genesis ∉ s.disk.ids ∧
          rowValid cfg.q (Function.update s.disk.blk (cfg.idOf cfg.genesis) cfg.genesis)
            cfg.genesis
      · simp only [Node.step, dif_pos h₂, if_pos h₁]
        let st := s.disk.insert (cfg.idOf cfg.genesis) cfg.genesis h₂.1
          (fun _ hj => absurd hj (Finset.notMem_empty _))
          (fun j hj => absurd hj (Finset.notMem_empty j))
        let s₀ : State Validator BlockId Payload :=
          { keep s (cfg.idOf cfg.genesis) cfg.genesis h₂.1
              (fun _ hj => absurd hj (Finset.notMem_empty _))
              (fun j hj => absurd hj (Finset.notMem_empty j)) with
              top := some 0, own := some (cfg.idOf cfg.genesis), recovering := false }
        exact fun e he => Or.inl (settle_sub (cfg := cfg) s₀ e he)
      · simp only [Node.step, dif_neg h₂, if_pos h₁]
        exact fun e he => Or.inl he
    · simp only [Node.step, if_neg h₁]
      exact fun e he => Or.inl he
  | deliver id b =>
    by_cases hc : Admits cfg s id b
    · rw [step_deliver hc]
      dsimp only
      intro e he
      have hm := flush_pending_sub (cfg := cfg) _ _ _ e (by
        rw [← afterFlush_pending]
        exact settle_sub (cfg := cfg) (afterFlush (cfg := cfg) s id b) e he)
      rcases List.mem_cons.mp hm with rfl | hm
      · exact Or.inr ⟨rfl, hc⟩
      · exact Or.inl hm
    · rw [step_deliver_not hc]
      exact fun e he => Or.inl he
  | timer r =>
    rw [step_timer_fst]
    exact fun e he => Or.inl
      (settle_sub (cfg := cfg) { s with fired := fire s r, recovering := false } e he)
  | fetchRequest peer r ids => exact fun e he => Or.inl he
  | restart => exact fun e he => Or.inl (settle_sub (cfg := cfg) { s with recovering := true } e he)

omit [Fintype Validator] in
/-- **What building persists is on the disk after it.** -/
theorem progress_persist : ∀ (fuel : ℕ) (s : State Validator BlockId Payload),
    ∀ e ∈ persists (Node.progress cfg fuel s).2, e.1 ∈ (Node.progress cfg fuel s).1.disk.ids ∧
      (Node.progress cfg fuel s).1.disk.blk e.1 = e.2
  | 0, _, e, he => by simp [Node.progress, persists] at he
  | fuel + 1, s, e, he => by
    rcases hb : tryBuild cfg s with _ | ⟨s₁, out⟩
    · simp [Node.progress, hb, persists] at he
    · simp only [Node.progress, hb] at he ⊢
      obtain ⟨r, id, b, hnew, hrefs, hpred, -, -, -, -, -, hst, -, -, -, hout⟩ :=
        tryBuild_some hb
      have hg := (Grows.progress (cfg := cfg) fuel s₁).1
      rw [hout] at he
      simp only [built, List.flatMap_cons, List.flatMap_nil, List.append_nil, List.cons_append,
        List.nil_append, persists, List.filterMap_cons] at he
      rcases List.mem_cons.mp he with rfl | he
      · have hin : id ∈ s₁.disk.ids := by rw [hst]; exact Store.mem_insert_self
        refine ⟨hg.1 hin, ?_⟩
        rw [hg.blk hin, hst]
        simp only [Store.blk, Store.insert, Std.TreeMap.getD_insert_self]
      · exact progress_persist fuel s₁ e he

omit [Fintype Validator] [DecidableEq Validator] [LinearOrder BlockId] in
/-- Commits persist no block. -/
theorem persists_commits (ds : List (ℕ × Option BlockId)) :
    persists (ds.map fun e => (Output.commit e.1 e.2 : Output Validator BlockId Payload)) =
      [] := by
  induction ds with
  | nil => rfl
  | cons e ds ih => simp [persists]

omit [Fintype Validator] in
/-- Deciding persists no block. -/
theorem decideStep_persist (s : State Validator BlockId Payload) :
    persists (Node.decideStep cfg s).2 = [] := by
  unfold Node.decideStep
  dsimp only
  split
  · exact persists_commits _
  · rfl

omit [Fintype Validator] in
/-- **What a pass persists is on the disk after it.** -/
theorem advance_persist (s : State Validator BlockId Payload) :
    ∀ e ∈ persists (Node.advance cfg s).2, e.1 ∈ (Node.advance cfg s).1.disk.ids ∧
      (Node.advance cfg s).1.disk.blk e.1 = e.2 := by
  intro e he
  have hp := progress_persist (cfg := cfg) (s.disk.topRound + 2) s
  rw [advance_disk]
  simp only [Node.advance, Node.pass, flush_disk] at he ⊢
  generalize Node.progress cfg (s.disk.topRound + 2) s = r at hp he ⊢
  rw [persists_append, persists_append, decideStep_persist, persists_arm, List.append_nil,
    List.append_nil] at he
  obtain ⟨hin, hval⟩ := hp e he
  have hd := decideStep_disk (cfg := cfg) r.1
  generalize Node.decideStep cfg r.1 = d at hd ⊢
  rw [← hd] at hin hval
  have hgf := Grows.flush (cfg := cfg) (d.1.pending.length + 1) d.1.disk d.1.pending
  exact ⟨hgf.1 hin, by rw [hgf.blk hin]; exact hval⟩

omit [Fintype Validator] in
/-- **What the passes persist is on the disk after them.** -/
theorem quiesce_persist : ∀ (n : ℕ) (s : State Validator BlockId Payload),
    ∀ e ∈ persists (quiesce cfg n s).2, e.1 ∈ (quiesce cfg n s).1.disk.ids ∧
      (quiesce cfg n s).1.disk.blk e.1 = e.2
  | 0, s => by intro e he; simp [Node.quiesce, persists] at he
  | n + 1, s => by
    rcases quiesce_succ_cases (cfg := cfg) n s with he | he <;> rw [he]
    · exact advance_persist s
    · have hga := Grows.quiesce (cfg := cfg) n (Node.advance cfg s).1
      intro e he
      rw [persists_append] at he
      rcases List.mem_append.mp he with he | he
      · obtain ⟨hin, hval⟩ := advance_persist s e he
        exact ⟨hga.1 hin, by rw [hga.blk hin]; exact hval⟩
      · exact quiesce_persist n _ e he

omit [Fintype Validator] in
/-- **What a settle persists is on the disk after it.** -/
theorem settle_persist (s : State Validator BlockId Payload) :
    ∀ e ∈ persists (Node.settle cfg s).2, e.1 ∈ (Node.settle cfg s).1.disk.ids ∧
      (Node.settle cfg s).1.disk.blk e.1 = e.2 :=
  quiesce_persist _ s

omit [Fintype Validator] in
/-- What a settle persists, after outputs persisting at most one block on
disk, is on the disk after it. -/
theorem settle_persist_of {s₀ : State Validator BlockId Payload}
    {pre : List (Output Validator BlockId Payload)}
    (hpre : persists pre = [] ∨ ∃ e₀, persists pre = [e₀] ∧ e₀.1 ∈ s₀.disk.ids ∧
      s₀.disk.blk e₀.1 = e₀.2) :
    ∀ e ∈ persists (pre ++ (Node.settle cfg s₀).2), e.1 ∈ (Node.settle cfg s₀).1.disk.ids ∧
      (Node.settle cfg s₀).1.disk.blk e.1 = e.2 := by
  intro e he
  rw [persists_append] at he
  rcases List.mem_append.mp he with he | he
  · rcases hpre with hpre | ⟨e₀, hpre, hin, hval⟩
    · rw [hpre] at he; exact absurd he (List.not_mem_nil)
    · rw [hpre, List.mem_singleton] at he
      subst he
      have hg := Grows.settle (cfg := cfg) s₀
      exact ⟨hg.1 hin, by rw [hg.blk hin]; exact hval⟩
  · exact settle_persist s₀ e he

/-- **What a step persists is on the disk after it.** -/
theorem step_persist {s : State Validator BlockId Payload} {inp : Input Validator BlockId Payload} :
    ∀ e ∈ persists (Node.step cfg s inp).2, e.1 ∈ (Node.step cfg s inp).1.disk.ids ∧
      (Node.step cfg s inp).1.disk.blk e.1 = e.2 := by
  cases inp with
  | start =>
    by_cases h₁ : s.top = none ∧ cfg.Admissible
    · by_cases h₂ : cfg.idOf cfg.genesis ∉ s.disk.ids ∧
          rowValid cfg.q (Function.update s.disk.blk (cfg.idOf cfg.genesis) cfg.genesis)
            cfg.genesis
      · let st := s.disk.insert (cfg.idOf cfg.genesis) cfg.genesis h₂.1
          (fun _ hj => absurd hj (Finset.notMem_empty _))
          (fun j hj => absurd hj (Finset.notMem_empty j))
        let s₀ : State Validator BlockId Payload :=
          { keep s (cfg.idOf cfg.genesis) cfg.genesis h₂.1
              (fun _ hj => absurd hj (Finset.notMem_empty _))
              (fun j hj => absurd hj (Finset.notMem_empty j)) with
              top := some 0, own := some (cfg.idOf cfg.genesis), recovering := false }
        have he : Node.step cfg s .start =
            ((Node.settle cfg s₀).1, built cfg [(cfg.idOf cfg.genesis, cfg.genesis)] ++
              (Node.settle cfg s₀).2) := by
          simp only [Node.step, dif_pos h₂, if_pos h₁]; rfl
        rw [he]
        exact settle_persist_of (Or.inr ⟨(cfg.idOf cfg.genesis, cfg.genesis), by
          simp [built, persists], (by simp [s₀, keep, Store.insert_ids]), by
          simp [s₀, keep, Store.insert_blk]⟩)
      · simp only [Node.step, dif_neg h₂, if_pos h₁]; simp [persists]
    · simp only [Node.step, if_neg h₁]; simp [persists]
  | deliver id b =>
    by_cases hc : Admits cfg s id b
    · rw [step_deliver hc]
      dsimp only
      refine settle_persist_of (Or.inl ?_)
      split <;> rfl
    · rw [step_deliver_not hc]; simp [persists]
  | timer r =>
    intro e he
    rw [step_timer_fst]
    rcases step_timer_snd (cfg := cfg) s r with h | h <;> rw [h] at he
    · exact settle_persist { s with fired := fire s r, recovering := false } e he
    · rw [persists_append, persists_resend, List.append_nil] at he
      exact settle_persist { s with fired := fire s r, recovering := false } e he
  | fetchRequest peer r ids =>
    intro e he
    change e ∈ persists (answer cfg s peer r ids) at he
    unfold answer persists at he
    rw [List.filterMap_map] at he
    simp at he
  | restart =>
    intro e he
    change e ∈ persists (Node.resend cfg s ++ Node.rearm cfg s ++
      (Node.settle cfg { s with recovering := true }).2) at he
    rw [persists_append, persists_append, persists_resend, persists_rearm, List.nil_append,
      List.nil_append] at he
    exact settle_persist { s with recovering := true } e he

variable (cfg) in
/-- No pending block is ready. -/
def NoReady (s : State Validator BlockId Payload) : Prop :=
  ∀ e ∈ s.pending, readyOn cfg s.disk e = false

omit [Fintype Validator] in
/-- After at least one pass no pending block is ready. -/
theorem noReady_quiesce : ∀ (n : ℕ) (s : State Validator BlockId Payload),
    NoReady cfg (quiesce cfg (n + 1) s).1
  | n, s => by
    rcases quiesce_succ_cases (cfg := cfg) n s with he | he <;> rw [he]
    · simp only [NoReady, advance_pending, advance_disk, Node.pass, flush_pending, flush_disk]
      exact flush_no_ready _ _ _ (Nat.lt_succ_self _)
    · cases n with
      | zero =>
        simp only [NoReady, Node.quiesce, advance_pending, advance_disk, Node.pass, flush_pending,
          flush_disk]
        exact flush_no_ready _ _ _ (Nat.lt_succ_self _)
      | succ n => exact noReady_quiesce n _

omit [Fintype Validator] in
/-- After a settle no pending block is ready. -/
theorem noReady_settle (s : State Validator BlockId Payload) :
    NoReady cfg (Node.settle cfg s).1 := by
  obtain ⟨n, hn⟩ := passes_succ (cfg := cfg) s
  unfold Node.settle
  rw [hn]
  exact noReady_quiesce n s

/-- **After every step no pending block is ready.** -/
theorem noReady_step {s : State Validator BlockId Payload} (h : NoReady cfg s)
    (inp : Input Validator BlockId Payload) : NoReady cfg (Node.step cfg s inp).1 := by
  cases inp with
  | start =>
    simp only [Node.step]
    split
    · split
      · exact noReady_settle _
      · exact h
    · exact h
  | deliver id b =>
    by_cases hc : Admits cfg s id b
    · rw [step_deliver hc]; exact noReady_settle _
    · rw [step_deliver_not hc]; exact h
  | timer r => rw [step_timer_fst]; exact noReady_settle _
  | fetchRequest peer r ids => exact h
  | restart => exact noReady_settle _

/-- **A delivery the node acts on keeps a fitting block it delivers**
pending or on disk. -/
theorem admit_keeps {s : State Validator BlockId Payload} {id : BlockId}
    {b : Block Validator BlockId Payload} (hc : Admits cfg s id b)
    (hR : ReadsAs g (Node.step cfg s (.deliver id b)).1.disk)
    (hp : ∀ e ∈ s.pending, g e.1 = e.2) (hgb : g id = b)
    (hf : Fits cfg g (id, b)) :
    (id, b) ∈ (Node.step cfg s (.deliver id b)).1.pending ∨
      id ∈ (Node.step cfg s (.deliver id b)).1.disk.ids := by
  have hRs : ReadsAs g s.disk := hR.of_grows (Grows.step (cfg := cfg) s (.deliver id b))
  have hstep := step_deliver (cfg := cfg) hc
  have hpb : ∀ e ∈ (id, b) :: s.pending, g e.1 = e.2 := by
    intro e he
    rcases List.mem_cons.mp he with rfl | he
    · exact hgb
    · exact hp e he
  have hfl := ReadsAs.flush (cfg := cfg) (s.pending.length + 1) hRs hpb
  have hk := flush_keeps (cfg := cfg) (s.pending.length + 1) hRs hpb hf List.mem_cons_self
  rw [hstep] at hR ⊢
  exact settle_keeps hR (by rw [afterFlush_pending]; exact hfl.2) hf
    (by rw [afterFlush_pending, afterFlush_disk]; exact hk)

end Node

end LeanDag
