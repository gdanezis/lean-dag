import LeanDag.Node.Helpers.Flush
/-!
# What one step does to pending, stored and requested blocks

On stores reading as a block map `g` at a horizon that does not rise, a
step keeps every block that fits pending or stored (`step_keeps`); a
block becomes pending only by being delivered (`pending_of_step`); a
request is recorded only on account of a block just delivered and not
dropped (`requested_of_step`); and a block the step broadcasts is in the
store after it (`broadcast_stored`).
-/

namespace LeanDag

namespace Node

variable {Validator BlockId Payload : Type} [Fintype Validator] [DecidableEq Validator]
variable [LinearOrder BlockId]
variable {cfg : Config Validator BlockId Payload} {g : BlockId → Block Validator BlockId Payload}

omit [Fintype Validator] in
theorem tryBuild_pending {s s' : State Validator BlockId Payload}
    {out : List (Output Validator BlockId Payload)} (h : tryBuild cfg s = some (s', out)) :
    s'.pending = s.pending ∧ s'.requested = s.requested := by
  unfold tryBuild at h
  split at h
  · dsimp only at h
    split at h
    · split at h
      · rw [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, -⟩ := h
        exact ⟨rfl, rfl⟩
      · exact absurd h (by simp)
    · exact absurd h (by simp)
  · exact absurd h (by simp)

omit [Fintype Validator] in
theorem progress_pending : ∀ (fuel : ℕ) (s : State Validator BlockId Payload),
    (Node.progress cfg fuel s).1.pending = s.pending ∧
      (Node.progress cfg fuel s).1.requested = s.requested
  | 0, _ => ⟨rfl, rfl⟩
  | fuel + 1, s => by
    unfold Node.progress
    split
    · rename_i s₁ out h
      have := tryBuild_pending h
      have ih := progress_pending fuel s₁
      exact ⟨ih.1.trans this.1, ih.2.trans this.2⟩
    · exact ⟨rfl, rfl⟩

omit [Fintype Validator] in
theorem decideStep_pending (s : State Validator BlockId Payload) :
    (Node.decideStep cfg s).1.pending = s.pending ∧
      (Node.decideStep cfg s).1.requested = s.requested := by
  unfold Node.decideStep
  dsimp only
  split <;> exact ⟨rfl, rfl⟩

omit [Fintype Validator] in
/-- **Collecting at a horizon that does not rise changes nothing.** -/
theorem collect_eq (s : State Validator BlockId Payload)
    (h : (Node.collect cfg s).1.store.base = s.store.base) : Node.collect cfg s = (s, []) := by
  rcases hs : s.top with _ | t
  · simp only [Node.collect, hs]
  · by_cases hG : s.store.base < min (cfg.per * (s.lo / cfg.m)) t - cfg.lag
    · exfalso
      simp only [Node.collect, hs, dif_pos hG] at h
      change min (cfg.per * (s.lo / cfg.m)) t - cfg.lag = s.store.base at h
      omega
    · simp only [Node.collect, hs, dif_neg hG]

omit [Fintype Validator] in
/-- **A block that fits stays pending or stored across a settle**, at a
horizon that does not rise. -/
theorem settle_keeps {s : State Validator BlockId Payload}
    (hR : ReadsAs g (Node.settle cfg s).1.store)
    (hb : (Node.settle cfg s).1.store.base = s.store.base)
    (hp : ∀ e ∈ s.pending, g e.1 = atBase 0 e.2) {y : BlockId × Block Validator BlockId Payload}
    (hf : Fits cfg g y) (hy : y ∈ s.pending ∨ y.1 ∈ s.store.ids) :
    y ∈ (Node.settle cfg s).1.pending ∨ y.1 ∈ (Node.settle cfg s).1.store.ids := by
  have hg₁ := (Grows.progress (cfg := cfg) (s.store.topRound + 2) s).1
  have hp₁ := (progress_pending (cfg := cfg) (s.store.topRound + 2) s).1
  simp only [Node.settle] at hR hb ⊢
  generalize Node.progress cfg (s.store.topRound + 2) s = r at hg₁ hp₁ hR hb ⊢
  have hd := decideStep_store (cfg := cfg) r.1
  have hdp := (decideStep_pending (cfg := cfg) r.1).1
  generalize Node.decideStep cfg r.1 = d at hd hdp hR hb ⊢
  have hgc := Grows.collect (cfg := cfg) d.1
  have hgf := Grows.flush (cfg := cfg) ((Node.collect cfg d.1).1.pending.length + 1)
    (Node.collect cfg d.1).1.store (Node.collect cfg d.1).1.pending
  change ReadsAs g (flush cfg ((Node.collect cfg d.1).1.pending.length + 1)
    (Node.collect cfg d.1).1.store (Node.collect cfg d.1).1.pending).1 at hR
  change (flush cfg ((Node.collect cfg d.1).1.pending.length + 1)
    (Node.collect cfg d.1).1.store (Node.collect cfg d.1).1.pending).1.base = s.store.base at hb
  have hdb : d.1.store.base = r.1.store.base := by rw [hd]
  have h1 := hg₁.1
  have h2 := hgc.1
  have h3 := hgf.1
  have hcb : (Node.collect cfg d.1).1.store.base = d.1.store.base := by omega
  have hbr : r.1.store.base = s.store.base := by omega
  have hce := collect_eq d.1 hcb
  have hfb : (flush cfg ((Node.collect cfg d.1).1.pending.length + 1)
      (Node.collect cfg d.1).1.store (Node.collect cfg d.1).1.pending).1.base =
      (Node.collect cfg d.1).1.store.base := by omega
  rw [hce] at hR hgf hfb ⊢
  dsimp only at hR hgf hfb ⊢
  have hbd := hfb
  have hRd : ReadsAs g d.1.store := ⟨by rw [← hbd]; exact hR.1, fun j hj => by
    rw [← hgf.blk hbd hj]; exact hR.2 j ((hgf.2 hbd).1 hj)⟩
  have hpd : ∀ e ∈ d.1.pending, g e.1 = atBase 0 e.2 := by rw [hdp, hp₁]; exact hp
  have hy' : y ∈ d.1.pending ∨ y.1 ∈ d.1.store.ids := by
    rw [hdp, hp₁, hd]
    rcases hy with hy | hy
    · exact Or.inl hy
    · exact Or.inr ((hg₁.2 hbr).1 hy)
  rcases hy' with hy' | hy'
  · exact flush_keeps _ hRd hpd hf hy'
  · exact Or.inr ((hgf.2 hbd).1 hy')

omit [Fintype Validator] in
theorem flush_pending_sub : ∀ (fuel : ℕ) (st : Store Validator BlockId Payload)
    (pend : List (BlockId × Block Validator BlockId Payload)),
    ∀ e ∈ (Node.flush cfg fuel st pend).2, e ∈ pend
  | 0, _, _, _, he => he
  | fuel + 1, st, pend, e, he => by
    unfold Node.flush at he
    dsimp only at he
    split at he
    · exact he
    · rw [List.partition_eq_filter_filter] at he
      exact (List.mem_filter.mp (flush_pending_sub fuel _ _ e he)).1

omit [Fintype Validator] in
theorem collect_sub (s : State Validator BlockId Payload) :
    (∀ e ∈ (Node.collect cfg s).1.pending, e ∈ s.pending) ∧
      ∀ e ∈ (Node.collect cfg s).1.requested, e ∈ s.requested := by
  unfold Node.collect
  split
  · dsimp only
    split
    · exact ⟨fun e he => (List.mem_filter.mp he).1, fun e he => (List.mem_filter.mp he).1⟩
    · exact ⟨fun _ h => h, fun _ h => h⟩
  · exact ⟨fun _ h => h, fun _ h => h⟩

omit [Fintype Validator] in
/-- **A settle adds no pending block and records no request.** -/
theorem settle_sub (s : State Validator BlockId Payload) :
    (∀ e ∈ (Node.settle cfg s).1.pending, e ∈ s.pending) ∧
      ∀ e ∈ (Node.settle cfg s).1.requested, e ∈ s.requested := by
  have hp := progress_pending (cfg := cfg) (s.store.topRound + 2) s
  have hd := decideStep_pending (cfg := cfg) (Node.progress cfg (s.store.topRound + 2) s).1
  have hc := collect_sub (cfg := cfg)
    (Node.decideStep cfg (Node.progress cfg (s.store.topRound + 2) s).1).1
  refine ⟨fun e he => ?_, fun e he => ?_⟩
  · have := flush_pending_sub (cfg := cfg) _ _ _ e he
    have := hc.1 e this
    rwa [hd.1, hp.1] at this
  · have := hc.2 e he
    rwa [hd.2, hp.2] at this

variable (cfg) in
/-- **A delivery the node acts on**: identified by its hash, not the
node's own, at or above the horizon, and new. -/
def Admits (s : State Validator BlockId Payload) (id : BlockId)
    (b : Block Validator BlockId Payload) : Prop :=
  id = cfg.idOf b ∧ b.creator ≠ cfg.me ∧ s.store.base ≤ b.round ∧ id ∉ s.store.ids ∧
    id ∉ s.pending.map Prod.fst

/-- The state a delivery the node acts on settles: the store and pending
blocks after flushing, and the requests the walk adds. -/
def afterFlush (s : State Validator BlockId Payload) (id : BlockId)
    (b : Block Validator BlockId Payload) : State Validator BlockId Payload :=
  let fl := flush cfg (s.pending.length + 1) s.store ((id, b) :: s.pending)
  { s with store := fl.1, pending := fl.2 }

theorem step_deliver {s : State Validator BlockId Payload} {id : BlockId}
    {b : Block Validator BlockId Payload} (h : Admits cfg s id b) :
    let s₁ := afterFlush (cfg := cfg) s id b
    let miss := missing s₁ id b
    Node.step cfg s (.deliver id b) =
      ((Node.settle cfg
          { s₁ with requested := s₁.requested ++ miss.map fun x => (x.1, id, x.2) }).1,
        (if miss.isEmpty then [] else [.fetch (miss.map Prod.fst)]) ++
          (Node.settle cfg
            { s₁ with requested := s₁.requested ++ miss.map fun x => (x.1, id, x.2) }).2) := by
  have h' : id = cfg.idOf b ∧ b.creator ≠ cfg.me ∧ s.store.base ≤ b.round ∧ id ∉ s.store.ids ∧
      id ∉ s.pending.map Prod.fst := h
  simp only [Node.step]
  rw [if_pos h']
  rfl

/-- **Across a step a fitting block stays pending or stored**, on stores
reading as `g` at a horizon that does not rise. -/
theorem step_keeps {s : State Validator BlockId Payload} {inp : Input Validator BlockId Payload}
    (hR : ReadsAs g (Node.step cfg s inp).1.store)
    (hb : (Node.step cfg s inp).1.store.base = s.store.base)
    (hp : ∀ e ∈ s.pending, g e.1 = atBase 0 e.2)
    (hd : ∀ id b, inp = .deliver id b → id = cfg.idOf b → g id = atBase 0 b)
    (hr : inp ≠ .restart)
    {y : BlockId × Block Validator BlockId Payload} (hf : Fits cfg g y)
    (hy : y ∈ s.pending ∨ y.1 ∈ s.store.ids) :
    y ∈ (Node.step cfg s inp).1.pending ∨ y.1 ∈ (Node.step cfg s inp).1.store.ids := by
  have hgs := Grows.step (cfg := cfg) s inp
  have hRs : ReadsAs g s.store := ⟨by rw [← hb]; exact hR.1, fun j hj => by
    rw [← hgs.blk hb hj]; exact hR.2 j ((hgs.2 hb).1 hj)⟩
  -- a step that settles `s₀`, whose pending blocks read as `g` and which keeps `y`
  have hset : ∀ s₀ : State Validator BlockId Payload,
      Node.step cfg s inp = ((Node.settle cfg s₀).1, (Node.step cfg s inp).2) →
      Grows s.store s₀.store → s₀.store.base = s.store.base →
      (∀ e ∈ s₀.pending, g e.1 = atBase 0 e.2) → (y ∈ s₀.pending ∨ y.1 ∈ s₀.store.ids) →
      y ∈ (Node.step cfg s inp).1.pending ∨ y.1 ∈ (Node.step cfg s inp).1.store.ids := by
    intro s₀ he hg₀ hb₀ hp₀ hy₀
    rw [he] at hR hb ⊢
    exact settle_keeps hR (hb.trans hb₀.symm) hp₀ hf hy₀
  cases inp with
  | start =>
    by_cases h₁ : s.top = none ∧ cfg.Admissible
    · by_cases h₂ : cfg.idOf cfg.genesis ∉ s.store.ids ∧ s.store.base ≤ cfg.genesis.round ∧
          rowValid cfg.q (Function.update s.store.blk (cfg.idOf cfg.genesis) cfg.genesis)
            cfg.genesis
      · let st := s.store.insert _ _ h₂.1 h₂.2.1 (fun _ => Finset.empty_subset _)
          (fun _ j hj => absurd hj (Finset.notMem_empty j))
        refine hset { s with store := st, top := some 0, own := some (cfg.idOf cfg.genesis) }
          ?_ (show Grows s.store st from Grows.insert _) rfl hp ?_
        · simp only [Node.step, dif_pos h₂, if_pos h₁]
          try rfl
        · rcases hy with hy | hy
          · exact Or.inl hy
          · exact Or.inr (Finset.mem_insert_of_mem hy)
      · simp only [Node.step, dif_neg h₂, if_pos h₁]; exact hy
    · simp only [Node.step, if_neg h₁]; exact hy
  | deliver id b =>
    by_cases hc : Admits cfg s id b
    · have hstep := step_deliver (cfg := cfg) hc
      let s₁ := afterFlush (cfg := cfg) s id b
      have hpb : ∀ e ∈ (id, b) :: s.pending, g e.1 = atBase 0 e.2 := by
        intro e he
        rcases List.mem_cons.mp he with rfl | he
        · exact hd _ _ rfl hc.1
        · exact hp e he
      have hfl := ReadsAs.flush (cfg := cfg) (s.pending.length + 1) hRs hpb
      let req := s₁.requested ++ (missing s₁ id b).map fun x => (x.1, id, x.2)
      refine hset { s₁ with requested := req } (by rw [hstep]) (Grows.flush _ _ _) ?_ hfl.2 ?_
      · exact hfl.1.1.trans hRs.1.symm
      · rcases hy with hy | hy
        · exact flush_keeps _ hRs hpb hf (List.mem_cons_of_mem _ hy)
        · have hg := Grows.flush (cfg := cfg) (s.pending.length + 1) s.store ((id, b) :: s.pending)
          exact Or.inr ((hg.2 (hfl.1.1.trans hRs.1.symm)).1 hy)
    · have h' : ¬ (id = cfg.idOf b ∧ b.creator ≠ cfg.me ∧ s.store.base ≤ b.round ∧
          id ∉ s.store.ids ∧ id ∉ s.pending.map Prod.fst) := hc
      simp only [Node.step, if_neg h']; exact hy
  | timer r =>
    exact hset { s with fired := insert r s.fired } (by simp only [Node.step]) (Grows.refl _) rfl
      hp hy
  | fetchRequest peer ids => exact hy
  | jump => exact hy
  | restart => exact absurd rfl hr
  | baseOffer => exact hy
  | baseRequest => exact hy

/-- **A block becomes pending only by being delivered**, and only when the
node acts on the delivery; a request is recorded only on account of such
a delivery. -/
theorem step_sub (s : State Validator BlockId Payload) (inp : Input Validator BlockId Payload) :
    (∀ e ∈ (Node.step cfg s inp).1.pending, e ∈ s.pending ∨
      (inp = .deliver e.1 e.2 ∧ Admits cfg s e.1 e.2)) ∧
    ∀ e ∈ (Node.step cfg s inp).1.requested, e ∈ s.requested ∨
      ∃ b, inp = .deliver e.2.1 b ∧ Admits cfg s e.2.1 b := by
  cases inp with
  | start =>
    by_cases h₁ : s.top = none ∧ cfg.Admissible
    · by_cases h₂ : cfg.idOf cfg.genesis ∉ s.store.ids ∧ s.store.base ≤ cfg.genesis.round ∧
          rowValid cfg.q (Function.update s.store.blk (cfg.idOf cfg.genesis) cfg.genesis)
            cfg.genesis
      · simp only [Node.step, dif_pos h₂, if_pos h₁]
        let st := s.store.insert _ _ h₂.1 h₂.2.1 (fun _ => Finset.empty_subset _)
          (fun _ j hj => absurd hj (Finset.notMem_empty j))
        let s₀ : State Validator BlockId Payload :=
          { s with store := st, top := some 0, own := some (cfg.idOf cfg.genesis) }
        have := settle_sub (cfg := cfg) s₀
        exact ⟨fun e he => Or.inl (this.1 e he), fun e he => Or.inl (this.2 e he)⟩
      · simp only [Node.step, dif_neg h₂, if_pos h₁]
        exact ⟨fun e he => Or.inl he, fun e he => Or.inl he⟩
    · simp only [Node.step, if_neg h₁]
      exact ⟨fun e he => Or.inl he, fun e he => Or.inl he⟩
  | deliver id b =>
    by_cases hc : Admits cfg s id b
    · rw [step_deliver hc]
      dsimp only
      let s₁ := afterFlush (cfg := cfg) s id b
      let req := s₁.requested ++ (missing s₁ id b).map fun x => (x.1, id, x.2)
      have := settle_sub (cfg := cfg) { s₁ with requested := req }
      refine ⟨fun e he => ?_, fun e he => ?_⟩
      · have hm := flush_pending_sub (cfg := cfg) _ _ _ e (this.1 e he)
        rcases List.mem_cons.mp hm with rfl | hm
        · exact Or.inr ⟨rfl, hc⟩
        · exact Or.inl hm
      · rcases List.mem_append.mp (this.2 e he) with he | he
        · exact Or.inl he
        · obtain ⟨x, -, rfl⟩ := List.mem_map.mp he
          exact Or.inr ⟨b, rfl, hc⟩
    · have h' : ¬ (id = cfg.idOf b ∧ b.creator ≠ cfg.me ∧ s.store.base ≤ b.round ∧
          id ∉ s.store.ids ∧ id ∉ s.pending.map Prod.fst) := hc
      simp only [Node.step, if_neg h']
      exact ⟨fun e he => Or.inl he, fun e he => Or.inl he⟩
  | timer r =>
    have := settle_sub (cfg := cfg) { s with fired := insert r s.fired }
    exact ⟨fun e he => Or.inl (this.1 e he), fun e he => Or.inl (this.2 e he)⟩
  | restart =>
    have := settle_sub (cfg := cfg) s.recover
    exact ⟨fun e he => absurd (this.1 e he) (by simp [State.recover]),
      fun e he => absurd (this.2 e he) (by simp [State.recover])⟩
  | _ => exact ⟨fun e he => Or.inl he, fun e he => Or.inl he⟩

omit [Fintype Validator] in
theorem progress_base : ∀ (fuel : ℕ) (s : State Validator BlockId Payload),
    (Node.progress cfg fuel s).1.store.base = s.store.base
  | 0, _ => rfl
  | fuel + 1, s => by
    unfold Node.progress
    split
    · rename_i s₁ out h
      obtain ⟨_, _, _, _, _, _, _, -, -, -, -, -, hst, -, -, -, -⟩ := tryBuild_some h
      rw [progress_base fuel s₁, hst]
      rfl
    · rfl

omit [Fintype Validator] in
/-- **What building broadcasts it stores.** -/
theorem progress_bcast : ∀ (fuel : ℕ) (s : State Validator BlockId Payload),
    ∀ e ∈ broadcasts (Node.progress cfg fuel s).2, e.1 ∈ (Node.progress cfg fuel s).1.store.ids ∧
      (Node.progress cfg fuel s).1.store.map.getD e.1 (Node.progress cfg fuel s).1.store.junk = e.2
  | 0, _, e, he => by simp [Node.progress, broadcasts] at he
  | fuel + 1, s, e, he => by
    rcases hb : tryBuild cfg s with _ | ⟨s₁, out⟩
    · simp [Node.progress, hb, broadcasts] at he
    · simp only [Node.progress, hb] at he ⊢
      obtain ⟨r, id, b, hnew, hab, hrefs, hpred, -, -, -, -, -, hst, -, -, -, hout⟩ :=
        tryBuild_some hb
      have hg := (Grows.progress (cfg := cfg) fuel s₁).1
      have hbs : (Node.progress cfg fuel s₁).1.store.base = s₁.store.base := progress_base fuel s₁
      rw [hout] at he
      simp only [built, List.flatMap_cons, List.flatMap_nil, List.append_nil, List.cons_append,
        List.nil_append, broadcasts, List.filterMap_cons] at he
      rcases List.mem_cons.mp he with rfl | he
      · have hin : id ∈ s₁.store.ids := by rw [hst]; exact Finset.mem_insert_self _ _
        refine ⟨(hg.2 hbs).1 hin, ?_⟩
        rw [(hg.2 hbs).2.2 _ hin, hst]
        exact Std.TreeMap.getD_insert_self
      · exact progress_bcast fuel s₁ e he

omit [Fintype Validator] [DecidableEq Validator] [LinearOrder BlockId] in
theorem broadcasts_commits (ds : List (ℕ × Option BlockId)) :
    broadcasts (ds.map fun e => (Output.commit e.1 e.2 : Output Validator BlockId Payload)) =
      [] := by
  induction ds with
  | nil => rfl
  | cons e ds ih => simp [broadcasts]

omit [Fintype Validator] in
theorem decideStep_bcast (s : State Validator BlockId Payload) :
    broadcasts (Node.decideStep cfg s).2 = [] := by
  unfold Node.decideStep
  dsimp only
  split
  · exact broadcasts_commits _
  · rfl

omit [Fintype Validator] in
theorem collect_bcast (s : State Validator BlockId Payload) :
    broadcasts (Node.collect cfg s).2 = [] := by
  unfold Node.collect
  split
  · dsimp only
    split <;> rfl
  · rfl

omit [Fintype Validator] in
/-- **What a settle broadcasts it stores**, at a horizon that does not
rise. -/
theorem settle_bcast (s : State Validator BlockId Payload)
    (hb : (Node.settle cfg s).1.store.base = s.store.base) :
    ∀ e ∈ broadcasts (Node.settle cfg s).2, e.1 ∈ (Node.settle cfg s).1.store.ids ∧
      (Node.settle cfg s).1.store.map.getD e.1 (Node.settle cfg s).1.store.junk = e.2 := by
  intro e he
  have hpb := progress_base (cfg := cfg) (s.store.topRound + 2) s
  have hp := progress_bcast (cfg := cfg) (s.store.topRound + 2) s
  simp only [Node.settle] at he hb ⊢
  generalize Node.progress cfg (s.store.topRound + 2) s = r at hpb hp he hb ⊢
  rw [broadcasts_append, broadcasts_append, decideStep_bcast, collect_bcast, List.append_nil,
    List.append_nil] at he
  obtain ⟨hin, hval⟩ := hp e he
  have hd := decideStep_store (cfg := cfg) r.1
  have hgc := Grows.collect (cfg := cfg) (Node.decideStep cfg r.1).1
  rw [hd] at hgc
  generalize Node.collect cfg (Node.decideStep cfg r.1).1 = c at hgc hb ⊢
  have hgf := Grows.flush (cfg := cfg) (c.1.pending.length + 1) c.1.store c.1.pending
  have hg := hgc.trans hgf
  have hbe : (flush cfg (c.1.pending.length + 1) c.1.store c.1.pending).1.base =
      r.1.store.base := by
    change _ = s.store.base at hb; rw [hb, hpb]
  exact ⟨(hg.2 hbe).1 hin, by rw [(hg.2 hbe).2.2 _ hin]; exact hval⟩

omit [Fintype Validator] in
theorem accept_base (st : Store Validator BlockId Payload) (id : BlockId)
    (b : Block Validator BlockId Payload) : (Node.accept cfg st id b).base = st.base := by
  unfold Node.accept; split <;> rfl

omit [Fintype Validator] in
theorem foldl_base : ∀ (l : List (BlockId × Block Validator BlockId Payload))
    (st : Store Validator BlockId Payload),
    (l.foldl (fun s e => Node.accept cfg s e.1 e.2) st).base = st.base
  | [], _ => rfl
  | e :: l, st => by rw [List.foldl_cons, foldl_base l, accept_base]

omit [Fintype Validator] in
theorem flush_base : ∀ (fuel : ℕ) (st : Store Validator BlockId Payload)
    (pend : List (BlockId × Block Validator BlockId Payload)),
    (Node.flush cfg fuel st pend).1.base = st.base
  | 0, _, _ => rfl
  | fuel + 1, st, pend => by
    unfold Node.flush
    dsimp only
    split
    · rfl
    · rw [flush_base fuel, foldl_base]

omit [Fintype Validator] in
theorem settle_bcast_of {s₀ : State Validator BlockId Payload}
    {pre : List (Output Validator BlockId Payload)}
    (hpre : broadcasts pre = [] ∨ ∃ e₀, broadcasts pre = [e₀] ∧ e₀.1 ∈ s₀.store.ids ∧
      s₀.store.map.getD e₀.1 s₀.store.junk = e₀.2)
    (hb : (Node.settle cfg s₀).1.store.base = s₀.store.base) :
    ∀ e ∈ broadcasts (pre ++ (Node.settle cfg s₀).2), e.1 ∈ (Node.settle cfg s₀).1.store.ids ∧
      (Node.settle cfg s₀).1.store.map.getD e.1 (Node.settle cfg s₀).1.store.junk = e.2 := by
  intro e he
  rw [broadcasts_append] at he
  rcases List.mem_append.mp he with he | he
  · rcases hpre with hpre | ⟨e₀, hpre, hin, hval⟩
    · rw [hpre] at he; exact absurd he (List.not_mem_nil)
    · rw [hpre, List.mem_singleton] at he
      subst he
      have hg := Grows.settle (cfg := cfg) s₀
      exact ⟨(hg.2 hb).1 hin, by rw [(hg.2 hb).2.2 _ hin]; exact hval⟩
  · exact settle_bcast s₀ hb e he

/-- **What a step broadcasts it stores**, at a horizon that does not rise. -/
theorem step_bcast {s : State Validator BlockId Payload} {inp : Input Validator BlockId Payload}
    (hb : (Node.step cfg s inp).1.store.base = s.store.base) :
    ∀ e ∈ broadcasts (Node.step cfg s inp).2, e.1 ∈ (Node.step cfg s inp).1.store.ids ∧
      (Node.step cfg s inp).1.store.map.getD e.1 (Node.step cfg s inp).1.store.junk = e.2 := by
  cases inp with
  | start =>
    by_cases h₁ : s.top = none ∧ cfg.Admissible
    · by_cases h₂ : cfg.idOf cfg.genesis ∉ s.store.ids ∧ s.store.base ≤ cfg.genesis.round ∧
          rowValid cfg.q (Function.update s.store.blk (cfg.idOf cfg.genesis) cfg.genesis)
            cfg.genesis
      · let st := s.store.insert _ _ h₂.1 h₂.2.1 (fun _ => Finset.empty_subset _)
          (fun _ j hj => absurd hj (Finset.notMem_empty j))
        let s₀ : State Validator BlockId Payload :=
          { s with store := st, top := some 0, own := some (cfg.idOf cfg.genesis) }
        have he : Node.step cfg s .start =
            ((Node.settle cfg s₀).1, built cfg [(cfg.idOf cfg.genesis, cfg.genesis)] ++
              (Node.settle cfg s₀).2) := by
          simp only [Node.step, dif_pos h₂, if_pos h₁]; rfl
        rw [he] at hb ⊢
        refine settle_bcast_of (Or.inr ⟨(cfg.idOf cfg.genesis, cfg.genesis), by
          simp [built, broadcasts], Finset.mem_insert_self _ _, Std.TreeMap.getD_insert_self⟩) ?_
        exact hb.trans rfl
      · simp only [Node.step, dif_neg h₂, if_pos h₁]; simp [broadcasts]
    · simp only [Node.step, if_neg h₁]; simp [broadcasts]
  | deliver id b =>
    by_cases hc : Admits cfg s id b
    · rw [step_deliver hc] at hb ⊢
      dsimp only at hb ⊢
      refine settle_bcast_of (Or.inl ?_) (hb.trans (flush_base _ _ _).symm)
      split <;> rfl
    · have h' : ¬ (id = cfg.idOf b ∧ b.creator ≠ cfg.me ∧ s.store.base ≤ b.round ∧
          id ∉ s.store.ids ∧ id ∉ s.pending.map Prod.fst) := hc
      simp only [Node.step, if_neg h']; simp [broadcasts]
  | timer r =>
    exact settle_bcast_of (s₀ := { s with fired := insert r s.fired }) (pre := []) (Or.inl rfl) hb
  | fetchRequest peer ids =>
    intro e he
    change e ∈ broadcasts (answer s peer ids) at he
    unfold answer broadcasts at he
    rw [List.filterMap_map] at he
    simp at he
  | restart => exact settle_bcast_of (s₀ := s.recover) (pre := []) (Or.inl rfl) hb
  | _ => intro e he; simp [Node.step, broadcasts] at he

/-- No pending block is ready. -/
def NoReady (s : State Validator BlockId Payload) : Prop :=
  ∀ e ∈ s.pending, ready s.store e.2 = false

omit [Fintype Validator] in
theorem noReady_settle (s : State Validator BlockId Payload) : NoReady (Node.settle cfg s).1 :=
  flush_no_ready _ _ _ (Nat.lt_succ_self _)

/-- **After every step no pending block is ready.** -/
theorem noReady_step {s : State Validator BlockId Payload} (h : NoReady s)
    (inp : Input Validator BlockId Payload) : NoReady (Node.step cfg s inp).1 := by
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
    · have h' : ¬ (id = cfg.idOf b ∧ b.creator ≠ cfg.me ∧ s.store.base ≤ b.round ∧
          id ∉ s.store.ids ∧ id ∉ s.pending.map Prod.fst) := hc
      simp only [Node.step, if_neg h']; exact h
  | timer r => exact noReady_settle _
  | restart => exact noReady_settle _
  | _ => exact h

/-- **A delivery the node acts on keeps a fitting block it delivers**
pending or stored. -/
theorem admit_keeps {s : State Validator BlockId Payload} {id : BlockId}
    {b : Block Validator BlockId Payload} (hc : Admits cfg s id b)
    (hR : ReadsAs g (Node.step cfg s (.deliver id b)).1.store)
    (hb : (Node.step cfg s (.deliver id b)).1.store.base = s.store.base)
    (hp : ∀ e ∈ s.pending, g e.1 = atBase 0 e.2) (hgb : g id = atBase 0 b)
    (hf : Fits cfg g (id, b)) :
    (id, b) ∈ (Node.step cfg s (.deliver id b)).1.pending ∨
      id ∈ (Node.step cfg s (.deliver id b)).1.store.ids := by
  have hgs := Grows.step (cfg := cfg) s (.deliver id b)
  have hRs : ReadsAs g s.store := ⟨by rw [← hb]; exact hR.1, fun j hj => by
    rw [← hgs.blk hb hj]; exact hR.2 j ((hgs.2 hb).1 hj)⟩
  have hstep := step_deliver (cfg := cfg) hc
  have hpb : ∀ e ∈ (id, b) :: s.pending, g e.1 = atBase 0 e.2 := by
    intro e he
    rcases List.mem_cons.mp he with rfl | he
    · exact hgb
    · exact hp e he
  have hfl := ReadsAs.flush (cfg := cfg) (s.pending.length + 1) hRs hpb
  have hk := flush_keeps (cfg := cfg) (s.pending.length + 1) hRs hpb hf List.mem_cons_self
  rw [hstep] at hR hb ⊢
  exact settle_keeps hR (hb.trans (flush_base _ _ _).symm) hfl.2 hf hk

end Node

end LeanDag
