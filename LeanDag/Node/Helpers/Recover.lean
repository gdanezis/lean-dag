import LeanDag.Node.Helpers.Catch
/-!
# Recovery from crashes

`docs/validator.md` §5.6. A node's own blocks form a chain (`Chain`): each
reaches every one of a round at or below its own, since each references
the node's block of the round below (`own_mem_refsAt`), and no block of
the node's own enters its store but those it builds (`Chain.step`).
-/

namespace LeanDag

namespace Node

variable {Validator BlockId Payload : Type} [Fintype Validator] [DecidableEq Validator]
variable [LinearOrder BlockId]
variable {cfg : Config Validator BlockId Payload} {tr : Trace Validator BlockId Payload}

/-! ## A node's chain -/

section Chain

omit [Fintype Validator] [DecidableEq Validator] in
/-- **A path through a store stays a path** in a store it grows into. -/
theorem ReachesFrom.grows {st st' : Store Validator BlockId Payload} (hg : Grows st st')
    {j : BlockId} (hj : j ∈ st.ids) {j' : BlockId} (h : ReachesFrom st.blk j j') :
    ReachesFrom st'.blk j j' := by
  have key : ReachesFrom st'.blk j j' ∧ j' ∈ st.ids := by
    induction h with
    | refl => exact ⟨ReachesFrom.refl, hj⟩
    | tail hrw hstep ih =>
      rename_i w z
      obtain ⟨ih₁, hw⟩ := ih
      change z ∈ (st.blk w).refs at hstep
      refine ⟨ih₁.trans (ReachesFrom.single (blk := st'.blk) ?_), st.complete w hw z hstep⟩
      rw [hg.blk hw]; exact hstep
  exact key.1

omit [Fintype Validator] in
/-- **The node's own block of round `r` is among the references** it
builds on above `r`. -/
theorem own_mem_refsAt {st : Store Validator BlockId Payload} {r : ℕ} {o : BlockId}
    (ho : o ∈ st.ids) (hor : (st.blk o).round = r) (hoc : (st.blk o).creator = cfg.me) :
    o ∈ refsAt cfg st r (some o) := by
  have hfor : o ∈ refsFor cfg st r (some o) := by
    unfold refsFor
    rw [Store.atRound_eq]
    refine Finset.mem_biUnion.mpr ⟨cfg.me, mem_creatorsOf.mpr ⟨o, ?_, hoc⟩, ?_⟩
    · simpa [blocksAt, Store.toRecord] using And.intro ho hor
    · simp
  unfold refsAt
  dsimp only
  split
  · exact hfor
  · rcases hf : List.find? _ _ with _ | R
    · exact hfor
    · obtain ⟨c, -, rfl⟩ := List.mem_map.mp (List.mem_of_find?_eq_some hf)
      unfold lent
      exact Finset.mem_union_right _ (by simp)

omit [Fintype Validator] in
/-- **The blocks accepting adds come from the list accepted**. -/
theorem foldl_accept_new : ∀ (l : List (BlockId × Block Validator BlockId Payload))
    (st : Store Validator BlockId Payload) {j : BlockId},
    j ∈ (l.foldl (fun s e => accept cfg s e.1 e.2) st).ids → j ∉ st.ids →
      ∃ e ∈ l, (l.foldl (fun s e => accept cfg s e.1 e.2) st).blk j = e.2
  | [], st, j, hj, hn => absurd hj hn
  | e :: l, st, j, hj, hn => by
    simp only [List.foldl_cons] at hj ⊢
    by_cases hj₁ : j ∈ (accept cfg st e.1 e.2).ids
    · -- `j` is `e`'s, accepted first
      have hg := Grows.foldl (cfg := cfg) l (accept cfg st e.1 e.2)
      rw [hg.blk hj₁]
      unfold accept at hj₁ ⊢
      split
      · rename_i h
        rw [dif_pos h, Store.insert_ids] at hj₁
        rcases Finset.mem_insert.mp hj₁ with rfl | hj₁
        · exact ⟨e, List.mem_cons_self, Std.TreeMap.getD_insert_self⟩
        · exact absurd hj₁ hn
      · rename_i h
        rw [dif_neg h] at hj₁
        exact absurd hj₁ hn
    · obtain ⟨e', he', hb⟩ := foldl_accept_new l _ hj hj₁
      exact ⟨e', List.mem_cons_of_mem _ he', hb⟩

omit [Fintype Validator] in
/-- **The blocks a flush adds come from the pending blocks**. -/
theorem flush_new : ∀ (fuel : ℕ) (st : Store Validator BlockId Payload)
    (pend : List (BlockId × Block Validator BlockId Payload)) {j : BlockId},
    j ∈ (flush cfg fuel st pend).1.ids → j ∉ st.ids →
      ∃ e ∈ pend, (flush cfg fuel st pend).1.blk j = e.2
  | 0, st, pend, j, hj, hn => absurd hj hn
  | fuel + 1, st, pend, j, hj, hn => by
    unfold flush at hj ⊢
    dsimp only at hj ⊢
    split at hj
    · rename_i h; rw [if_pos h]; exact absurd hj hn
    · rename_i h
      rw [if_neg h]
      have hsub : ∀ e ∈ (pend.partition fun e => ready cfg st e).1 ++
          (pend.partition fun e => ready cfg st e).2, e ∈ pend := by
        intro e he
        rw [List.partition_eq_filter_filter] at he
        rcases List.mem_append.mp he with he | he
        · exact (List.mem_filter.mp he).1
        · exact (List.mem_filter.mp he).1
      set st₁ := (pend.partition fun e => ready cfg st e).1.foldl
        (fun s e => accept cfg s e.1 e.2) st with hst₁
      by_cases hj₁ : j ∈ st₁.ids
      · have hg := Grows.flush (cfg := cfg) fuel st₁ (pend.partition fun e => ready cfg st e).2
        rw [hg.blk hj₁]
        obtain ⟨e, he, hb⟩ := foldl_accept_new _ st hj₁ hn
        exact ⟨e, hsub e (List.mem_append_left _ he), hb⟩
      · obtain ⟨e, he, hb⟩ := flush_new fuel st₁ _ hj hj₁
        exact ⟨e, hsub e (List.mem_append_right _ he), hb⟩

variable (cfg) in
/-- **A node's chain**: no pending block is its own; its own blocks in its
store lie at or below its top, none before it starts; and each reaches
every one of a round at or below its own. -/
structure Chain (s : State Validator BlockId Payload) : Prop where
  pend : ∀ e ∈ s.pending, e.2.creator ≠ cfg.me
  top : ∀ j ∈ s.store.ids, (s.store.blk j).creator = cfg.me →
    s.top.isSome ∧ (s.store.blk j).round ≤ s.top.getD 0
  reach : ∀ j ∈ s.store.ids, ∀ j' ∈ s.store.ids, (s.store.blk j).creator = cfg.me →
    (s.store.blk j').creator = cfg.me → (s.store.blk j').round ≤ (s.store.blk j).round →
      ReachesFrom s.store.blk j j'

omit [Fintype Validator] in
/-- The chain reads only the store, the pending blocks and the top. -/
theorem Chain.congr {s s' : State Validator BlockId Payload} (h : Chain cfg s)
    (hst : s'.store = s.store) (hpd : s'.pending = s.pending) (ht : s'.top = s.top) :
    Chain cfg s' :=
  ⟨hpd ▸ h.pend, hst ▸ ht ▸ h.top, hst ▸ h.reach⟩

omit [Fintype Validator] in
/-- **The chain survives a store grown by blocks of others**, with the
top kept and no pending block of the node's own. -/
theorem Chain.grow {s s' : State Validator BlockId Payload} (h : Chain cfg s)
    (hg : Grows s.store s'.store)
    (hnew : ∀ j ∈ s'.store.ids, j ∉ s.store.ids → (s'.store.blk j).creator ≠ cfg.me)
    (hpend : ∀ e ∈ s'.pending, e.2.creator ≠ cfg.me) (ht : s'.top = s.top) : Chain cfg s' := by
  have hold : ∀ j ∈ s'.store.ids, (s'.store.blk j).creator = cfg.me →
      j ∈ s.store.ids ∧ s'.store.blk j = s.store.blk j := fun j hj hc => by
    by_cases hjs : j ∈ s.store.ids
    · exact ⟨hjs, hg.blk hjs⟩
    · exact absurd hc (hnew j hj hjs)
  refine ⟨hpend, fun j hj hc => ?_, fun j hj j' hj' hc hc' hr => ?_⟩
  · obtain ⟨hjs, hb⟩ := hold j hj hc
    rw [hb] at hc ⊢
    rw [ht]
    exact h.top j hjs hc
  · obtain ⟨hjs, hb⟩ := hold j hj hc
    obtain ⟨hjs', hb'⟩ := hold j' hj' hc'
    rw [hb] at hc hr
    rw [hb'] at hc' hr
    exact ReachesFrom.grows hg hjs (h.reach j hjs j' hjs' hc hc' hr)

omit [Fintype Validator] in
/-- **Flushing keeps the chain.** -/
theorem Chain.flushAll {s : State Validator BlockId Payload} (h : Chain cfg s) (fuel : ℕ) :
    Chain cfg
      { s with
        store := (flush cfg fuel s.store s.pending).1
        pending := (flush cfg fuel s.store s.pending).2 } := by
  refine h.grow (Grows.flush _ _ _) (fun j hj hn => ?_) (fun e he => ?_) rfl
  · obtain ⟨e, he, hb⟩ := flush_new (cfg := cfg) fuel s.store s.pending hj hn
    change (flush cfg fuel s.store s.pending).1.blk j = e.2 at hb
    change ((flush cfg fuel s.store s.pending).1.blk j).creator ≠ cfg.me
    rw [hb]
    exact h.pend e he
  · exact h.pend e (flush_pending_sub _ _ _ e he)

omit [Fintype Validator] in
/-- **Building keeps the chain**: the new block references the node's
block of the round below, which reaches the rest. -/
theorem Chain.tryBuild {s s' : State Validator BlockId Payload}
    {out : List (Output Validator BlockId Payload)} (h : Chain cfg s) (hown : OwnTop cfg s)
    (hb : tryBuild cfg s = some (s', out)) : Chain cfg s' := by
  obtain ⟨r, id, b, hnew, hrefs, hpred, hr, hbr, hbc, hid, -, hst, htop, hpd, -, hout⟩ :=
    tryBuild_some hb
  obtain ⟨r', hr', -, -, hout'⟩ := tryBuild_exit hb
  rw [hr] at hr'
  cases hr'
  have hAB := congrArg persists (hout.symm.trans hout')
  rw [persists_built, persists_built, List.singleton_inj] at hAB
  have hbR : b.refs = refsAt cfg s.store r s.own := by
    have := congrArg (fun e => e.2.refs) hAB
    simp only at this
    exact this
  obtain ⟨o, ho, hoi, hor, hoc⟩ := hown r hr
  have hoR : o ∈ b.refs := by rw [hbR, ho]; exact own_mem_refsAt hoi hor hoc
  have hblk : ∀ j ∈ s.store.ids, s'.store.blk j = s.store.blk j := fun j hj => by
    rw [hst]; exact (Grows.insert s.store).blk hj
  have hid' : s'.store.blk id = b := by
    rw [hst]; exact Std.TreeMap.getD_insert_self
  have hmem : ∀ j ∈ s'.store.ids, j = id ∨ j ∈ s.store.ids := fun j hj => by
    rw [hst, Store.insert_ids] at hj
    exact Finset.mem_insert.mp hj
  have hg : Grows s.store s'.store := hst ▸ Grows.insert s.store
  have hidm : id ∈ s'.store.ids := by rw [hst, Store.insert_ids]; exact Finset.mem_insert_self _ _
  -- the old blocks of the node's own lie at or below `r`
  have hle : ∀ j ∈ s.store.ids, (s.store.blk j).creator = cfg.me → (s.store.blk j).round ≤ r :=
    fun j hj hc => by have := (h.top j hj hc).2; rw [hr] at this; exact this
  refine ⟨by rw [hpd]; exact h.pend, fun j hj hc => ?_, fun j hj j' hj' hc hc' hjr => ?_⟩
  · rw [htop]
    refine ⟨rfl, ?_⟩
    rcases hmem j hj with rfl | hjs
    · rw [hid', hbr]; rfl
    · rw [hblk j hjs] at hc ⊢; have := hle j hjs hc; simp; omega
  · rcases hmem j hj with rfl | hjs <;> rcases hmem j' hj' with rfl | hjs'
    · exact ReachesFrom.refl
    · -- the new block, through the node's block of round `r`
      rw [hblk j' hjs'] at hc' hjr
      have hoj : ReachesFrom s.store.blk o j' :=
        h.reach o hoi j' hjs' hoc hc' (by rw [hor]; exact hle j' hjs' hc')
      refine ReachesFrom.of_mem_refs (by rw [hid']; exact hoR) (ReachesFrom.grows hg hoi hoj)
    · -- an old block below the new one: impossible
      rw [hblk j hjs] at hc hjr
      rw [hid', hbr] at hjr
      have := hle j hjs hc
      omega
    · rw [hblk j hjs] at hc hjr
      rw [hblk j' hjs'] at hc' hjr
      exact ReachesFrom.grows hg hjs (h.reach j hjs j' hjs' hc hc' hjr)

omit [Fintype Validator] in
theorem Chain.progress : ∀ (fuel : ℕ) {s : State Validator BlockId Payload}, Chain cfg s →
    OwnTop cfg s → Chain cfg (Node.progress cfg fuel s).1
  | 0, _, h, _ => h
  | fuel + 1, s, h, hown => by
    unfold Node.progress
    split
    · rename_i s₁ out hb
      exact Chain.progress fuel (h.tryBuild hown hb) (OwnTop.tryBuild hb)
    · exact h

omit [Fintype Validator] in
theorem Chain.advance {s : State Validator BlockId Payload} (h : Chain cfg s)
    (hown : OwnTop cfg s) : Chain cfg (Node.advance cfg s).1 := by
  refine Chain.congr ?_ (advance_store s) (advance_pending s) (advance_top s)
  simp only [Node.pass]
  have h₁ := Chain.progress (s.store.topRound + 2) h hown
  generalize Node.progress cfg (s.store.topRound + 2) s = r at h₁
  have h₂ : Chain cfg (Node.decideStep cfg r.1).1 := by
    have hd : (Node.decideStep cfg r.1).1 =
        { r.1 with
          lo := (Node.decideStep cfg r.1).1.lo
          decided := (Node.decideStep cfg r.1).1.decided } := by
      unfold Node.decideStep; dsimp only; split <;> rfl
    rw [hd]; exact h₁.congr rfl rfl rfl
  exact h₂.flushAll _

omit [Fintype Validator] in
theorem Chain.settle {s : State Validator BlockId Payload} (h : Chain cfg s)
    (hown : OwnTop cfg s) : Chain cfg (Node.settle cfg s).1 :=
  (quiesce_ind (P := fun s => Chain cfg s ∧ OwnTop cfg s)
    (fun _ h => ⟨h.1.advance h.2, h.2.advance⟩) _ _ ⟨h, hown⟩).1

/-- **A step keeps the chain.** -/
theorem Chain.step {s : State Validator BlockId Payload} (h : Chain cfg s) (hown : OwnTop cfg s)
    (i : Input Validator BlockId Payload) : Chain cfg (Node.step cfg s i).1 := by
  cases i with
  | start =>
    simp only [Node.step]
    split
    · rename_i h₁
      split
      · rename_i h₂
        set g := cfg.idOf cfg.genesis
        let st := s.store.insert g cfg.genesis h₂.1 (fun _ hj => absurd hj (Finset.notMem_empty _))
          (fun j hj => absurd hj (Finset.notMem_empty j))
        let s₀ : State Validator BlockId Payload :=
          { s with store := st, top := some 0, own := some g }
        have hnone : ∀ j ∈ s.store.ids, (s.store.blk j).creator ≠ cfg.me := fun j hj hc => by
          have := (h.top j hj hc).1; rw [h₁.1] at this; cases this
        have hmem : ∀ j ∈ st.ids, j = g ∨ j ∈ s.store.ids := fun j hj => by
          rw [Store.insert_ids] at hj; exact Finset.mem_insert.mp hj
        have hblk : ∀ j ∈ s.store.ids, st.blk j = s.store.blk j :=
          fun j hj => (Grows.insert s.store).blk hj
        have hg : st.blk g = cfg.genesis := Std.TreeMap.getD_insert_self
        have hown₀ : OwnTop cfg s₀ := by
          intro r hr
          change some 0 = some r at hr
          rw [Option.some.injEq] at hr
          subst hr
          refine ⟨g, rfl, (by simp [s₀, st, Store.insert_ids]), ?_, ?_⟩
          · change (st.blk g).round = 0; rw [hg]; rfl
          · change (st.blk g).creator = cfg.me; rw [hg]; rfl
        refine Chain.settle ⟨h.pend, fun j hj hc => ?_, fun j hj j' hj' hc hc' _ => ?_⟩ hown₀
        · refine ⟨rfl, ?_⟩
          rcases hmem j hj with rfl | hjs
          · change (st.blk _).round ≤ 0; rw [hg]; rfl
          · change (st.blk j).creator = cfg.me at hc
            rw [hblk j hjs] at hc; exact absurd hc (hnone j hjs)
        · change (st.blk j).creator = cfg.me at hc
          change (st.blk j').creator = cfg.me at hc'
          rcases hmem j hj with rfl | hjs
          · rcases hmem j' hj' with rfl | hjs'
            · exact ReachesFrom.refl
            · rw [hblk j' hjs'] at hc'; exact absurd hc' (hnone j' hjs')
          · rw [hblk j hjs] at hc; exact absurd hc (hnone j hjs)
      · exact h
    · exact h
  | deliver id b =>
    by_cases hA : Admits cfg s id b
    · rw [step_deliver hA]
      dsimp only
      refine Chain.settle ?_ ?_
      · have h₀ : Chain cfg { s with pending := (id, b) :: s.pending } :=
          ⟨fun e he => by
            rcases List.mem_cons.mp he with rfl | he
            · exact hA.2.1
            · exact h.pend e he, h.top, h.reach⟩
        exact (h₀.flushAll (s.pending.length + 1)).congr rfl rfl rfl
      · exact hown.grow (Grows.flush _ _ _) rfl rfl
    · rw [step_deliver_not hA]; exact h
  | timer r =>
    rw [step_timer_fst]
    exact Chain.settle (h.congr rfl rfl rfl)
      (hown.grow (s' := { s with fired := insert r s.fired }) (Grows.refl _) rfl rfl)
  | fetchRequest peer r ids => exact h
  | restart => exact h

omit [Fintype Validator] in
theorem Chain.init : Chain cfg (State.init cfg) :=
  ⟨fun _ h => absurd h List.not_mem_nil, fun _ h => absurd h (Finset.notMem_empty _),
    fun _ h => absurd h (Finset.notMem_empty _)⟩

/-- **A node's chain holds before every event.** -/
theorem chain_before (tr : Trace Validator BlockId Payload) (v : Validator) (i : ℕ) :
    Chain (cfg.at v) (stateBefore cfg tr i v) :=
  (inv_before (cfg := cfg) (tr := tr) v (fun s => Chain (cfg.at v) s ∧ OwnTop (cfg.at v) s)
    ⟨Chain.init, fun _ h => by simp [stateBefore, inputsBefore, run, State.init] at h⟩
    (fun s inp h => ⟨h.1.step h.2 inp, h.2.step inp⟩) i).1

/-- **A node's own blocks reach each other**: of two blocks an honest node
built, the higher reaches the lower through the blocks the honest nodes
know. -/
theorem own_reaches {H : Finset Validator} (hinj : Converge.HashInjective cfg H tr)
    {u : Validator} (hu : u ∈ H) {a b : ℕ} {inpa inpb : Input Validator BlockId Payload}
    (ha : tr[a]? = some (u, inpa)) (hb : tr[b]? = some (u, inpb))
    {y e : BlockId × Block Validator BlockId Payload} (hy : y ∈ persists (outputsAt cfg tr a))
    (he : e ∈ persists (outputsAt cfg tr b)) (hr : e.2.round ≤ y.2.round) :
    ReachesFrom (Live.knownBlock cfg H tr) y.1 e.1 := by
  set E := max a b + 1
  set st := (stateBefore cfg tr E u).store
  have hya := Converge.persist_stored (cfg := cfg) ha hy
  have heb := Converge.persist_stored (cfg := cfg) hb he
  have hga := grows_before (cfg := cfg) (tr := tr) u (show a + 1 ≤ E by omega)
  have hgb := grows_before (cfg := cfg) (tr := tr) u (show b + 1 ≤ E by omega)
  have hyS : y.1 ∈ st.ids := hga.1 hya.1
  have heS : e.1 ∈ st.ids := hgb.1 heb.1
  have hyb : st.blk y.1 = y.2 := by rw [hga.blk hya.1]; exact hya.2
  have heb' : st.blk e.1 = e.2 := by rw [hgb.blk heb.1]; exact heb.2
  have hcy : y.2.creator = u :=
    (Local.authored _ _ _ (cfg.at u) (inputsBefore tr (a + 1) u) y (persists_of_event ha hy)).2
  have hce : e.2.creator = u :=
    (Local.authored _ _ _ (cfg.at u) (inputsBefore tr (b + 1) u) e (persists_of_event hb he)).2
  have hch := chain_before (cfg := cfg) tr u E
  have hreach : ReachesFrom st.blk y.1 e.1 :=
    hch.reach y.1 hyS e.1 heS (by rw [hyb]; exact hcy) (by rw [heb']; exact hce)
      (by rw [hyb, heb']; exact hr)
  have hK : ∀ w ∈ st.ids, Live.knownBlock cfg H tr w = st.blk w := fun w hw =>
    knownBlock_eq hinj (Converge.knownBefore_sub hu E
      ((Converge.inv_before (cfg := cfg) (tr := tr) E u).known w hw))
  exact (reaches_known hK hyS hreach).1

end Chain

/-! ## Timers past the last restart -/

section Timers

variable {T : Finset Validator} {time : ℕ → ℕ} {t_r t₁ : ℕ}

omit [Fintype Validator] in
/-- Resending sets the retry timer. -/
theorem setTimer_mem_resend {s : State Validator BlockId Payload} {n : ℕ} {j : BlockId}
    (ht : s.top = some n) (ho : s.own = some j) :
    Output.setTimer (n - 1) (2 * cfg.timeout (n - 1)) ∈ Node.resend cfg s := by
  simp [Node.resend, ht, ho]

omit [Fintype Validator] in
/-- Resending broadcasts the node's own block at its top. -/
theorem broadcast_mem_resend {s : State Validator BlockId Payload} {n : ℕ} {j : BlockId}
    (ht : s.top = some n) (ho : s.own = some j) :
    Output.broadcast j (s.store.blk j) ∈ Node.resend cfg s := by
  simp [Node.resend, ht, ho]

open Classical in
/-- **The retry timer is set past the last restart**: a reliable node at
round `n` at `s ≥ t_r` set the timer of round `n - 1` at a last event
before `s`, its build of round `n`, a restart or a resend, and that timer
fires twice the round's timeout later. -/
theorem retry_last (hmono : Live.TimeMono tr time) (hup : Live.UpFrom T tr time t_r)
    (hfire : Live.TimersFireUp cfg T tr time t₁) {v : Validator} (hv : v ∈ T) {s n : ℕ}
    (hrs : t_r ≤ s) (hts : (stateAt cfg tr time v s).top = some n)
    (ht₁ : s + 2 * cfg.timeout (n - 1) ≤ t₁) :
    ∃ a f, a < eventsBy tr time s ∧ (tr[a]?.map Prod.fst) = some v ∧
      Output.setTimer (n - 1) (2 * cfg.timeout (n - 1)) ∈ outputsAt cfg tr a ∧
      (∀ a', a < a' → a' < eventsBy tr time s → (tr[a']?.map Prod.fst) = some v →
        Output.setTimer (n - 1) (2 * cfg.timeout (n - 1)) ∉ outputsAt cfg tr a') ∧
      (∀ k, a < k → k ≤ eventsBy tr time s → (stateBefore cfg tr k v).top = some n) ∧
      a < f ∧ tr[f]? = some (v, .timer (n - 1)) ∧ time f = time a + 2 * cfg.timeout (n - 1) := by
  set E := eventsBy tr time s with hE
  change (stateBefore cfg tr E v).top = some n at hts
  let P : ℕ → Prop := fun a =>
    (tr[a]?.map Prod.fst) = some v ∧
      Output.setTimer (n - 1) (2 * cfg.timeout (n - 1)) ∈ outputsAt cfg tr a
  -- the build of round `n` set the timer
  obtain ⟨b, hbE, hbv, e, hep, her⟩ := built_by (cfg := cfg) (tr := tr) E
    (by rw [hts]; rfl) (show n ≤ _ by rw [hts]; rfl)
  obtain ⟨inpb, hb⟩ := Converge.event_of_map hbv
  have hPb : P b := ⟨hbv, by have := timer_of_persist hb hep; rwa [her] at this⟩
  -- the last event before `E` that set it
  set a := Nat.findGreatest P (E - 1) with ha
  have hPa : P a := Nat.findGreatest_spec (P := P) (m := b) (by omega) hPb
  have hba : b ≤ a := Nat.le_findGreatest (by omega) hPb
  have haE : a < E := lt_of_le_of_lt (Nat.findGreatest_le (E - 1)) (by omega)
  have hmax : ∀ a', a < a' → a' < E → ¬ P a' := fun a' h₁ h₂ =>
    Nat.findGreatest_is_greatest h₁ (by omega)
  obtain ⟨inpa, hai⟩ := Converge.event_of_map hPa.1
  have hal : a < tr.length := (List.getElem?_eq_some_iff.mp hai).1
  have hta : time a ≤ s := (lt_eventsBy hmono hal).mp haE
  -- the node is at round `n` from it to `E`
  obtain ⟨t₀, ht₀, hbt₀⟩ := built_le_top hb hep
  have hat : ∀ k, b < k → k ≤ E → (stateBefore cfg tr k v).top = some n := by
    intro k hbk hkE
    have hr := rises_before (cfg := cfg) (tr := tr) v (show b + 1 ≤ k by omega)
    refine top_between (cfg := cfg) hkE (hr.2.1 (by rw [ht₀]; rfl)) ?_ hts
    have := hr.1
    rw [ht₀] at this; simp only [Option.getD_some] at this; omega
  -- no restart after it
  have hnr : ∀ k, a < k → time k ≤ time a + 2 * cfg.timeout (n - 1) →
      tr[k]? ≠ some (v, .restart) := by
    intro k hak _ hk
    have hkl : k < tr.length := (List.getElem?_eq_some_iff.mp hk).1
    by_cases hkE : k < E
    · -- a restart before `E` would set the timer again
      have htk := hat k (by omega) (by omega)
      obtain ⟨j, hj, -⟩ := ownTop_before (cfg := cfg) (tr := tr) (v := v) k n htk
      refine hmax k hak hkE ⟨by rw [hk]; rfl, ?_⟩
      rw [outputsAt_eq hk]
      exact List.mem_append_left _ (setTimer_mem_resend (cfg := cfg.at v) htk hj)
    · have := hup k v hk hv
      have := (lt_eventsBy hmono hkl).not.mp hkE
      omega
  obtain ⟨f, haf, hf, htf⟩ :=
    hfire a v inpa hai hv (n - 1) (2 * cfg.timeout (n - 1)) hPa.2 (by omega) hnr
  exact ⟨a, f, haE, hPa.1, hPa.2, fun a' h₁ h₂ h₃ h₄ => hmax a' h₁ h₂ ⟨h₃, h₄⟩,
    fun k hak hkE => hat k (by omega) hkE, haf, hf, htf⟩

/-- **A reliable node sends one of its blocks again past the last
restart**: at round `m` at `t₀ ≥ t_r`, it broadcasts a block of its own of
round `m` or above after `t₀` and within twice the timeout of round
`m - 1`. When the retry timer fires, it builds above `m`, or resends its round-`m`
block, or it built above `m` before. -/
theorem sends_again (hmono : Live.TimeMono tr time) (hup : Live.UpFrom T tr time t_r)
    (hfire : Live.TimersFireUp cfg T tr time t₁) {u : Validator} (hu : u ∈ T) {t₀ m : ℕ}
    (hrt : t_r ≤ t₀) (hts : (stateAt cfg tr time u t₀).top = some m)
    (ht₁ : t₀ + 2 * cfg.timeout (m - 1) ≤ t₁) :
    ∃ k inp y, tr[k]? = some (u, inp) ∧ t₀ < time k ∧ time k ≤ t₀ + 2 * cfg.timeout (m - 1) ∧
      y ∈ broadcasts (outputsAt cfg tr k) ∧ m ≤ y.2.round ∧ y.2.creator = u := by
  obtain ⟨a, f, haE, -, -, hmax, hat, haf, hf, htf⟩ := retry_last hmono hup hfire hu hrt hts ht₁
  set E := eventsBy tr time t₀ with hE
  have hal : a < tr.length := lt_of_lt_of_le haE (eventsBy_le_length t₀)
  have hta : time a ≤ t₀ := (lt_eventsBy hmono hal).mp haE
  have hfl : f < tr.length := (List.getElem?_eq_some_iff.mp hf).1
  change (stateBefore cfg tr E u).top = some m at hts
  -- the node after its timer's event
  have hsucc : stateBefore cfg tr (f + 1) u =
      (Node.step (cfg.at u) (stateBefore cfg tr f u) (.timer (m - 1))).1 := by
    rw [stateBefore_succ hf, if_pos rfl]
  -- the step of the timer, when the node stays at `m`, resends
  have hres : (stateBefore cfg tr f u).top = some m → (stateBefore cfg tr (f + 1) u).top = some m →
      (∃ j, (stateBefore cfg tr (f + 1) u).own = some j ∧
        ((stateBefore cfg tr (f + 1) u).store.blk j).round = m ∧
        ((stateBefore cfg tr (f + 1) u).store.blk j).creator = u ∧
        Output.setTimer (m - 1) (2 * cfg.timeout (m - 1)) ∈ outputsAt cfg tr f ∧
        Output.broadcast j ((stateBefore cfg tr (f + 1) u).store.blk j) ∈ outputsAt cfg tr f) := by
    intro h₁ h₂
    obtain ⟨j, hj, -, hjr, hjc⟩ := ownTop_before (cfg := cfg) (tr := tr) (v := u) (f + 1) m h₂
    have h₂' := h₂
    rw [hsucc, step_timer_fst] at h₂'
    have hout : outputsAt cfg tr f =
        (Node.settle (cfg.at u) { stateBefore cfg tr f u with
          fired := insert (m - 1) (stateBefore cfg tr f u).fired }).2 ++
        Node.resend (cfg.at u) (Node.settle (cfg.at u) { stateBefore cfg tr f u with
          fired := insert (m - 1) (stateBefore cfg tr f u).fired }).1 := by
      have hm : (stateBefore cfg tr f u).top = some (m - 1) ∨
          (stateBefore cfg tr f u).top = some (m - 1 + 1) := by
        rcases Nat.eq_zero_or_pos m with h0 | hpos
        · left; rw [h₁, h0]
        · right; rw [h₁, Nat.sub_add_cancel hpos]
      rw [outputsAt_eq hf]
      simp only [Node.step]
      rw [if_pos ⟨h₂'.trans h₁.symm, hm⟩]
    have hsame : stateBefore cfg tr (f + 1) u = (Node.settle (cfg.at u)
        { stateBefore cfg tr f u with
          fired := insert (m - 1) (stateBefore cfg tr f u).fired }).1 := by
      rw [hsucc, step_timer_fst]
    refine ⟨j, hj, hjr, hjc, ?_, ?_⟩
    · rw [hout]
      refine List.mem_append_right _ ?_
      rw [← hsame]
      exact setTimer_mem_resend (cfg := cfg.at u) h₂ hj
    · rw [hout]
      refine List.mem_append_right _ ?_
      rw [← hsame]
      exact broadcast_mem_resend (cfg := cfg.at u) h₂ hj
  -- the timer fires after `t₀`: before, the node would have set it again
  have hfE : E ≤ f := by
    by_contra hlt
    have h₁ := hat f haf (by omega)
    have h₂ := hat (f + 1) (by omega) (by omega)
    obtain ⟨-, -, -, -, hset, -⟩ := hres h₁ h₂
    exact hmax f haf (by omega) (by rw [hf]; rfl) hset
  have htf₀ : t₀ < time f := by
    by_contra h
    have : f < E := (lt_eventsBy hmono hfl).mpr (by omega)
    omega
  have hfle : time f ≤ t₀ + 2 * cfg.timeout (m - 1) := by omega
  -- the node at the timer's event is at `m` or above
  have hsf : (stateBefore cfg tr f u).top.isSome ∧ m ≤ (stateBefore cfg tr f u).top.getD 0 := by
    obtain ⟨h₁, h₂, -⟩ := rises_before (cfg := cfg) (tr := tr) u hfE
    rw [hts] at h₁ h₂
    exact ⟨h₂ rfl, by simpa using h₁⟩
  have hcre : ∀ {k inp} {y : BlockId × Block Validator BlockId Payload},
      tr[k]? = some (u, inp) → y ∈ persists (outputsAt cfg tr k) → y.2.creator = u :=
    fun hk hy => (Local.authored _ _ _ (cfg.at u) _ _ (persists_of_event hk hy)).2
  by_cases hfm : (stateBefore cfg tr f u).top = some m
  · by_cases hstay : (stateBefore cfg tr (f + 1) u).top = some m
    · -- it resends its round-`m` block
      obtain ⟨j, -, hjr, hjc, -, hb⟩ := hres hfm hstay
      exact ⟨f, _, (j, (stateBefore cfg tr (f + 1) u).store.blk j), hf, htf₀, hfle,
        mem_broadcasts.mpr hb, by simp [hjr], hjc⟩
    · -- it builds above `m`
      obtain ⟨h₁, h₂, -⟩ := rises_before (cfg := cfg) (tr := tr) u (show f ≤ f + 1 by omega)
      rw [hfm] at h₁ h₂
      obtain ⟨t, ht⟩ := Option.isSome_iff_exists.mp (h₂ rfl)
      have hmt : m + 1 ≤ t := by
        have := h₁; rw [ht] at this; simp only [Option.getD_some] at this
        have : t ≠ m := fun h => hstay (by rw [ht, h])
        omega
      rw [hsucc] at ht
      obtain ⟨e, hep, her⟩ := step_every (cfg := cfg.at u) (s := stateBefore cfg tr f u)
        (inp := .timer (m - 1)) (by rw [ht]; rfl) (m + 1) (Or.inr (by rw [hfm]; simp))
        (by rw [ht]; simpa using hmt)
      rw [← outputsAt_eq hf] at hep
      exact ⟨f, _, e, hf, htf₀, hfle, broadcasts_of_persists hep, by omega, hcre hf hep⟩
  · -- it built above `m` after `t₀`, before its timer fired
    have hmf : m + 1 ≤ (stateBefore cfg tr f u).top.getD 0 := by
      obtain ⟨t, ht⟩ := Option.isSome_iff_exists.mp hsf.1
      have h₂ := hsf.2
      rw [ht] at h₂ ⊢
      simp only [Option.getD_some] at h₂ ⊢
      have : t ≠ m := fun h => hfm (by rw [ht, h])
      omega
    obtain ⟨b', hb'f, hb'u, e, hep, her⟩ := built_by (cfg := cfg) (tr := tr) f hsf.1 hmf
    obtain ⟨inpb, hb'⟩ := Converge.event_of_map hb'u
    have hb'l : b' < tr.length := (List.getElem?_eq_some_iff.mp hb').1
    have hEb : E ≤ b' := by
      by_contra hlt
      obtain ⟨t, ht, het⟩ := built_le_top hb' hep
      have hr := (rises_before (cfg := cfg) (tr := tr) u (show b' + 1 ≤ E by omega)).1
      rw [ht, hts] at hr
      simp only [Option.getD_some] at hr
      omega
    have htb : t₀ < time b' := by
      by_contra h
      have : b' < E := (lt_eventsBy hmono hb'l).mpr (by omega)
      omega
    have := hmono b' f hb'f.le hfl
    exact ⟨b', _, e, hb', htb, by omega, broadcasts_of_persists hep, by omega, hcre hb' hep⟩

end Timers

/-! ## Arrival past the recovery -/

section Arrival

variable {P : Validity Validator BlockId Payload} {H T : Finset Validator} {time : ℕ → ℕ}
  {gst Δ Δₛ t_r t₁ : ℕ}

/-- **Reliable blocks arrive past the recovery**: with the reliable nodes
up from `t_r` on, a reliable block built at `s` is held by every other
reliable node by `max s G + Δ + Δₛ`, for `G = max t_r gst + W` and `W`
twice the largest timeout of the round below the one a reliable node is
at by `max t_r gst`. A
block built from `t_r` on is delivered and synchronised as before; one
built earlier lies in the history of a block its author sends again
within `W` (`sends_again`), which is delivered and synchronised, and its
author's blocks reach each other (`own_reaches`). -/
theorem arrival_of_recovered (hσ : cfg.σ = boundedSel) (hadm : cfg.Admissible)
    (hf : Hᶜ.card ≤ cfg.f) (hid : Function.Injective cfg.idOf)
    (htime : Converge.TimelyAuthentic cfg H tr) (hinj : Converge.HashInjective cfg H tr)
    (hTH : T ⊆ H) (hmono : Live.TimeMono tr time)
    (hdel : Live.DeliveredFrom cfg T tr time gst Δ t_r t₁)
    (hsync : Live.SyncedFrom cfg H T tr time gst Δₛ t_r t₁) (hup : Live.UpFrom T tr time t_r)
    (hfire : Live.TimersFireUp cfg T tr time t₁) (hstart : Live.StartedBy T tr time gst) :
    Arrival cfg T tr time
      (max t_r gst + T.sup fun u => 2 * cfg.timeout (topAt cfg tr time u (max t_r gst) - 1))
      (Δ + Δₛ) t₁ := by
  intro u hu v hv huv b inp hb e hep s τ htb hτ ht₁
  set t₀ := max t_r gst with ht₀
  set W := T.sup fun u => 2 * cfg.timeout (topAt cfg tr time u t₀ - 1) with hW
  have hbl : b < tr.length := (List.getElem?_eq_some_iff.mp hb).1
  -- a block of `u` delivered to `v` at `j`, from `t_r` on, is held by `τ`
  have hheld : ∀ {q k j : ℕ} {inpq : Input Validator BlockId Payload}
      {y : BlockId × Block Validator BlockId Payload},
      tr[q]? = some (u, inpq) → y ∈ persists (outputsAt cfg tr q) →
      tr[j]? = some (v, .deliver y.1 y.2) → k < j → t_r ≤ time k →
      max (time j) gst + Δₛ ≤ τ → y.1 ∈ (stateAt cfg tr time v τ).store.ids := by
    intro q k j inpq y hq hyq hj hkj hrk hjτ
    have hjl : j < tr.length := (List.getElem?_eq_some_iff.mp hj).1
    have hjr : t_r ≤ time j := hrk.trans (hmono k j hkj.le hjl)
    have hgood := ((Converge.inv_before (cfg := cfg) (tr := tr) (q + 1) u).good y
      (persists_of_event hq hyq)).2.1
    by_cases hn0 : y.2.round = 0
    · exact arrives_zero hinj hTH hmono hu hv huv (by rw [hq]; rfl) hyq hgood hn0 hj (by omega)
    · obtain ⟨x, y', o, hx, hxb, heo, -⟩ := build_witness hσ hadm hf htime hinj (hTH hu) hq hyq hn0
      exact arrives hinj htime hTH hmono hsync hu hv huv hq hyq hx hxb heo hj hjr hjτ (by omega)
  have hsend : ∀ {k : ℕ} {inpk : Input Validator BlockId Payload}
      {y : BlockId × Block Validator BlockId Payload}, tr[k]? = some (u, inpk) →
      y ∈ broadcasts (outputsAt cfg tr k) → t_r ≤ time k → max (time k) gst + Δ ≤ t₁ →
      ∃ j, k < j ∧ tr[j]? = some (v, .deliver y.1 y.2) ∧ time j ≤ max (time k) gst + Δ :=
    fun hk hy hrk ht => hdel _ u _ hk hu hrk (v, .deliver _ _)
      ⟨.broadcast _ _, mem_broadcasts.mp hy, Ne.symm huv, rfl⟩ hv ht
  by_cases hbr : t_r ≤ time b
  · -- built from `t_r` on: delivered and synchronised
    obtain ⟨j, hbj, hj, htj⟩ := hsend hb (broadcasts_of_persists hep) hbr (by omega)
    exact hheld hb hep hj hbj hbr (by omega)
  · -- built before: in the history of a block `u` sends again
    have hus : (stateAt cfg tr time u t₀).top.isSome :=
      started_at hadm hid htime hTH hmono hstart hu (le_max_right _ _)
    obtain ⟨m, hm⟩ := Option.isSome_iff_exists.mp hus
    have htm : topAt cfg tr time u t₀ = m := by unfold topAt; rw [hm]; rfl
    have hem : e.2.round ≤ m := by
      have := (top_of_built hmono hb hep (τ := t₀) (by omega)).2
      rw [htm] at this; exact this
    have hmW : 2 * cfg.timeout (m - 1) ≤ W := by
      rw [← htm]
      exact Finset.le_sup (f := fun u => 2 * cfg.timeout (topAt cfg tr time u t₀ - 1)) hu
    obtain ⟨k, inpk, y, hk, htk, hkle, hyb, hym, hyc⟩ :=
      sends_again hmono hup hfire hu (le_max_left _ _) hm (by omega)
    obtain ⟨q, hqk, inpq, hq, hyq⟩ := Converge.persists_of_broadcasts hk hyb
    obtain ⟨j, hkj, hj, htj⟩ := hsend hk hyb (by omega) (by omega)
    have hyin := hheld hq hyq hj hkj (by omega) (by omega)
    have hreach := own_reaches hinj (hTH hu) hq hb hyq hep (hem.trans hym)
    set Z := stateBefore cfg tr (eventsBy tr time τ) v
    have hK : ∀ w ∈ Z.store.ids, Live.knownBlock cfg H tr w = Z.store.blk w := fun w hw =>
      knownBlock_eq hinj (Converge.knownBefore_sub (hTH hv) _
        ((Converge.inv_before (cfg := cfg) (tr := tr) _ v).known w hw))
    exact mem_of_reaches_known hK hyin hreach

end Arrival

end Node

end LeanDag
