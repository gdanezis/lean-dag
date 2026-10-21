import LeanDag.Node.Helpers.Reliable
/-!
# Holding a history under a rising horizon

`docs/validator.md` §13.2. A store agrees with a map `g` of the blocks on
their rounds and authors (`AgreesWith`), which pruning keeps. A block
delivered at or above the horizon stays stored, pending or below the
horizon (`Stays`) from then on, since a pending block is accepted only
when ready and then always. A settled node then holds every block of a
set closed under references at or above its horizon, once each stays
and is ready when its references are accepted (`holds_of_stays`).
-/

namespace LeanDag

namespace Node

variable {Validator BlockId Payload : Type} [Fintype Validator] [DecidableEq Validator]
variable [LinearOrder BlockId]
variable {cfg : Config Validator BlockId Payload}

variable (g : BlockId → Block Validator BlockId Payload)

/-- **A store agreeing with `g`** on the rounds and authors of its blocks. -/
def AgreesWith (st : Store Validator BlockId Payload) : Prop :=
  ∀ j ∈ st.ids, (st.blk j).round = (g j).round ∧ (st.blk j).creator = (g j).creator

/-- **A block agreeing with `g`** under its identifier. -/
def Agrees (y : BlockId × Block Validator BlockId Payload) : Prop :=
  (g y.1).round = y.2.round ∧ (g y.1).creator = y.2.creator

/-- **A block that stays**: stored, pending, or below the horizon. -/
def Stays (st : Store Validator BlockId Payload)
    (pend : List (BlockId × Block Validator BlockId Payload))
    (y : BlockId × Block Validator BlockId Payload) : Prop :=
  y.1 ∈ st.ids ∨ y ∈ pend ∨ y.2.round < st.base

variable {g}

/-! ## Agreeing with `g` -/

omit [Fintype Validator] in
theorem AgreesWith.accept {st : Store Validator BlockId Payload} (h : AgreesWith g st)
    {id : BlockId} {b : Block Validator BlockId Payload} (hb : Agrees g (id, b)) :
    AgreesWith g (Node.accept cfg st id b) := by
  unfold Node.accept
  split
  · rename_i hc
    intro j hj
    change j ∈ Insert.insert id st.ids at hj
    by_cases hj' : j = id
    · subst hj'
      simp only [Store.blk, lookup, Store.insert, Std.TreeMap.getD_insert_self, atBase_round,
        atBase_creator]
      exact ⟨hb.1.symm, hb.2.symm⟩
    · have := Grows.blk (Grows.insert st (hnew := hc.1) (hab := hc.2.1) (hrefs := hc.2.2.1)
        (hpred := hc.2.2.2.1)) rfl ((Finset.mem_insert.mp hj).resolve_left hj')
      rw [this]
      exact h j ((Finset.mem_insert.mp hj).resolve_left hj')
  · exact h

omit [Fintype Validator] [DecidableEq Validator] in
theorem AgreesWith.insert {st : Store Validator BlockId Payload} (h : AgreesWith g st)
    {id : BlockId} {b : Block Validator BlockId Payload} (hb : Agrees g (id, b)) {hnew hab hrefs hpred} :
    AgreesWith g (st.insert id b hnew hab hrefs hpred) := by
  intro j hj
  change j ∈ Insert.insert id st.ids at hj
  by_cases hj' : j = id
  · subst hj'
    simp only [Store.blk, lookup, Store.insert, Std.TreeMap.getD_insert_self, atBase_round,
      atBase_creator]
    exact ⟨hb.1.symm, hb.2.symm⟩
  · have := Grows.blk (Grows.insert st (hnew := hnew) (hab := hab) (hrefs := hrefs)
      (hpred := hpred)) rfl ((Finset.mem_insert.mp hj).resolve_left hj')
    rw [this]
    exact h j ((Finset.mem_insert.mp hj).resolve_left hj')

omit [Fintype Validator] in
theorem AgreesWith.foldl : ∀ (l : List (BlockId × Block Validator BlockId Payload))
    {st : Store Validator BlockId Payload}, AgreesWith g st → (∀ e ∈ l, Agrees g e) →
    AgreesWith g (l.foldl (fun s e => Node.accept cfg s e.1 e.2) st)
  | [], _, h, _ => h
  | e :: l, _, h, hl =>
    AgreesWith.foldl l (h.accept (hl e List.mem_cons_self))
      fun x hx => hl x (List.mem_cons_of_mem _ hx)

omit [Fintype Validator] in
theorem AgreesWith.flush : ∀ (fuel : ℕ) {st : Store Validator BlockId Payload}
    {pend : List (BlockId × Block Validator BlockId Payload)}, AgreesWith g st →
    (∀ e ∈ pend, Agrees g e) → AgreesWith g (Node.flush cfg fuel st pend).1
  | 0, _, _, h, _ => h
  | fuel + 1, st, pend, h, hp => by
    unfold Node.flush
    dsimp only
    split
    · exact h
    · rw [List.partition_eq_filter_filter]
      exact AgreesWith.flush fuel (h.foldl _ fun e he => hp e (List.mem_filter.mp he).1)
        fun e he => hp e (List.mem_filter.mp he).1

omit [Fintype Validator] [DecidableEq Validator] in
theorem AgreesWith.prune {st : Store Validator BlockId Payload} (h : AgreesWith g st) {G : ℕ}
    (hG : st.base ≤ G) : AgreesWith g (st.prune G hG) := by
  intro j hj
  have hj' := Finset.mem_filter.mp hj
  have hjr : G ≤ (st.blk j).round := by simpa [Store.blk, lookup] using hj'.2
  refine ⟨by rw [prune_blk_round _ hG hjr]; exact (h j hj'.1).1, ?_⟩
  simp only [Store.blk, Store.prune, lookup, atBase_creator]
  rw [treeMap_getD_filter_of (by simpa [Store.blk, lookup] using hjr)]
  have := (h j hj'.1).2
  simpa [Store.blk, lookup] using this

/-! ## Accepting a ready block -/

omit [Fintype Validator] in
/-- **`accept` takes a block when it is ready**, at or above the horizon. -/
theorem accept_takes {st : Store Validator BlockId Payload}
    {y : BlockId × Block Validator BlockId Payload} (hr : ready cfg st y = true)
    (hb : st.base ≤ y.2.round) : y.1 ∈ (Node.accept cfg st y.1 y.2).ids := by
  unfold Node.accept
  by_cases hin : y.1 ∈ st.ids
  · split
    · exact Finset.mem_insert_self _ _
    · exact hin
  · simp only [ready, Bool.or_eq_true, decide_eq_true_eq] at hr
    rcases Nat.lt_or_ge st.base y.2.round with hlt | hle
    · obtain hr | ⟨h₁, h₂, h₃⟩ := hr
      · omega
      · rw [dif_pos ⟨hin, hb, fun _ => h₁, fun _ => h₂, fun _ => h₃⟩]
        exact Finset.mem_insert_self _ _
    · rw [dif_pos ⟨hin, hb, fun h => absurd h (by omega), fun h => absurd h (by omega),
        fun h => absurd h (by omega)⟩]
      exact Finset.mem_insert_self _ _

/-! ## Staying through a flush -/

omit [Fintype Validator] in
/-- **A fold of ready blocks takes each**, on a store agreeing with `g`. -/
theorem foldl_takes_under : ∀ (l : List (BlockId × Block Validator BlockId Payload))
    {st : Store Validator BlockId Payload} {y : BlockId × Block Validator BlockId Payload},
    AgreesWith g st → (∀ e ∈ l, Agrees g e) → ready cfg st y = true →
    st.base ≤ y.2.round →
    (y ∈ l ∨ y.1 ∈ st.ids) → y.1 ∈ (l.foldl (fun s e => Node.accept cfg s e.1 e.2) st).ids
  | [], _, _, _, _, _, _, h => by
    rcases h with h | h
    · exact absurd h List.not_mem_nil
    · exact h
  | e :: l, st, y, hA, hl, hr, hb, h => by
    simp only [List.foldl_cons]
    have hg := Grows.accept (cfg := cfg) st e.1 e.2
    have hb' := accept_base (cfg := cfg) st e.1 e.2
    refine foldl_takes_under l (hA.accept (hl e List.mem_cons_self))
      (fun x hx => hl x (List.mem_cons_of_mem _ hx)) (ready_mono hg hb' hr)
      (by rw [hb']; exact hb) ?_
    rcases h with h | h
    · rcases List.mem_cons.mp h with rfl | h
      · exact Or.inr (accept_takes hr hb)
      · exact Or.inl h
    · exact Or.inr ((hg.2 hb').1 h)

omit [Fintype Validator] in
/-- **A flush keeps a block stored or pending**, at or above the horizon,
on a store agreeing with `g`. -/
theorem flush_stays : ∀ (fuel : ℕ) {st : Store Validator BlockId Payload}
    {pend : List (BlockId × Block Validator BlockId Payload)}
    {y : BlockId × Block Validator BlockId Payload},
    AgreesWith g st → (∀ e ∈ pend, Agrees g e) → Agrees g y → st.base ≤ y.2.round →
    (y.1 ∈ st.ids ∨ y ∈ pend) →
    y.1 ∈ (Node.flush cfg fuel st pend).1.ids ∨ y ∈ (Node.flush cfg fuel st pend).2
  | 0, _, _, _, _, _, _, _, h => h
  | fuel + 1, st, pend, y, hA, hp, hy, hb, h => by
    unfold Node.flush
    dsimp only
    split
    · exact h
    · rw [List.partition_eq_filter_filter]
      set rd := pend.filter fun e => ready cfg st e
      have hg := Grows.foldl (cfg := cfg) rd st
      have hb' := foldl_base (cfg := cfg) rd st
      have hfold : y.1 ∈ (rd.foldl (fun s e => Node.accept cfg s e.1 e.2) st).ids ∨
          y ∈ pend.filter (not ∘ fun e => ready cfg st e) := by
        by_cases hry : ready cfg st y = true
        · left
          refine foldl_takes_under rd hA (fun e he => hp e (List.mem_filter.mp he).1) hry hb ?_
          rcases h with h | h
          · exact Or.inr h
          · exact Or.inl (List.mem_filter.mpr ⟨h, hry⟩)
        · rcases h with h | h
          · exact Or.inl ((hg.2 hb').1 h)
          · right
            refine List.mem_filter.mpr ⟨h, ?_⟩
            simp only [Function.comp_apply, Bool.not_eq_true'] at hry ⊢
            simp [hry]
      exact flush_stays fuel (hA.foldl _ fun e he => hp e (List.mem_filter.mp he).1)
        (fun e he => hp e (List.mem_filter.mp he).1) hy (by rw [hb']; exact hb) hfold

/-! ## Staying through a pass -/

omit [Fintype Validator] in
theorem AgreesWith.progress : ∀ (fuel : ℕ) {s : State Validator BlockId Payload},
    AgreesWith g s.store → (∀ e ∈ persists (Node.progress cfg fuel s).2, Agrees g e) →
    AgreesWith g (Node.progress cfg fuel s).1.store
  | 0, _, h, _ => h
  | fuel + 1, s, h, hK => by
    rcases hb : Node.tryBuild cfg s with _ | ⟨s₁, out⟩
    · simp only [Node.progress, hb]; exact h
    · simp only [Node.progress, hb] at hK ⊢
      rw [persists_append] at hK
      obtain ⟨r, id, b, hnew, hab, hrefs, hpred, -, -, -, -, -, hst, -, -, -, hout⟩ :=
        tryBuild_some hb
      have hyb : Agrees g (id, b) := hK _ (List.mem_append_left _ (by rw [hout]; simp [built,
        persists]))
      refine AgreesWith.progress fuel ?_ fun e he => hK e (List.mem_append_right _ he)
      rw [hst]
      intro j hj
      change j ∈ Insert.insert id s.store.ids at hj
      by_cases hj' : j = id
      · subst hj'
        simp only [Store.blk, lookup, Store.insert, Std.TreeMap.getD_insert_self, atBase_round,
          atBase_creator]
        exact ⟨hyb.1.symm, hyb.2.symm⟩
      · have := Grows.blk (Grows.insert s.store (hnew := hnew) (hab := hab) (hrefs := hrefs)
          (hpred := hpred)) rfl ((Finset.mem_insert.mp hj).resolve_left hj')
        rw [this]
        exact h j ((Finset.mem_insert.mp hj).resolve_left hj')

omit [Fintype Validator] in
/-- **Collecting** keeps the store agreeing with `g`, the pending blocks,
and a block staying. -/
theorem collect_stays {s : State Validator BlockId Payload} (hA : AgreesWith g s.store)
    {y : BlockId × Block Validator BlockId Payload} (hy : Agrees g y)
    (hst : Stays s.store s.pending y) :
    AgreesWith g (Node.collect cfg s).1.store ∧
      (∀ e ∈ (Node.collect cfg s).1.pending, e ∈ s.pending) ∧
      Stays (Node.collect cfg s).1.store (Node.collect cfg s).1.pending y := by
  unfold Node.collect
  split
  · rename_i t ht
    dsimp only
    split
    · rename_i hG
      set G := horizonAt cfg s t
      refine ⟨hA.prune hG.le, fun e he => (List.mem_filter.mp he).1, ?_⟩
      rcases hst with h | h | h
      · by_cases hr : G ≤ (s.store.blk y.1).round
        · exact Or.inl ((mem_prune_ids (hG := hG.le)).mpr ⟨h, hr⟩)
        · right; right
          change y.2.round < G
          have := (hA y.1 h).1
          rw [hy.1] at this
          omega
      · by_cases hr : G ≤ y.2.round
        · exact Or.inr (Or.inl (List.mem_filter.mpr ⟨h, decide_eq_true hr⟩))
        · exact Or.inr (Or.inr (by change y.2.round < G; omega))
      · exact Or.inr (Or.inr (by change y.2.round < G; omega))
    · exact ⟨hA, fun e he => he, hst⟩
  · exact ⟨hA, fun e he => he, hst⟩

omit [Fintype Validator] in
/-- **A pass keeps a block staying**, the store agreeing with `g` and the
pending and built blocks too. -/
theorem advance_stays {x : State Validator BlockId Payload} (hA : AgreesWith g x.store)
    (hP : ∀ e ∈ x.pending, Agrees g e) (hO : ∀ e ∈ persists (Node.advance cfg x).2, Agrees g e)
    {y : BlockId × Block Validator BlockId Payload} (hy : Agrees g y)
    (hst : Stays x.store x.pending y) :
    AgreesWith g (Node.advance cfg x).1.store ∧ (∀ e ∈ (Node.advance cfg x).1.pending, Agrees g e) ∧
      Stays (Node.advance cfg x).1.store (Node.advance cfg x).1.pending y := by
  simp only [Node.advance] at hO ⊢
  rw [persists_append, persists_append, decideStep_persist, collect_persist, List.append_nil,
    List.append_nil] at hO
  have hA₁ := AgreesWith.progress (cfg := cfg) (x.store.topRound + 2) hA hO
  have hg₁ := (Grows.progress (cfg := cfg) (x.store.topRound + 2) x).1
  have hb₁ := progress_base (cfg := cfg) (x.store.topRound + 2) x
  have hp₁ := (progress_pending (cfg := cfg) (x.store.topRound + 2) x).1
  generalize Node.progress cfg (x.store.topRound + 2) x = r at hA₁ hg₁ hb₁ hp₁ ⊢
  have hst₁ : Stays r.1.store r.1.pending y := by
    rcases hst with h | h | h
    · exact Or.inl ((hg₁.2 hb₁).1 h)
    · exact Or.inr (Or.inl (hp₁ ▸ h))
    · exact Or.inr (Or.inr (by rw [hb₁]; exact h))
  have hd := decideStep_store (cfg := cfg) r.1
  have hdp := (decideStep_pending (cfg := cfg) r.1).1
  obtain ⟨hA₃, hp₃, hst₃⟩ := collect_stays (cfg := cfg) (s := (Node.decideStep cfg r.1).1)
    (by rw [hd]; exact hA₁) hy (by rw [hd, hdp]; exact hst₁)
  have hb₃ : x.store.base ≤ (Node.collect cfg (Node.decideStep cfg r.1).1).1.store.base := by
    have := (Grows.collect (cfg := cfg) (Node.decideStep cfg r.1).1).1
    rw [hd, hb₁] at this; exact this
  generalize Node.collect cfg (Node.decideStep cfg r.1).1 = c at hA₃ hp₃ hst₃ hb₃ ⊢
  have hpc : ∀ e ∈ c.1.pending, Agrees g e := fun e he => hP e (by
    have := hp₃ e he; rwa [hdp, hp₁] at this)
  refine ⟨AgreesWith.flush _ hA₃ hpc,
    fun e he => hpc e (flush_pending_sub (cfg := cfg) _ _ _ e he), ?_⟩
  have hfb := flush_base (cfg := cfg) (c.1.pending.length + 1) c.1.store c.1.pending
  by_cases hlt : y.2.round < c.1.store.base
  · exact Or.inr (Or.inr (by rw [hfb]; exact hlt))
  · rcases hst₃ with h | h | h
    · exact (flush_stays _ hA₃ hpc hy (not_lt.mp hlt) (Or.inl h)).imp id Or.inl
    · exact (flush_stays _ hA₃ hpc hy (not_lt.mp hlt) (Or.inr h)).imp id Or.inl
    · exact absurd h hlt

omit [Fintype Validator] in
theorem quiesce_stays {y : BlockId × Block Validator BlockId Payload} (hy : Agrees g y) :
    ∀ (n : ℕ) {x : State Validator BlockId Payload}, AgreesWith g x.store →
    (∀ e ∈ x.pending, Agrees g e) → (∀ e ∈ persists (quiesce cfg n x).2, Agrees g e) →
    Stays x.store x.pending y →
    AgreesWith g (quiesce cfg n x).1.store ∧ (∀ e ∈ (quiesce cfg n x).1.pending, Agrees g e) ∧
      Stays (quiesce cfg n x).1.store (quiesce cfg n x).1.pending y
  | 0, x, hA, hP, _, hst => ⟨hA, hP, hst⟩
  | n + 1, x, hA, hP, hO, hst => by
    rcases quiesce_succ_cases (cfg := cfg) n x with he | he <;> rw [he] at hO ⊢
    · exact advance_stays hA hP hO hy hst
    · rw [persists_append] at hO
      obtain ⟨hA₁, hP₁, hst₁⟩ := advance_stays hA hP
        (fun e he => hO e (List.mem_append_left _ he)) hy hst
      exact quiesce_stays hy n hA₁ hP₁ (fun e he => hO e (List.mem_append_right _ he)) hst₁

omit [Fintype Validator] in
/-- **A settle keeps a block staying**, the store agreeing with `g` and
the pending and built blocks too. -/
theorem settle_stays {x : State Validator BlockId Payload} (hA : AgreesWith g x.store)
    (hP : ∀ e ∈ x.pending, Agrees g e) (hO : ∀ e ∈ persists (Node.settle cfg x).2, Agrees g e)
    {y : BlockId × Block Validator BlockId Payload} (hy : Agrees g y)
    (hst : Stays x.store x.pending y) :
    Stays (Node.settle cfg x).1.store (Node.settle cfg x).1.pending y := by
  rcases settle_cases (cfg := cfg) x with h | ⟨x₁, hj, h⟩ <;> rw [h] at hO ⊢
  · exact (quiesce_stays hy _ hA hP hO hst).2.2
  · obtain ⟨hst', hpd, -⟩ := tryResume_keeps hj
    refine (quiesce_stays hy _ (by rw [hst']; exact hA) (by rw [hpd]; exact hP) hO
      (by rw [hst', hpd]; exact hst)).2.2

/-! ## Staying through a step -/

/-- **A step keeps a block staying**, of a node not recovering, other than
a restart, without rate limiting, the store agreeing with `g` and the
pending, built and delivered blocks too;
and a delivery of the block, by its hash and of another author, leaves
it staying. -/
theorem step_stays (hl : cfg.limit = none) {s : State Validator BlockId Payload}
    {inp : Input Validator BlockId Payload} (hs : s.recovering = false) (hr : inp ≠ .restart)
    (hA : AgreesWith g s.store) (hP : ∀ e ∈ s.pending, Agrees g e)
    (hD : ∀ id b, inp = .deliver id b → id = cfg.idOf b → Agrees g (id, b))
    (hO : ∀ e ∈ persists (Node.step cfg s inp).2, Agrees g e)
    {y : BlockId × Block Validator BlockId Payload} (hy : Agrees g y)
    (hst : Stays s.store s.pending y ∨ (inp = .deliver y.1 y.2 ∧ y.1 = cfg.idOf y.2 ∧
      y.2.creator ≠ cfg.me ∧ ∀ e ∈ s.pending, e.1 = y.1 → e = y)) :
    Stays (Node.step cfg s inp).1.store (Node.step cfg s inp).1.pending y := by
  -- a step that settles a state whose store and pending blocks keep `y`
  have hset : ∀ (x : State Validator BlockId Payload) (pre : List (Output Validator BlockId Payload)),
      Node.step cfg s inp = ((Node.settle cfg x).1, pre ++ (Node.settle cfg x).2) →
      AgreesWith g x.store → (∀ e ∈ x.pending, Agrees g e) → s.store.base ≤ x.store.base →
      Stays x.store x.pending y → Stays (Node.step cfg s inp).1.store
        (Node.step cfg s inp).1.pending y := by
    intro x pre he hAx hPx hbx hstx
    have hOx : ∀ e ∈ persists (Node.settle cfg x).2, Agrees g e := fun e he' =>
      hO e (by rw [he, persists_append]; exact List.mem_append_right _ he')
    rw [he]
    exact settle_stays hAx hPx hOx hy hstx
  -- the delivered block itself, not acted on, already stays
  have hnot : ∀ (id : BlockId) (b : Block Validator BlockId Payload), inp = .deliver id b →
      ¬ Admits cfg s id b → Stays s.store s.pending y := by
    intro id b hi hna
    rcases hst with hst | ⟨hinp, hid, hcr, huniq⟩
    · exact hst
    · rw [hi] at hinp
      injection hinp with h₁ h₂
      subst h₁ h₂
      have hk : kept cfg s y.1 y.2 = true := by simp [kept, hl]
      by_cases hb : s.store.base ≤ y.2.round
      · by_cases hin : y.1 ∈ s.store.ids
        · exact Or.inl hin
        · by_cases hp : y.1 ∈ s.pending.map Prod.fst
          · obtain ⟨e, he, he1⟩ := List.mem_map.mp hp
            exact Or.inr (Or.inl (huniq e he he1 ▸ he))
          · exact absurd ⟨hid, hcr, hb, hin, hp, hk⟩ hna
      · exact Or.inr (Or.inr (not_le.mp hb))
  cases inp with
  | start =>
    have hst' : Stays s.store s.pending y := hst.elim id fun h => by cases h.1
    by_cases h₁ : s.top = none ∧ cfg.Admissible
    · by_cases h₂ : cfg.idOf cfg.genesis ∉ s.store.ids ∧ s.store.base ≤ cfg.genesis.round ∧
          rowValid cfg.q (Function.update s.store.blk (cfg.idOf cfg.genesis) cfg.genesis)
            cfg.genesis
      · let st := s.store.insert _ _ h₂.1 h₂.2.1 (fun _ => Finset.empty_subset _)
          (fun _ j hj => absurd hj (Finset.notMem_empty j))
        let gid := cfg.idOf cfg.genesis
        let s₀ : State Validator BlockId Payload :=
          { { s with store := st, top := some 0, own := some gid } with
            owner := slotted cfg [(gid, cfg.genesis)] ++ s.owner, recovering := false }
        refine hset s₀ (built cfg [(cfg.idOf cfg.genesis, cfg.genesis)])
          (by simp only [Node.step, dif_pos h₂, if_pos h₁]; rfl) ?_ hP le_rfl ?_
        · exact hA.insert (hnew := h₂.1) (hab := h₂.2.1) (hrefs := fun _ => Finset.empty_subset _)
            (hpred := fun _ j hj => absurd hj (Finset.notMem_empty j))
            (hO _ (by simp only [Node.step, dif_pos h₂, if_pos h₁]; simp [persists]))
        · rcases hst' with h | h | h
          · exact Or.inl (Finset.mem_insert_of_mem h)
          · exact Or.inr (Or.inl h)
          · exact Or.inr (Or.inr h)
      · rw [show (Node.step cfg s .start).1 = s by simp only [Node.step, dif_neg h₂, if_pos h₁]]
        exact hst'
    · rw [show (Node.step cfg s .start).1 = s by simp only [Node.step, if_neg h₁]]
      exact hst'
  | deliver id b =>
    by_cases hAd : Admits cfg s id b
    · set fl := flush cfg (s.pending.length + 1) s.store ((id, b) :: s.pending) with hfl
      have hPf : ∀ e ∈ (id, b) :: s.pending, Agrees g e := fun e he => by
        rcases List.mem_cons.mp he with rfl | he
        · exact hD _ _ rfl hAd.1
        · exact hP e he
      have hb₁ : fl.1.base = s.store.base := flush_base _ _ _
      have hA₁ : AgreesWith g fl.1 := AgreesWith.flush _ hA hPf
      have hP₁ : ∀ e ∈ fl.2, Agrees g e :=
        fun e he => hPf e (flush_pending_sub (cfg := cfg) _ _ _ e he)
      have hy₁ : y.1 ∈ s.store.ids ∨ y ∈ (id, b) :: s.pending ∨ y.2.round < s.store.base := by
        rcases hst with hst | ⟨hinp, -, -, -⟩
        · rcases hst with h | h | h
          · exact Or.inl h
          · exact Or.inr (Or.inl (List.mem_cons_of_mem _ h))
          · exact Or.inr (Or.inr h)
        · injection hinp with h₁ h₂
          have hyb : y = (id, b) := Prod.ext h₁.symm h₂.symm
          exact Or.inr (Or.inl (hyb ▸ List.mem_cons_self))
      have hst₁ : Stays fl.1 fl.2 y := by
        by_cases hlt : y.2.round < s.store.base
        · exact Or.inr (Or.inr (by rw [hb₁]; exact hlt))
        · rcases hy₁ with h | h | h
          · exact (flush_stays _ hA hPf hy (not_lt.mp hlt) (Or.inl h)).imp (fun h => h) Or.inl
          · exact (flush_stays _ hA hPf hy (not_lt.mp hlt) (Or.inr h)).imp (fun h => h) Or.inl
          · exact absurd h hlt
      exact hset _ _ (step_deliver hAd) hA₁ hP₁ hb₁.ge hst₁
    · rw [step_deliver_not_of hAd hs]
      exact hnot id b rfl hAd
  | timer r =>
    exact hset { s with fired := insert r s.fired } (timerAsk s r) (step_timer_eq s r) hA hP le_rfl
      (hst.elim id fun h => by cases h.1)
  | restart => exact absurd rfl hr
  | baseOffer p G bs =>
    simp only [Node.step, hs, Bool.false_eq_true, false_and, if_false]
    exact hst.elim id fun h => by cases h.1
  | baseRequest p => exact hst.elim id fun h => by cases h.1
  | fetchRequest p G ids => exact hst.elim id fun h => by cases h.1
  | decisionRequest p lo => exact hst.elim id fun h => by cases h.1
  | certOffer p c ds =>
    have hst' : Stays s.store s.pending y := hst.elim id fun h => by cases h.1
    rcases certOffer_cases (cfg := cfg) s p c ds with ⟨h₁, -, -⟩ | ⟨l, hcl, ds', -, -, -, he⟩ |
      ⟨l, hcl, -, -, he⟩ | ⟨l, hcl, he⟩
    all_goals try obtain rfl := certs_of_not hcl hs
    · rw [hs] at h₁; cases h₁
    · rw [adopt_eq] at he; exact hset _ _ he hA hP le_rfl hst'
    · exact hset { s with cert := some c, props := above (some c) s.props } [] (by rw [he]; rfl)
        hA hP le_rfl hst'
    · rw [he]; exact hst'
  | announced p c =>
    have hst' : Stays s.store s.pending y := hst.elim id fun h => by cases h.1
    rcases announced_cases (cfg := cfg) s p c with ⟨-, -, he⟩ | he | he
    · exact hset { s with cert := some c, props := above (some c) s.props } [] (by rw [he]; rfl)
        hA hP le_rfl hst'
    · rw [he]; exact hst'
    · rw [he]; exact hst'
  | proposal p k kh =>
    have hst' : Stays s.store s.pending y := hst.elim id fun h => by cases h.1
    by_cases hpm : p ≠ cfg.me
    · refine hset (record cfg s p k kh) ([] : List (Output Validator BlockId Payload))
        (by rw [step_proposal, if_pos hpm]) (by exact hA) (by exact hP)
        (by exact le_rfl) (by exact hst')
    · rw [step_proposal, if_neg hpm]; exact hst'

/-! ## Holding a closed set -/

omit [Fintype Validator] in
/-- **A store holds a set of blocks closed under references** at or above
its horizon, if each of them stays, each is ready once its references
are accepted, and no pending block is ready. -/
theorem holds_of_stays {st : Store Validator BlockId Payload}
    {pend : List (BlockId × Block Validator BlockId Payload)}
    (hnr : ∀ e ∈ pend, ready cfg st e = false) {Z : Finset BlockId}
    (raw : BlockId → Block Validator BlockId Payload)
    (hst : ∀ z ∈ Z, st.base ≤ (raw z).round → Stays st pend (z, raw z))
    (hcl : ∀ z ∈ Z, st.base < (raw z).round → ∀ r ∈ (raw z).refs,
      r ∈ Z ∧ (raw r).round + 1 = (raw z).round)
    (hrd : ∀ z ∈ Z, st.base < (raw z).round → (raw z).refs ⊆ st.ids →
      ready cfg st (z, raw z) = true) :
    ∀ z ∈ Z, st.base ≤ (raw z).round → z ∈ st.ids := by
  suffices h : ∀ n z, z ∈ Z → (raw z).round = st.base + n → z ∈ st.ids from
    fun z hz hb => h ((raw z).round - st.base) z hz (by omega)
  intro n
  induction n with
  | zero =>
    intro z hz hr
    rcases hst z hz (by omega) with h | h | h
    · exact h
    · have := hnr _ h
      simp only [ready, Bool.or_eq_false_iff, decide_eq_false_iff_not] at this
      exact absurd (by omega : (raw z).round ≤ st.base) this.1
    · simp only at h; omega
  | succ n ih =>
    intro z hz hr
    rcases hst z hz (by omega) with h | h | h
    · exact h
    · have hrefs : (raw z).refs ⊆ st.ids := fun r hr' => by
        obtain ⟨hrZ, hrr⟩ := hcl z hz (by omega) r hr'
        exact ih r hrZ (by omega)
      have := hnr _ h
      rw [hrd z hz (by omega) hrefs] at this
      cases this
    · simp only at h; omega

/-! ## Along a trace -/

variable {tr : Trace Validator BlockId Payload} {H : Finset Validator}

theorem agrees_known (hinj : Converge.HashInjective cfg H tr)
    {x : BlockId × Block Validator BlockId Payload} (hx : x ∈ Converge.knownIn cfg H tr) :
    Agrees (Converge.gT cfg H tr) x := by
  unfold Agrees
  rw [Converge.gT_of_known hinj hx]
  simp

theorem agreesWith_before (hinj : Converge.HashInjective cfg H tr) {v : Validator} (hv : v ∈ H)
    (i : ℕ) : AgreesWith (Converge.gT cfg H tr) (stateBefore cfg tr i v).store := by
  intro j hj
  have hk := Converge.knownBefore_sub hv i ((Converge.inv_before (cfg := cfg) i v).known j hj)
  have := agrees_known hinj hk
  simp only [Store.blk, lookup, atBase_round, atBase_creator]
  exact ⟨this.1.symm, this.2.symm⟩

theorem pending_agree_before (hinj : Converge.HashInjective cfg H tr) {v : Validator} (hv : v ∈ H)
    (i : ℕ) : ∀ e ∈ (stateBefore cfg tr i v).pending, Agrees (Converge.gT cfg H tr) e :=
  fun e he => agrees_known hinj
    (Converge.knownBefore_sub hv i ((Converge.inv_before (cfg := cfg) i v).pend e he))

theorem outputs_agree (hinj : Converge.HashInjective cfg H tr) {i : ℕ} {u : Validator}
    (hu : u ∈ H) (hi : (tr[i]?.map Prod.fst) = some u) :
    ∀ e ∈ persists (outputsAt cfg tr i), Agrees (Converge.gT cfg H tr) e :=
  fun e he => agrees_known hinj (Or.inr ⟨i, u, hi, hu, he⟩)

/-- **A step keeps a known block staying**, at an honest node that never
restarts, without rate limiting; and a delivery of it, of another
author, leaves it staying. -/
theorem stays_succ (hl : cfg.limit = none) (hinj : Converge.HashInjective cfg H tr)
    {v : Validator} (hv : v ∈ H) (hnr : ∀ i : ℕ, tr[i]? ≠ some (v, Input.restart))
    {y : BlockId × Block Validator BlockId Payload} (hyk : y ∈ Converge.knownIn cfg H tr)
    {a : ℕ}
    (hst : Stays (stateBefore cfg tr a v).store (stateBefore cfg tr a v).pending y ∨
      (tr[a]? = some (v, .deliver y.1 y.2) ∧ y.2.creator ≠ v)) :
    Stays (stateBefore cfg tr (a + 1) v).store (stateBefore cfg tr (a + 1) v).pending y := by
  rcases he : tr[a]? with _ | ⟨w, inp⟩
  · have hlen : tr.length ≤ a := List.getElem?_eq_none_iff.mp he
    have heq : stateBefore cfg tr (a + 1) v = stateBefore cfg tr a v := by
      unfold stateBefore
      rw [inputsBefore_of_le hlen, inputsBefore_of_le (by omega : tr.length ≤ a + 1)]
    rw [heq]
    rcases hst with hst | ⟨h, -⟩
    · exact hst
    · rw [he] at h; cases h
  · rw [stateBefore_succ he]
    split
    · rename_i hw
      subst hw
      have hio := outputs_agree (cfg := cfg) hinj hv (i := a) (by rw [he]; rfl)
      rw [outputsAt_eq he] at hio
      refine step_stays (cfg := cfg.at w) hl (fired_before (cfg := cfg) hnr a).1
        (fun h => hnr a (by rw [he, h])) (agreesWith_before hinj hv a)
        (pending_agree_before hinj hv a) (fun id b hib hid => agrees_known hinj (Or.inl
          ⟨a, w, inp, he, hv, by rw [hib]; simp [delivered, hid]⟩)) hio
        (agrees_known hinj hyk) ?_
      rcases hst with hst | ⟨h, hcr⟩
      · exact Or.inl hst
      · have h₂ : inp = .deliver y.1 y.2 := by rw [he] at h; simpa using h
        refine Or.inr ⟨h₂, Converge.id_of_knownIn hyk, hcr, fun e he' he1 => ?_⟩
        have hek := Converge.knownBefore_sub hv a
          ((Converge.inv_before (cfg := cfg) a w).pend e he')
        exact Prod.ext he1 (Converge.content_eq hinj hek hyk he1)
    · rename_i hw
      rcases hst with hst | ⟨h, -⟩
      · exact hst
      · rw [he] at h; simp only [Option.some.injEq, Prod.mk.injEq] at h; exact absurd h.1 hw

/-- **A known block stays from then on**, at an honest node that never
restarts, without rate limiting, once it stays. -/
theorem stays_from (hl : cfg.limit = none) (hinj : Converge.HashInjective cfg H tr)
    {v : Validator} (hv : v ∈ H) (hnr : ∀ i : ℕ, tr[i]? ≠ some (v, Input.restart))
    {y : BlockId × Block Validator BlockId Payload} (hyk : y ∈ Converge.knownIn cfg H tr)
    {a : ℕ}
    (hst : Stays (stateBefore cfg tr a v).store (stateBefore cfg tr a v).pending y) :
    ∀ b, a ≤ b →
      Stays (stateBefore cfg tr b v).store (stateBefore cfg tr b v).pending y := by
  intro b hab
  induction b, hab using Nat.le_induction with
  | base => exact hst
  | succ b hab ih => exact stays_succ hl hinj hv hnr hyk (Or.inl ih)

end Node

end LeanDag
