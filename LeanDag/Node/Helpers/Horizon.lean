import LeanDag.Node.Helpers.Steps
/-!
# The node's own top and its horizon

Along a run the node's store holds a block at or above its top round, or
the node has decided a slot whose round lies there, and its horizon stays
at or below its top and the round of its next undecided slot (`Held`):
building adds the block of the new top, resuming moves the top to a
round the store holds, a jump to a round at or below that of a decided
slot, deciding moves the next slot up, and collecting raises the horizon
to at most the lesser of that round and the top. Across a step the store keeps what lies at or
above the new horizon, and its top round does not fall (`Keeps`).
-/

namespace LeanDag

namespace Node

variable {Validator BlockId Payload : Type} [Fintype Validator] [DecidableEq Validator]
variable [LinearOrder BlockId]
variable {cfg : Config Validator BlockId Payload}

variable (cfg) in
/-- **The node holds its top and keeps its horizon low.** -/
structure Held (s : State Validator BlockId Payload) : Prop where
  /-- A stored block lies at or above its top round, or, while it
  recovers, a decided slot's round does. -/
  top : ∀ t, s.top = some t → (∃ o ∈ s.store.ids, t ≤ (s.store.blk o).round) ∨
    s.recovering = true ∧ ∃ k < s.lo, t ≤ cfg.slots.slotRound k
  /-- The horizon lies at or below the next undecided slot's round. -/
  horizon : s.store.base ≤ cfg.per * (s.lo / cfg.m)
  /-- Before the node starts, the horizon is `0`. -/
  low : s.top = none → s.store.base = 0
  /-- After, it lies at or below the top. -/
  le_top : ∀ t, s.top = some t → s.store.base ≤ t
  /-- An identifier outside the store denotes the genesis block. -/
  junk : s.store.junk = cfg.genesis

/-- **A store keeps another**: its horizon is no lower, it holds the
other's blocks at or above its horizon, and its top round is no lower. -/
def Keeps (st st' : Store Validator BlockId Payload) : Prop :=
  st.base ≤ st'.base ∧ (∀ i ∈ st.ids, st'.base ≤ (st.blk i).round → i ∈ st'.ids) ∧
    st.topRound ≤ st'.topRound

omit [Fintype Validator] [DecidableEq Validator] in
theorem Keeps.refl (st : Store Validator BlockId Payload) : Keeps st st :=
  ⟨le_rfl, fun _ hi _ => hi, le_rfl⟩

omit [Fintype Validator] [DecidableEq Validator] in
theorem Keeps.trans {a b c : Store Validator BlockId Payload} (h₁ : Keeps a b) (h₂ : Keeps b c)
    (hab : ∀ i ∈ a.ids, b.base ≤ (a.blk i).round → (b.blk i).round = (a.blk i).round) :
    Keeps a c :=
  ⟨h₁.1.trans h₂.1, fun i hi hr => by
    have hb : b.base ≤ (a.blk i).round := h₂.1.trans hr
    exact h₂.2.1 i (h₁.2.1 i hi hb) (by rw [hab i hi hb]; exact hr), h₁.2.2.trans h₂.2.2⟩

omit [Fintype Validator] [DecidableEq Validator] in
/-- A store grown at a fixed horizon has no lower top round. -/
theorem Grows.topRound {st st' : Store Validator BlockId Payload} (hg : Grows st st')
    (hb : st'.base = st.base) : st.topRound ≤ st'.topRound := by
  unfold Store.topRound
  refine Finset.sup_le fun i hi => ?_
  rw [← hg.blk hb hi]
  exact Finset.le_sup (f := fun i => (st'.blk i).round) ((hg.2 hb).1 hi)

omit [Fintype Validator] [DecidableEq Validator] in
theorem Grows.keeps {st st' : Store Validator BlockId Payload} (hg : Grows st st')
    (hb : st'.base = st.base) : Keeps st st' :=
  ⟨hb.ge, fun _ hi _ => (hg.2 hb).1 hi, hg.topRound hb⟩

omit [Fintype Validator] [DecidableEq Validator] in
/-- A pruned store reads its blocks at or above the horizon at the same
rounds. -/
theorem prune_blk_round (st : Store Validator BlockId Payload) {G : ℕ} (hG : st.base ≤ G)
    {i : BlockId} (hi : G ≤ (st.blk i).round) : ((st.prune G hG).blk i).round = (st.blk i).round := by
  simp only [Store.blk, Store.prune, lookup, atBase_round]
  rw [treeMap_getD_filter_of (by simpa [Store.blk, lookup] using hi)]

omit [Fintype Validator] [DecidableEq Validator] in
theorem mem_prune_ids {st : Store Validator BlockId Payload} {G : ℕ} {hG : st.base ≤ G}
    {i : BlockId} : i ∈ (st.prune G hG).ids ↔ i ∈ st.ids ∧ G ≤ (st.blk i).round :=
  Finset.mem_filter

omit [Fintype Validator] [DecidableEq Validator] in
/-- **Pruning below a held block keeps the store.** -/
theorem Keeps.prune (st : Store Validator BlockId Payload) {G : ℕ} (hG : st.base ≤ G)
    {o : BlockId} (ho : o ∈ st.ids) (hoG : G ≤ (st.blk o).round) : Keeps st (st.prune G hG) := by
  refine ⟨hG, fun i hi hr => mem_prune_ids.mpr ⟨hi, hr⟩, ?_⟩
  obtain ⟨j, hj, hmax⟩ := Finset.exists_max_image st.ids (fun i => (st.blk i).round) ⟨o, ho⟩
  have hjG : G ≤ (st.blk j).round := hoG.trans (hmax o ho)
  have htop : st.topRound = (st.blk j).round :=
    le_antisymm (Finset.sup_le fun i hi => hmax i hi)
      (Finset.le_sup (f := fun i => (st.blk i).round) hj)
  rw [htop, ← prune_blk_round st hG hjG]
  exact Finset.le_sup (f := fun i => ((st.prune G hG).blk i).round) (mem_prune_ids.mpr ⟨hj, hjG⟩)

omit [Fintype Validator] [DecidableEq Validator] in
/-- **Pruning at or below the store's top round keeps the store.** -/
theorem Keeps.prune_top (st : Store Validator BlockId Payload) {G : ℕ} (hG : st.base ≤ G)
    (hGt : G ≤ st.topRound) : Keeps st (st.prune G hG) := by
  rcases st.ids.eq_empty_or_nonempty with he | ⟨j, hj⟩
  · refine ⟨hG, fun i hi => absurd hi (by rw [he]; exact Finset.notMem_empty i), ?_⟩
    have : st.topRound = 0 := by unfold Store.topRound; rw [he]; rfl
    omega
  · obtain ⟨i, hi, hmax⟩ := Finset.exists_max_image st.ids (fun i => (st.blk i).round) ⟨j, hj⟩
    have htop : st.topRound = (st.blk i).round :=
      le_antisymm (Finset.sup_le fun i' hi' => hmax i' hi')
        (Finset.le_sup (f := fun i => (st.blk i).round) hi)
    exact Keeps.prune st hG hi (htop ▸ hGt)

omit [Fintype Validator] in
theorem Held.grow {s s' : State Validator BlockId Payload} (h : Held cfg s)
    (hg : Grows s.store s'.store) (hb : s'.store.base = s.store.base) (htop : s'.top = s.top)
    (hlo : s.lo ≤ s'.lo)
    (hrec : s.recovering = true → s'.recovering = true := by first | exact id | exact fun _ => rfl) :
    Held cfg s' where
  top t ht := by
    rcases h.top t (htop.symm.trans ht) with ⟨o, hoi, hor⟩ | ⟨hr, k, hk, hkt⟩
    · exact Or.inl ⟨o, (hg.2 hb).1 hoi, by rw [hg.blk hb hoi]; exact hor⟩
    · exact Or.inr ⟨hrec hr, k, lt_of_lt_of_le hk hlo, hkt⟩
  horizon := by
    rw [hb]
    exact h.horizon.trans (Nat.mul_le_mul_left _ (Nat.div_le_div_right hlo))
  low ht := by rw [hb]; exact h.low (htop.symm.trans ht)
  le_top t ht := by rw [hb]; exact h.le_top t (htop.symm.trans ht)
  junk := ((hg.2 hb).2.1).trans h.junk

omit [Fintype Validator] in
theorem Held.tryBuild {s s' : State Validator BlockId Payload}
    {out : List (Output Validator BlockId Payload)} (h : Held cfg s)
    (hb : Node.tryBuild cfg s = some (s', out)) : Held cfg s' := by
  unfold Node.tryBuild at hb
  split at hb
  · rename_i r hr
    dsimp only at hb
    split at hb
    · split at hb
      · rw [Option.some.injEq, Prod.mk.injEq] at hb
        obtain ⟨rfl, rfl⟩ := hb
        refine ⟨fun t ht => Or.inl ⟨_, Finset.mem_insert_self _ _, ?_⟩, h.horizon,
          fun ht => absurd ht (by simp), fun t ht => ?_, h.junk⟩
        · simp only [Option.some.injEq] at ht
          simp only [Store.blk, Store.insert, lookup, Std.TreeMap.getD_insert_self, atBase_round]
          exact ht.ge
        · simp only [Option.some.injEq] at ht
          have := h.le_top r hr
          change s.store.base ≤ t
          omega
      · exact absurd hb (by simp)
    · exact absurd hb (by simp)
  · exact absurd hb (by simp)

omit [Fintype Validator] in
/-- **Building keeps the store, at a fixed horizon.** -/
theorem Held.progress : ∀ (fuel : ℕ) {s : State Validator BlockId Payload}, Held cfg s →
    Held cfg (Node.progress cfg fuel s).1
  | 0, _, h => h
  | fuel + 1, s, h => by
    unfold Node.progress
    split
    · rename_i s₁ out hb
      exact Held.progress fuel (h.tryBuild hb)
    · exact h

omit [Fintype Validator] in
theorem decideStep_lo (s : State Validator BlockId Payload) :
    s.lo ≤ (Node.decideStep cfg s).1.lo := by
  unfold Node.decideStep
  dsimp only
  split
  · rw [(proposeAt_keeps _).2.2.2.2.2.1]; exact Nat.le_add_right _ _
  · exact (proposeAt_keeps _).2.2.2.2.2.1.ge

omit [Fintype Validator] in
theorem decideStep_top (s : State Validator BlockId Payload) :
    (Node.decideStep cfg s).1.top = s.top := by
  unfold Node.decideStep
  dsimp only
  split
  all_goals exact (proposeAt_keeps _).2.2.1

omit [Fintype Validator] in
theorem decideStep_recovering (s : State Validator BlockId Payload) :
    (Node.decideStep cfg s).1.recovering = s.recovering := by
  unfold Node.decideStep
  dsimp only
  split
  all_goals exact (proposeAt_keeps _).2.2.2.2.2.2.2.1

omit [Fintype Validator] in
theorem Held.decideStep {s : State Validator BlockId Payload} (h : Held cfg s) :
    Held cfg (Node.decideStep cfg s).1 :=
  h.grow (by rw [decideStep_store]; exact Grows.refl _) (by rw [decideStep_store])
    (decideStep_top s) (decideStep_lo s) (fun hr => by rw [decideStep_recovering]; exact hr)

omit [Fintype Validator] in
/-- **Collecting keeps the node its top and its horizon**, and keeps the
store when its top round reaches the top. -/
theorem Held.collect {s : State Validator BlockId Payload} (h : Held cfg s) :
    Held cfg (Node.collect cfg s).1 ∧
      ((∀ t, s.top = some t → t ≤ s.store.topRound) →
        Keeps s.store (Node.collect cfg s).1.store) := by
  unfold Node.collect
  split
  · rename_i t ht
    dsimp only
    split
    · rename_i hG
      have hF : cfg.per * (min s.lo s.certHeight / cfg.m) ≤ cfg.per * (s.lo / cfg.m) :=
        Nat.mul_le_mul_left _ (Nat.div_le_div_right (min_le_left _ _))
      refine ⟨⟨fun t' ht' => ?_, ?_, fun ht' => absurd (ht.symm.trans ht') (by simp),
        fun t' ht' => ?_, h.junk⟩, fun hst => ?_⟩
      · rw [ht, Option.some.injEq] at ht'
        subst ht'
        rcases h.top t ht with ⟨o, hoi, hor⟩ | hk
        · have hoG : horizonAt cfg s t ≤ (s.store.blk o).round := (horizonAt_le_top s t).trans hor
          exact Or.inl ⟨o, (mem_prune_ids (hG := hG.le)).mpr ⟨hoi, hoG⟩,
            by rw [prune_blk_round _ _ hoG]; exact hor⟩
        · exact Or.inr hk
      · exact (horizonAt_le_frontier s t).trans hF
      · rw [ht, Option.some.injEq] at ht'
        subst ht'
        exact horizonAt_le_top s t
      · exact Keeps.prune_top s.store hG.le ((horizonAt_le_top s t).trans (hst t ht))
    · exact ⟨h, fun _ => Keeps.refl _⟩
  · exact ⟨h, fun _ => Keeps.refl _⟩

omit [Fintype Validator] in
theorem Held.store {s : State Validator BlockId Payload} (h : Held cfg s)
    {st : Store Validator BlockId Payload} (pend : List (BlockId × Block Validator BlockId Payload))
    (hg : Grows s.store st) (hb : st.base = s.store.base) :
    Held cfg { s with store := st, pending := pend } :=
  h.grow hg hb rfl le_rfl

omit [Fintype Validator] in
theorem Held.advance {s : State Validator BlockId Payload} (h : Held cfg s) :
    Held cfg (Node.advance cfg s).1 := by
  have h₁ := (Held.progress (s.store.topRound + 2) h).decideStep
  exact (Held.collect h₁).1.store _ (Grows.flush _ _ _) (flush_base _ _ _)

omit [Fintype Validator] in
/-- **A resume keeps the store and the horizon**, its new top a round the
store holds or, after a jump, at or below the round of a decided slot. -/
theorem Held.tryResume {s s' : State Validator BlockId Payload} (h : Held cfg s)
    (hr : Node.tryResume cfg s = some s') : Held cfg s' := by
  obtain ⟨t, R, ht, htR, hcase, hst, -, htop, -, hlo, -⟩ := tryResume_some hr
  refine ⟨fun t' ht' => ?_, ?_, fun ht' => absurd (htop.symm.trans ht') (by simp),
    fun t' ht' => ?_, by rw [hst]; exact h.junk⟩
  · rw [htop, Option.some.injEq] at ht'
    subst ht'
    rcases hcase with ⟨-, hR, -⟩ | hJ
    · obtain ⟨v, hv⟩ := Finset.card_pos.mp hR
      obtain ⟨o, hoi, hor, -⟩ := mem_authorsIn.mp hv
      exact Or.inl ⟨o, hst ▸ hoi, by rw [hst]; exact hor.ge⟩
    · obtain ⟨hJ, -, hrec'⟩ := hJ
      obtain ⟨-, hpos, hJr, -⟩ := jumpRound_some hJ
      refine Or.inr ⟨hrec', min s.lo s.certHeight - 1, ?_, hJr⟩
      rw [hlo]
      have := min_le_left s.lo s.certHeight
      omega
  · rw [hst, hlo]; exact h.horizon
  · rw [htop, Option.some.injEq] at ht'
    have := h.le_top t ht
    rw [hst]
    omega

omit [Fintype Validator] in
/-- **Settling keeps the store, and the node its top and its horizon.** -/
theorem Held.settle {s : State Validator BlockId Payload} (h : Held cfg s) :
    Held cfg (Node.settle cfg s).1 := by
  rcases settle_cases (cfg := cfg) s with he | ⟨s₁, hj, he⟩ <;> rw [he]
  · exact quiesce_ind (fun _ h => h.advance) _ _ h
  · exact quiesce_ind (fun _ h => h.advance) _ _ (h.tryResume hj)

omit [Fintype Validator] in
/-- A block at the horizon is accepted, unless its identifier is. -/
theorem mem_accept_of_base {st : Store Validator BlockId Payload} {id : BlockId}
    {b : Block Validator BlockId Payload} (hb : b.round = st.base) :
    id ∈ (Node.accept cfg st id b).ids := by
  unfold Node.accept
  split
  · exact Finset.mem_insert_self _ _
  · rename_i hn
    by_contra hid
    exact hn ⟨hid, hb.ge, fun h => absurd hb (ne_of_gt h), fun h => absurd hb (ne_of_gt h),
      fun h => absurd hb (ne_of_gt h)⟩

omit [Fintype Validator] in
/-- Accepting blocks at the horizon stores each identifier. -/
theorem mem_foldl_of_base : ∀ (l : List (BlockId × Block Validator BlockId Payload))
    (st : Store Validator BlockId Payload), (∀ e ∈ l, e.2.round = st.base) →
    ∀ e ∈ l, e.1 ∈ (l.foldl (fun s e => Node.accept cfg s e.1 e.2) st).ids
  | [], _, _, _, he => absurd he List.not_mem_nil
  | e' :: l, st, hl, e, he => by
    rw [List.foldl_cons]
    have hb' := accept_base (cfg := cfg) st e'.1 e'.2
    rcases List.mem_cons.mp he with rfl | he
    · have hin := mem_accept_of_base (cfg := cfg) (id := e.1) (hl e List.mem_cons_self)
      have hg := Grows.foldl (cfg := cfg) l (Node.accept cfg st e.1 e.2)
      exact (hg.2 (foldl_base _ _)).1 hin
    · exact mem_foldl_of_base l _
        (fun x hx => (hl x (List.mem_cons_of_mem _ hx)).trans hb'.symm) e he

/-- **A step keeps the node's top and its horizon.** -/
theorem Held.step {s : State Validator BlockId Payload} (h : Held cfg s)
    (i : Input Validator BlockId Payload) : Held cfg (Node.step cfg s i).1 := by
  cases i with
  | start =>
    simp only [Node.step]
    split
    · split
      · rename_i h₁ h₂
        have h0 := h.low h₁.1
        refine Held.settle ⟨fun t ht => Or.inl ⟨_, Finset.mem_insert_self _ _, ?_⟩, h.horizon,
          fun ht => absurd ht (by simp), fun t _ => ?_, h.junk⟩
        · simp only [Option.some.injEq] at ht
          simp only [Store.blk, Store.insert, lookup, Std.TreeMap.getD_insert_self, atBase_round]
          exact ht.ge
        · change s.store.base ≤ t
          omega
      · exact h
    · exact h
  | deliver id b =>
    simp only [Node.step]
    split
    · exact Held.settle (h.grow (Grows.flush _ _ _) (flush_base _ _ _) rfl le_rfl (fun hr => hr))
    · split
      · exact h.grow (Grows.refl _) rfl rfl le_rfl (fun _ => rfl)
      · exact h
  | timer r => exact Held.settle (h.grow (Grows.refl _) rfl rfl le_rfl)
  | restart => exact Held.settle (h.grow (Grows.refl _) rfl rfl le_rfl)
  | baseOffer p G =>
    rw [step_offer]
    split
    · exact Held.settle (h.grow (s' := withOffer s p G) (Grows.refl _) rfl rfl le_rfl)
    · exact h
  | certOffer p c ds =>
    rcases certOffer_cases (cfg := cfg) s p c ds with ⟨ds', -, -, ha, he⟩ |
      ⟨-, -, he⟩ | he <;> rw [he]
    · rw [adopt_eq]
      exact Held.settle (h.grow (s' := adopted s c ds') (Grows.refl _) rfl rfl
        (adoptable_lo ha).le)
    · exact Held.settle (h.grow (s' := { s with cert := some c, props := above (some c) s.props })
        (Grows.refl _) rfl rfl le_rfl)
    · exact h
  | announced p c =>
    rcases announced_cases (cfg := cfg) s p c with ⟨-, -, he⟩ | he | he <;> rw [he]
    · exact Held.settle (h.grow (s' := { s with cert := some c, props := above (some c) s.props })
        (Grows.refl _) rfl rfl le_rfl)
    · exact h
    · exact h
  | proposal p k kh =>
    rw [step_proposal]
    split
    · exact Held.settle (h.grow (Grows.refl _) rfl rfl le_rfl)
    · exact h
  | _ => exact h

/-- **A run keeps the node's top and its horizon.** -/
theorem Held.run : ∀ (is : List (Input Validator BlockId Payload))
    {s : State Validator BlockId Payload}, Held cfg s → Held cfg (Node.run cfg s is).1
  | [], _, h => h
  | i :: is, _, h => Held.run is (h.step i)

omit [Fintype Validator] in
theorem Held.init : Held cfg (State.init cfg) :=
  ⟨fun _ h => absurd h (by simp [State.init]), Nat.zero_le _, fun _ => rfl,
    fun _ h => absurd h (by simp [State.init]), rfl⟩

end Node

end LeanDag
