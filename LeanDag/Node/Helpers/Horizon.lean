import LeanDag.Node.Helpers.Steps
/-!
# The node's own top and its horizon

Along a run the node holds its own block at its top round, and its
horizon stays at or below its top and the round of its next undecided
slot (`Held`): building adds the block of the new top, deciding moves the
next slot up, and collecting raises the horizon to at most the lesser of
that round and the top. Across a step the store keeps what lies at or
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
  /-- Its block at its top round is in its store. -/
  own : ∀ t, s.top = some t → ∃ o, s.own = some o ∧ o ∈ s.store.ids ∧ (s.store.blk o).round = t
  /-- The horizon lies at or below the next undecided slot's round. -/
  horizon : s.store.base ≤ cfg.per * (s.lo / cfg.m)
  /-- Before the node starts, the horizon is `0`. -/
  low : s.top = none → s.store.base = 0
  /-- After, it lies at or below the top. -/
  le_top : ∀ t, s.top = some t → s.store.base ≤ t
  /-- Before the node starts, it has no block of its own. -/
  own_none : s.top = none → s.own = none
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

omit [Fintype Validator] in
theorem Held.grow {s s' : State Validator BlockId Payload} (h : Held cfg s)
    (hg : Grows s.store s'.store) (hb : s'.store.base = s.store.base) (htop : s'.top = s.top)
    (hown : s'.own = s.own) (hlo : s.lo ≤ s'.lo) : Held cfg s' where
  own t ht := by
    obtain ⟨o, ho, hoi, hor⟩ := h.own t (htop.symm.trans ht)
    exact ⟨o, hown.trans ho, (hg.2 hb).1 hoi, by rw [hg.blk hb hoi]; exact hor⟩
  horizon := by
    rw [hb]
    exact h.horizon.trans (Nat.mul_le_mul_left _ (Nat.div_le_div_right hlo))
  low ht := by rw [hb]; exact h.low (htop.symm.trans ht)
  le_top t ht := by rw [hb]; exact h.le_top t (htop.symm.trans ht)
  own_none ht := hown.trans (h.own_none (htop.symm.trans ht))
  junk := ((hg.2 hb).2.1).trans h.junk

omit [Fintype Validator] in
theorem Held.tryBuild {s s' : State Validator BlockId Payload}
    {out : List (Output Validator BlockId Payload)} (h : Held cfg s)
    (hb : Node.tryBuild cfg s = some (s', out)) : Held cfg s' := by
  unfold Node.tryBuild at hb
  split at hb
  · rename_i r o hr ho
    dsimp only at hb
    split at hb
    · split at hb
      · rw [Option.some.injEq, Prod.mk.injEq] at hb
        obtain ⟨rfl, rfl⟩ := hb
        refine ⟨fun t ht => ⟨_, rfl, Finset.mem_insert_self _ _, ?_⟩, h.horizon,
          fun ht => absurd ht (by simp), fun t ht => ?_, fun ht => absurd ht (by simp), h.junk⟩
        · simp only [Option.some.injEq] at ht
          simp only [Store.blk, Store.insert, lookup, Std.TreeMap.getD_insert_self, atBase_round]
          exact ht
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
  · exact Nat.le_add_right _ _
  · exact le_rfl

omit [Fintype Validator] in
theorem decideStep_top (s : State Validator BlockId Payload) :
    (Node.decideStep cfg s).1.top = s.top ∧ (Node.decideStep cfg s).1.own = s.own := by
  unfold Node.decideStep
  dsimp only
  split <;> exact ⟨rfl, rfl⟩

omit [Fintype Validator] in
theorem Held.decideStep {s : State Validator BlockId Payload} (h : Held cfg s) :
    Held cfg (Node.decideStep cfg s).1 :=
  h.grow (by rw [decideStep_store]; exact Grows.refl _) (by rw [decideStep_store])
    (decideStep_top s).1 (decideStep_top s).2 (decideStep_lo s)

omit [Fintype Validator] in
/-- **Collecting keeps the store, and the node its top and its horizon.** -/
theorem Held.collect {s : State Validator BlockId Payload} (h : Held cfg s) :
    Held cfg (Node.collect cfg s).1 ∧ Keeps s.store (Node.collect cfg s).1.store := by
  unfold Node.collect
  split
  · rename_i t ht
    dsimp only
    split
    · rename_i hG
      obtain ⟨o, ho, hoi, hor⟩ := h.own t ht
      have hoG : min (cfg.per * (s.lo / cfg.m)) t - cfg.lag ≤ (s.store.blk o).round := by
        rw [hor]; omega
      refine ⟨⟨fun t' ht' => ?_, ?_, fun ht' => absurd (ht.symm.trans ht') (by simp),
        fun t' ht' => ?_, fun ht' => absurd (ht.symm.trans ht') (by simp), h.junk⟩,
        Keeps.prune s.store hG.le hoi hoG⟩
      · rw [ht, Option.some.injEq] at ht'
        subst ht'
        exact ⟨o, ho, (mem_prune_ids (hG := hG.le)).mpr ⟨hoi, hoG⟩,
          by rw [prune_blk_round _ _ hoG, hor]⟩
      · change min (cfg.per * (s.lo / cfg.m)) t - cfg.lag ≤ cfg.per * (s.lo / cfg.m)
        omega
      · rw [ht, Option.some.injEq] at ht'
        subst ht'
        change min (cfg.per * (s.lo / cfg.m)) t - cfg.lag ≤ t
        omega
    · exact ⟨h, Keeps.refl _⟩
  · exact ⟨h, Keeps.refl _⟩

omit [Fintype Validator] in
theorem Held.store {s : State Validator BlockId Payload} (h : Held cfg s)
    {st : Store Validator BlockId Payload} (pend : List (BlockId × Block Validator BlockId Payload))
    (hg : Grows s.store st) (hb : st.base = s.store.base) :
    Held cfg { s with store := st, pending := pend } :=
  h.grow hg hb rfl rfl le_rfl

omit [Fintype Validator] in
theorem Held.advance {s : State Validator BlockId Payload} (h : Held cfg s) :
    Held cfg (Node.advance cfg s).1 := by
  have h₁ := (Held.progress (s.store.topRound + 2) h).decideStep
  exact (Held.collect h₁).1.store _ (Grows.flush _ _ _) (flush_base _ _ _)

omit [Fintype Validator] in
/-- **A jump keeps the store and the horizon**, its last filled block the
node's top. -/
theorem Held.tryJump {s s' : State Validator BlockId Payload}
    {out : List (Output Validator BlockId Payload)} (h : Held cfg s)
    (hj : Node.tryJump cfg s = some (s', out)) : Held cfg s' := by
  obtain ⟨r0, B1, B2, F, e, htop, -, -, hF, hst, he, htop', hown', -, hlo, -, -, -, -, hr0, -⟩ :=
    tryJump_some hj
  obtain ⟨-, -, -, -, -, hmap, -⟩ := jumpFills_spec hF
  have hlast := round_of_getLast hmap he
  have hlt : r0 < e.2.round := by
    have := (jumpFills_spec hF).2.2.2.1; rw [hr0] at this hlast; omega
  have hb := insertAll_base hst
  have hg := Grows.insertAll hst
  have hem := (insertAll_mem hst).2 e (List.mem_of_getLast? he)
  refine ⟨fun t ht => ⟨e.1, hown', hem.1, ?_⟩, ?_, fun ht => absurd (htop'.symm.trans ht) (by simp),
    fun t ht => ?_, fun ht => absurd (htop'.symm.trans ht) (by simp), ((hg.2 hb).2.1).trans h.junk⟩
  · rw [htop', Option.some.injEq] at ht
    simp only [Store.blk, lookup, atBase_round, hem.2, ht]
  · rw [hb, hlo]; exact h.horizon
  · rw [htop', Option.some.injEq] at ht
    rw [hb, ← ht]
    have := h.le_top r0 htop
    omega

omit [Fintype Validator] in
/-- **Settling keeps the store, and the node its top and its horizon.** -/
theorem Held.settle {s : State Validator BlockId Payload} (h : Held cfg s) :
    Held cfg (Node.settle cfg s).1 := by
  rcases settle_cases (cfg := cfg) s with he | ⟨s₁, out, hj, he⟩ <;> rw [he]
  · exact h.advance
  · exact (h.tryJump hj).advance

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
        refine Held.settle ⟨fun t ht => ⟨_, rfl, Finset.mem_insert_self _ _, ?_⟩, h.horizon,
          fun ht => absurd ht (by simp), fun t _ => ?_, fun ht => absurd ht (by simp), h.junk⟩
        · simp only [Option.some.injEq] at ht
          simp only [Store.blk, Store.insert, lookup, Std.TreeMap.getD_insert_self, atBase_round]
          exact ht
        · change s.store.base ≤ t
          omega
      · exact h
    · exact h
  | deliver id b =>
    simp only [Node.step]
    split
    · exact Held.settle (h.grow (Grows.flush _ _ _) (flush_base _ _ _) rfl rfl le_rfl)
    · exact h
  | timer r => exact Held.settle (h.grow (Grows.refl _) rfl rfl rfl le_rfl)
  | restart => exact Held.settle (h.grow (Grows.refl _) rfl rfl rfl le_rfl)
  | jump v1 B1 v2 B2 =>
    rw [step_jump]
    split
    · exact h
    · exact Held.settle (h.grow (Grows.flush _ _ _) (flush_base _ _ _) rfl rfl le_rfl)
  | _ => exact h

/-- **A run keeps the node's top and its horizon.** -/
theorem Held.run : ∀ (is : List (Input Validator BlockId Payload))
    {s : State Validator BlockId Payload}, Held cfg s → Held cfg (Node.run cfg s is).1
  | [], _, h => h
  | i :: is, _, h => Held.run is (h.step i)

omit [Fintype Validator] in
theorem Held.init : Held cfg (State.init cfg) :=
  ⟨fun _ h => absurd h (by simp [State.init]), Nat.zero_le _, fun _ => rfl,
    fun _ h => absurd h (by simp [State.init]), fun _ => rfl, rfl⟩

end Node

end LeanDag
