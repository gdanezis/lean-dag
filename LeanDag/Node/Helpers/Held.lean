import LeanDag.Node.Helpers.Steps
/-!
# The node's own top

Along a run the node's store holds a block at or above its top round, and
an identifier outside the store denotes the genesis block (`Held`):
building adds the block of the new top, and every other change only adds
blocks to the store and leaves the top alone. Across a step the store
holds the blocks it held, read alike, and its top round does not fall
(`Keeps`).

At a top round `r ≥ 1` the store holds blocks of at least `q` distinct
authors of round `r − 1` (`Quorate`): the top rises only by a build,
whose rule asks for that quorum, and the store only grows.
-/

namespace LeanDag

namespace Node

variable {Validator BlockId Payload : Type} [Fintype Validator] [DecidableEq Validator]
variable [LinearOrder BlockId]
variable {cfg : Config Validator BlockId Payload}

variable (cfg) in
/-- **The node holds its top**: a stored block lies at or above its top
round, and an identifier outside the store denotes the genesis block. -/
structure Held (s : State Validator BlockId Payload) : Prop where
  /-- A stored block lies at or above its top round. -/
  top : ∀ t, s.top = some t → ∃ o ∈ s.store.ids, t ≤ (s.store.blk o).round
  /-- An identifier outside the store denotes the genesis block. -/
  junk : s.store.junk = cfg.genesis

/-- **A store keeps another**: it holds the other's blocks, reads them
alike, and its top round is no lower. -/
def Keeps (st st' : Store Validator BlockId Payload) : Prop :=
  st.ids ⊆ st'.ids ∧ (∀ i ∈ st.ids, st'.blk i = st.blk i) ∧ st.topRound ≤ st'.topRound

omit [Fintype Validator] [DecidableEq Validator] in
theorem Keeps.refl (st : Store Validator BlockId Payload) : Keeps st st :=
  ⟨subset_rfl, fun _ _ => rfl, le_rfl⟩

omit [Fintype Validator] [DecidableEq Validator] in
/-- A grown store has no lower top round. -/
theorem Grows.topRound {st st' : Store Validator BlockId Payload} (hg : Grows st st') :
    st.topRound ≤ st'.topRound := by
  rw [Store.topRound_eq, Store.topRound_eq]
  refine Finset.sup_le fun i hi => ?_
  rw [← hg.blk hi]
  exact Finset.le_sup (f := fun i => (st'.blk i).round) (hg.1 hi)

omit [Fintype Validator] [DecidableEq Validator] in
theorem Grows.keeps {st st' : Store Validator BlockId Payload} (hg : Grows st st') : Keeps st st' :=
  ⟨hg.1, hg.2.2, hg.topRound⟩

omit [Fintype Validator] in
/-- A change that grows the store and leaves the top alone keeps `Held`. -/
theorem Held.grow {s s' : State Validator BlockId Payload} (h : Held cfg s)
    (hg : Grows s.store s'.store) (htop : s'.top = s.top) : Held cfg s' where
  top t ht := by
    obtain ⟨o, hoi, hor⟩ := h.top t (htop.symm.trans ht)
    exact ⟨o, hg.1 hoi, by rw [hg.blk hoi]; exact hor⟩
  junk := hg.2.1.trans h.junk

omit [Fintype Validator] in
theorem Held.tryBuild {s s' : State Validator BlockId Payload}
    {out : List (Output Validator BlockId Payload)} (h : Held cfg s)
    (hb : Node.tryBuild cfg s = some (s', out)) : Held cfg s' := by
  obtain ⟨r, id, b, hnew, hrefs, hpred, -, hbr, -, -, -, hst, htop, -, -, -⟩ := tryBuild_some hb
  refine ⟨fun t ht => ⟨id, ?_, ?_⟩, by rw [hst]; exact h.junk⟩
  · rw [hst]; exact Store.mem_insert_self
  · rw [htop, Option.some.injEq] at ht
    rw [hst]
    simp only [Store.blk, Store.insert, Std.TreeMap.getD_insert_self]
    omega

omit [Fintype Validator] in
/-- **Building keeps `Held`.** -/
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
    (Node.decideStep cfg s).1.top = s.top := by
  unfold Node.decideStep
  dsimp only
  split <;> rfl

omit [Fintype Validator] in
theorem Held.decideStep {s : State Validator BlockId Payload} (h : Held cfg s) :
    Held cfg (Node.decideStep cfg s).1 :=
  h.grow (by rw [decideStep_store]; exact Grows.refl _) (decideStep_top s)

omit [Fintype Validator] in
theorem Held.store {s : State Validator BlockId Payload} (h : Held cfg s)
    {st : Store Validator BlockId Payload} (pend : List (BlockId × Block Validator BlockId Payload))
    (hg : Grows s.store st) : Held cfg { s with store := st, pending := pend } :=
  h.grow hg rfl

omit [Fintype Validator] in
theorem Held.advance {s : State Validator BlockId Payload} (h : Held cfg s) :
    Held cfg (Node.advance cfg s).1 :=
  (Held.progress (s.store.topRound + 2) h).decideStep.store _ (Grows.flush _ _ _)

omit [Fintype Validator] in
/-- **Settling keeps `Held`.** -/
theorem Held.settle {s : State Validator BlockId Payload} (h : Held cfg s) :
    Held cfg (Node.settle cfg s).1 :=
  quiesce_ind (fun _ h => h.advance) _ _ h

/-- **A step keeps `Held`.** -/
theorem Held.step {s : State Validator BlockId Payload} (h : Held cfg s)
    (i : Input Validator BlockId Payload) : Held cfg (Node.step cfg s i).1 := by
  cases i with
  | start =>
    simp only [Node.step]
    split
    · split
      · refine Held.settle
          ⟨fun t ht => ⟨_, by rw [Store.insert_ids]; exact Finset.mem_insert_self _ _, ?_⟩, h.junk⟩
        simp only [Option.some.injEq] at ht
        subst ht
        exact Nat.zero_le _
      · exact h
    · exact h
  | deliver id b =>
    simp only [Node.step]
    split
    · exact Held.settle (h.grow (Grows.flush _ _ _) rfl)
    · exact h
  | timer r => exact Held.settle (h.grow (Grows.refl _) rfl)
  | fetchRequest peer r ids => exact h

/-- **A run keeps `Held`.** -/
theorem Held.run : ∀ (is : List (Input Validator BlockId Payload))
    {s : State Validator BlockId Payload}, Held cfg s → Held cfg (Node.run cfg s is).1
  | [], _, h => h
  | i :: is, _, h => Held.run is (h.step i)

omit [Fintype Validator] in
theorem Held.init : Held cfg (State.init cfg) :=
  ⟨fun _ h => absurd h (by simp [State.init]), rfl⟩

/-! ## The quorum below the top -/

variable (cfg) in
/-- **The node built on a quorum**: at a top round `r ≥ 1` the store holds
blocks of at least `q` distinct authors of round `r − 1`. -/
def Quorate (s : State Validator BlockId Payload) : Prop :=
  ∀ r, s.top = some r → 1 ≤ r → cfg.q ≤ (authorsIn s.store.toRecord s.store.ids (r - 1)).card

omit [Fintype Validator] in
/-- A grown store has the authors of each round it had. -/
theorem Grows.authorsIn {st st' : Store Validator BlockId Payload} (hg : Grows st st') (n : ℕ) :
    authorsIn st.toRecord st.ids n ⊆ authorsIn st'.toRecord st'.ids n := by
  intro a ha
  obtain ⟨b, hb, hr, hc⟩ := mem_authorsIn.mp ha
  refine mem_authorsIn.mpr ⟨b, hg.1 hb, ?_, ?_⟩
  · change (st'.blk b).round = n
    rw [hg.blk hb]; exact hr
  · change (st'.blk b).creator = a
    rw [hg.blk hb]; exact hc

omit [Fintype Validator] in
/-- **A build sees a quorum at the top.** -/
theorem tryBuild_quorum {s s' : State Validator BlockId Payload}
    {out : List (Output Validator BlockId Payload)} (h : Node.tryBuild cfg s = some (s', out)) :
    ∃ r, s.top = some r ∧ cfg.q ≤ (authorsIn s.store.toRecord s.store.ids r).card := by
  unfold Node.tryBuild at h
  split at h
  · rename_i r hr
    dsimp only at h
    split at h
    · rename_i hc
      exact ⟨r, hr, by rw [← Store.authorsAt_eq]; exact hc.1⟩
    · exact absurd h (by simp)
  · exact absurd h (by simp)

omit [Fintype Validator] in
/-- A change that grows the store and leaves the top alone keeps `Quorate`. -/
theorem Quorate.grow {s s' : State Validator BlockId Payload} (h : Quorate cfg s)
    (hg : Grows s.store s'.store) (htop : s'.top = s.top) : Quorate cfg s' :=
  fun r hr h1 => (h r (htop.symm.trans hr) h1).trans
    (Finset.card_le_card (hg.authorsIn _))

omit [Fintype Validator] in
/-- **A build leaves the store a quorum below its new top.** -/
theorem Quorate.tryBuild {s s' : State Validator BlockId Payload}
    {out : List (Output Validator BlockId Payload)}
    (hb : Node.tryBuild cfg s = some (s', out)) : Quorate cfg s' := by
  obtain ⟨r, id, b, hnew, hrefs, hpred, htop₀, -, -, -, -, hst, htop, -, -, -⟩ := tryBuild_some hb
  obtain ⟨r', htop', hq⟩ := tryBuild_quorum hb
  rw [htop₀, Option.some.injEq] at htop'
  subst htop'
  intro t ht _
  rw [htop, Option.some.injEq] at ht
  subst ht
  rw [Nat.add_sub_cancel, hst]
  exact hq.trans (Finset.card_le_card ((Grows.insert s.store).authorsIn _))

omit [Fintype Validator] in
/-- **Building keeps `Quorate`.** -/
theorem Quorate.progress : ∀ (fuel : ℕ) {s : State Validator BlockId Payload}, Quorate cfg s →
    Quorate cfg (Node.progress cfg fuel s).1
  | 0, _, h => h
  | fuel + 1, s, h => by
    unfold Node.progress
    split
    · rename_i s₁ out hb
      exact Quorate.progress fuel (Quorate.tryBuild hb)
    · exact h

omit [Fintype Validator] in
theorem Quorate.advance {s : State Validator BlockId Payload} (h : Quorate cfg s) :
    Quorate cfg (Node.advance cfg s).1 := by
  have hp := Quorate.progress (s.store.topRound + 2) h
  have hd : Quorate cfg (Node.decideStep cfg (Node.progress cfg (s.store.topRound + 2) s).1).1 :=
    hp.grow (by rw [decideStep_store]; exact Grows.refl _) (decideStep_top _)
  exact hd.grow (Grows.flush _ _ _) rfl

omit [Fintype Validator] in
/-- **Settling keeps `Quorate`.** -/
theorem Quorate.settle {s : State Validator BlockId Payload} (h : Quorate cfg s) :
    Quorate cfg (Node.settle cfg s).1 :=
  quiesce_ind (fun _ h => h.advance) _ _ h

/-- **A step keeps `Quorate`.** -/
theorem Quorate.step {s : State Validator BlockId Payload} (h : Quorate cfg s)
    (i : Input Validator BlockId Payload) : Quorate cfg (Node.step cfg s i).1 := by
  cases i with
  | start =>
    simp only [Node.step]
    split
    · split
      · refine Quorate.settle fun t ht h1 => ?_
        simp only [Option.some.injEq] at ht
        omega
      · exact h
    · exact h
  | deliver id b =>
    simp only [Node.step]
    split
    · exact Quorate.settle (h.grow (Grows.flush _ _ _) rfl)
    · exact h
  | timer r => exact Quorate.settle (h.grow (Grows.refl _) rfl)
  | fetchRequest peer r ids => exact h

/-- **A run keeps `Quorate`.** -/
theorem Quorate.run : ∀ (is : List (Input Validator BlockId Payload))
    {s : State Validator BlockId Payload}, Quorate cfg s → Quorate cfg (Node.run cfg s is).1
  | [], _, h => h
  | i :: is, _, h => Quorate.run is (h.step i)

omit [Fintype Validator] in
theorem Quorate.init : Quorate cfg (State.init cfg) :=
  fun _ h => absurd h (by simp [State.init])

end Node

end LeanDag
