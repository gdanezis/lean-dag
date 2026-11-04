import LeanDag.Node.Helpers.Local
/-!
# A node's disk grows

Deciding keeps the disk's blocks, as accepted, but those it drops
(`decideStep_shrinks`), and keeps the node's own block
(`decideStep_own_mem`). At a node that does not drop, the disk only gains
blocks across a step (`Grows`, `Helpers/Local.lean`): building and taking
blocks in insert, and deciding keeps the disk's blocks, those below the new
floor perhaps without their references (`decideStep_disk`). At any node a
step raises the floor and keeps the disk's blocks from the new floor up,
and at a node that drops, its floor lies at or above the round of its next
undecided slot once that slot changes (`DiskRises`, `diskRises_step`).
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
  rw [absorb_disk]; exact Grows.foldl _ _ _

omit [Fintype Validator] in
/-- **Deciding on a proof keeps the disk's blocks**, as accepted. -/
theorem Grows.decideOn (s : State Validator BlockId Payload) (k : ℕ) (d : Option BlockId)
    (L : List (BlockId × Block Validator BlockId Payload)) :
    Grows s.disk (Node.decideOn cfg s k d L).disk := by
  let s₁ : State Validator BlockId Payload :=
    { s with
      lo := k + 1
      decided := (k, d) :: s.decided
      proofs := (k, (proofStore cfg k L).ids) :: s.proofs }
  exact (Grows.of_restrips (release_disk (cfg := cfg) s₁)).trans (Grows.absorb (release cfg s₁) _)

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
  exact Grows.foldl _ _ _

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
  | askProof peer k => exact Grows.refl _
  | proof u k L => rw [step_proof_of_false hd]; exact Grows.refl _

/-! ## Regular stretches -/

variable (cfg) in
/-- **A regular stretch from `s` to `s'`**: when the node drops, its floor
lies at or below its top and at or above the floor at its next undecided
slot (`floorAt`), and neither the floor nor that slot changes; so it builds
each round in turn. -/
def Regular (s s' : State Validator BlockId Payload) : Prop :=
  cfg.drops = true → s.floor ≤ s.top.getD 0 ∧ floorAt cfg s.lo ≤ s.floor ∧
    s'.lo = s.lo ∧ s'.floor = s.floor

omit [Fintype Validator] in
theorem Regular.of_false (hd : cfg.drops = false) {s s' : State Validator BlockId Payload} :
    Regular cfg s s' :=
  fun h => absurd (hd.symm.trans h) Bool.false_ne_true

/-! ## The floor rises, and the disk keeps its blocks from the floor up -/

variable (cfg) in
/-- **The floor rises**, and, when the node drops, lies at or above the
floor at the next undecided slot (`floorAt`) once that slot changes. -/
def FloorRises (s s' : State Validator BlockId Payload) : Prop :=
  s.floor ≤ s'.floor ∧ (cfg.drops = true → s'.lo = s.lo ∨ floorAt cfg s'.lo ≤ s'.floor)

/-- **`st'` keeps the blocks of `st` as accepted**, those from round `F` up,
or all of them when the node does not drop (`d = false`). -/
def KeepsFrom (d : Bool) (F : ℕ) (st st' : Store Validator BlockId Payload) : Prop :=
  ∀ j ∈ st.ids, (d = false ∨ F ≤ (st.blk j).round) → j ∈ st'.ids ∧ st'.full j = st.full j

variable (cfg) in
/-- **The floor rises and the disk keeps its blocks from the new floor
up.** -/
def DiskRises (s s' : State Validator BlockId Payload) : Prop :=
  FloorRises cfg s s' ∧ KeepsFrom cfg.drops s'.floor s.disk s'.disk

omit [Fintype Validator] [DecidableEq Validator] in
theorem KeepsFrom.of_grows {d : Bool} {F : ℕ} {st st' : Store Validator BlockId Payload}
    (h : Grows st st') : KeepsFrom d F st st' :=
  fun j hj _ => ⟨h.1 hj, h.2.2 j hj⟩

omit [Fintype Validator] [DecidableEq Validator] in
/-- A block a store keeps from `F` up is kept as it was. -/
theorem KeepsFrom.keeps {d : Bool} {F : ℕ} {st st' : Store Validator BlockId Payload}
    (h : KeepsFrom d F st st') {e : BlockId × Block Validator BlockId Payload}
    (hin : e.1 ∈ st.ids) (hval : st.full e.1 = e.2) (hg : d = false ∨ F ≤ e.2.round) :
    e.1 ∈ st'.ids ∧ st'.full e.1 = e.2 := by
  have hr : (st.blk e.1).round = e.2.round := by rw [← (st.full_fields _).1, hval]
  obtain ⟨h₁, h₂⟩ := h e.1 hin (by rwa [hr])
  exact ⟨h₁, h₂.trans hval⟩

omit [Fintype Validator] [DecidableEq Validator] in
theorem KeepsFrom.mono {d : Bool} {F F' : ℕ} {st st' : Store Validator BlockId Payload}
    (hF : F ≤ F') (h : KeepsFrom d F st st') : KeepsFrom d F' st st' :=
  fun j hj hg => h j hj (hg.imp_right hF.trans)

omit [Fintype Validator] [DecidableEq Validator] in
theorem KeepsFrom.trans {d : Bool} {F : ℕ} {a b c : Store Validator BlockId Payload}
    (h₁ : KeepsFrom d F a b) (h₂ : KeepsFrom d F b c) : KeepsFrom d F a c := by
  intro j hj hg
  obtain ⟨hb, hfb⟩ := h₁ j hj hg
  have hr : (b.blk j).round = (a.blk j).round := by
    rw [← (b.full_fields j).1, hfb, (a.full_fields j).1]
  obtain ⟨hc, hfc⟩ := h₂ j hb (by rwa [hr])
  exact ⟨hc, hfc.trans hfb⟩

omit [Fintype Validator] in
theorem FloorRises.refl (s : State Validator BlockId Payload) : FloorRises cfg s s :=
  ⟨le_rfl, fun _ => Or.inl rfl⟩

omit [Fintype Validator] in
theorem FloorRises.trans {a b c : State Validator BlockId Payload} (h₁ : FloorRises cfg a b)
    (h₂ : FloorRises cfg b c) : FloorRises cfg a c := by
  refine ⟨h₁.1.trans h₂.1, fun hd => ?_⟩
  rcases h₂.2 hd with h | h
  · rcases h₁.2 hd with h' | h'
    · exact Or.inl (h.trans h')
    · exact Or.inr (by rw [h]; exact h'.trans h₂.1)
  · exact Or.inr h

omit [Fintype Validator] in
theorem DiskRises.refl (s : State Validator BlockId Payload) : DiskRises cfg s s :=
  ⟨FloorRises.refl s, fun _ hj _ => ⟨hj, rfl⟩⟩

omit [Fintype Validator] in
theorem DiskRises.trans {a b c : State Validator BlockId Payload} (h₁ : DiskRises cfg a b)
    (h₂ : DiskRises cfg b c) : DiskRises cfg a c :=
  ⟨h₁.1.trans h₂.1, (h₁.2.mono h₂.1.1).trans h₂.2⟩

omit [Fintype Validator] in
/-- A part of a step that grows the disk and keeps the floor and the next
undecided slot. -/
theorem DiskRises.of_grows {s s' : State Validator BlockId Payload} (hg : Grows s.disk s'.disk)
    (hf : s.floor ≤ s'.floor) (hlo : s'.lo = s.lo) : DiskRises cfg s s' :=
  ⟨⟨hf, fun _ => Or.inl hlo⟩, KeepsFrom.of_grows hg⟩

omit [Fintype Validator] in
/-- **Letting go keeps the disk's blocks from the floor up.** -/
theorem KeepsFrom.of_drop (s : State Validator BlockId Payload) :
    KeepsFrom cfg.drops s.floor s.disk (Node.drop cfg s).disk := by
  intro j hj hg
  cases hd : cfg.drops with
  | false => rw [drop_of_false _ hd]; exact ⟨hj, rfl⟩
  | true =>
    rw [hd] at hg
    have hr : s.floor ≤ (s.disk.blk j).round := hg.resolve_left (by simp)
    have hn : j ∉ dropSet cfg s := fun hm => by
      unfold dropSet at hm
      have := (List.mem_filter.mp hm).2
      simp only [decide_eq_true_eq] at this
      omega
    have hm : j ∈ (Node.drop cfg s).disk.ids := by
      unfold Node.drop; rw [if_pos hd]
      exact (s.disk.eraseAll_spec (dropSet cfg s)).2.1 j hj hn
    exact ⟨hm, (drop_disk (cfg := cfg) (s := s)).full j hm⟩

omit [Fintype Validator] in
theorem diskRises_tryBuild {s s' : State Validator BlockId Payload}
    {out : List (Output Validator BlockId Payload)} (h : tryBuild cfg s = some (s', out)) :
    DiskRises cfg s s' := by
  obtain ⟨r, id, b, hnew, hrefs, hpred, -, -, -, -, -, hst, -, -, hlo, -⟩ := tryBuild_some h
  exact DiskRises.of_grows ((Grows.insert s.disk).trans (Grows.of_restrips hst))
    (by rw [tryBuild_floor h]; exact le_max_left _ _) hlo

omit [Fintype Validator] in
theorem diskRises_progress : ∀ (fuel : ℕ) (s : State Validator BlockId Payload),
    DiskRises cfg s (Node.progress cfg fuel s).1
  | 0, s => DiskRises.refl s
  | fuel + 1, s => by
    unfold Node.progress
    split
    · rename_i s₁ out h
      exact (diskRises_tryBuild h).trans (diskRises_progress fuel s₁)
    · exact DiskRises.refl s

omit [Fintype Validator] in
/-- **Deciding raises the floor to the floor at the next undecided slot**,
when the node drops, and keeps the disk from the floor up. -/
theorem diskRises_decideStep (s : State Validator BlockId Payload) :
    DiskRises cfg s (Node.decideStep cfg s).1 := by
  unfold Node.decideStep
  dsimp only
  split
  · have h : ∀ t : State Validator BlockId Payload, t.disk = s.disk → t.floor = s.floor →
        DiskRises cfg s (drop cfg (release cfg t)) := by
      intro t hd hf
      have hrel := release_disk (cfg := cfg) t
      refine ⟨⟨?_, fun hdr => Or.inr ?_⟩, ?_⟩
      · rw [drop_floor, release_floor, ← hf]; exact le_max_left _ _
      · rw [drop_lo, drop_floor, release_lo, release_floor]
        unfold floorOf; rw [if_pos hdr]; exact le_max_right _ _
      · rw [drop_floor, ← hd]
        exact (KeepsFrom.of_grows (Grows.of_restrips hrel)).trans (KeepsFrom.of_drop _)
    exact h _ rfl rfl
  · exact DiskRises.refl s

omit [Fintype Validator] in
theorem diskRises_flushSyncs (fuel : ℕ) (s : State Validator BlockId Payload) :
    DiskRises cfg s (Node.flushSyncs cfg fuel s) := by
  obtain ⟨⟨L, -, hL⟩, hf, -, -, -, -, hlo, -⟩ := flushSyncs_eq (cfg := cfg) fuel s
  exact DiskRises.of_grows (by rw [hL]; exact Grows.foldl _ _ _) hf.ge hlo

omit [Fintype Validator] in
/-- After building, the rest of a pass raises the floor and keeps the disk
from the new floor up. -/
theorem diskRises_advance_rest (s : State Validator BlockId Payload) :
    DiskRises cfg (Node.progress cfg (s.disk.topRound + 2) s).1 (Node.advance cfg s).1 := by
  set p := (Node.progress cfg (s.disk.topRound + 2) s).1
  have h₂ := diskRises_decideStep (cfg := cfg) p
  have h₃ := diskRises_flushSyncs (cfg := cfg)
    ((Node.decideStep cfg p).1.syncs.length + 1) (Node.decideStep cfg p).1
  have h₄ : DiskRises cfg (Node.pass cfg s).1 (Node.advance cfg s).1 :=
    DiskRises.of_grows (by rw [advance_disk]; exact Grows.refl _) (by rw [advance_floor])
      (by simp [Node.advance])
  exact h₂.trans (h₃.trans h₄)

omit [Fintype Validator] in
theorem diskRises_advance (s : State Validator BlockId Payload) :
    DiskRises cfg s (Node.advance cfg s).1 :=
  (diskRises_progress _ s).trans (diskRises_advance_rest s)

omit [Fintype Validator] in
theorem diskRises_quiesce (n : ℕ) (s : State Validator BlockId Payload) :
    DiskRises cfg s (Node.quiesce cfg n s).1 :=
  (quiesce_rel (P := fun _ => True) (R := fun a _ b => DiskRises cfg a b) DiskRises.refl
    (fun _ _ _ _ _ h₁ h₂ => h₁.trans h₂) (fun s _ => ⟨diskRises_advance s, trivial⟩) n s
    trivial).1

omit [Fintype Validator] in
theorem diskRises_settle (s : State Validator BlockId Payload) :
    DiskRises cfg s (Node.settle cfg s).1 :=
  diskRises_quiesce _ s

omit [Fintype Validator] in
/-- **Deciding on a proof raises the floor to the floor at the next
undecided slot**, when the node drops, and keeps the disk. -/
theorem diskRises_decideOn (s : State Validator BlockId Payload) (k : ℕ) (d : Option BlockId)
    (L : List (BlockId × Block Validator BlockId Payload)) :
    DiskRises cfg s (Node.decideOn cfg s k d L) := by
  refine ⟨⟨?_, fun hdr => Or.inr ?_⟩, KeepsFrom.of_grows (Grows.decideOn s k d L)⟩
  · unfold Node.decideOn
    rw [(absorb_rest (cfg := cfg) _ _).1, release_floor]; exact le_max_left _ _
  · unfold Node.decideOn
    rw [(absorb_rest (cfg := cfg) _ _).2.2.2.2.2.1, (absorb_rest (cfg := cfg) _ _).1, release_lo,
      release_floor]
    unfold floorOf; rw [if_pos hdr]; exact le_max_right _ _

/-- **A step raises the floor and keeps the disk from the new floor up.** -/
theorem diskRises_step (s : State Validator BlockId Payload) (i : Input Validator BlockId Payload) :
    DiskRises cfg s (Node.step cfg s i).1 := by
  have hset : ∀ x : State Validator BlockId Payload, DiskRises cfg s x →
      DiskRises cfg s (Node.settle cfg x).1 := fun x hx => hx.trans (diskRises_settle x)
  have hab : ∀ L, DiskRises cfg s (Node.absorb cfg s L) := fun L =>
    DiskRises.of_grows (Grows.absorb s L) (absorb_rest (cfg := cfg) s L).1.ge
      (absorb_rest (cfg := cfg) s L).2.2.2.2.2.1
  cases i with
  | start =>
    simp only [Node.step]
    split
    · split
      · rename_i h₂
        dsimp only
        exact hset _ (DiskRises.of_grows (Grows.insert s.disk (id := cfg.idOf cfg.genesis)
          (b := cfg.genesis) (hnew := h₂.1)
          (hrefs := fun _ hj => absurd hj (Finset.notMem_empty _))
          (hpred := fun j hj => absurd hj (Finset.notMem_empty j))) le_rfl rfl)
      · exact DiskRises.refl _
    · exact DiskRises.refl _
  | deliver u id b =>
    simp only [Node.step]
    split
    · split
      · exact hset _ (hab [(id, b)])
      · split
        · exact hset _ (DiskRises.of_grows (Grows.refl _) le_rfl rfl)
        · exact DiskRises.refl _
    · exact DiskRises.refl _
  | stream u L =>
    have htk : ∀ t L', DiskRises cfg s (Node.takeIn cfg s t L') := by
      intro t L'
      unfold Node.takeIn
      split
      · exact hab _
      · exact DiskRises.refl _
    simp only [Node.step]
    split
    · exact DiskRises.refl _
    · split
      · exact hset _ (htk _ _)
      · exact hset _ ((htk _ _).trans (DiskRises.of_grows (Grows.refl _) le_rfl rfl))
  | timer r => rw [step_timer_fst]; exact hset _ (DiskRises.of_grows (Grows.refl _) le_rfl rfl)
  | syncRequest peer t fr ids => exact DiskRises.refl _
  | ask peer r => exact DiskRises.refl _
  | restart =>
    exact hset { s with recovering := true } (DiskRises.of_grows (Grows.refl _) le_rfl rfl)
  | askProof peer k => exact DiskRises.refl _
  | proof u k L =>
    simp only [Node.step]
    split
    · split
      · exact hset _ (diskRises_decideOn s k _ L)
      · exact DiskRises.refl _
    · exact DiskRises.refl _

/-! ## The disk grows while the next undecided slot stays -/

/-- **The disk grows unless the node decides**: the next undecided slot
rises, or stays and the disk grows. -/
def GrowsUnless (s s' : State Validator BlockId Payload) : Prop :=
  s.lo ≤ s'.lo ∧ (s.lo < s'.lo ∨ Grows s.disk s'.disk)

omit [Fintype Validator] [DecidableEq Validator] in
theorem GrowsUnless.refl (s : State Validator BlockId Payload) : GrowsUnless s s :=
  ⟨le_rfl, Or.inr (Grows.refl _)⟩

omit [Fintype Validator] [DecidableEq Validator] in
theorem GrowsUnless.trans {a b c : State Validator BlockId Payload} (h₁ : GrowsUnless a b)
    (h₂ : GrowsUnless b c) : GrowsUnless a c := by
  refine ⟨h₁.1.trans h₂.1, ?_⟩
  rcases h₁.2 with h | h
  · exact Or.inl (lt_of_lt_of_le h h₂.1)
  · rcases h₂.2 with h' | h'
    · exact Or.inl (lt_of_le_of_lt h₁.1 h')
    · exact Or.inr (h.trans h')

omit [Fintype Validator] [DecidableEq Validator] in
theorem GrowsUnless.of_grows {s s' : State Validator BlockId Payload} (hg : Grows s.disk s'.disk)
    (hlo : s'.lo = s.lo) : GrowsUnless s s' :=
  ⟨hlo.ge, Or.inr hg⟩

omit [Fintype Validator] [DecidableEq Validator] in
/-- With the next undecided slot the same at both ends, the disk grows. -/
theorem GrowsUnless.grows {s s' : State Validator BlockId Payload} (h : GrowsUnless s s')
    (hlo : s'.lo = s.lo) : Grows s.disk s'.disk :=
  h.2.resolve_left (by omega)

omit [Fintype Validator] in
theorem growsUnless_progress : ∀ (fuel : ℕ) (s : State Validator BlockId Payload),
    GrowsUnless s (Node.progress cfg fuel s).1 := fun fuel s =>
  GrowsUnless.of_grows (Grows.progress fuel s).1 (Grows.progress fuel s).2

omit [Fintype Validator] in
/-- **Deciding nothing leaves the state**, and deciding raises the next
undecided slot. -/
theorem growsUnless_decideStep (s : State Validator BlockId Payload) :
    GrowsUnless s (Node.decideStep cfg s).1 := by
  unfold Node.decideStep
  dsimp only
  split
  · rename_i h
    refine ⟨?_, Or.inl ?_⟩ <;> rw [drop_lo, release_lo] <;> dsimp only
    · omega
    · have := List.length_pos_of_ne_nil h.2.2; omega
  · exact GrowsUnless.refl s

omit [Fintype Validator] in
/-- After building, the rest of a pass grows the disk unless it decides. -/
theorem growsUnless_advance_rest (s : State Validator BlockId Payload) :
    GrowsUnless (Node.progress cfg (s.disk.topRound + 2) s).1 (Node.advance cfg s).1 := by
  set p := (Node.progress cfg (s.disk.topRound + 2) s).1
  have h₂ := growsUnless_decideStep (cfg := cfg) p
  have h₃ : GrowsUnless (Node.decideStep cfg p).1 (Node.pass cfg s).1 := by
    obtain ⟨⟨L, -, hL⟩, -, -, -, -, -, hlo, -⟩ := flushSyncs_eq (cfg := cfg)
      ((Node.decideStep cfg p).1.syncs.length + 1) (Node.decideStep cfg p).1
    exact GrowsUnless.of_grows (by simp only [Node.pass]; rw [hL]; exact Grows.foldl _ _ _) hlo
  have h₄ : GrowsUnless (Node.pass cfg s).1 (Node.advance cfg s).1 :=
    GrowsUnless.of_grows (by rw [advance_disk]; exact Grows.refl _) (by simp [Node.advance])
  exact h₂.trans (h₃.trans h₄)

omit [Fintype Validator] in
theorem growsUnless_advance (s : State Validator BlockId Payload) :
    GrowsUnless s (Node.advance cfg s).1 :=
  (growsUnless_progress _ s).trans (growsUnless_advance_rest s)

omit [Fintype Validator] in
theorem growsUnless_quiesce (n : ℕ) (s : State Validator BlockId Payload) :
    GrowsUnless s (Node.quiesce cfg n s).1 :=
  (quiesce_rel (P := fun _ => True) (R := fun a _ b => GrowsUnless a b) GrowsUnless.refl
    (fun _ _ _ _ _ h₁ h₂ => h₁.trans h₂) (fun s _ => ⟨growsUnless_advance s, trivial⟩) n s
    trivial).1

omit [Fintype Validator] in
theorem growsUnless_settle (s : State Validator BlockId Payload) :
    GrowsUnless s (Node.settle cfg s).1 :=
  growsUnless_quiesce _ s

/-- **A step grows the disk unless the node decides.** -/
theorem growsUnless_step (s : State Validator BlockId Payload)
    (i : Input Validator BlockId Payload) : GrowsUnless s (Node.step cfg s i).1 := by
  have hset : ∀ x : State Validator BlockId Payload, GrowsUnless s x →
      GrowsUnless s (Node.settle cfg x).1 := fun x hx => hx.trans (growsUnless_settle x)
  have hab : ∀ L, GrowsUnless s (Node.absorb cfg s L) := fun L =>
    GrowsUnless.of_grows (Grows.absorb s L) (absorb_rest (cfg := cfg) s L).2.2.2.2.2.1
  cases i with
  | start =>
    simp only [Node.step]
    split
    · split
      · rename_i h₂
        dsimp only
        exact hset _ (GrowsUnless.of_grows (Grows.insert s.disk (id := cfg.idOf cfg.genesis)
          (b := cfg.genesis) (hnew := h₂.1)
          (hrefs := fun _ hj => absurd hj (Finset.notMem_empty _))
          (hpred := fun j hj => absurd hj (Finset.notMem_empty j))) rfl)
      · exact GrowsUnless.refl _
    · exact GrowsUnless.refl _
  | deliver u id b =>
    simp only [Node.step]
    split
    · split
      · exact hset _ (hab [(id, b)])
      · split
        · exact hset _ (GrowsUnless.of_grows (Grows.refl _) rfl)
        · exact GrowsUnless.refl _
    · exact GrowsUnless.refl _
  | stream u L =>
    have htk : ∀ t L', GrowsUnless s (Node.takeIn cfg s t L') := by
      intro t L'
      unfold Node.takeIn
      split
      · exact hab _
      · exact GrowsUnless.refl _
    simp only [Node.step]
    split
    · exact GrowsUnless.refl _
    · split
      · exact hset _ (htk _ _)
      · exact hset _ ((htk _ _).trans (GrowsUnless.of_grows (Grows.refl _) rfl))
  | timer r =>
    rw [step_timer_fst]; exact hset _ (GrowsUnless.of_grows (Grows.refl _) rfl)
  | syncRequest peer t fr ids => exact GrowsUnless.refl _
  | ask peer r => exact GrowsUnless.refl _
  | restart =>
    exact hset { s with recovering := true } (GrowsUnless.of_grows (Grows.refl _) rfl)
  | askProof peer k => exact GrowsUnless.refl _
  | proof u k L =>
    simp only [Node.step]
    split
    · rename_i hc
      split
      · rename_i d _
        have hlo := (decideOn_rest (cfg := cfg) s k d L).2.2.2.2.1
        exact hset _ ⟨by simp only [Node.tidy]; omega, Or.inl (by simp only [Node.tidy]; omega)⟩
      · exact GrowsUnless.refl _
    · exact GrowsUnless.refl _

/-! ## The blocks as accepted stay closed under references -/

omit [Fintype Validator] in
theorem closed_accept (hd : cfg.drops = false) {F : ℕ} {st : Store Validator BlockId Payload}
    (h : st.FullClosed) (id : BlockId) (b : Block Validator BlockId Payload) :
    (acceptOn cfg F st id b).FullClosed := by
  unfold acceptOn
  split
  · exact h.insert
  · split
    · rename_i h'; rw [hd] at h'; cases h'.1
    · exact h

omit [Fintype Validator] in
theorem closed_foldl (hd : cfg.drops = false) {F : ℕ} :
    ∀ (l : List (BlockId × Block Validator BlockId Payload))
    (st : Store Validator BlockId Payload), st.FullClosed →
    (l.foldl (fun s e => acceptOn cfg F s e.1 e.2) st).FullClosed
  | [], _, h => h
  | e :: l, _, h => closed_foldl hd l _ (closed_accept hd h e.1 e.2)

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
theorem closed_absorb (hd : cfg.drops = false) (s : State Validator BlockId Payload)
    (L : List (BlockId × Block Validator BlockId Payload)) (h : s.disk.FullClosed) :
    (Node.absorb cfg s L).disk.FullClosed := by
  rw [absorb_disk]; exact closed_foldl hd _ _ h

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
  exact closed_foldl hd _ _ h₂

omit [Fintype Validator] in
theorem closed_settle (s : State Validator BlockId Payload) (hd : cfg.drops = false)
    (h : s.disk.FullClosed) : (Node.settle cfg s).1.disk.FullClosed :=
  quiesce_ind (fun s h => closed_advance s hd h) _ s h

omit [Fintype Validator] in
theorem closed_takeIn (hd : cfg.drops = false) (s : State Validator BlockId Payload)
    (t : BlockId × Block Validator BlockId Payload)
    (L : List (BlockId × Block Validator BlockId Payload)) (h : s.disk.FullClosed) :
    (Node.takeIn cfg s t L).disk.FullClosed := by
  unfold Node.takeIn
  split
  · exact closed_absorb hd s L h
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
      · exact closed_settle _ hd (closed_absorb (cfg := cfg) hd s [(id, b)] h)
      · split
        · exact closed_settle _ hd h
        · exact h
    · exact h
  | stream u L =>
    simp only [Node.step]
    split
    · exact h
    · split
      · exact closed_settle _ hd (closed_takeIn (cfg := cfg) hd s _ _ h)
      · exact closed_settle _ hd (closed_takeIn (cfg := cfg) hd s _ _ h)
  | timer r => rw [step_timer_fst]; exact closed_settle _ hd h
  | syncRequest peer t fr ids => exact h
  | ask peer r => exact h
  | restart => exact closed_settle { s with recovering := true } hd h
  | askProof peer k => exact h
  | proof u k L => rw [step_proof_of_false hd]; exact h

end Node

end LeanDag
