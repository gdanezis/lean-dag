import LeanDag.Node.Model.Run
import LeanDag.Node.Helpers.Memory
import LeanDag.Node.Helpers.ReadsView
/-!
# One node at a time — the lemmas

A successful build step adds one block at the round above the node's top,
its own, identified by its hash, with accepted references, and valid
under the disk's map (`tryBuild_some`); building, deciding and flushing
change the parts of the state the claims read only so. Along any run the
node's state meets `Inv`: what it holds and has pending it was given or
made, its own blocks lie at strictly increasing rounds up to its top,
each its own, identified by its hash and valid against what it knew, its
disk is valid at the row, and its block at its top is on disk and one
of its own blocks. A step persists the blocks it builds and broadcasts
them, and broadcasts besides only its own blocks of earlier steps, which
it resends (`Sent`). Across these the disk only gains blocks (`Grows`).
-/

namespace LeanDag

namespace Node

variable {Validator BlockId Payload : Type} [Fintype Validator] [DecidableEq Validator]
variable [LinearOrder BlockId]
variable {cfg : Config Validator BlockId Payload}

omit [Fintype Validator] in
/-- **A successful build step.** -/
theorem tryBuild_some {s s' : State Validator BlockId Payload}
    {out : List (Output Validator BlockId Payload)} (h : tryBuild cfg s = some (s', out)) :
    ∃ r id, ∃ b : Block Validator BlockId Payload, ∃ hnew hrefs hpred,
      s.top = some r ∧ b.round = r + 1 ∧ b.creator = cfg.me ∧ id = cfg.idOf b ∧
      rowValid cfg.q (Function.update s.disk.blk id b) b ∧
      s'.disk = s.disk.insert id b hnew hrefs hpred ∧ s'.top = some (r + 1) ∧
      s'.pending = s.pending ∧ s'.lo = s.lo ∧ out = built cfg [(id, b)] := by
  unfold tryBuild at h
  split at h
  · rename_i r hr
    dsimp only at h
    split at h
    · split at h
      · rename_i hc
        rw [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        have hd := s.mirrors.checks_disk hc.2
        refine ⟨r, _, _, hc.1, hd.1, hd.2.1, hr, rfl, rfl, rfl,
          hd.2.2, release_disk _, release_top _, release_pending _, release_lo _, ?_⟩
        simp [built]
      · exact absurd h (by simp)
    · exact absurd h (by simp)
  · exact absurd h (by simp)

omit [Fintype Validator] in
/-- **A successful build step makes its block the node's own**, on its disk. -/
theorem tryBuild_own {s s' : State Validator BlockId Payload}
    {out : List (Output Validator BlockId Payload)} (h : tryBuild cfg s = some (s', out)) :
    ∃ id b, out = built cfg [(id, b)] ∧ s'.own = some id ∧ id ∈ s'.disk.ids ∧
      s'.disk.blk id = b := by
  unfold tryBuild at h
  split at h
  · rename_i r hr
    dsimp only at h
    split at h
    · split at h
      · rw [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        refine ⟨_, ⟨r + 1, cfg.me, refsAt cfg s.memory r s.own, cfg.payload (r + 1)⟩,
          by simp [built], release_own _, by simp [keep, Store.insert_ids], ?_⟩
        simp [keep, Store.insert_blk]
      · exact absurd h (by simp)
    · exact absurd h (by simp)
  · exact absurd h (by simp)

omit [Fintype Validator] in
/-- **The row's validity reads only rounds and authors** of the
references. -/
theorem rowValid_congr {q : ℕ} {blk blk' : BlockId → Block Validator BlockId Payload}
    {b : Block Validator BlockId Payload}
    (h : ∀ j ∈ b.refs, (blk j).round = (blk' j).round ∧ (blk j).creator = (blk' j).creator)
    (hv : rowValid q blk b) : rowValid q blk' b := by
  have hcr : creators blk b = creators blk' b :=
    Finset.image_congr fun j hj => (h j hj).2
  refine ⟨fun i hi => ?_, fun h0 => ?_, fun i hi j hj hij => ?_⟩
  · rw [← (h i hi).1]; exact hv.predecessor i hi
  · rw [← hcr]; exact hv.quorum h0
  · exact hv.clause i hi j hj (by rw [(h i hi).2, (h j hj).2]; exact hij)

/-- **One of the node's own blocks is good** against what it knew, `K`: its
own, identified by its hash, its references known, and valid under every
block map agreeing with `K`. -/
def Good (cfg : Config Validator BlockId Payload)
    (K : Set (BlockId × Block Validator BlockId Payload))
    (e : BlockId × Block Validator BlockId Payload) : Prop :=
  e.1 = cfg.idOf e.2 ∧ e.2.creator = cfg.me ∧ (∀ j ∈ e.2.refs, ∃ c, (j, c) ∈ K) ∧
    ∀ blk : BlockId → Block Validator BlockId Payload, (∀ x ∈ K, blk x.1 = x.2) →
      rowValid cfg.q blk e.2

omit [Fintype Validator] in
theorem Good.mono {K K' : Set (BlockId × Block Validator BlockId Payload)} (hK : K ⊆ K')
    {e : BlockId × Block Validator BlockId Payload} (h : Good cfg K e) : Good cfg K' e :=
  ⟨h.1, h.2.1, fun j hj => let ⟨c, hc⟩ := h.2.2.1 j hj; ⟨c, hK hc⟩,
    fun blk hblk => h.2.2.2 blk fun x hx => hblk x (hK hx)⟩

/-- **Own blocks below a top**: at strictly increasing rounds, none above
`t`. -/
def Rounds (B : List (BlockId × Block Validator BlockId Payload)) (t : ℕ) : Prop :=
  (B.map fun e => e.2.round).Pairwise (· < ·) ∧ ∀ e ∈ B, e.2.round ≤ t

omit [Fintype Validator] [DecidableEq Validator] [LinearOrder BlockId] in
/-- Blocks above the top, at strictly increasing rounds, extend the own
blocks to a new top. -/
theorem Rounds.append {B F : List (BlockId × Block Validator BlockId Payload)} {t t' : ℕ}
    (h : Rounds B t) (hF : (F.map fun e => e.2.round).Pairwise (· < ·))
    (hFt : ∀ e ∈ F, t < e.2.round ∧ e.2.round ≤ t') (htt : t ≤ t') : Rounds (B ++ F) t' := by
  refine ⟨?_, fun e he => ?_⟩
  · rw [List.map_append, List.pairwise_append]
    refine ⟨h.1, hF, fun a ha b hb => ?_⟩
    obtain ⟨x, hx, rfl⟩ := List.mem_map.mp ha
    obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hb
    exact lt_of_le_of_lt (h.2 x hx) (hFt y hy).1
  · rcases List.mem_append.mp he with he | he
    · exact (h.2 e he).trans htt
    · exact (hFt e he).2

/-- **Every block of the store is valid at the row**, under its map. -/
def StoreValid (q : ℕ) (st : Store Validator BlockId Payload) : Prop :=
  ∀ j ∈ st.ids, rowValid q st.blk (st.blk j)

omit [Fintype Validator] in
/-- **Accepting a block valid under the extended map keeps the store
valid.** -/
theorem StoreValid.insert {q : ℕ} {st : Store Validator BlockId Payload} (hs : StoreValid q st)
    {id : BlockId} {b : Block Validator BlockId Payload} {hnew hrefs hpred}
    (hv : rowValid q (Function.update st.blk id b) b) :
    StoreValid q (st.insert id b hnew hrefs hpred) := by
  have hlk : ∀ i, i ≠ id → (st.insert id b hnew hrefs hpred).blk i = st.blk i :=
    fun i hi => by simp only [Store.blk, Store.insert, treeMap_getD_insert_ne (Ne.symm hi)]
  intro j hj
  rw [Store.insert_ids] at hj
  by_cases h : j = id
  · subst h
    have hself : (st.insert j b hnew hrefs hpred).blk j = b := by
      simp only [Store.blk, Store.insert, Std.TreeMap.getD_insert_self]
    rw [hself]
    refine rowValid_congr (fun i hi => ?_) hv
    have hi' : i ≠ j := fun e => hnew (e ▸ hrefs hi)
    rw [Function.update_of_ne hi', hlk i hi']
    exact ⟨rfl, rfl⟩
  · rw [hlk j h]
    have hj' := (Finset.mem_insert.mp hj).resolve_left h
    refine rowValid_congr (fun i hi => ?_) (hs j hj')
    have hi' : i ≠ id := fun e => hnew (e ▸ st.complete j hj' i hi)
    rw [hlk i hi']
    exact ⟨rfl, rfl⟩

/-- **The store grows**: no block is lost and none changes. -/
def Grows (st st' : Store Validator BlockId Payload) : Prop :=
  st.ids ⊆ st'.ids ∧ st'.junk = st.junk ∧ ∀ j ∈ st.ids, st'.blk j = st.blk j

omit [Fintype Validator] [DecidableEq Validator] in
theorem Grows.refl (st : Store Validator BlockId Payload) : Grows st st :=
  ⟨subset_rfl, rfl, fun _ _ => rfl⟩

omit [Fintype Validator] [DecidableEq Validator] in
theorem Grows.trans {a b c : Store Validator BlockId Payload} (h₁ : Grows a b) (h₂ : Grows b c) :
    Grows a c :=
  ⟨h₁.1.trans h₂.1, h₂.2.1.trans h₁.2.1, fun j hj => (h₂.2.2 j (h₁.1 hj)).trans (h₁.2.2 j hj)⟩

omit [Fintype Validator] [DecidableEq Validator] in
/-- A grown store reads its old blocks alike. -/
theorem Grows.blk {st st' : Store Validator BlockId Payload} (h : Grows st st')
    {j : BlockId} (hj : j ∈ st.ids) : st'.blk j = st.blk j :=
  h.2.2 j hj

omit [Fintype Validator] [DecidableEq Validator] in
theorem Grows.insert (st : Store Validator BlockId Payload) {id : BlockId}
    {b : Block Validator BlockId Payload} {hnew hrefs hpred} :
    Grows st (st.insert id b hnew hrefs hpred) :=
  ⟨fun _ hj => Finset.mem_cons_of_mem (hb := hnew) hj, rfl, fun _ hj =>
    treeMap_getD_insert_ne (fun e => hnew (e ▸ hj))⟩

omit [Fintype Validator] in
theorem Grows.accept (st : Store Validator BlockId Payload) (id : BlockId)
    (b : Block Validator BlockId Payload) : Grows st (acceptOn cfg st id b) := by
  unfold acceptOn
  split
  · exact Grows.insert st
  · exact Grows.refl st

omit [Fintype Validator] in
theorem Grows.foldl : ∀ (l : List (BlockId × Block Validator BlockId Payload))
    (st : Store Validator BlockId Payload),
    Grows st (l.foldl (fun s e => acceptOn cfg s e.1 e.2) st)
  | [], st => Grows.refl st
  | e :: l, st => (Grows.accept st e.1 e.2).trans (Grows.foldl l _)

omit [Fintype Validator] in
theorem Grows.flush : ∀ (fuel : ℕ) (st : Store Validator BlockId Payload)
    (pend : List (BlockId × Block Validator BlockId Payload)),
    Grows st (flushOn cfg fuel st pend).1
  | 0, st, _ => Grows.refl st
  | fuel + 1, st, pend => by
    unfold flushOn
    dsimp only
    split
    · exact Grows.refl st
    · exact (Grows.foldl _ st).trans (Grows.flush fuel _ _)

omit [Fintype Validator] in
/-- The lowest round the node reads does not fall as its next undecided
slot and its top rise. -/
theorem floorOf_mono {s s' : State Validator BlockId Payload} (hlo : s.lo ≤ s'.lo)
    (ht : s.top.getD 0 ≤ s'.top.getD 0) : floorOf cfg s ≤ floorOf cfg s' :=
  min_le_min (cfg.slots.mono hlo) (Nat.sub_le_sub_right ht _)

omit [Fintype Validator] in
theorem tryBuild_floor {s s' : State Validator BlockId Payload}
    {out : List (Output Validator BlockId Payload)} (h : tryBuild cfg s = some (s', out)) :
    s'.floor = max s.floor (floorOf cfg s') := by
  unfold tryBuild at h
  split at h
  · dsimp only at h
    split at h
    · split at h
      · rw [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, -⟩ := h
        rw [release_floor]
        simp only [floorOf, release_lo, release_top]
        rfl
      · exact absurd h (by simp)
    · exact absurd h (by simp)
  · exact absurd h (by simp)

/-- **The invariant** of a node's state, against what it knew, `K`, and
its own blocks, `B`. -/
structure Inv (cfg : Config Validator BlockId Payload) (s : State Validator BlockId Payload)
    (K : Set (BlockId × Block Validator BlockId Payload))
    (B : List (BlockId × Block Validator BlockId Payload)) : Prop where
  known : ∀ j ∈ s.disk.ids, (j, s.disk.blk j) ∈ K
  pend : ∀ e ∈ s.pending, e ∈ K
  rounds : (s.top = none ∧ B = []) ∨ ∃ t, s.top = some t ∧ Rounds B t
  good : ∀ e ∈ B, Good cfg K e
  sub : ∀ e ∈ B, e ∈ K
  valid : StoreValid cfg.q s.disk
  own : ∀ j, s.own = some j → j ∈ s.disk.ids ∧ (j, s.disk.blk j) ∈ B
  floor : s.floor ≤ floorOf cfg s

omit [Fintype Validator] in
theorem Inv.mono {s : State Validator BlockId Payload}
    {K K' : Set (BlockId × Block Validator BlockId Payload)}
    {B : List (BlockId × Block Validator BlockId Payload)} (h : Inv cfg s K B) (hK : K ⊆ K') :
    Inv cfg s K' B :=
  ⟨fun j hj => hK (h.known j hj), fun e he => hK (h.pend e he), h.rounds,
    fun e he => (h.good e he).mono hK, fun e he => hK (h.sub e he), h.valid, h.own, h.floor⟩

omit [Fintype Validator] [DecidableEq Validator] in
/-- Accepting a known block keeps the store known. -/
theorem known_insert {st : Store Validator BlockId Payload}
    {K : Set (BlockId × Block Validator BlockId Payload)}
    (hK : ∀ j ∈ st.ids, (j, st.blk j) ∈ K) {id : BlockId}
    {b : Block Validator BlockId Payload} (hb : (id, b) ∈ K) {hnew hrefs hpred} :
    ∀ j ∈ (st.insert id b hnew hrefs hpred).ids, (j, (st.insert id b hnew hrefs hpred).blk j) ∈ K := by
  intro j hj
  rw [Store.insert_ids] at hj
  change (j, (st.map.insert id b).getD j st.junk) ∈ K
  by_cases h : j = id
  · subst h; rw [Std.TreeMap.getD_insert_self]; exact hb
  · rw [treeMap_getD_insert_ne (Ne.symm h)]
    exact hK j ((Finset.mem_insert.mp hj).resolve_left h)

omit [Fintype Validator] in
/-- **A build step keeps the invariant**, the new block known and good. -/
theorem Inv.tryBuild {s s' : State Validator BlockId Payload}
    {K : Set (BlockId × Block Validator BlockId Payload)}
    {B : List (BlockId × Block Validator BlockId Payload)}
    {out : List (Output Validator BlockId Payload)} (hi : Inv cfg s K B)
    (h : tryBuild cfg s = some (s', out)) :
    ∃ e, out = built cfg [e] ∧ Inv cfg s' (K ∪ {e}) (B ++ [e]) := by
  obtain ⟨r, id, b, hnew, hrefs, hpred, hr, hbr, hbc, hid, hv, hst, htop, hpd, hlo, hout⟩ :=
    tryBuild_some h
  obtain ⟨id', b', hout', hown, hid', hblk⟩ := tryBuild_own h
  have hK : K ⊆ K ∪ {(id, b)} := Set.subset_union_left
  have hmem : (id, b) ∈ K ∪ {(id, b)} := Set.mem_union_right _ rfl
  refine ⟨(id, b), hout, ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩⟩
  · rw [hst]
    exact known_insert (fun j hj => hK (hi.known j hj)) hmem
  · rw [hpd]; exact fun e he => hK (hi.pend e he)
  · right
    refine ⟨r + 1, htop, ?_⟩
    rcases hi.rounds with ⟨h0, -⟩ | ⟨t, ht, hB⟩
    · rw [hr] at h0; exact absurd h0 (by simp)
    · rw [hr, Option.some.injEq] at ht
      subst ht
      exact hB.append (by simp) (fun e he => by
        rw [List.mem_singleton] at he; subst he; rw [hbr]; omega) (by omega)
  · intro e he
    rcases List.mem_append.mp he with he | he
    · exact (hi.good e he).mono hK
    · rw [List.mem_singleton] at he
      subst he
      refine ⟨hid, hbc, fun j hj => ⟨_, hK (hi.known j (hrefs hj))⟩, fun blk hblk => ?_⟩
      refine rowValid_congr (fun j hj => ?_) hv
      have hjid : j ≠ id := fun e => hnew (e ▸ hrefs hj)
      rw [Function.update_of_ne hjid, hblk _ (hK (hi.known j (hrefs hj)))]
      exact ⟨rfl, rfl⟩
  · intro e he
    rcases List.mem_append.mp he with he | he
    · exact hK (hi.sub e he)
    · rw [List.mem_singleton] at he; subst he; exact hmem
  · rw [hst]; exact hi.valid.insert hv
  · have he : id' = id ∧ b' = b := by
      have h' := hout'.symm.trans hout
      simp only [built, List.flatMap_cons, List.flatMap_nil, List.append_nil, List.cons.injEq,
        Output.persist.injEq] at h'
      exact h'.1
    obtain ⟨rfl, rfl⟩ := he
    intro j hj
    rw [hown, Option.some.injEq] at hj
    subst hj
    exact ⟨hid', by rw [hblk]; simp⟩
  · rw [tryBuild_floor h]
    exact max_le (hi.floor.trans (floorOf_mono hlo.ge (by rw [hr, htop]; simp))) le_rfl

omit [Fintype Validator] in
/-- **Building keeps the invariant**, the new blocks known and good. -/
theorem Inv.progress : ∀ (fuel : ℕ) {s : State Validator BlockId Payload}
    {K : Set (BlockId × Block Validator BlockId Payload)}
    {B : List (BlockId × Block Validator BlockId Payload)}, Inv cfg s K B →
    ∃ bs, (progress cfg fuel s).2 = built cfg bs ∧
      Inv cfg (progress cfg fuel s).1 (K ∪ {x | x ∈ bs}) (B ++ bs)
  | 0, s, K, B, hi => ⟨[], rfl, by simpa [Node.progress] using hi⟩
  | fuel + 1, s, K, B, hi => by
    unfold Node.progress
    split
    · rename_i s₁ out h
      obtain ⟨e, hout, hi₁⟩ := hi.tryBuild h
      obtain ⟨bs, hbs, hi₂⟩ := Inv.progress fuel hi₁
      refine ⟨e :: bs, ?_, ?_⟩
      · simp only [hbs, hout, built, List.flatMap_cons, List.flatMap_nil, List.append_nil]
      · have hK : (K ∪ {e}) ∪ {x | x ∈ bs} = K ∪ {x | x ∈ e :: bs} := by
          ext x; simp only [Set.mem_union, Set.mem_singleton_iff, Set.mem_setOf_eq,
            List.mem_cons]; tauto
        rw [← hK]
        simpa using hi₂
    · exact ⟨[], rfl, by simpa using hi⟩

omit [Fintype Validator] [DecidableEq Validator] [LinearOrder BlockId] in
theorem broadcasts_append (a b : List (Output Validator BlockId Payload)) :
    broadcasts (a ++ b) = broadcasts a ++ broadcasts b :=
  List.filterMap_append

omit [Fintype Validator] [DecidableEq Validator] [LinearOrder BlockId] in
theorem commitsOf_append (a b : List (Output Validator BlockId Payload)) :
    commitsOf (a ++ b) = commitsOf a ++ commitsOf b :=
  List.filterMap_append

omit [Fintype Validator] [DecidableEq Validator] [LinearOrder BlockId] in
theorem persists_append (a b : List (Output Validator BlockId Payload)) :
    persists (a ++ b) = persists a ++ persists b :=
  List.filterMap_append

omit [Fintype Validator] in
theorem persists_built (bs : List (BlockId × Block Validator BlockId Payload)) :
    persists (built cfg bs) = bs := by
  induction bs with
  | nil => rfl
  | cons e bs ih =>
    simp only [built, List.flatMap_cons] at ih ⊢
    rw [persists_append, ih]
    rfl

omit [Fintype Validator] in
theorem broadcasts_built (bs : List (BlockId × Block Validator BlockId Payload)) :
    broadcasts (built cfg bs) = bs := by
  induction bs with
  | nil => rfl
  | cons e bs ih =>
    simp only [built, List.flatMap_cons] at ih ⊢
    rw [broadcasts_append, ih]
    rfl

/-- **A step's own blocks**: its outputs persist exactly `bs`, and
broadcast exactly `bs`. -/
def Out (bs : List (BlockId × Block Validator BlockId Payload))
    (out : List (Output Validator BlockId Payload)) : Prop :=
  persists out = bs ∧ broadcasts out = bs

omit [Fintype Validator] [DecidableEq Validator] [LinearOrder BlockId] in
theorem Out.append {a b : List (BlockId × Block Validator BlockId Payload)}
    {x y : List (Output Validator BlockId Payload)} (h₁ : Out a x) (h₂ : Out b y) :
    Out (a ++ b) (x ++ y) :=
  ⟨by rw [persists_append, h₁.1, h₂.1], by rw [broadcasts_append, h₁.2, h₂.2]⟩

omit [Fintype Validator] [DecidableEq Validator] [LinearOrder BlockId] in
theorem out_quiet {xs : List (Output Validator BlockId Payload)} (h : ∀ o ∈ xs, o.isQuiet) :
    Out [] xs := by
  induction xs with
  | nil => exact ⟨rfl, rfl⟩
  | cons o xs ih =>
    have ho := h o List.mem_cons_self
    obtain ⟨h₁, h₂⟩ := ih fun o' h' => h o' (List.mem_cons_of_mem _ h')
    have hp : persists [o] = [] ∧ broadcasts [o] = [] := by
      cases o <;> first | exact ⟨rfl, rfl⟩ | exact absurd ho (by simp [Output.isQuiet])
    refine ⟨?_, ?_⟩
    · rw [show o :: xs = [o] ++ xs from rfl, persists_append, hp.1, h₁]; rfl
    · rw [show o :: xs = [o] ++ xs from rfl, broadcasts_append, hp.2, h₂]; rfl

omit [Fintype Validator] in
theorem out_built (bs : List (BlockId × Block Validator BlockId Payload)) :
    Out bs (built cfg bs) :=
  ⟨persists_built bs, broadcasts_built bs⟩

omit [Fintype Validator] [DecidableEq Validator] [LinearOrder BlockId] in
theorem quiet_commits (ds : List (ℕ × Option BlockId)) :
    ∀ o ∈ (ds.map fun e => (Output.commit e.1 e.2 : Output Validator BlockId Payload)),
      o.isQuiet := by
  intro o ho
  obtain ⟨e, -, rfl⟩ := List.mem_map.mp ho
  rfl

omit [Fintype Validator] in
/-- An invariant read only from the disk, the pending blocks, the top
and the own block carries over to a state that keeps them. -/
theorem Inv.of_eq {s s' : State Validator BlockId Payload}
    {K : Set (BlockId × Block Validator BlockId Payload)}
    {B : List (BlockId × Block Validator BlockId Payload)} (hi : Inv cfg s K B)
    (hst : s'.disk = s.disk) (hpd : s'.pending = s.pending) (htop : s'.top = s.top)
    (hown : s'.own = s.own) (hfl : s'.floor = s.floor) (hlo : s.lo ≤ s'.lo) :
    Inv cfg s' K B :=
  ⟨by rw [hst]; exact hi.known, by rw [hpd]; exact hi.pend,
    by rw [htop]; exact hi.rounds, hi.good, hi.sub, by rw [hst]; exact hi.valid,
    by rw [hst, hown]; exact hi.own,
    by rw [hfl]; exact hi.floor.trans (floorOf_mono hlo (by rw [htop]))⟩

omit [Fintype Validator] in
/-- **Releasing the memory keeps the invariant.** -/
theorem Inv.release {s : State Validator BlockId Payload}
    {K : Set (BlockId × Block Validator BlockId Payload)}
    {B : List (BlockId × Block Validator BlockId Payload)} (hi : Inv cfg s K B) :
    Inv cfg (Node.release cfg s) K B := by
  have hf : floorOf cfg (Node.release cfg s) = floorOf cfg s := by
    simp only [floorOf, release_lo, release_top]
  refine ⟨?_, ?_, ?_, hi.good, hi.sub, ?_, ?_, ?_⟩
  · rw [release_disk]; exact hi.known
  · rw [release_pending]; exact hi.pend
  · rw [release_top]; exact hi.rounds
  · rw [release_disk]; exact hi.valid
  · rw [release_own, release_disk]; exact hi.own
  · rw [hf, release_floor]; exact max_le hi.floor le_rfl

omit [Fintype Validator] in
/-- **Deciding keeps the invariant** and outputs no block. -/
theorem Inv.decideStep {s : State Validator BlockId Payload}
    {K : Set (BlockId × Block Validator BlockId Payload)}
    {B : List (BlockId × Block Validator BlockId Payload)} (hi : Inv cfg s K B) :
    Out [] (decideStep cfg s).2 ∧ Inv cfg (decideStep cfg s).1 K B := by
  unfold Node.decideStep
  dsimp only
  split
  · exact ⟨out_quiet (quiet_commits _), Inv.release (hi.of_eq rfl rfl rfl rfl rfl
      (Nat.le_add_right _ _))⟩
  · exact ⟨⟨rfl, rfl⟩, hi⟩

omit [Fintype Validator] in
/-- Accepting a known block keeps the store known and valid. -/
theorem accept_known {st : Store Validator BlockId Payload}
    {K : Set (BlockId × Block Validator BlockId Payload)}
    (hK : ∀ j ∈ st.ids, (j, st.blk j) ∈ K) (hV : StoreValid cfg.q st)
    {id : BlockId} {b : Block Validator BlockId Payload} (hb : (id, b) ∈ K) :
    (∀ j ∈ (acceptOn cfg st id b).ids, (j, (acceptOn cfg st id b).blk j) ∈ K) ∧
      StoreValid cfg.q (acceptOn cfg st id b) := by
  unfold acceptOn
  split
  · rename_i h
    exact ⟨known_insert hK hb, hV.insert h.2.2.2⟩
  · exact ⟨hK, hV⟩

omit [Fintype Validator] in
theorem foldl_accept_known {K : Set (BlockId × Block Validator BlockId Payload)} :
    ∀ (l : List (BlockId × Block Validator BlockId Payload)) {st : Store Validator BlockId Payload},
    (∀ j ∈ st.ids, (j, st.blk j) ∈ K) → StoreValid cfg.q st → (∀ e ∈ l, e ∈ K) →
    let st' := l.foldl (fun s e => acceptOn cfg s e.1 e.2) st
    (∀ j ∈ st'.ids, (j, st'.blk j) ∈ K) ∧ StoreValid cfg.q st'
  | [], _, hK, hV, _ => ⟨hK, hV⟩
  | e :: l, st, hK, hV, hl => by
    have h₁ := accept_known (cfg := cfg) hK hV (hl e List.mem_cons_self)
    exact foldl_accept_known l h₁.1 h₁.2 fun x hx => hl x (List.mem_cons_of_mem _ hx)

omit [Fintype Validator] in
/-- **Flushing the pending blocks keeps store and pending known**, and the
store valid. -/
theorem flush_known {K : Set (BlockId × Block Validator BlockId Payload)} :
    ∀ (fuel : ℕ) {st : Store Validator BlockId Payload}
      {pend : List (BlockId × Block Validator BlockId Payload)},
    (∀ j ∈ st.ids, (j, st.blk j) ∈ K) → StoreValid cfg.q st → (∀ e ∈ pend, e ∈ K) →
    let r := flushOn cfg fuel st pend
    (∀ j ∈ r.1.ids, (j, r.1.blk j) ∈ K) ∧ (∀ e ∈ r.2, e ∈ K) ∧ StoreValid cfg.q r.1
  | 0, _, _, hK, hV, hp => ⟨hK, hp, hV⟩
  | fuel + 1, st, pend, hK, hV, hp => by
    unfold flushOn
    dsimp only
    split
    · exact ⟨hK, hp, hV⟩
    · have hsplit : ∀ e ∈ (pend.partition fun e => readyOn cfg st e).1 ++
          (pend.partition fun e => readyOn cfg st e).2, e ∈ K := by
        intro e he
        rw [List.partition_eq_filter_filter] at he
        rcases List.mem_append.mp he with he | he
        · exact hp e (List.mem_filter.mp he).1
        · exact hp e (List.mem_filter.mp he).1
      have h₁ := foldl_accept_known (cfg := cfg) _ hK hV
        fun e he => hsplit e (List.mem_append_left _ he)
      exact flush_known fuel h₁.1 h₁.2 fun e he => hsplit e (List.mem_append_right _ he)

omit [Fintype Validator] in
/-- **A flush keeps the invariant.** -/
theorem Inv.flushAll {s : State Validator BlockId Payload}
    {K : Set (BlockId × Block Validator BlockId Payload)}
    {B : List (BlockId × Block Validator BlockId Payload)} (hi : Inv cfg s K B) (fuel : ℕ) :
    Inv cfg (flush cfg fuel s) K B := by
  have hfl := flush_known (cfg := cfg) (K := K) fuel (st := s.disk) (pend := s.pending)
    hi.known hi.valid hi.pend
  have hg := Grows.flush (cfg := cfg) fuel s.disk s.pending
  refine ⟨?_, ?_, ?_, hi.good, hi.sub, ?_, ?_, ?_⟩
  · rw [flush_disk]; exact hfl.1
  · rw [flush_pending]; exact hfl.2.1
  · rw [flush_top]; exact hi.rounds
  · rw [flush_disk]; exact hfl.2.2
  · intro j hj
    rw [flush_own] at hj
    rw [flush_disk]
    exact ⟨hg.1 (hi.own j hj).1, by rw [hg.blk (hi.own j hj).1]; exact (hi.own j hj).2⟩
  · rw [flush_floor, show floorOf cfg (flush cfg fuel s) = floorOf cfg s by
      simp only [floorOf, flush_lo, flush_top]]
    exact hi.floor

omit [Fintype Validator] in
/-- **Arming changes only the armed round.** -/
theorem arm_eq (s : State Validator BlockId Payload) :
    ∃ a, (Node.arm cfg s).1 = { s with armed := a } := by
  unfold Node.arm
  split
  · split
    · exact ⟨_, rfl⟩
    · exact ⟨s.armed, rfl⟩
  · exact ⟨s.armed, rfl⟩

omit [Fintype Validator] in
@[simp] theorem arm_disk (s : State Validator BlockId Payload) :
    (Node.arm cfg s).1.disk = s.disk := by
  obtain ⟨a, ha⟩ := arm_eq (cfg := cfg) s; rw [ha]

omit [Fintype Validator] in
@[simp] theorem arm_pending (s : State Validator BlockId Payload) :
    (Node.arm cfg s).1.pending = s.pending := by
  obtain ⟨a, ha⟩ := arm_eq (cfg := cfg) s; rw [ha]

omit [Fintype Validator] in
@[simp] theorem arm_top (s : State Validator BlockId Payload) :
    (Node.arm cfg s).1.top = s.top := by
  obtain ⟨a, ha⟩ := arm_eq (cfg := cfg) s; rw [ha]

omit [Fintype Validator] in
@[simp] theorem arm_own (s : State Validator BlockId Payload) :
    (Node.arm cfg s).1.own = s.own := by
  obtain ⟨a, ha⟩ := arm_eq (cfg := cfg) s; rw [ha]

omit [Fintype Validator] in
@[simp] theorem arm_fired (s : State Validator BlockId Payload) :
    (Node.arm cfg s).1.fired = s.fired := by
  obtain ⟨a, ha⟩ := arm_eq (cfg := cfg) s; rw [ha]

omit [Fintype Validator] in
@[simp] theorem arm_lo (s : State Validator BlockId Payload) :
    (Node.arm cfg s).1.lo = s.lo := by
  obtain ⟨a, ha⟩ := arm_eq (cfg := cfg) s; rw [ha]

omit [Fintype Validator] in
@[simp] theorem arm_decided (s : State Validator BlockId Payload) :
    (Node.arm cfg s).1.decided = s.decided := by
  obtain ⟨a, ha⟩ := arm_eq (cfg := cfg) s; rw [ha]

omit [Fintype Validator] in
@[simp] theorem arm_memory (s : State Validator BlockId Payload) :
    (Node.arm cfg s).1.memory = s.memory := by
  obtain ⟨a, ha⟩ := arm_eq (cfg := cfg) s; rw [ha]

omit [Fintype Validator] in
@[simp] theorem arm_floor (s : State Validator BlockId Payload) :
    (Node.arm cfg s).1.floor = s.floor := by
  obtain ⟨a, ha⟩ := arm_eq (cfg := cfg) s; rw [ha]

omit [Fintype Validator] in
theorem advance_memory (s : State Validator BlockId Payload) :
    (Node.advance cfg s).1.memory = (Node.pass cfg s).1.memory := arm_memory _

omit [Fintype Validator] in
theorem advance_floor (s : State Validator BlockId Payload) :
    (Node.advance cfg s).1.floor = (Node.pass cfg s).1.floor := arm_floor _

omit [Fintype Validator] in
theorem advance_disk (s : State Validator BlockId Payload) :
    (Node.advance cfg s).1.disk = (Node.pass cfg s).1.disk := arm_disk _

omit [Fintype Validator] in
theorem advance_pending (s : State Validator BlockId Payload) :
    (Node.advance cfg s).1.pending = (Node.pass cfg s).1.pending := arm_pending _

omit [Fintype Validator] in
theorem advance_top (s : State Validator BlockId Payload) :
    (Node.advance cfg s).1.top = (Node.pass cfg s).1.top := arm_top _

omit [Fintype Validator] in
theorem advance_own (s : State Validator BlockId Payload) :
    (Node.advance cfg s).1.own = (Node.pass cfg s).1.own := arm_own _

omit [Fintype Validator] in
theorem advance_fired (s : State Validator BlockId Payload) :
    (Node.advance cfg s).1.fired = (Node.pass cfg s).1.fired := arm_fired _

omit [Fintype Validator] in
theorem advance_lo (s : State Validator BlockId Payload) :
    (Node.advance cfg s).1.lo = (Node.pass cfg s).1.lo := arm_lo _

omit [Fintype Validator] in
theorem advance_snd (s : State Validator BlockId Payload) :
    (Node.advance cfg s).2 = (Node.pass cfg s).2 ++ (Node.arm cfg (Node.pass cfg s).1).2 := rfl

omit [Fintype Validator] in
/-- **Arming outputs only the timer of the top round**, set once the disk
holds `q` authors of it. -/
theorem mem_arm {s : State Validator BlockId Payload} {o : Output Validator BlockId Payload}
    (h : o ∈ (Node.arm cfg s).2) :
    ∃ r, s.top = some r ∧ cfg.q ≤ (s.disk.authorsAt r).card ∧ (Node.arm cfg s).1.armed = some r ∧
      o = .setTimer r (cfg.timeout r) := by
  unfold Node.arm at h ⊢
  split at h
  · rename_i r ht
    split at h
    · rename_i hc
      rw [List.mem_singleton] at h
      refine ⟨r, ht, hc.2.trans (Finset.card_le_card (s.mirrors.authorsAt_sub r)), ?_, h⟩
      simp only [ht, if_pos hc]
    · exact absurd h List.not_mem_nil
  · exact absurd h List.not_mem_nil

omit [Fintype Validator] in
theorem arm_quiet (s : State Validator BlockId Payload) :
    ∀ o ∈ (Node.arm cfg s).2, o.isQuiet := fun o ho => by
  obtain ⟨r, -, -, -, rfl⟩ := mem_arm ho; rfl

omit [Fintype Validator] in
theorem persists_arm (s : State Validator BlockId Payload) : persists (Node.arm cfg s).2 = [] :=
  List.filterMap_eq_nil_iff.mpr fun o ho => by obtain ⟨r, -, -, -, rfl⟩ := mem_arm ho; rfl

omit [Fintype Validator] in
theorem commitsOf_arm (s : State Validator BlockId Payload) : commitsOf (Node.arm cfg s).2 = [] :=
  List.filterMap_eq_nil_iff.mpr fun o ho => by obtain ⟨r, -, -, -, rfl⟩ := mem_arm ho; rfl

omit [Fintype Validator] in
/-- **Advancing keeps the invariant**, and its own blocks are the built
ones. -/
theorem Inv.advance {s : State Validator BlockId Payload}
    {K : Set (BlockId × Block Validator BlockId Payload)}
    {B : List (BlockId × Block Validator BlockId Payload)} (hi : Inv cfg s K B) :
    ∃ bs, Out bs (advance cfg s).2 ∧ Inv cfg (advance cfg s).1 (K ∪ {x | x ∈ bs}) (B ++ bs) := by
  obtain ⟨bs, hbs, hi₁⟩ := hi.progress (s.disk.topRound + 2)
  obtain ⟨hds, hi₂⟩ := hi₁.decideStep
  have hi₃ := hi₂.flushAll (fuel := ((Node.decideStep cfg
    (Node.progress cfg (s.disk.topRound + 2) s).1).1.pending.length + 1))
  obtain ⟨a, ha⟩ := arm_eq (cfg := cfg) (Node.pass cfg s).1
  refine ⟨bs, ?_, ?_⟩
  · simp only [Node.advance, Node.pass]
    rw [hbs]
    simpa using ((out_built bs).append hds).append (out_quiet (arm_quiet _))
  · simp only [Node.advance]
    rw [ha]
    exact hi₃.of_eq rfl rfl rfl rfl rfl le_rfl

omit [Fintype Validator] in
/-- A settle takes at least one pass. -/
theorem passes_succ (s : State Validator BlockId Payload) : ∃ n, passes cfg s = n + 1 := ⟨_, rfl⟩

omit [Fintype Validator] in
theorem quiesce_succ (n : ℕ) (s : State Validator BlockId Payload) :
    quiesce cfg (n + 1) s =
      if (advance cfg s).1.top = s.top ∧ (advance cfg s).1.pending.length = s.pending.length ∧
          (advance cfg s).1.lo = s.lo then advance cfg s
      else ((quiesce cfg n (advance cfg s).1).1,
        (advance cfg s).2 ++ (quiesce cfg n (advance cfg s).1).2) := rfl

omit [Fintype Validator] in
/-- **A pass stops the settle or is followed by the rest.** -/
theorem quiesce_succ_cases (n : ℕ) (s : State Validator BlockId Payload) :
    quiesce cfg (n + 1) s = advance cfg s ∨
      quiesce cfg (n + 1) s = ((quiesce cfg n (advance cfg s).1).1,
        (advance cfg s).2 ++ (quiesce cfg n (advance cfg s).1).2) := by
  rw [quiesce_succ]
  split
  · exact Or.inl rfl
  · exact Or.inr rfl

omit [Fintype Validator] in
/-- **A relation pass by pass holds across the passes**: one reflexive
and transitive along outputs, that each pass keeps under an invariant. -/
theorem quiesce_rel {P : State Validator BlockId Payload → Prop}
    {R : State Validator BlockId Payload → List (Output Validator BlockId Payload) →
      State Validator BlockId Payload → Prop}
    (hrefl : ∀ s, R s [] s) (htrans : ∀ a o₁ b o₂ c, R a o₁ b → R b o₂ c → R a (o₁ ++ o₂) c)
    (hadv : ∀ s, P s → R s (advance cfg s).2 (advance cfg s).1 ∧ P (advance cfg s).1) :
    ∀ (n : ℕ) (s : State Validator BlockId Payload), P s →
      R s (quiesce cfg n s).2 (quiesce cfg n s).1 ∧ P (quiesce cfg n s).1
  | 0, s, h => ⟨hrefl s, h⟩
  | n + 1, s, h => by
    rw [quiesce_succ]
    split
    · exact hadv s h
    · obtain ⟨h₁, h₂⟩ := hadv s h
      obtain ⟨h₃, h₄⟩ := quiesce_rel hrefl htrans hadv n _ h₂
      exact ⟨htrans _ _ _ _ _ h₁ h₃, h₄⟩

omit [Fintype Validator] in
/-- **An invariant each pass keeps holds across the passes.** -/
theorem quiesce_ind {P : State Validator BlockId Payload → Prop}
    (hadv : ∀ s, P s → P (advance cfg s).1) (n : ℕ) (s : State Validator BlockId Payload)
    (h : P s) : P (quiesce cfg n s).1 :=
  (quiesce_rel (P := P) (R := fun _ _ _ => True) (fun _ => trivial) (fun _ _ _ _ _ _ _ => trivial)
    (fun s h => ⟨trivial, hadv s h⟩) n s h).2

omit [Fintype Validator] in
/-- **Advancing until nothing changes keeps the invariant**, and its own
blocks are the built ones. -/
theorem Inv.quiesce : ∀ (n : ℕ) {s : State Validator BlockId Payload}
    {K : Set (BlockId × Block Validator BlockId Payload)}
    {B : List (BlockId × Block Validator BlockId Payload)}, Inv cfg s K B →
    ∃ bs, Out bs (quiesce cfg n s).2 ∧
      Inv cfg (quiesce cfg n s).1 (K ∪ {x | x ∈ bs}) (B ++ bs)
  | 0, s, K, B, hi => ⟨[], ⟨rfl, rfl⟩, by
      simp only [Node.quiesce, List.append_nil]; exact hi.mono fun x hx => Or.inl hx⟩
  | n + 1, s, K, B, hi => by
    rw [quiesce_succ]
    split
    · exact hi.advance
    · obtain ⟨bs, ho, hi₁⟩ := hi.advance
      obtain ⟨bs', ho', hi₂⟩ := Inv.quiesce n hi₁
      refine ⟨bs ++ bs', ho.append ho', ?_⟩
      rw [← List.append_assoc]
      exact hi₂.mono fun x hx => by
        simp only [Set.mem_union, Set.mem_setOf_eq, List.mem_append] at hx ⊢
        tauto

omit [Fintype Validator] in
/-- **Settling keeps the invariant**, and its own blocks are the built
ones. -/
theorem Inv.settle {s : State Validator BlockId Payload}
    {K : Set (BlockId × Block Validator BlockId Payload)}
    {B : List (BlockId × Block Validator BlockId Payload)} (hi : Inv cfg s K B) :
    ∃ bs, Out bs (Node.settle cfg s).2 ∧
      Inv cfg (Node.settle cfg s).1 (K ∪ {x | x ∈ bs}) (B ++ bs) :=
  Inv.quiesce _ hi

omit [Fintype Validator] in
/-- **Settling keeps the invariant**, after outputs with no block of the
node's own, at a larger knowledge. -/
theorem Inv.settle_of {s : State Validator BlockId Payload}
    {K K' : Set (BlockId × Block Validator BlockId Payload)}
    {B : List (BlockId × Block Validator BlockId Payload)} (hi : Inv cfg s K B) (hK : K ⊆ K')
    (pre : List (Output Validator BlockId Payload)) (hpre : ∀ o ∈ pre, o.isQuiet) :
    ∃ bs, Out bs (pre ++ (Node.settle cfg s).2) ∧
      Inv cfg (Node.settle cfg s).1 (K' ∪ {x | x ∈ bs}) (B ++ bs) := by
  obtain ⟨bs, ho, hi'⟩ := hi.settle
  refine ⟨bs, by simpa using (out_quiet hpre).append ho, hi'.mono fun x hx => ?_⟩
  rcases hx with hx | hx
  · exact Or.inl (hK hx)
  · exact Or.inr hx

/-- **A step's blocks**: its outputs persist exactly `bs` and broadcast
each of them, and besides broadcast only blocks of `B`, the node's own
blocks before the step. -/
def Sent (B bs : List (BlockId × Block Validator BlockId Payload))
    (out : List (Output Validator BlockId Payload)) : Prop :=
  persists out = bs ∧ (∀ e ∈ bs, e ∈ broadcasts out) ∧ ∀ e ∈ broadcasts out, e ∈ B ++ bs

omit [Fintype Validator] [DecidableEq Validator] [LinearOrder BlockId] in
theorem Sent.of_out {B bs : List (BlockId × Block Validator BlockId Payload)}
    {out : List (Output Validator BlockId Payload)} (h : Out bs out) : Sent B bs out :=
  ⟨h.1, fun e he => h.2 ▸ he, fun e he => List.mem_append_right _ (h.2 ▸ he)⟩

/-- **A timer step's state** is the settle's after the timer fires,
whether or not the node resends. -/
theorem step_timer_fst (s : State Validator BlockId Payload) (r : ℕ) :
    (Node.step cfg s (.timer r)).1 = (Node.settle cfg { s with fired := fire s r }).1 := by
  simp only [Node.step]; split <;> rfl

/-- A timer step, read as the settle's state and the step's outputs. -/
theorem step_timer_eq (s : State Validator BlockId Payload) (r : ℕ) :
    Node.step cfg s (.timer r) =
      ((Node.settle cfg { s with fired := fire s r }).1, (Node.step cfg s (.timer r)).2) :=
  Prod.ext (step_timer_fst s r) rfl

/-- **A timer step's outputs**: the settle's, then possibly a resend. -/
theorem step_timer_snd (s : State Validator BlockId Payload) (r : ℕ) :
    (Node.step cfg s (.timer r)).2 = (Node.settle cfg { s with fired := fire s r }).2 ∨
      (Node.step cfg s (.timer r)).2 = (Node.settle cfg { s with fired := fire s r }).2 ++
        Node.resend cfg (Node.settle cfg { s with fired := fire s r }).1 := by
  simp only [Node.step]; split
  · exact Or.inr rfl
  · exact Or.inl rfl

omit [Fintype Validator] in
/-- **Asking again is a request**: its outputs are fetches. -/
theorem mem_refetch {s : State Validator BlockId Payload} {o : Output Validator BlockId Payload}
    (h : o ∈ Node.refetch s) : ∃ peer r ids, o = .fetch peer r ids := by
  unfold Node.refetch at h
  obtain ⟨e, -, he⟩ := List.mem_filterMap.mp h
  dsimp only at he
  split at he
  · cases he
  · rw [Option.some.injEq] at he; exact ⟨_, _, _, he.symm⟩

omit [Fintype Validator] in
/-- **Resending outputs, besides fetches, the top block and the retry
timer.** -/
theorem mem_resend {s : State Validator BlockId Payload} {o : Output Validator BlockId Payload}
    (h : o ∈ Node.resend cfg s) :
    (∃ peer r ids, o = .fetch peer r ids) ∨ ∃ r j, s.top = some r ∧ s.own = some j ∧
      (o = .broadcast j (s.disk.blk j) ∨ o = .setTimer (r - 1) (2 * cfg.timeout (r - 1))) := by
  unfold Node.resend at h
  rcases List.mem_append.mp h with h | h
  · split at h
    · rename_i r j ht ho
      simp only [List.mem_cons, List.not_mem_nil, or_false] at h
      exact Or.inr ⟨r, j, ht, ho, h⟩
    · exact absurd h List.not_mem_nil
  · exact Or.inl (mem_refetch h)

omit [Fintype Validator] in
/-- **Setting the top round's timer again** sets it, if it was set. -/
theorem mem_rearm {s : State Validator BlockId Payload} {o : Output Validator BlockId Payload}
    (h : o ∈ Node.rearm cfg s) :
    ∃ r, s.top = some r ∧ s.armed = some r ∧ o = .setTimer r (cfg.timeout r) := by
  unfold Node.rearm at h
  split at h
  · rename_i r ht
    split at h
    · rename_i ha
      rw [List.mem_singleton] at h; exact ⟨r, ht, ha, h⟩
    · exact absurd h List.not_mem_nil
  · exact absurd h List.not_mem_nil

omit [Fintype Validator] in
theorem persists_rearm (s : State Validator BlockId Payload) : persists (Node.rearm cfg s) = [] :=
  List.filterMap_eq_nil_iff.mpr fun o ho => by obtain ⟨r, -, -, rfl⟩ := mem_rearm ho; rfl

omit [Fintype Validator] in
theorem commitsOf_rearm (s : State Validator BlockId Payload) :
    commitsOf (Node.rearm cfg s) = [] :=
  List.filterMap_eq_nil_iff.mpr fun o ho => by obtain ⟨r, -, -, rfl⟩ := mem_rearm ho; rfl

omit [Fintype Validator] in
theorem rearm_quiet (s : State Validator BlockId Payload) :
    ∀ o ∈ Node.rearm cfg s, o.isQuiet := fun o ho => by
  obtain ⟨r, -, -, rfl⟩ := mem_rearm ho; rfl

omit [Fintype Validator] [DecidableEq Validator] [LinearOrder BlockId] in
/-- **Outputs with no block of the node's own keep a step's blocks.** -/
theorem Sent.quiet_append {B bs : List (BlockId × Block Validator BlockId Payload)}
    {out out' : List (Output Validator BlockId Payload)} (h : Sent B bs out)
    (hq : ∀ o ∈ out', o.isQuiet) : Sent B bs (out ++ out') := by
  obtain ⟨hp, hb⟩ := out_quiet hq
  refine ⟨by rw [persists_append, hp, h.1, List.append_nil], fun e he => ?_, fun e he => ?_⟩
  · rw [broadcasts_append]; exact List.mem_append_left _ (h.2.1 e he)
  · rw [broadcasts_append, hb, List.append_nil] at he; exact h.2.2 e he

omit [Fintype Validator] in
/-- Resending outputs no decision. -/
theorem commitsOf_resend (s : State Validator BlockId Payload) :
    commitsOf (Node.resend cfg s) = [] :=
  List.filterMap_eq_nil_iff.mpr fun o ho => by
    rcases mem_resend ho with ⟨_, _, _, rfl⟩ | ⟨_, _, -, -, rfl | rfl⟩ <;> rfl

omit [Fintype Validator] in
/-- Resending persists no block. -/
theorem persists_resend (s : State Validator BlockId Payload) :
    persists (Node.resend cfg s) = [] :=
  List.filterMap_eq_nil_iff.mpr fun o ho => by
    rcases mem_resend ho with ⟨_, _, _, rfl⟩ | ⟨_, _, -, -, rfl | rfl⟩ <;> rfl

/-- A timer step persists what its settle persists. -/
theorem persists_step_timer (s : State Validator BlockId Payload) (r : ℕ) :
    persists (Node.step cfg s (.timer r)).2 =
      persists (Node.settle cfg { s with fired := fire s r }).2 := by
  rcases step_timer_snd (cfg := cfg) s r with h | h <;> rw [h]
  rw [persists_append, persists_resend, List.append_nil]

/-- A timer step outputs the decisions its settle outputs. -/
theorem commitsOf_step_timer (s : State Validator BlockId Payload) (r : ℕ) :
    commitsOf (Node.step cfg s (.timer r)).2 =
      commitsOf (Node.settle cfg { s with fired := fire s r }).2 := by
  rcases step_timer_snd (cfg := cfg) s r with h | h <;> rw [h]
  rw [commitsOf_append, commitsOf_resend, List.append_nil]

omit [Fintype Validator] in
/-- **The timer a resend sets** is the round's below the top, for twice
its timeout. -/
theorem mem_resend_setTimer {s : State Validator BlockId Payload} {r a : ℕ}
    (h : Output.setTimer r a ∈ Node.resend cfg s) :
    ∃ t, s.top = some t ∧ r = t - 1 ∧ a = 2 * cfg.timeout r := by
  rcases mem_resend h with ⟨_, _, _, h⟩ | ⟨t, j, ht, -, h | h⟩
  · cases h
  · cases h
  · rw [Output.setTimer.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨t, ht, rfl, rfl⟩

omit [Fintype Validator] in
/-- **Resending broadcasts one of the node's own blocks** and persists
none. -/
theorem Sent.resend {s : State Validator BlockId Payload}
    {K : Set (BlockId × Block Validator BlockId Payload)}
    {B bs : List (BlockId × Block Validator BlockId Payload)}
    {out : List (Output Validator BlockId Payload)} (h : Sent B bs out)
    (hi : Inv cfg s K (B ++ bs)) : Sent B bs (out ++ Node.resend cfg s) := by
  have hr : persists (Node.resend cfg s) = [] ∧
      ∀ e ∈ broadcasts (Node.resend cfg s), e ∈ B ++ bs := by
    refine ⟨persists_resend s, fun e he => ?_⟩
    obtain ⟨o, ho, he⟩ := List.mem_filterMap.mp he
    rcases mem_resend ho with ⟨_, _, _, rfl⟩ | ⟨r, j, -, hj, rfl | rfl⟩
    · cases he
    · simp only [Option.some.injEq] at he
      subst he
      exact (hi.own j hj).2
    · cases he
  refine ⟨by rw [persists_append, hr.1, h.1, List.append_nil], fun e he => ?_, fun e he => ?_⟩
  · rw [broadcasts_append]; exact List.mem_append_left _ (h.2.1 e he)
  · rw [broadcasts_append] at he
    rcases List.mem_append.mp he with he | he
    · exact h.2.2 e he
    · exact hr.2 e he

/-- **A step keeps the invariant**: what it was given and its own blocks
are known, and its own blocks are good. -/
theorem Inv.step {s : State Validator BlockId Payload}
    {K : Set (BlockId × Block Validator BlockId Payload)}
    {B : List (BlockId × Block Validator BlockId Payload)} (hi : Inv cfg s K B)
    (i : Input Validator BlockId Payload) :
    ∃ bs, Sent B bs (Node.step cfg s i).2 ∧
      Inv cfg (Node.step cfg s i).1 (K ∪ {x | x ∈ delivered cfg [i]} ∪ {x | x ∈ bs}) (B ++ bs) := by
  let K' := K ∪ {x | x ∈ delivered cfg [i]}
  have hsub : K ⊆ K' := fun x hx => Or.inl hx
  have hnil : ∀ (xs : List (Output Validator BlockId Payload)), (∀ o ∈ xs, o.isQuiet) →
      ∃ bs, Sent B bs xs ∧ Inv cfg s (K' ∪ {x | x ∈ bs}) (B ++ bs) :=
    fun xs hxs => ⟨[], Sent.of_out (out_quiet hxs), by simpa using hi.mono hsub⟩
  have hnil' := hnil [] (by simp)
  cases i with
  | start =>
    simp only [Node.step]
    split
    · rename_i h₁
      split
      · rename_i h₂
        have hB : B = [] := by
          rcases hi.rounds with ⟨-, hB⟩ | ⟨t, ht, -⟩
          · exact hB
          · rw [h₁.1] at ht; exact absurd ht (by simp)
        let e : BlockId × Block Validator BlockId Payload := (cfg.idOf cfg.genesis, cfg.genesis)
        have hr₀ : e.2.refs ⊆ s.disk.ids := fun _ hj => absurd hj (Finset.notMem_empty _)
        have hp₀ : ∀ j ∈ e.2.refs, (s.disk.blk j).round + 1 = e.2.round :=
          fun j hj => absurd hj (Finset.notMem_empty j)
        have hi₀ : Inv cfg { keep s e.1 e.2 h₂.1 hr₀ hp₀ with top := some 0, own := some e.1 }
            (K ∪ {x | x ∈ [e]}) (B ++ [e]) := by
          refine ⟨known_insert (hnew := h₂.1) (hrefs := hr₀) (hpred := hp₀)
              (fun j hj => Set.subset_union_left (hi.known j hj)) (by simp [e]),
            fun x hx => Set.subset_union_left (hi.pend x hx), Or.inr ⟨0, rfl, ?_⟩,
            fun x hx => ?_, fun x hx => ?_, hi.valid.insert (hnew := h₂.1) (hrefs := hr₀)
              (hpred := hp₀) h₂.2, fun j hj => ?_, ?_⟩
          · rw [hB, List.nil_append]
            exact ⟨by simp, fun x hx => by rw [List.mem_singleton] at hx; subst hx; rfl⟩
          · rw [hB, List.nil_append, List.mem_singleton] at hx
            subst hx
            refine ⟨rfl, rfl, fun j hj => absurd hj (Finset.notMem_empty j), fun blk _ => ?_⟩
            exact rowValid_congr (fun j hj => absurd hj (Finset.notMem_empty j)) h₂.2
          · rw [hB, List.nil_append, List.mem_singleton] at hx
            subst hx; simp
          · rw [Option.some.injEq] at hj
            subst hj
            refine ⟨by simp [keep, Store.insert_ids], ?_⟩
            simp [keep, Store.insert_blk, e]
          · have := hi.floor
            simp only [floorOf, h₁.1, Option.getD_none] at this
            simpa [floorOf, keep] using this
        obtain ⟨bs, ho, hi'⟩ := hi₀.settle
        refine ⟨e :: bs, ?_, ?_⟩
        · exact Sent.of_out ((out_built [e]).append ho)
        · refine (by simpa using hi' : Inv cfg _ (K ∪ {x | x ∈ [e]} ∪ {x | x ∈ bs}) (B ++ e :: bs)).mono
            fun x hx => ?_
          simp only [Set.mem_union, Set.mem_setOf_eq, List.mem_cons] at hx ⊢
          tauto
      · exact hnil'
    · exact hnil'
  | deliver id b =>
    simp only [Node.step]
    split
    · rename_i hc
      have hd : delivered cfg [Input.deliver id b] = [(id, b)] := by simp [delivered, hc.1]
      have hmem : (id, b) ∈ K' := Or.inr (by rw [hd]; exact List.mem_singleton_self _)
      have hi₁ : Inv cfg { s with pending := (id, b) :: s.pending } K' B :=
        ⟨fun j hj => hsub (hi.known j hj), fun x hx => by
          rcases List.mem_cons.mp hx with rfl | hx
          · exact hmem
          · exact hsub (hi.pend x hx), hi.rounds, fun x hx => (hi.good x hx).mono hsub,
          fun x hx => hsub (hi.sub x hx), hi.valid, hi.own, hi.floor⟩
      have hi₀ := hi₁.flushAll (s.pending.length + 1)
      generalize missing
        (flush cfg (s.pending.length + 1) { s with pending := (id, b) :: s.pending }) b = miss
      refine Exists.imp (fun bs h => ⟨Sent.of_out h.1, h.2⟩)
        (hi₀.settle_of subset_rfl _ fun o ho => ?_)
      split at ho
      · simp at ho
      · rw [List.mem_singleton] at ho; subst ho; rfl
    · exact hnil'
  | timer r =>
    simp only [Node.step]
    obtain ⟨bs, ho, hi'⟩ :=
      ((hi.mono hsub).of_eq (s' := { s with fired := fire s r }) rfl rfl rfl rfl rfl le_rfl).settle
    split
    · exact ⟨bs, (Sent.of_out ho).resend hi', hi'⟩
    · exact ⟨bs, Sent.of_out ho, hi'⟩
  | fetchRequest peer r ids =>
    simp only [Node.step]
    refine hnil _ fun o ho => ?_
    obtain ⟨j, -, rfl⟩ := List.mem_map.mp ho
    rfl
  | restart =>
    simp only [Node.step]
    have h := (Sent.of_out (B := B) (bs := []) (out := []) ⟨rfl, rfl⟩).resend (cfg := cfg)
      (s := s) (K := K) (by simpa using hi)
    refine ⟨[], ?_, by simpa using hi.mono hsub⟩
    have h' := h.quiet_append (rearm_quiet (cfg := cfg) s)
    simpa using h'

omit [Fintype Validator] in
/-- What was delivered is identified by its hash. -/
theorem id_of_delivered {is : List (Input Validator BlockId Payload)}
    {x : BlockId × Block Validator BlockId Payload} (hx : x ∈ delivered cfg is) :
    x.1 = cfg.idOf x.2 := by
  obtain ⟨i, -, hx⟩ := List.mem_flatMap.mp hx
  cases i with
  | deliver id b =>
    simp only at hx
    split at hx
    · rename_i h; rw [List.mem_singleton] at hx; subst hx; exact h
    · exact absurd hx List.not_mem_nil
  | _ => exact absurd hx List.not_mem_nil

omit [Fintype Validator] in
theorem delivered_cons (i : Input Validator BlockId Payload)
    (is : List (Input Validator BlockId Payload)) :
    delivered cfg (i :: is) = delivered cfg [i] ++ delivered cfg is := by
  simp [delivered, List.flatMap_cons]

/-- **A run keeps the invariant**: what it was given and its own blocks
are known, and its own blocks are good. -/
theorem Inv.run : ∀ (is : List (Input Validator BlockId Payload))
    {s : State Validator BlockId Payload} {K : Set (BlockId × Block Validator BlockId Payload)}
    {B : List (BlockId × Block Validator BlockId Payload)}, Inv cfg s K B →
    Inv cfg (Node.run cfg s is).1
      (K ∪ {x | x ∈ delivered cfg is} ∪ {x | x ∈ persists (Node.run cfg s is).2})
      (B ++ persists (Node.run cfg s is).2)
  | [], s, K, B, hi => by simpa [Node.run, delivered, persists] using hi
  | i :: is, s, K, B, hi => by
    obtain ⟨bs, ho, hi₁⟩ := hi.step i
    have ih := Inv.run is hi₁
    simp only [Node.run]
    rw [persists_append, ho.1]
    have hK : K ∪ {x | x ∈ delivered cfg [i]} ∪ {x | x ∈ bs} ∪
        {x | x ∈ delivered cfg is} ∪
          {x | x ∈ persists (Node.run cfg (Node.step cfg s i).1 is).2} =
        K ∪ {x | x ∈ delivered cfg (i :: is)} ∪
          {x | x ∈ bs ++ persists (Node.run cfg (Node.step cfg s i).1 is).2} := by
      rw [delivered_cons i is]
      ext x
      simp only [Set.mem_union, Set.mem_setOf_eq, List.mem_append]
      tauto
    rw [← hK, ← List.append_assoc]
    exact ih

/-- **A run broadcasts what it persists**, and besides only the node's
own blocks before it. -/
theorem broadcasts_run : ∀ (is : List (Input Validator BlockId Payload))
    {s : State Validator BlockId Payload} {K : Set (BlockId × Block Validator BlockId Payload)}
    {B : List (BlockId × Block Validator BlockId Payload)}, Inv cfg s K B →
    (∀ e ∈ persists (Node.run cfg s is).2, e ∈ broadcasts (Node.run cfg s is).2) ∧
      ∀ e ∈ broadcasts (Node.run cfg s is).2, e ∈ B ++ persists (Node.run cfg s is).2
  | [], _, _, _, _ => ⟨fun _ h => absurd h (by simp [Node.run, persists]),
      fun _ h => absurd h (by simp [Node.run, broadcasts])⟩
  | i :: is, _, _, B, hi => by
    obtain ⟨bs, ho, hi₁⟩ := hi.step i
    obtain ⟨ih₁, ih₂⟩ := broadcasts_run is hi₁
    simp only [Node.run]
    rw [broadcasts_append, persists_append, ho.1]
    refine ⟨fun e he => ?_, fun e he => ?_⟩
    · rcases List.mem_append.mp he with he | he
      · exact List.mem_append_left _ (ho.2.1 e he)
      · exact List.mem_append_right _ (ih₁ e he)
    · rcases List.mem_append.mp he with he | he
      · rw [← List.append_assoc]; exact List.mem_append_left _ (ho.2.2 e he)
      · rw [← List.append_assoc]; exact ih₂ e he

omit [Fintype Validator] in
/-- The initial state meets the invariant, with nothing known or broadcast. -/
theorem Inv.init : Inv cfg (State.init cfg) ∅ [] where
  known := fun _ h => absurd h (Finset.notMem_empty _)
  pend := fun _ h => absurd h (List.not_mem_nil)
  rounds := Or.inl ⟨rfl, rfl⟩
  good := fun _ h => absurd h (List.not_mem_nil)
  sub := fun _ h => absurd h (List.not_mem_nil)
  valid := fun _ h => absurd h (Finset.notMem_empty _)
  own := fun _ h => absurd h (by simp [State.init])
  floor := Nat.zero_le _

end Node

end LeanDag
