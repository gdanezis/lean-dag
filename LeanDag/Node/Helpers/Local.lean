import LeanDag.Node.Model.Run
import LeanDag.Node.Helpers.ReadsView
/-!
# One node at a time — the lemmas

A successful build step adds one block at the round above the node's top,
its own, identified by its hash, with accepted references, and valid
under the store's map (`tryBuild_some`); building, deciding and flushing
change the parts of the state the claims read only so. Along any run the
node's state meets `Inv`: what it holds and has pending it was given or
made, its own blocks lie at strictly increasing rounds up to its top,
each its own, identified by its hash and valid against what it knew, and
its store is valid at the row.
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
      rowValid cfg.q (Function.update s.store.blk id b) b ∧
      s'.store = s.store.insert id b hnew hrefs hpred ∧ s'.top = some (r + 1) ∧
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
        refine ⟨r, _, _, hc.1, hc.2.1, hc.2.2.1, hr, rfl, rfl, rfl,
          hc.2.2.2, rfl, rfl, rfl, rfl, ?_⟩
        simp [built]
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
theorem Rounds.mono {B : List (BlockId × Block Validator BlockId Payload)} {t t' : ℕ}
    (h : Rounds B t) (htt : t ≤ t') : Rounds B t' :=
  ⟨h.1, fun e he => (h.2 e he).trans htt⟩

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

/-- **Every stored block is valid at the row**, under the store's map. -/
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
  change j ∈ Insert.insert id st.ids at hj
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

/-- **The invariant** of a node's state, against what it knew, `K`, and
its own blocks, `B`. -/
structure Inv (cfg : Config Validator BlockId Payload) (s : State Validator BlockId Payload)
    (K : Set (BlockId × Block Validator BlockId Payload))
    (B : List (BlockId × Block Validator BlockId Payload)) : Prop where
  known : ∀ j ∈ s.store.ids, (j, s.store.blk j) ∈ K
  pend : ∀ e ∈ s.pending, e ∈ K
  rounds : (s.top = none ∧ B = []) ∨ ∃ t, s.top = some t ∧ Rounds B t
  good : ∀ e ∈ B, Good cfg K e
  sub : ∀ e ∈ B, e ∈ K
  valid : StoreValid cfg.q s.store

omit [Fintype Validator] in
theorem Inv.mono {s : State Validator BlockId Payload}
    {K K' : Set (BlockId × Block Validator BlockId Payload)}
    {B : List (BlockId × Block Validator BlockId Payload)} (h : Inv cfg s K B) (hK : K ⊆ K') :
    Inv cfg s K' B :=
  ⟨fun j hj => hK (h.known j hj), fun e he => hK (h.pend e he), h.rounds,
    fun e he => (h.good e he).mono hK, fun e he => hK (h.sub e he), h.valid⟩

omit [Fintype Validator] [DecidableEq Validator] in
/-- Accepting a known block keeps the store known. -/
theorem known_insert {st : Store Validator BlockId Payload}
    {K : Set (BlockId × Block Validator BlockId Payload)}
    (hK : ∀ j ∈ st.ids, (j, st.blk j) ∈ K) {id : BlockId}
    {b : Block Validator BlockId Payload} (hb : (id, b) ∈ K) {hnew hrefs hpred} :
    ∀ j ∈ (st.insert id b hnew hrefs hpred).ids, (j, (st.insert id b hnew hrefs hpred).blk j) ∈ K := by
  intro j hj
  change j ∈ Insert.insert id st.ids at hj
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
  obtain ⟨r, id, b, hnew, hrefs, hpred, hr, hbr, hbc, hid, hv, hst, htop, hpd, -, hout⟩ :=
    tryBuild_some h
  have hK : K ⊆ K ∪ {(id, b)} := Set.subset_union_left
  have hmem : (id, b) ∈ K ∪ {(id, b)} := Set.mem_union_right _ rfl
  refine ⟨(id, b), hout, ⟨?_, ?_, ?_, ?_, ?_, ?_⟩⟩
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
/-- An invariant read only from the store, the pending blocks and the top
carries over to a state that keeps them. -/
theorem Inv.of_eq {s s' : State Validator BlockId Payload}
    {K : Set (BlockId × Block Validator BlockId Payload)}
    {B : List (BlockId × Block Validator BlockId Payload)} (hi : Inv cfg s K B)
    (hst : s'.store = s.store) (hpd : s'.pending = s.pending) (htop : s'.top = s.top) :
    Inv cfg s' K B :=
  ⟨by rw [hst]; exact hi.known, by rw [hpd]; exact hi.pend,
    by rw [htop]; exact hi.rounds, hi.good, hi.sub, by rw [hst]; exact hi.valid⟩

omit [Fintype Validator] in
/-- **Deciding keeps the invariant** and outputs no block. -/
theorem Inv.decideStep {s : State Validator BlockId Payload}
    {K : Set (BlockId × Block Validator BlockId Payload)}
    {B : List (BlockId × Block Validator BlockId Payload)} (hi : Inv cfg s K B) :
    Out [] (decideStep cfg s).2 ∧ Inv cfg (decideStep cfg s).1 K B := by
  unfold Node.decideStep
  dsimp only
  split
  · exact ⟨out_quiet (quiet_commits _), hi.of_eq rfl rfl rfl⟩
  · exact ⟨⟨rfl, rfl⟩, hi⟩

omit [Fintype Validator] in
/-- Accepting a known block keeps the store known and valid. -/
theorem accept_known {st : Store Validator BlockId Payload}
    {K : Set (BlockId × Block Validator BlockId Payload)}
    (hK : ∀ j ∈ st.ids, (j, st.blk j) ∈ K) (hV : StoreValid cfg.q st)
    {id : BlockId} {b : Block Validator BlockId Payload} (hb : (id, b) ∈ K) :
    (∀ j ∈ (accept cfg st id b).ids, (j, (accept cfg st id b).blk j) ∈ K) ∧
      StoreValid cfg.q (accept cfg st id b) := by
  unfold accept
  split
  · rename_i h
    exact ⟨known_insert hK hb, hV.insert h.2.2.2⟩
  · exact ⟨hK, hV⟩

omit [Fintype Validator] in
theorem foldl_accept_known {K : Set (BlockId × Block Validator BlockId Payload)} :
    ∀ (l : List (BlockId × Block Validator BlockId Payload)) {st : Store Validator BlockId Payload},
    (∀ j ∈ st.ids, (j, st.blk j) ∈ K) → StoreValid cfg.q st → (∀ e ∈ l, e ∈ K) →
    let st' := l.foldl (fun s e => accept cfg s e.1 e.2) st
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
    let r := flush cfg fuel st pend
    (∀ j ∈ r.1.ids, (j, r.1.blk j) ∈ K) ∧ (∀ e ∈ r.2, e ∈ K) ∧ StoreValid cfg.q r.1
  | 0, _, _, hK, hV, hp => ⟨hK, hp, hV⟩
  | fuel + 1, st, pend, hK, hV, hp => by
    unfold flush
    dsimp only
    split
    · exact ⟨hK, hp, hV⟩
    · have hsplit : ∀ e ∈ (pend.partition fun e => ready cfg st e).1 ++
          (pend.partition fun e => ready cfg st e).2, e ∈ K := by
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
    let fl := flush cfg fuel s.store s.pending
    Inv cfg { s with store := fl.1, pending := fl.2 } K B := by
  intro fl
  have hfl := flush_known (cfg := cfg) (K := K) fuel (st := s.store) (pend := s.pending)
    hi.known hi.valid hi.pend
  exact ⟨hfl.1, hfl.2.1, hi.rounds, hi.good, hi.sub, hfl.2.2⟩

omit [Fintype Validator] in
/-- **Advancing keeps the invariant**, and its own blocks are the built
ones. -/
theorem Inv.advance {s : State Validator BlockId Payload}
    {K : Set (BlockId × Block Validator BlockId Payload)}
    {B : List (BlockId × Block Validator BlockId Payload)} (hi : Inv cfg s K B) :
    ∃ bs, Out bs (advance cfg s).2 ∧ Inv cfg (advance cfg s).1 (K ∪ {x | x ∈ bs}) (B ++ bs) := by
  obtain ⟨bs, hbs, hi₁⟩ := hi.progress (s.store.topRound + 2)
  obtain ⟨hds, hi₂⟩ := hi₁.decideStep
  refine ⟨bs, ?_, hi₂.flushAll _⟩
  simp only [Node.advance]
  rw [hbs]
  simpa using (out_built (cfg := cfg) bs).append hds

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
/-- **A property of each pass's outputs** holds of all of them. -/
theorem quiesce_out {P : State Validator BlockId Payload → Prop}
    {Q : Output Validator BlockId Payload → Prop}
    (hadv : ∀ s, P s → (∀ o ∈ (advance cfg s).2, Q o) ∧ P (advance cfg s).1) (n : ℕ)
    (s : State Validator BlockId Payload) (h : P s) : ∀ o ∈ (quiesce cfg n s).2, Q o :=
  (quiesce_rel (P := P) (R := fun _ out _ => ∀ o ∈ out, Q o)
    (fun _ _ h => absurd h List.not_mem_nil)
    (fun _ _ _ _ _ h₁ h₂ o ho => (List.mem_append.mp ho).elim (h₁ o) (h₂ o)) hadv n s h).1

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

/-- **A step keeps the invariant**: what it was given and its own blocks
are known, and its own blocks are good. -/
theorem Inv.step {s : State Validator BlockId Payload}
    {K : Set (BlockId × Block Validator BlockId Payload)}
    {B : List (BlockId × Block Validator BlockId Payload)} (hi : Inv cfg s K B)
    (i : Input Validator BlockId Payload) :
    ∃ bs, Out bs (Node.step cfg s i).2 ∧
      Inv cfg (Node.step cfg s i).1 (K ∪ {x | x ∈ delivered cfg [i]} ∪ {x | x ∈ bs}) (B ++ bs) := by
  let K' := K ∪ {x | x ∈ delivered cfg [i]}
  have hsub : K ⊆ K' := fun x hx => Or.inl hx
  have hnil : ∀ (xs : List (Output Validator BlockId Payload)), (∀ o ∈ xs, o.isQuiet) →
      ∃ bs, Out bs xs ∧ Inv cfg s (K' ∪ {x | x ∈ bs}) (B ++ bs) :=
    fun xs hxs => ⟨[], out_quiet hxs, by simpa using hi.mono hsub⟩
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
        have hr₀ : e.2.refs ⊆ s.store.ids := fun _ hj => absurd hj (Finset.notMem_empty _)
        have hp₀ : ∀ j ∈ e.2.refs, (s.store.blk j).round + 1 = e.2.round :=
          fun j hj => absurd hj (Finset.notMem_empty j)
        have hi₀ : Inv cfg
            { s with
              store := s.store.insert e.1 e.2 h₂.1 hr₀ hp₀
              top := some 0
              own := some e.1 } (K ∪ {x | x ∈ [e]}) (B ++ [e]) := by
          refine ⟨known_insert (hnew := h₂.1) (hrefs := hr₀) (hpred := hp₀)
              (fun j hj => Set.subset_union_left (hi.known j hj)) (by simp [e]),
            fun x hx => Set.subset_union_left (hi.pend x hx), Or.inr ⟨0, rfl, ?_⟩,
            fun x hx => ?_, fun x hx => ?_, hi.valid.insert (hnew := h₂.1) (hrefs := hr₀)
              (hpred := hp₀) h₂.2⟩
          · rw [hB, List.nil_append]
            exact ⟨by simp, fun x hx => by rw [List.mem_singleton] at hx; subst hx; rfl⟩
          · rw [hB, List.nil_append, List.mem_singleton] at hx
            subst hx
            refine ⟨rfl, rfl, fun j hj => absurd hj (Finset.notMem_empty j), fun blk _ => ?_⟩
            exact rowValid_congr (fun j hj => absurd hj (Finset.notMem_empty j)) h₂.2
          · rw [hB, List.nil_append, List.mem_singleton] at hx
            subst hx; simp
        obtain ⟨bs, ho, hi'⟩ := hi₀.settle
        refine ⟨e :: bs, ?_, ?_⟩
        · exact (out_built (cfg := cfg) [e]).append ho
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
      have hfl := flush_known (cfg := cfg) (K := K') (s.pending.length + 1) (st := s.store)
        (pend := (id, b) :: s.pending) (fun j hj => hsub (hi.known j hj)) hi.valid
        (fun x hx => by
          rcases List.mem_cons.mp hx with rfl | hx
          · exact hmem
          · exact hsub (hi.pend x hx))
      dsimp only at hfl ⊢
      generalize flush cfg (s.pending.length + 1) s.store ((id, b) :: s.pending) = fl at hfl ⊢
      generalize missing { s with store := fl.1, pending := fl.2 } id b = miss
      have hi₀ : Inv cfg
          { s with store := fl.1, pending := fl.2, requested := s.requested ++ miss.map (·, id) }
          K' B :=
        ⟨hfl.1, hfl.2.1, hi.rounds, fun x hx => (hi.good x hx).mono hsub,
          fun x hx => hsub (hi.sub x hx), hfl.2.2⟩
      refine hi₀.settle_of subset_rfl _ fun o ho => ?_
      split at ho
      · simp at ho
      · rw [List.mem_singleton] at ho; subst ho; rfl
    · exact hnil'
  | timer r =>
    simp only [Node.step]
    exact ((hi.mono hsub).of_eq (s' := { s with fired := insert r s.fired }) rfl rfl rfl).settle
  | fetchRequest peer ids =>
    simp only [Node.step]
    refine hnil _ fun o ho => ?_
    obtain ⟨j, -, rfl⟩ := List.mem_map.mp ho
    rfl

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

/-- **A run broadcasts what it persists.** -/
theorem broadcasts_run : ∀ (is : List (Input Validator BlockId Payload))
    {s : State Validator BlockId Payload} {K : Set (BlockId × Block Validator BlockId Payload)}
    {B : List (BlockId × Block Validator BlockId Payload)}, Inv cfg s K B →
    broadcasts (Node.run cfg s is).2 = persists (Node.run cfg s is).2
  | [], _, _, _, _ => rfl
  | i :: is, _, _, _, hi => by
    obtain ⟨bs, ho, hi₁⟩ := hi.step i
    simp only [Node.run]
    rw [broadcasts_append, persists_append, ho.1, ho.2, broadcasts_run is hi₁]

omit [Fintype Validator] in
/-- The initial state meets the invariant, with nothing known or broadcast. -/
theorem Inv.init : Inv cfg (State.init cfg) ∅ [] where
  known := fun _ h => absurd h (Finset.notMem_empty _)
  pend := fun _ h => absurd h (List.not_mem_nil)
  rounds := Or.inl ⟨rfl, rfl⟩
  good := fun _ h => absurd h (List.not_mem_nil)
  sub := fun _ h => absurd h (List.not_mem_nil)
  valid := fun _ h => absurd h (Finset.notMem_empty _)

end Node

end LeanDag
