import LeanDag.Node.Model.Run
import LeanDag.Node.Helpers.ReadsView
/-!
# One node at a time — the lemmas

A successful build step adds one block at the round above the node's top,
its own, identified by its hash, with accepted references, and valid
under the store's map (`tryBuild_some`); building, deciding and
collecting change the parts of the state the claims read only so.
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
    ∃ r id, ∃ b : Block Validator BlockId Payload, ∃ hnew hab hrefs hpred,
      s.top = some r ∧ b.round = r + 1 ∧ b.creator = cfg.me ∧ id = cfg.idOf b ∧
      rowValid cfg.q (Function.update s.store.blk id b) b ∧
      s'.store = s.store.insert id b hnew hab hrefs hpred ∧ s'.top = some (r + 1) ∧
      s'.pending = s.pending ∧ s'.lo = s.lo ∧ out = built cfg [(id, b)] := by
  unfold tryBuild at h
  split at h
  · rename_i r o hr ho
    dsimp only at h
    split at h
    · split at h
      · rename_i hc
        rw [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        refine ⟨r, _, _, hc.1, hc.2.1, hc.2.2.1, hc.2.2.2.1, hr, rfl, rfl, rfl,
          hc.2.2.2.2, rfl, rfl, rfl, rfl, ?_⟩
        simp [built]
      · exact absurd h (by simp)
    · exact absurd h (by simp)
  · exact absurd h (by simp)

omit [Fintype Validator] [LinearOrder BlockId] in
/-- **The row's validity reads only rounds and authors** of the
references. -/
theorem rowValid_congr {q : ℕ} {blk blk' : BlockId → Block Validator BlockId Payload}
    {b : Block Validator BlockId Payload}
    (h : ∀ j ∈ b.refs, (blk j).round = (blk' j).round ∧ (blk j).creator = (blk' j).creator)
    (hv : rowValid q blk b) : rowValid q blk' b := by
  have hcr : creators blk b = creators blk' b :=
    Finset.image_congr fun j hj => (h j hj).2
  refine ⟨fun i hi => ?_, fun h0 => ?_, ⟨fun i hi j hj hij => ?_, fun h0 => ?_⟩⟩
  · rw [← (h i hi).1]; exact hv.predecessor i hi
  · rw [← hcr]; exact hv.quorum h0
  · exact hv.clause.1 i hi j hj (by rw [(h i hi).2, (h j hj).2]; exact hij)
  · obtain ⟨i, hi, hc⟩ := hv.clause.2 h0
    exact ⟨i, hi, by rw [← (h i hi).2]; exact hc⟩

/-- **A broadcast block is good** against what the node knew, `K`: its
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

/-- **Every stored block above the horizon is valid at the row**, under
the store's map. -/
def StoreValid (q : ℕ) (st : Store Validator BlockId Payload) : Prop :=
  ∀ j ∈ st.ids, st.base < (st.map.getD j st.junk).round →
    rowValid q st.blk (st.map.getD j st.junk)

omit [Fintype Validator] [DecidableEq Validator] in
/-- A stored block above the horizon is read as it was stored. -/
theorem Store.blk_of_lt {st : Store Validator BlockId Payload} {j : BlockId}
    (h : st.base < (st.map.getD j st.junk).round) : st.blk j = st.map.getD j st.junk := by
  unfold Store.blk lookup atBase
  rw [if_neg (by omega)]

omit [Fintype Validator] in
/-- **Accepting a block valid under the extended map keeps the store
valid.** -/
theorem StoreValid.insert {q : ℕ} {st : Store Validator BlockId Payload} (hs : StoreValid q st)
    {id : BlockId} {b : Block Validator BlockId Payload} {hnew hab hrefs hpred}
    (hv : st.base < b.round → rowValid q (Function.update st.blk id b) b) :
    StoreValid q (st.insert id b hnew hab hrefs hpred) := by
  have hlk : ∀ i, i ≠ id → (st.insert id b hnew hab hrefs hpred).blk i = st.blk i :=
    fun i hi => by simp only [Store.blk, lookup, Store.insert, treeMap_getD_insert_ne (Ne.symm hi)]
  intro j hj hr
  change j ∈ Insert.insert id st.ids at hj
  change st.base < ((st.map.insert id b).getD j st.junk).round at hr
  change rowValid q (st.insert id b hnew hab hrefs hpred).blk ((st.map.insert id b).getD j st.junk)
  by_cases h : j = id
  · subst h
    rw [Std.TreeMap.getD_insert_self] at hr ⊢
    refine rowValid_congr (fun i hi => ?_) (hv hr)
    have hi' : i ≠ j := fun e => hnew (e ▸ hrefs hr hi)
    rw [Function.update_of_ne hi', hlk i hi']
    exact ⟨rfl, rfl⟩
  · rw [treeMap_getD_insert_ne (Ne.symm h)] at hr ⊢
    have hj' := (Finset.mem_insert.mp hj).resolve_left h
    refine rowValid_congr (fun i hi => ?_) (hs j hj' hr)
    have hir : i ∈ (st.blk j).refs := by rw [Store.blk_of_lt hr]; exact hi
    have hi' : i ≠ id := fun e => hnew (e ▸ st.complete j hj' i hir)
    rw [hlk i hi']
    exact ⟨rfl, rfl⟩

omit [Fintype Validator] in
/-- **Raising the horizon keeps the store valid.** -/
theorem StoreValid.prune {q : ℕ} {st : Store Validator BlockId Payload} (hs : StoreValid q st)
    {G : ℕ} {hG : st.base ≤ G} : StoreValid q (st.prune G hG) := by
  have hraw : ∀ i, G ≤ (st.blk i).round →
      (st.map.filter fun _ b => decide (G ≤ b.round)).getD i st.junk = st.map.getD i st.junk :=
    fun i hi => treeMap_getD_filter_of (by simpa [Store.blk, lookup] using hi)
  intro j hj hr
  have hj' := Finset.mem_filter.mp hj
  change j ∈ st.ids.filter _ at hj
  change G < ((st.map.filter fun _ b => decide (G ≤ b.round)).getD j st.junk).round at hr
  rw [hraw j hj'.2] at hr
  change rowValid q (st.prune G hG).blk
    ((st.map.filter fun _ b => decide (G ≤ b.round)).getD j st.junk)
  rw [hraw j hj'.2]
  have hlt : st.base < (st.map.getD j st.junk).round := by omega
  refine rowValid_congr (fun i hi => ?_) (hs j hj'.1 hlt)
  have hir : i ∈ (st.blk j).refs := by rw [Store.blk_of_lt hlt]; exact hi
  have hp := st.pred j hj'.1 i hir
  change (st.blk i).round + 1 = (st.blk j).round at hp
  rw [Store.blk_of_lt hlt] at hp
  have hiG : G ≤ (st.blk i).round := by omega
  change (st.blk i).round = (lookup (st.prune G hG).map st.junk G i).round ∧
    (st.blk i).creator = (lookup (st.prune G hG).map st.junk G i).creator
  have e : (st.prune G hG).map.getD i st.junk = st.map.getD i st.junk := hraw i hiG
  simp only [lookup, atBase_round, atBase_creator, Store.blk]
  rw [e]
  exact ⟨rfl, rfl⟩

/-- **The invariant** of a node's state, against what it knew, `K`, and
what it broadcast, `B`. -/
structure Inv (cfg : Config Validator BlockId Payload) (s : State Validator BlockId Payload)
    (K : Set (BlockId × Block Validator BlockId Payload))
    (B : List (BlockId × Block Validator BlockId Payload)) : Prop where
  known : ∀ j ∈ s.store.ids, (j, s.store.map.getD j s.store.junk) ∈ K
  pend : ∀ e ∈ s.pending, e ∈ K
  rounds : (s.top = none ∧ B = [] ∧ s.store.base = 0) ∨
    ∃ t, s.top = some t ∧ s.store.base ≤ t ∧ B.map (fun e => e.2.round) = List.range (t + 1)
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
    (hK : ∀ j ∈ st.ids, (j, st.map.getD j st.junk) ∈ K) {id : BlockId}
    {b : Block Validator BlockId Payload} (hb : (id, b) ∈ K) {hnew hab hrefs hpred} :
    ∀ j ∈ (st.insert id b hnew hab hrefs hpred).ids,
      (j, (st.insert id b hnew hab hrefs hpred).map.getD j
        (st.insert id b hnew hab hrefs hpred).junk) ∈ K := by
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
  obtain ⟨r, id, b, hnew, hab, hrefs, hpred, hr, hbr, hbc, hid, hv, hst, htop, hpd, -, hout⟩ :=
    tryBuild_some h
  have hbase : s.store.base ≤ r := by
    rcases hi.rounds with ⟨h0, -⟩ | ⟨t, ht, hb, -⟩
    · rw [hr] at h0; exact absurd h0 (by simp)
    · rw [hr, Option.some.injEq] at ht; omega
  have hrefs' : b.refs ⊆ s.store.ids := hrefs (by omega)
  have hK : K ⊆ K ∪ {(id, b)} := Set.subset_union_left
  have hmem : (id, b) ∈ K ∪ {(id, b)} := Set.mem_union_right _ rfl
  refine ⟨(id, b), hout, ⟨?_, ?_, ?_, ?_, ?_, ?_⟩⟩
  · rw [hst]
    exact known_insert (fun j hj => hK (hi.known j hj)) hmem
  · rw [hpd]; exact fun e he => hK (hi.pend e he)
  · right
    refine ⟨r + 1, htop, ?_, ?_⟩
    · rw [hst]; change s.store.base ≤ r + 1; omega
    · rcases hi.rounds with ⟨h0, -⟩ | ⟨t, ht, -, hB⟩
      · rw [hr] at h0; exact absurd h0 (by simp)
      · rw [hr, Option.some.injEq] at ht
        subst ht
        rw [List.map_append, hB]
        simp [hbr, List.range_succ]
  · intro e he
    rcases List.mem_append.mp he with he | he
    · exact (hi.good e he).mono hK
    · rw [List.mem_singleton] at he
      subst he
      refine ⟨hid, hbc, fun j hj => ⟨_, hK (hi.known j (hrefs' hj))⟩, fun blk hblk => ?_⟩
      refine rowValid_congr (fun j hj => ?_) hv
      have hjid : j ≠ id := fun e => hnew (e ▸ hrefs' hj)
      rw [Function.update_of_ne hjid, hblk _ (hK (hi.known j (hrefs' hj)))]
      simp [Store.blk, lookup]
  · intro e he
    rcases List.mem_append.mp he with he | he
    · exact hK (hi.sub e he)
    · rw [List.mem_singleton] at he; subst he; exact hmem
  · rw [hst]; exact hi.valid.insert fun _ => hv

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

omit [Fintype Validator] in
/-- **Deciding keeps the invariant** and outputs only decisions. -/
theorem Inv.decideStep {s : State Validator BlockId Payload}
    {K : Set (BlockId × Block Validator BlockId Payload)}
    {B : List (BlockId × Block Validator BlockId Payload)} (hi : Inv cfg s K B) :
    ∃ ds : List (ℕ × Option BlockId), (decideStep cfg s).2 = ds.map (fun e => .commit e.1 e.2) ∧
      Inv cfg (decideStep cfg s).1 K B := by
  unfold Node.decideStep
  dsimp only
  split
  · exact ⟨_, rfl, ⟨hi.known, hi.pend, hi.rounds, hi.good, hi.sub, hi.valid⟩⟩
  · exact ⟨[], rfl, hi⟩

omit [Fintype Validator] in
/-- **Collecting keeps the invariant** and outputs at most one horizon. -/
theorem Inv.collect {s : State Validator BlockId Payload}
    {K : Set (BlockId × Block Validator BlockId Payload)}
    {B : List (BlockId × Block Validator BlockId Payload)} (hi : Inv cfg s K B) :
    ∃ gs : List ℕ, gs.length ≤ 1 ∧ (collect cfg s).2 = gs.map .prune ∧
      Inv cfg (collect cfg s).1 K B := by
  unfold Node.collect
  split
  · rename_i t ht
    dsimp only
    split
    · rename_i hG
      refine ⟨[_], by simp, rfl, ⟨?_, ?_, ?_, hi.good, hi.sub, hi.valid.prune (hG := hG.le)⟩⟩
      · intro j hj
        have hj' := (Finset.mem_filter.mp hj)
        have hraw := treeMap_getD_filter_of (t := s.store.map)
          (f := fun _ b => decide (min (cfg.per * (s.lo / cfg.m)) t - cfg.lag ≤ b.round)) (k := j)
          (fb := s.store.junk) (by simpa [Store.blk, lookup] using hj'.2)
        change (j, (s.store.map.filter _).getD j s.store.junk) ∈ K
        rw [hraw]
        exact hi.known j hj'.1
      · intro e he
        exact hi.pend e (List.mem_filter.mp he).1
      · right
        rcases hi.rounds with ⟨h0, -⟩ | ⟨t', ht', -, hB⟩
        · rw [ht] at h0; exact absurd h0 (by simp)
        · rw [ht, Option.some.injEq] at ht'
          subst ht'
          exact ⟨t, ht, by change _ - _ ≤ t; omega, hB⟩
    · exact ⟨[], by simp, rfl, hi⟩
  · exact ⟨[], by simp, rfl, hi⟩

omit [Fintype Validator] in
/-- Accepting a known block keeps the store known, at the same horizon. -/
theorem accept_known {st : Store Validator BlockId Payload}
    {K : Set (BlockId × Block Validator BlockId Payload)}
    (hK : ∀ j ∈ st.ids, (j, st.map.getD j st.junk) ∈ K) (hV : StoreValid cfg.q st)
    {id : BlockId} {b : Block Validator BlockId Payload} (hb : (id, b) ∈ K) :
    (∀ j ∈ (accept cfg st id b).ids,
      (j, (accept cfg st id b).map.getD j (accept cfg st id b).junk) ∈ K) ∧
      (accept cfg st id b).base = st.base ∧ StoreValid cfg.q (accept cfg st id b) := by
  unfold accept
  split
  · rename_i h
    exact ⟨known_insert hK hb, rfl, hV.insert h.2.2.2.2⟩
  · exact ⟨hK, rfl, hV⟩

omit [Fintype Validator] in
theorem foldl_accept_known {K : Set (BlockId × Block Validator BlockId Payload)} :
    ∀ (l : List (BlockId × Block Validator BlockId Payload)) {st : Store Validator BlockId Payload},
    (∀ j ∈ st.ids, (j, st.map.getD j st.junk) ∈ K) → StoreValid cfg.q st → (∀ e ∈ l, e ∈ K) →
    let st' := l.foldl (fun s e => accept cfg s e.1 e.2) st
    (∀ j ∈ st'.ids, (j, st'.map.getD j st'.junk) ∈ K) ∧ st'.base = st.base ∧
      StoreValid cfg.q st'
  | [], _, hK, hV, _ => ⟨hK, rfl, hV⟩
  | e :: l, st, hK, hV, hl => by
    have h₁ := accept_known (cfg := cfg) hK hV (hl e List.mem_cons_self)
    have h₂ := foldl_accept_known l h₁.1 h₁.2.2 fun x hx => hl x (List.mem_cons_of_mem _ hx)
    exact ⟨h₂.1, h₂.2.1.trans h₁.2.1, h₂.2.2⟩

omit [Fintype Validator] in
/-- **Flushing the pending blocks keeps store and pending known**, at the
same horizon. -/
theorem flush_known {K : Set (BlockId × Block Validator BlockId Payload)} :
    ∀ (fuel : ℕ) {st : Store Validator BlockId Payload}
      {pend : List (BlockId × Block Validator BlockId Payload)},
    (∀ j ∈ st.ids, (j, st.map.getD j st.junk) ∈ K) → StoreValid cfg.q st → (∀ e ∈ pend, e ∈ K) →
    let r := flush cfg fuel st pend
    (∀ j ∈ r.1.ids, (j, r.1.map.getD j r.1.junk) ∈ K) ∧ (∀ e ∈ r.2, e ∈ K) ∧
      r.1.base = st.base ∧ StoreValid cfg.q r.1
  | 0, _, _, hK, hV, hp => ⟨hK, hp, rfl, hV⟩
  | fuel + 1, st, pend, hK, hV, hp => by
    unfold flush
    dsimp only
    split
    · exact ⟨hK, hp, rfl, hV⟩
    · have hsplit : ∀ e ∈ (pend.partition fun e => ready st e.2).1 ++
          (pend.partition fun e => ready st e.2).2, e ∈ K := by
        intro e he
        rw [List.partition_eq_filter_filter] at he
        rcases List.mem_append.mp he with he | he
        · exact hp e (List.mem_filter.mp he).1
        · exact hp e (List.mem_filter.mp he).1
      have h₁ := foldl_accept_known (cfg := cfg) _ hK hV
        fun e he => hsplit e (List.mem_append_left _ he)
      have h₂ := flush_known fuel h₁.1 h₁.2.2 fun e he => hsplit e (List.mem_append_right _ he)
      exact ⟨h₂.1, h₂.2.1, h₂.2.2.1.trans h₁.2.1, h₂.2.2.2⟩

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
  refine ⟨hfl.1, hfl.2.1, ?_, hi.good, hi.sub, hfl.2.2.2⟩
  rcases hi.rounds with ⟨h0, hB, hb⟩ | ⟨t, ht, hb, hB⟩
  · exact Or.inl ⟨h0, hB, by rw [hfl.2.2.1]; exact hb⟩
  · exact Or.inr ⟨t, ht, by rw [hfl.2.2.1]; exact hb, hB⟩

omit [Fintype Validator] in
/-- **Settling keeps the invariant**: built blocks, then decisions, then at
most one horizon. -/
theorem Inv.settle {s : State Validator BlockId Payload}
    {K : Set (BlockId × Block Validator BlockId Payload)}
    {B : List (BlockId × Block Validator BlockId Payload)} (hi : Inv cfg s K B) :
    ∃ (bs : List (BlockId × Block Validator BlockId Payload)) (ds : List (ℕ × Option BlockId))
      (gs : List ℕ), gs.length ≤ 1 ∧
      (settle cfg s).2 = built cfg bs ++ ds.map (fun e => .commit e.1 e.2) ++ gs.map .prune ∧
      Inv cfg (settle cfg s).1 (K ∪ {x | x ∈ bs}) (B ++ bs) := by
  obtain ⟨bs, hbs, hi₁⟩ := hi.progress (s.store.topRound + 2)
  obtain ⟨ds, hds, hi₂⟩ := hi₁.decideStep
  obtain ⟨gs, hgs, hgo, hi₃⟩ := hi₂.collect
  exact ⟨bs, ds, gs, hgs, by simp only [Node.settle, hbs, hds, hgo], hi₃.flushAll _⟩

omit [Fintype Validator] in
/-- Settling keeps the invariant, at a larger knowledge. -/
theorem Inv.settle_of {s : State Validator BlockId Payload}
    {K K₀ : Set (BlockId × Block Validator BlockId Payload)}
    {B B₀ : List (BlockId × Block Validator BlockId Payload)}
    {pre : List (BlockId × Block Validator BlockId Payload)}
    (hi : Inv cfg s (K ∪ {x | x ∈ pre}) (B ++ pre)) (_hK : K₀ ⊆ K) (hB : B₀ = B) :
    ∃ (bs : List (BlockId × Block Validator BlockId Payload)) (ds : List (ℕ × Option BlockId))
      (gs : List ℕ), gs.length ≤ 1 ∧
      built cfg pre ++ (Node.settle cfg s).2 = built cfg bs ++ ds.map (fun e => .commit e.1 e.2) ++
        gs.map .prune ∧
      Inv cfg (Node.settle cfg s).1 (K ∪ {x | x ∈ bs}) (B₀ ++ bs) := by
  subst hB
  obtain ⟨bs, ds, gs, hgs, ho, hi'⟩ := hi.settle
  refine ⟨pre ++ bs, ds, gs, hgs, by rw [ho]; simp [built, List.flatMap_append], ?_⟩
  have hset : K ∪ {x | x ∈ pre} ∪ {x | x ∈ bs} = K ∪ {x | x ∈ pre ++ bs} := by
    ext x; simp only [Set.mem_union, Set.mem_setOf_eq, List.mem_append]; tauto
  rw [← hset, ← List.append_assoc]
  exact hi'

/-- **A step keeps the invariant**: what it delivered and built is known,
and what it built is good. -/
theorem Inv.step {s : State Validator BlockId Payload}
    {K : Set (BlockId × Block Validator BlockId Payload)}
    {B : List (BlockId × Block Validator BlockId Payload)} (hi : Inv cfg s K B)
    (i : Input Validator BlockId Payload) :
    ∃ (xs : List (Output Validator BlockId Payload))
      (bs : List (BlockId × Block Validator BlockId Payload)) (ds : List (ℕ × Option BlockId))
      (gs : List ℕ), (∀ o ∈ xs, o.isFetch) ∧ gs.length ≤ 1 ∧
      (Node.step cfg s i).2 =
        xs ++ built cfg bs ++ ds.map (fun e => .commit e.1 e.2) ++ gs.map .prune ∧
      Inv cfg (Node.step cfg s i).1 (K ∪ {x | x ∈ delivered cfg [i]} ∪ {x | x ∈ bs}) (B ++ bs) := by
  have hnil : ∀ {K' : Set (BlockId × Block Validator BlockId Payload)}, K ⊆ K' →
      ∀ (xs : List (Output Validator BlockId Payload)), (∀ o ∈ xs, o.isFetch) →
      ∃ (xs' : List (Output Validator BlockId Payload))
        (bs : List (BlockId × Block Validator BlockId Payload)) (ds : List (ℕ × Option BlockId))
        (gs : List ℕ), (∀ o ∈ xs', o.isFetch) ∧ gs.length ≤ 1 ∧
        xs = xs' ++ built cfg bs ++ ds.map (fun e => .commit e.1 e.2) ++ gs.map .prune ∧
        Inv cfg s (K' ∪ {x | x ∈ bs}) (B ++ bs) :=
    fun hK xs hxs => ⟨xs, [], [], [], hxs, by simp, by simp [built], by simpa using hi.mono hK⟩
  have hnil' : ∀ {K' : Set (BlockId × Block Validator BlockId Payload)}, K ⊆ K' → _ :=
    fun hK => hnil hK [] (by simp)
  have hsub : K ⊆ K ∪ {x | x ∈ delivered cfg [i]} := Set.subset_union_left
  cases i with
  | start =>
    simp only [Node.step]
    split
    · rename_i h₁
      split
      · rename_i h₂
        have hB : B = [] ∧ s.store.base = 0 := by
          rcases hi.rounds with ⟨-, hB, hb⟩ | ⟨t, ht, -⟩
          · exact ⟨hB, hb⟩
          · rw [h₁.1] at ht; exact absurd ht (by simp)
        let e : BlockId × Block Validator BlockId Payload := (cfg.idOf cfg.genesis, cfg.genesis)
        let st := s.store.insert e.1 e.2 h₂.1 h₂.2.1 (fun _ => Finset.empty_subset _)
          (fun _ j hj => absurd hj (Finset.notMem_empty j))
        have hi₀ : Inv cfg { s with store := st, top := some 0, own := some e.1 }
            (K ∪ {x | x ∈ [e]}) (B ++ [e]) := by
          refine ⟨known_insert (hnew := h₂.1) (hab := h₂.2.1)
              (hrefs := fun _ => Finset.empty_subset _)
              (hpred := fun _ j hj => absurd hj (Finset.notMem_empty j))
              (fun j hj => Set.subset_union_left (hi.known j hj)) (by simp [e]),
            fun x hx => Set.subset_union_left (hi.pend x hx), Or.inr ⟨0, rfl, ?_, ?_⟩,
            fun x hx => ?_, fun x hx => ?_,
            hi.valid.insert (hnew := h₂.1) (hab := h₂.2.1)
              (hrefs := fun _ => Finset.empty_subset _)
              (hpred := fun _ j hj => absurd hj (Finset.notMem_empty j))
              fun h => absurd h (by simp [Config.genesis])⟩
          · change s.store.base ≤ 0; omega
          · rw [hB.1]; rfl
          · rw [hB.1, List.nil_append, List.mem_singleton] at hx
            subst hx
            refine ⟨rfl, rfl, fun j hj => absurd hj (Finset.notMem_empty j), fun blk _ => ?_⟩
            exact rowValid_congr (fun j hj => absurd hj (Finset.notMem_empty j)) h₂.2.2
          · rw [hB.1, List.nil_append, List.mem_singleton] at hx
            subst hx; simp
        obtain ⟨bs, ds, gs, hgs, ho, hi'⟩ := hi₀.settle_of (K₀ := K) subset_rfl rfl
        refine ⟨[], bs, ds, gs, by simp, hgs, ?_, hi'.mono ?_⟩
        · rw [List.nil_append, ← ho]; simp [built, e, Config.genesis]; rfl
        · intro x hx
          rcases hx with hx | hx
          · exact Or.inl (Or.inl hx)
          · exact Or.inr hx
      · exact hnil' hsub
    · exact hnil' hsub
  | deliver id b =>
    simp only [Node.step]
    split
    · rename_i hc
      have hd : delivered cfg [Input.deliver id b] = [(id, b)] := by simp [delivered, hc.1]
      rw [hd]
      have hmem : (id, b) ∈ K ∪ {x | x ∈ [(id, b)]} := by simp
      have hfl := flush_known (cfg := cfg) (K := K ∪ {x | x ∈ [(id, b)]})
        (s.pending.length + 1) (st := s.store) (pend := (id, b) :: s.pending)
        (fun j hj => Set.subset_union_left (hi.known j hj)) hi.valid
        (fun x hx => by
          rcases List.mem_cons.mp hx with rfl | hx
          · exact hmem
          · exact Set.subset_union_left (hi.pend x hx))
      dsimp only at hfl ⊢
      generalize flush cfg (s.pending.length + 1) s.store ((id, b) :: s.pending) = fl at hfl ⊢
      generalize missing { s with store := fl.1, pending := fl.2 } id b = miss
      let req := s.requested ++ miss.map fun x => (x.1, id, x.2)
      have hi₀ : Inv cfg { s with store := fl.1, pending := fl.2, requested := req }
          (K ∪ {x | x ∈ [(id, b)]} ∪
            {x | x ∈ ([] : List (BlockId × Block Validator BlockId Payload))})
          (B ++ []) := by
        refine ⟨by simpa using hfl.1, by simpa using hfl.2.1, ?_, ?_, ?_, hfl.2.2.2⟩
        · rcases hi.rounds with ⟨h0, hB, hb⟩ | ⟨t, ht, hb, hB⟩
          · exact Or.inl ⟨h0, by simpa using hB, by rw [hfl.2.2.1]; exact hb⟩
          · exact Or.inr ⟨t, ht, by rw [hfl.2.2.1]; exact hb, by simpa using hB⟩
        · intro x hx; exact (hi.good x (by simpa using hx)).mono (by intro y hy; simp [hy])
        · intro x hx; simp [hi.sub x (by simpa using hx)]
      obtain ⟨bs, ds, gs, hgs, ho, hi'⟩ := hi₀.settle_of (K₀ := K) (by intro x hx; simp [hx]) rfl
      refine ⟨if miss.isEmpty then [] else [.fetch (miss.map Prod.fst)], bs, ds, gs, ?_, hgs,
        ?_, by simpa using hi'⟩
      · intro o ho'
        split at ho'
        · simp at ho'
        · rw [List.mem_singleton] at ho'; subst ho'; rfl
      · simp only [List.append_assoc]
        congr 1
        simpa [built] using ho
    · exact hnil' hsub
  | timer r =>
    simp only [Node.step]
    have h₀ := hi.mono hsub
    have hi₀ : Inv cfg { s with fired := insert r s.fired }
        (K ∪ {x | x ∈ delivered cfg [Input.timer r]} ∪
          {x | x ∈ ([] : List (BlockId × Block Validator BlockId Payload))}) (B ++ []) := by
      simpa using (⟨h₀.known, h₀.pend, h₀.rounds, h₀.good, h₀.sub, h₀.valid⟩ :
        Inv cfg { s with fired := insert r s.fired } _ B)
    obtain ⟨bs, ds, gs, hgs, ho, hi'⟩ := hi₀.settle_of
      (K₀ := K ∪ {x | x ∈ delivered cfg [Input.timer r]}) subset_rfl rfl
    exact ⟨[], bs, ds, gs, by simp, hgs, by simpa [built] using ho, by simpa using hi'⟩
  | fetchRequest peer ids =>
    simp only [Node.step]
    refine hnil hsub _ fun o ho => ?_
    obtain ⟨j, -, rfl⟩ := List.mem_map.mp ho
    rfl
  | jump => exact hnil' hsub
  | restart => exact hnil' hsub
  | baseOffer => exact hnil' hsub
  | baseRequest => exact hnil' hsub

omit [Fintype Validator] [DecidableEq Validator] [LinearOrder BlockId] in
theorem broadcasts_append (a b : List (Output Validator BlockId Payload)) :
    broadcasts (a ++ b) = broadcasts a ++ broadcasts b :=
  List.filterMap_append

omit [Fintype Validator] in
/-- The blocks broadcast by built blocks, decisions and horizons: the built
ones. -/
theorem broadcasts_shape (bs : List (BlockId × Block Validator BlockId Payload))
    (ds : List (ℕ × Option BlockId)) (gs : List ℕ) :
    broadcasts (built cfg bs ++ ds.map (fun e => .commit e.1 e.2) ++ gs.map .prune) = bs := by
  induction bs with
  | nil =>
    simp only [built, List.flatMap_nil, List.nil_append, broadcasts]
    rw [List.filterMap_append, List.filterMap_map, List.filterMap_map]
    simp
  | cons e bs ih =>
    simp only [built, List.flatMap_cons, List.append_assoc] at ih ⊢
    rw [broadcasts_append]
    simp only [broadcasts, List.filterMap_cons] at ih ⊢
    simp [ih]

omit [Fintype Validator] [DecidableEq Validator] [LinearOrder BlockId] in
theorem broadcasts_of_isFetch {xs : List (Output Validator BlockId Payload)}
    (h : ∀ o ∈ xs, o.isFetch) : broadcasts xs = [] := by
  induction xs with
  | nil => rfl
  | cons o xs ih =>
    have ho := h o List.mem_cons_self
    have := ih fun o' h' => h o' (List.mem_cons_of_mem _ h')
    cases o <;> simp_all [broadcasts, Output.isFetch]

omit [Fintype Validator] in
theorem delivered_cons (i : Input Validator BlockId Payload)
    (is : List (Input Validator BlockId Payload)) :
    delivered cfg (i :: is) = delivered cfg [i] ++ delivered cfg is := by
  simp only [delivered, List.filterMap_cons, List.filterMap_nil]
  split <;> simp

/-- **A run keeps the invariant**: what it delivered and broadcast is
known, and what it broadcast is good. -/
theorem Inv.run : ∀ (is : List (Input Validator BlockId Payload))
    {s : State Validator BlockId Payload} {K : Set (BlockId × Block Validator BlockId Payload)}
    {B : List (BlockId × Block Validator BlockId Payload)}, Inv cfg s K B →
    Inv cfg (Node.run cfg s is).1
      (K ∪ {x | x ∈ delivered cfg is} ∪ {x | x ∈ broadcasts (Node.run cfg s is).2})
      (B ++ broadcasts (Node.run cfg s is).2)
  | [], s, K, B, hi => by simpa [Node.run, delivered, broadcasts] using hi
  | i :: is, s, K, B, hi => by
    obtain ⟨xs, bs, ds, gs, hxs, -, ho, hi₁⟩ := hi.step i
    have ih := Inv.run is hi₁
    simp only [Node.run]
    rw [broadcasts_append, ho, List.append_assoc, List.append_assoc, broadcasts_append,
      broadcasts_of_isFetch hxs, List.nil_append, ← List.append_assoc, broadcasts_shape]
    have hK : K ∪ {x | x ∈ delivered cfg [i]} ∪ {x | x ∈ bs} ∪
        {x | x ∈ delivered cfg is} ∪
          {x | x ∈ broadcasts (Node.run cfg (Node.step cfg s i).1 is).2} =
        K ∪ {x | x ∈ delivered cfg (i :: is)} ∪
          {x | x ∈ bs ++ broadcasts (Node.run cfg (Node.step cfg s i).1 is).2} := by
      rw [delivered_cons i is]
      ext x
      simp only [Set.mem_union, Set.mem_setOf_eq, List.mem_append]
      tauto
    rw [← hK, ← List.append_assoc]
    exact ih

omit [Fintype Validator] in
/-- The initial state meets the invariant, with nothing known or broadcast. -/
theorem Inv.init : Inv cfg (State.init cfg) ∅ [] where
  known := fun _ h => absurd h (Finset.notMem_empty _)
  pend := fun _ h => absurd h (List.not_mem_nil)
  rounds := Or.inl ⟨rfl, rfl, rfl⟩
  good := fun _ h => absurd h (List.not_mem_nil)
  sub := fun _ h => absurd h (List.not_mem_nil)
  valid := fun _ h => absurd h (Finset.notMem_empty _)

end Node

end LeanDag
