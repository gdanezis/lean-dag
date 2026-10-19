import LeanDag.Node.Model.Run
import LeanDag.Node.Helpers.ReadsView
import LeanDag.Node.Helpers.Fills
/-!
# One node at a time — the lemmas

A successful build step adds one block at the round above the node's top,
its own, identified by its hash, with accepted references, and valid
under the store's map (`tryBuild_some`); a jump adds its own blocks at
the rounds above the top, likewise (`tryJump_some`); building, jumping,
deciding and collecting change the parts of the state the claims read
only so.
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

omit [Fintype Validator] in
theorem tryBuild_offers {s s' : State Validator BlockId Payload}
    {out : List (Output Validator BlockId Payload)} (h : tryBuild cfg s = some (s', out)) :
    s'.offers = s.offers := by
  unfold tryBuild at h
  split at h
  · dsimp only at h
    split at h
    · split at h
      · rw [Option.some.injEq, Prod.mk.injEq] at h
        rw [← h.1]
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

/-- **One of the node's own blocks is good** against what it knew, `K`: its
own, identified by its hash, its references known, and, if it has any,
valid under every block map agreeing with `K`. -/
def Good (cfg : Config Validator BlockId Payload)
    (K : Set (BlockId × Block Validator BlockId Payload))
    (e : BlockId × Block Validator BlockId Payload) : Prop :=
  e.1 = cfg.idOf e.2 ∧ e.2.creator = cfg.me ∧ (∀ j ∈ e.2.refs, ∃ c, (j, c) ∈ K) ∧
    (e.2.refs.Nonempty → ∀ blk : BlockId → Block Validator BlockId Payload,
      (∀ x ∈ K, blk x.1 = x.2) → rowValid cfg.q blk e.2)

omit [Fintype Validator] in
theorem Good.mono {K K' : Set (BlockId × Block Validator BlockId Payload)} (hK : K ⊆ K')
    {e : BlockId × Block Validator BlockId Payload} (h : Good cfg K e) : Good cfg K' e :=
  ⟨h.1, h.2.1, fun j hj => let ⟨c, hc⟩ := h.2.2.1 j hj; ⟨c, hK hc⟩,
    fun hn blk hblk => h.2.2.2 hn blk fun x hx => hblk x (hK hx)⟩

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
its own blocks, `B`. -/
structure Inv (cfg : Config Validator BlockId Payload) (s : State Validator BlockId Payload)
    (K : Set (BlockId × Block Validator BlockId Payload))
    (B : List (BlockId × Block Validator BlockId Payload)) : Prop where
  known : ∀ j ∈ s.store.ids, (j, s.store.map.getD j s.store.junk) ∈ K
  pend : ∀ e ∈ s.pending, e ∈ K
  rounds : (s.top = none ∧ B = [] ∧ s.store.base = 0) ∨
    ∃ t, s.top = some t ∧ s.store.base ≤ t ∧ Rounds B t
  good : ∀ e ∈ B, Good cfg K e
  sub : ∀ e ∈ B, e ∈ K
  valid : StoreValid cfg.q s.store
  offered : ∀ o ∈ s.offers, ∀ e ∈ o.2.2, e.1 = cfg.idOf e.2 → e ∈ K

omit [Fintype Validator] in
theorem Inv.mono {s : State Validator BlockId Payload}
    {K K' : Set (BlockId × Block Validator BlockId Payload)}
    {B : List (BlockId × Block Validator BlockId Payload)} (h : Inv cfg s K B) (hK : K ⊆ K') :
    Inv cfg s K' B :=
  ⟨fun j hj => hK (h.known j hj), fun e he => hK (h.pend e he), h.rounds,
    fun e he => (h.good e he).mono hK, fun e he => hK (h.sub e he), h.valid,
    fun o ho e he hid => hK (h.offered o ho e he hid)⟩

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
  have hst' := tryBuild_offers h
  have hbase : s.store.base ≤ r := by
    rcases hi.rounds with ⟨h0, -⟩ | ⟨t, ht, hb, -⟩
    · rw [hr] at h0; exact absurd h0 (by simp)
    · rw [hr, Option.some.injEq] at ht; omega
  have hrefs' : b.refs ⊆ s.store.ids := hrefs (by omega)
  have hK : K ⊆ K ∪ {(id, b)} := Set.subset_union_left
  have hmem : (id, b) ∈ K ∪ {(id, b)} := Set.mem_union_right _ rfl
  refine ⟨(id, b), hout, ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩⟩
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
        exact hB.append (by simp) (fun e he => by
          rw [List.mem_singleton] at he; subst he; rw [hbr]; omega) (by omega)
  · intro e he
    rcases List.mem_append.mp he with he | he
    · exact (hi.good e he).mono hK
    · rw [List.mem_singleton] at he
      subst he
      refine ⟨hid, hbc, fun j hj => ⟨_, hK (hi.known j (hrefs' hj))⟩, fun _ blk hblk => ?_⟩
      refine rowValid_congr (fun j hj => ?_) hv
      have hjid : j ≠ id := fun e => hnew (e ▸ hrefs' hj)
      rw [Function.update_of_ne hjid, hblk _ (hK (hi.known j (hrefs' hj)))]
      simp [Store.blk, lookup]
  · intro e he
    rcases List.mem_append.mp he with he | he
    · exact hK (hi.sub e he)
    · rw [List.mem_singleton] at he; subst he; exact hmem
  · rw [hst]; exact hi.valid.insert fun _ => hv
  · rw [hst']; exact fun o ho e he hid => hK (hi.offered o ho e he hid)

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
  · exact ⟨_, rfl, ⟨hi.known, hi.pend, hi.rounds, hi.good, hi.sub, hi.valid, hi.offered⟩⟩
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
      refine ⟨[_], by simp, rfl, ⟨?_, ?_, ?_, hi.good, hi.sub, hi.valid.prune (hG := hG.le),
        hi.offered⟩⟩
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
  refine ⟨hfl.1, hfl.2.1, ?_, hi.good, hi.sub, hfl.2.2.2, hi.offered⟩
  rcases hi.rounds with ⟨h0, hB, hb⟩ | ⟨t, ht, hb, hB⟩
  · exact Or.inl ⟨h0, hB, by rw [hfl.2.2.1]; exact hb⟩
  · exact Or.inr ⟨t, ht, by rw [hfl.2.2.1]; exact hb, hB⟩

omit [Fintype Validator] in
/-- **Advancing keeps the invariant**: built blocks, then decisions, then
at most one horizon. -/
theorem Inv.advance {s : State Validator BlockId Payload}
    {K : Set (BlockId × Block Validator BlockId Payload)}
    {B : List (BlockId × Block Validator BlockId Payload)} (hi : Inv cfg s K B) :
    ∃ (bs : List (BlockId × Block Validator BlockId Payload)) (ds : List (ℕ × Option BlockId))
      (gs : List ℕ), gs.length ≤ 1 ∧
      (advance cfg s).2 = built cfg bs ++ ds.map (fun e => .commit e.1 e.2) ++ gs.map .prune ∧
      Inv cfg (advance cfg s).1 (K ∪ {x | x ∈ bs}) (B ++ bs) := by
  obtain ⟨bs, hbs, hi₁⟩ := hi.progress (s.store.topRound + 2)
  obtain ⟨ds, hds, hi₂⟩ := hi₁.decideStep
  obtain ⟨gs, hgs, hgo, hi₃⟩ := hi₂.collect
  exact ⟨bs, ds, gs, hgs, by simp only [Node.advance, hbs, hds, hgo], hi₃.flushAll _⟩

omit [Fintype Validator] in
/-- **Accepting the filled blocks in turn**: each references known blocks
and is valid at the row under every map agreeing with what is known. -/
theorem insertAll_good {K : Set (BlockId × Block Validator BlockId Payload)} :
    ∀ {F : List (BlockId × Block Validator BlockId Payload)} {st st' : Store Validator BlockId Payload},
    insertAll cfg st F = some st' → (∀ j ∈ st.ids, (j, st.map.getD j st.junk) ∈ K) →
    (∀ e ∈ F, e ∈ K) → ∀ e ∈ F, (∀ j ∈ e.2.refs, ∃ c, (j, c) ∈ K) ∧
      ∀ blk : BlockId → Block Validator BlockId Payload, (∀ x ∈ K, blk x.1 = x.2) →
        rowValid cfg.q blk e.2
  | [], _, _, _, _, _, _, h => absurd h List.not_mem_nil
  | e :: F, st, st', h, hK, hF, x, hx => by
    simp only [insertAll] at h
    split at h
    · rename_i hc
      rcases List.mem_cons.mp hx with rfl | hx
      · refine ⟨fun j hj => ⟨_, hK j (hc.2.2.1 hj)⟩, fun blk hblk => ?_⟩
        refine rowValid_congr (fun j hj => ?_) hc.2.2.2.2
        have hjid : j ≠ x.1 := fun e => hc.1 (e ▸ hc.2.2.1 hj)
        rw [Function.update_of_ne hjid, hblk _ (hK j (hc.2.2.1 hj))]
        simp [Store.blk, lookup]
      · exact insertAll_good h (known_insert hK (hF e List.mem_cons_self))
          (fun y hy => hF y (List.mem_cons_of_mem _ hy)) x hx
    · cases h

omit [Fintype Validator] in
/-- **A successful jump**: from a top `r0` and own block `B1`, the filled
blocks lie at the rounds above `r0`, the last at the new top, which the
node holds as its own block, each its own and identified by its hash,
and accepted in turn. -/
theorem tryJump_some {s s' : State Validator BlockId Payload}
    {out : List (Output Validator BlockId Payload)} (h : tryJump cfg s = some (s', out)) :
    ∃ r0 B1 B2 F e, s.top = some r0 ∧ s.own = some B1 ∧ s.recovering = true ∧
      jumpFills cfg.idOf s.store cfg.me B1 B2 = some F ∧ insertAll cfg s.store F = some s'.store ∧
      F.getLast? = some e ∧ s'.top = some e.2.round ∧ s'.own = some e.1 ∧
      s'.pending = s.pending ∧ s'.lo = s.lo ∧ s'.requested = s.requested ∧
      s'.fired = insert e.2.round s.fired ∧ s'.recovering = false ∧ r0 + 2 ≤ s.store.topRound ∧
      (s.store.blk B1).round = r0 ∧ out = jumped F cfg.me B1 (s.store.blk B2).creator B2 := by
  unfold tryJump at h
  split at h
  · rename_i r0 B1 hrec htop hown
    dsimp only at h
    split at h
    · rename_i B2 _
      split at h
      · rename_i hR
        split at h
        · rename_i F hF
          split at h
          · rename_i st e hst he
            rw [Option.some.injEq, Prod.mk.injEq] at h
            obtain ⟨rfl, rfl⟩ := h
            exact ⟨r0, B1, B2, F, e, htop, hown, hrec, hF, hst, he, rfl, rfl, rfl, rfl, rfl, rfl,
              rfl, hR.1, hR.2, rfl⟩
          · cases h
        · cases h
      · cases h
    · cases h
  · cases h

omit [Fintype Validator] in
theorem tryJump_offers {s s' : State Validator BlockId Payload}
    {out : List (Output Validator BlockId Payload)} (h : tryJump cfg s = some (s', out)) :
    s'.offers = s.offers := by
  unfold tryJump at h
  split at h
  · dsimp only at h
    split at h
    · split at h
      · split at h
        · split at h
          · rw [Option.some.injEq, Prod.mk.injEq] at h
            rw [← h.1]
          · cases h
        · cases h
      · cases h
    · cases h
  · cases h

omit [Fintype Validator] in
theorem tryJump_of_idle {s : State Validator BlockId Payload} (h : s.recovering = false) :
    tryJump cfg s = none := by
  unfold tryJump; rw [h]

omit [Fintype Validator] in
theorem settle_of_idle {s : State Validator BlockId Payload} (h : s.recovering = false) :
    settle cfg s = advance cfg s := by
  unfold settle; rw [tryJump_of_idle h]

omit [Fintype Validator] in
/-- **A settle advances**, after a jump or not. -/
theorem settle_cases (s : State Validator BlockId Payload) :
    Node.settle cfg s = advance cfg s ∨ ∃ s₁ out, tryJump cfg s = some (s₁, out) ∧
      Node.settle cfg s = ((advance cfg s₁).1, out ++ (advance cfg s₁).2) := by
  unfold Node.settle
  split
  · rename_i s₁ out h; exact Or.inr ⟨s₁, out, h, rfl⟩
  · exact Or.inl rfl

omit [Fintype Validator] in
/-- The last of some blocks at consecutive rounds lies at the last of them. -/
theorem round_of_getLast {F : List (BlockId × Block Validator BlockId Payload)} {a n : ℕ}
    {e : BlockId × Block Validator BlockId Payload}
    (hF : F.map (fun e => e.2.round) = List.range' a n) (he : F.getLast? = some e) :
    e.2.round + 1 = a + n := by
  have hl := congrArg List.getLast? hF
  rw [List.getLast?_map, he] at hl
  have hn : n ≠ 0 := by rintro rfl; simp at hl
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn
  rw [List.range'_concat, List.getLast?_append] at hl
  simp at hl
  omega

variable (cfg) in
/-- **The outputs of at most one jump**, from a store whose blocks are
known: the filled blocks are those the message denotes on that store. -/
def Jumps (K : Set (BlockId × Block Validator BlockId Payload))
    (fs : List (BlockId × Block Validator BlockId Payload)) (js : List (Output Validator BlockId Payload)) :
    Prop :=
  js = [] ∧ fs = [] ∨ ∃ B1 v2 B2, ∃ st : Store Validator BlockId Payload,
    js = jumped fs cfg.me B1 v2 B2 ∧ jumpFills cfg.idOf st cfg.me B1 B2 = some fs ∧
    ∀ j ∈ st.ids, (j, st.map.getD j st.junk) ∈ K

omit [Fintype Validator] in
theorem Jumps.mono {K K' : Set (BlockId × Block Validator BlockId Payload)} (hK : K ⊆ K')
    {fs : List (BlockId × Block Validator BlockId Payload)} {js : List (Output Validator BlockId Payload)}
    (h : Jumps cfg K fs js) : Jumps cfg K' fs js := by
  rcases h with h | ⟨B1, v2, B2, st, h₁, h₂, h₃⟩
  · exact Or.inl h
  · exact Or.inr ⟨B1, v2, B2, st, h₁, h₂, fun j hj => hK (h₃ j hj)⟩

omit [Fintype Validator] in
theorem Jumps.shape {K : Set (BlockId × Block Validator BlockId Payload)}
    {fs : List (BlockId × Block Validator BlockId Payload)} {js : List (Output Validator BlockId Payload)}
    (h : Jumps cfg K fs js) : js = [] ∧ fs = [] ∨ ∃ B1 v2 B2, js = jumped fs cfg.me B1 v2 B2 := by
  rcases h with h | ⟨B1, v2, B2, -, h₁, -⟩
  · exact Or.inl h
  · exact Or.inr ⟨B1, v2, B2, h₁⟩

omit [Fintype Validator] in
/-- **A jump keeps the invariant**, the filled blocks known and good. -/
theorem Inv.tryJump {s s' : State Validator BlockId Payload}
    {K : Set (BlockId × Block Validator BlockId Payload)}
    {B : List (BlockId × Block Validator BlockId Payload)}
    {out : List (Output Validator BlockId Payload)} (hi : Inv cfg s K B)
    (h : tryJump cfg s = some (s', out)) :
    ∃ F, Jumps cfg K F out ∧ Inv cfg s' (K ∪ {x | x ∈ F}) (B ++ F) := by
  obtain ⟨r0, B1, B2, F, e, htop, -, -, hF, hst, he, htop', -, hpd, -, -, -, -, -, hr0, hout⟩ :=
    tryJump_some h
  obtain ⟨-, hc, hb0, hlt, -, hmap, hid⟩ := jumpFills_spec hF
  have hK : K ⊆ K ∪ {x | x ∈ F} := Set.subset_union_left
  have hFK : ∀ x ∈ F, x ∈ K ∪ {x | x ∈ F} := fun x hx => Set.mem_union_right _ hx
  have hkn : ∀ j ∈ s.store.ids, (j, s.store.map.getD j s.store.junk) ∈ K ∪ {x | x ∈ F} :=
    fun j hj => hK (hi.known j hj)
  have hbase := insertAll_base hst
  have hgood := insertAll_good hst hkn hFK
  refine ⟨F, Or.inr ⟨B1, _, B2, s.store, hout, hF, hi.known⟩, ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩⟩
  · exact insertAll_induct (cfg := cfg)
      (fun t => ∀ j ∈ t.ids, (j, t.map.getD j t.junk) ∈ K ∪ {x | x ∈ F})
      (fun _ x hx _ ht => known_insert ht (hFK x hx)) hst hkn
  · rw [hpd]; exact fun x hx => hK (hi.pend x hx)
  · right
    have hlast := round_of_getLast hmap he
    refine ⟨e.2.round, htop', by rw [hbase]; omega, ?_⟩
    rcases hi.rounds with ⟨h0, -⟩ | ⟨t, ht, -, hB⟩
    · rw [htop] at h0; exact absurd h0 (by simp)
    · rw [htop, Option.some.injEq] at ht
      subst ht
      rw [hr0] at hmap hlast
      have hFr : ∀ x ∈ F, r0 < x.2.round ∧ x.2.round ≤ e.2.round := by
        intro x hx
        have : x.2.round ∈ List.range' (r0 + 1) ((s.store.blk B2).round - r0) := by
          rw [← hmap]; exact List.mem_map_of_mem hx
        obtain ⟨i, hi', hxi⟩ := List.mem_range'.mp this
        omega
      exact hB.append (by rw [hmap]; exact List.pairwise_lt_range') hFr
        (by have := hFr e (List.mem_of_getLast? he); omega)
  · intro x hx
    rcases List.mem_append.mp hx with hx | hx
    · exact (hi.good x hx).mono hK
    · exact ⟨(hid x hx).1, (hid x hx).2, (hgood x hx).1, fun _ => (hgood x hx).2⟩
  · intro x hx
    rcases List.mem_append.mp hx with hx | hx
    · exact hK (hi.sub x hx)
    · exact hFK x hx
  · exact insertAll_induct (cfg := cfg) (fun t => StoreValid cfg.q t)
      (fun _ _ _ hc ht => ht.insert fun _ => hc.2.2.2.2) hst hi.valid
  · rw [tryJump_offers h]; exact fun o ho x hx hid => hK (hi.offered o ho x hx hid)

omit [Fintype Validator] in
/-- **Settling keeps the invariant**: at most one jump, then built blocks,
then decisions, then at most one horizon. -/
theorem Inv.settle {s : State Validator BlockId Payload}
    {K : Set (BlockId × Block Validator BlockId Payload)}
    {B : List (BlockId × Block Validator BlockId Payload)} (hi : Inv cfg s K B) :
    ∃ (js : List (Output Validator BlockId Payload))
      (fs bs : List (BlockId × Block Validator BlockId Payload)) (ds : List (ℕ × Option BlockId))
      (gs : List ℕ), Jumps cfg K fs js ∧ gs.length ≤ 1 ∧
      (Node.settle cfg s).2 = js ++ built cfg bs ++ ds.map (fun e => .commit e.1 e.2) ++ gs.map .prune ∧
      Inv cfg (Node.settle cfg s).1 (K ∪ {x | x ∈ fs ++ bs}) (B ++ (fs ++ bs)) := by
  unfold Node.settle
  split
  · rename_i s₁ out h
    obtain ⟨F, hout, hi₁⟩ := hi.tryJump h
    obtain ⟨bs, ds, gs, hgs, ho, hi₂⟩ := hi₁.advance
    refine ⟨out, F, bs, ds, gs, hout, hgs, by
      simp only [ho, List.append_assoc], ?_⟩
    have hset : K ∪ {x | x ∈ F} ∪ {x | x ∈ bs} = K ∪ {x | x ∈ F ++ bs} := by
      ext x; simp only [Set.mem_union, Set.mem_setOf_eq, List.mem_append]; tauto
    rw [← hset, ← List.append_assoc]
    exact hi₂
  · obtain ⟨bs, ds, gs, hgs, ho, hi'⟩ := hi.advance
    exact ⟨[], [], bs, ds, gs, Or.inl ⟨rfl, rfl⟩, hgs, by simpa using ho, by simpa using hi'⟩

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
/-- **A successful bootstrap**, at a round `G` above the node's top and
its horizon: the pruned store takes the attested base and the new own
block, then flushes the offered blocks above `G` and the pending ones at
or above it. -/
theorem tryBoot_some {s s' : State Validator BlockId Payload}
    {out : List (Output Validator BlockId Payload)} (h : tryBoot cfg s = some (s', out)) :
    ∃ t G, ∃ hb : s.store.base < G, s.top = some t ∧ t < G ∧ bootRound cfg s t = some G ∧
      let g : Block Validator BlockId Payload := ⟨G, cfg.me, ∅, cfg.payload G⟩
      let st₀ := (baseAt cfg s G).foldl (fun st e => accept cfg st e.1 e.2) (s.store.prune G hb.le)
      ∃ hg : cfg.idOf g ∉ st₀.ids ∧ st₀.base ≤ g.round,
      let st₁ := st₀.insert (cfg.idOf g) g hg.1 hg.2 (fun _ => Finset.empty_subset _)
        (fun _ j hj => absurd hj (Finset.notMem_empty j))
      let pend := (s.offers.flatMap (·.2.2)).filter (fun e =>
        decide (G < e.2.round ∧ e.1 = cfg.idOf e.2)) ++ s.pending.filter fun e => G ≤ e.2.round
      s'.store = (flush cfg (pend.length + 1) st₁ pend).1 ∧
      s'.pending = (flush cfg (pend.length + 1) st₁ pend).2 ∧
      s'.top = some G ∧ s'.own = some (cfg.idOf g) ∧
      s'.lo = max s.lo (cfg.m * ((G + cfg.per - 1) / cfg.per)) ∧
      s'.recovering = s.recovering ∧ s'.offers = [] ∧
      s'.requested = s.requested.filter (fun x => G ≤ x.2.2) ∧
      out = built cfg [(cfg.idOf g, g)] := by
  unfold tryBoot at h
  split at h
  · rename_i t G ht hG
    split at h
    · rename_i hbase
      dsimp only at h
      split at h
      · rename_i hg
        rw [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        have hG' : bootRound cfg s t = some G := by rw [ht] at hG; exact hG
        have htG : t < G := by
          have := List.mem_filter.mp (List.max?_mem hG')
          exact (by simpa using this.2 : t < G ∧ _).1
        exact ⟨t, G, hbase, ht, htG, hG', hg, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
      · cases h
    · cases h
  · cases h

omit [Fintype Validator] in
/-- **A bootstrap raises the horizon** to its round. -/
theorem boot_base {s s' : State Validator BlockId Payload}
    {out : List (Output Validator BlockId Payload)} (h : tryBoot cfg s = some (s', out)) :
    s.store.base < s'.store.base := by
  obtain ⟨t, G, hb, -, -, -, hg, hst, -⟩ := tryBoot_some h
  rw [hst, flush_base]
  change s.store.base < ((baseAt cfg s G).foldl (fun st e => accept cfg st e.1 e.2)
    (s.store.prune G hb.le)).base
  rw [foldl_base]
  exact hb

omit [Fintype Validator] in
/-- **A bootstrap keeps the invariant**: the new horizon lies at the
node's new top, its chain restarts with a reference-free block above its
old top, and what it takes from the offers is known. -/
theorem Inv.tryBoot {s s' : State Validator BlockId Payload}
    {K : Set (BlockId × Block Validator BlockId Payload)}
    {B : List (BlockId × Block Validator BlockId Payload)}
    {out : List (Output Validator BlockId Payload)} (hi : Inv cfg s K B)
    (h : tryBoot cfg s = some (s', out)) :
    ∃ e, out = built cfg [e] ∧ e.2.refs = ∅ ∧ Inv cfg s' (K ∪ {e}) (B ++ [e]) := by
  unfold Node.tryBoot at h
  split at h
  · rename_i t G ht hG
    split at h
    · rename_i hbase
      dsimp only at h
      split at h
      · rename_i hg
        rw [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        -- the round lies above the top
        have htG : t < G := by
          rw [ht] at hG
          change bootRound cfg s t = some G at hG
          have := List.mem_filter.mp (List.max?_mem hG)
          exact (by simpa using this.2 : t < G ∧ _).1
        let e : BlockId × Block Validator BlockId Payload :=
          (cfg.idOf ⟨G, cfg.me, ∅, cfg.payload G⟩, ⟨G, cfg.me, ∅, cfg.payload G⟩)
        have hK : K ⊆ K ∪ {e} := Set.subset_union_left
        have hoff : ∀ o ∈ s.offers, ∀ x ∈ o.2.2, x.1 = cfg.idOf x.2 → x ∈ K ∪ {e} :=
          fun o ho x hx hid => hK (hi.offered o ho x hx hid)
        have hfo : ∀ x ∈ s.offers.flatMap (·.2.2), x.1 = cfg.idOf x.2 → x ∈ K ∪ {e} := by
          intro x hx hid
          obtain ⟨o, ho, hxo⟩ := List.mem_flatMap.mp hx
          exact hoff o ho x hxo hid
        -- the pruned store, with the attested base
        have hkp : ∀ j ∈ (s.store.prune G hbase.le).ids,
            (j, (s.store.prune G hbase.le).map.getD j (s.store.prune G hbase.le).junk) ∈ K ∪ {e} := by
          intro j hj
          have hj' := Finset.mem_filter.mp hj
          have hraw := treeMap_getD_filter_of (t := s.store.map)
            (f := fun _ b => decide (G ≤ b.round)) (k := j) (fb := s.store.junk)
            (by simpa [Store.blk, lookup] using hj'.2)
          change (j, (s.store.map.filter _).getD j s.store.junk) ∈ K ∪ {e}
          rw [hraw]
          exact hK (hi.known j hj'.1)
        have h₀ := foldl_accept_known (cfg := cfg) (baseAt cfg s G) hkp (hi.valid.prune (hG := hbase.le))
          fun x hx => by
            obtain ⟨hx, hc⟩ := List.mem_filter.mp hx
            simp only [decide_eq_true_eq] at hc
            exact hfo x hx hc.2.1
        set st₀ := (baseAt cfg s G).foldl (fun st e => accept cfg st e.1 e.2)
          (s.store.prune G hbase.le) with hst₀
        have hb₀ : st₀.base = G := h₀.2.1
        let st₁ := st₀.insert e.1 e.2 hg.1 hg.2 (fun _ => Finset.empty_subset _)
          (fun _ j hj => absurd hj (Finset.notMem_empty j))
        have hk₁ : ∀ j ∈ st₁.ids, (j, st₁.map.getD j st₁.junk) ∈ K ∪ {e} :=
          known_insert h₀.1 (Set.mem_union_right _ rfl)
        have hv₁ : StoreValid cfg.q st₁ :=
          h₀.2.2.insert fun h => absurd h (by change ¬ st₀.base < G; omega)
        have hfl := flush_known (cfg := cfg) (K := K ∪ {e})
          (((s.offers.flatMap (·.2.2)).filter (fun x =>
            decide (G < x.2.round ∧ x.1 = cfg.idOf x.2)) ++
            s.pending.filter fun x => G ≤ x.2.round).length + 1) hk₁ hv₁ (pend :=
          (s.offers.flatMap (·.2.2)).filter (fun x => decide (G < x.2.round ∧ x.1 = cfg.idOf x.2))
            ++ s.pending.filter fun x => G ≤ x.2.round)
          (fun x hx => by
            rcases List.mem_append.mp hx with hx | hx
            · obtain ⟨hx, hc⟩ := List.mem_filter.mp hx
              simp only [decide_eq_true_eq] at hc
              exact hfo x hx hc.2
            · exact hK (hi.pend x (List.mem_filter.mp hx).1))
        refine ⟨e, rfl, rfl, ⟨hfl.1, hfl.2.1, Or.inr ⟨G, rfl, ?_, ?_⟩, ?_, ?_, hfl.2.2.2,
          fun o ho => absurd ho (by simp)⟩⟩
        · rw [hfl.2.2.1]; change st₀.base ≤ G; omega
        · rcases hi.rounds with ⟨h0, -⟩ | ⟨t', ht', -, hB⟩
          · rw [ht] at h0; exact absurd h0 (by simp)
          · rw [ht, Option.some.injEq] at ht'
            subst ht'
            exact hB.append (by simp) (fun x hx => by
              rw [List.mem_singleton] at hx; subst hx; exact ⟨htG, le_rfl⟩) htG.le
        · intro x hx
          rcases List.mem_append.mp hx with hx | hx
          · exact (hi.good x hx).mono hK
          · rw [List.mem_singleton] at hx
            subst hx
            exact ⟨rfl, rfl, fun j hj => absurd hj (Finset.notMem_empty j),
              fun hn => absurd hn (by simp [e])⟩
        · intro x hx
          rcases List.mem_append.mp hx with hx | hx
          · exact hK (hi.sub x hx)
          · rw [List.mem_singleton] at hx; subst hx; exact Set.mem_union_right _ rfl
      · cases h
    · cases h
  · cases h

omit [Fintype Validator] in
/-- **Settling keeps the invariant**, after outputs that move blocks
only, at a larger knowledge. -/
theorem Inv.settle_of {s : State Validator BlockId Payload}
    {K K' : Set (BlockId × Block Validator BlockId Payload)}
    {B : List (BlockId × Block Validator BlockId Payload)} (hi : Inv cfg s K B) (hK : K ⊆ K')
    (pre : List (Output Validator BlockId Payload)) (hpre : ∀ o ∈ pre, o.isFetch) :
    ∃ (xs js : List (Output Validator BlockId Payload))
      (fs bs : List (BlockId × Block Validator BlockId Payload)) (ds : List (ℕ × Option BlockId))
      (gs : List ℕ), (∀ o ∈ xs, o.isFetch) ∧ Jumps cfg K' fs js ∧ gs.length ≤ 1 ∧
      pre ++ (Node.settle cfg s).2 =
        xs ++ js ++ built cfg bs ++ ds.map (fun e => .commit e.1 e.2) ++ gs.map .prune ∧
      Inv cfg (Node.settle cfg s).1 (K' ∪ {x | x ∈ fs ++ bs}) (B ++ (fs ++ bs)) := by
  obtain ⟨js, fs, bs, ds, gs, hjs, hgs, ho, hi'⟩ := hi.settle
  refine ⟨pre, js, fs, bs, ds, gs, hpre, hjs.mono hK, hgs, by rw [ho]; simp only [List.append_assoc],
    hi'.mono fun x hx => ?_⟩
  rcases hx with hx | hx
  · exact Or.inl (hK hx)
  · exact Or.inr hx

/-- **A step keeps the invariant**: what it was given and its own blocks
are known, and its own blocks are good. -/
theorem Inv.step {s : State Validator BlockId Payload}
    {K : Set (BlockId × Block Validator BlockId Payload)}
    {B : List (BlockId × Block Validator BlockId Payload)} (hi : Inv cfg s K B)
    (i : Input Validator BlockId Payload) :
    ∃ (xs js : List (Output Validator BlockId Payload))
      (fs bs : List (BlockId × Block Validator BlockId Payload)) (ds : List (ℕ × Option BlockId))
      (gs : List ℕ), (∀ o ∈ xs, o.isFetch) ∧
      Jumps cfg (K ∪ {x | x ∈ delivered cfg [i]} ∪ {x | x ∈ received cfg s i}) fs js ∧
      gs.length ≤ 1 ∧ (Node.step cfg s i).2 =
        xs ++ js ++ built cfg bs ++ ds.map (fun e => .commit e.1 e.2) ++ gs.map .prune ∧
      Inv cfg (Node.step cfg s i).1
        (K ∪ {x | x ∈ delivered cfg [i]} ∪ {x | x ∈ received cfg s i} ∪ {x | x ∈ fs ++ bs})
        (B ++ (fs ++ bs)) := by
  let K' := K ∪ {x | x ∈ delivered cfg [i]} ∪ {x | x ∈ received cfg s i}
  have hsub : K ⊆ K' := fun x hx => Or.inl (Or.inl hx)
  have hnil : ∀ (xs : List (Output Validator BlockId Payload)), (∀ o ∈ xs, o.isFetch) →
      ∃ (xs' js : List (Output Validator BlockId Payload))
        (fs bs : List (BlockId × Block Validator BlockId Payload)) (ds : List (ℕ × Option BlockId))
        (gs : List ℕ), (∀ o ∈ xs', o.isFetch) ∧ Jumps cfg K' fs js ∧ gs.length ≤ 1 ∧
        xs = xs' ++ js ++ built cfg bs ++ ds.map (fun e => .commit e.1 e.2) ++ gs.map .prune ∧
        Inv cfg s (K' ∪ {x | x ∈ fs ++ bs}) (B ++ (fs ++ bs)) :=
    fun xs hxs => ⟨xs, [], [], [], [], [], hxs, Or.inl ⟨rfl, rfl⟩, by simp, by simp [built],
      by simpa using hi.mono hsub⟩
  have hnil' := hnil [] (by simp)
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
        let s₀ := { s with store := st, top := some 0, own := some e.1 }
        have hi₀ : Inv cfg { s₀ with recovering := false } (K ∪ {x | x ∈ [e]}) (B ++ [e]) := by
          refine ⟨known_insert (hnew := h₂.1) (hab := h₂.2.1)
              (hrefs := fun _ => Finset.empty_subset _)
              (hpred := fun _ j hj => absurd hj (Finset.notMem_empty j))
              (fun j hj => Set.subset_union_left (hi.known j hj)) (by simp [e]),
            fun x hx => Set.subset_union_left (hi.pend x hx), Or.inr ⟨0, rfl, ?_, ?_⟩,
            fun x hx => ?_, fun x hx => ?_,
            hi.valid.insert (hnew := h₂.1) (hab := h₂.2.1)
              (hrefs := fun _ => Finset.empty_subset _)
              (hpred := fun _ j hj => absurd hj (Finset.notMem_empty j))
              fun h => absurd h (by simp [Config.genesis]),
            fun o ho x hx hid => Set.subset_union_left (hi.offered o ho x hx hid)⟩
          · change s.store.base ≤ 0; omega
          · rw [hB.1, List.nil_append]
            exact ⟨by simp, fun x hx => by rw [List.mem_singleton] at hx; subst hx; rfl⟩
          · rw [hB.1, List.nil_append, List.mem_singleton] at hx
            subst hx
            exact ⟨rfl, rfl, fun j hj => absurd hj (Finset.notMem_empty j),
              fun hn => absurd hn (by simp [e, Config.genesis])⟩
          · rw [hB.1, List.nil_append, List.mem_singleton] at hx
            subst hx; simp
        rw [settle_of_idle rfl]
        obtain ⟨bs, ds, gs, hgs, ho, hi'⟩ := hi₀.advance
        refine ⟨[], [], [], e :: bs, ds, gs, by simp, Or.inl ⟨rfl, rfl⟩, hgs, ?_, ?_⟩
        · rw [ho]; simp [built, e, Config.genesis]
        · refine (by simpa using hi' : Inv cfg _ (K ∪ {x | x ∈ [e]} ∪ {x | x ∈ bs}) (B ++ e :: bs)).mono
            fun x hx => ?_
          simp only [Set.mem_union, Set.mem_setOf_eq, List.mem_singleton, List.mem_cons,
            List.nil_append] at hx ⊢
          tauto
      · exact hnil' 
    · exact hnil'
  | deliver id b =>
    simp only [Node.step]
    split
    · rename_i hc
      have hd : delivered cfg [Input.deliver id b] = [(id, b)] := by simp [delivered, hc.1]
      have hmem : (id, b) ∈ K' := Or.inl (Or.inr (by rw [hd]; exact List.mem_singleton_self _))
      have hfl := flush_known (cfg := cfg) (K := K') (s.pending.length + 1) (st := s.store)
        (pend := (id, b) :: s.pending) (fun j hj => hsub (hi.known j hj)) hi.valid
        (fun x hx => by
          rcases List.mem_cons.mp hx with rfl | hx
          · exact hmem
          · exact hsub (hi.pend x hx))
      dsimp only at hfl ⊢
      generalize flush cfg (s.pending.length + 1) s.store ((id, b) :: s.pending) = fl at hfl ⊢
      generalize missing { s with store := fl.1, pending := fl.2 } id b = miss
      let req := s.requested ++ miss.map fun x => (x.1, id, x.2)
      have hi₀ : ∀ a, Inv cfg
          { s with store := fl.1, pending := fl.2, requested := req, asked := a } K' B :=
        fun _ => ⟨hfl.1, hfl.2.1, by
          rcases hi.rounds with ⟨h0, hB, hb⟩ | ⟨t, ht, hb, hB⟩
          · exact Or.inl ⟨h0, hB, by rw [hfl.2.2.1]; exact hb⟩
          · exact Or.inr ⟨t, ht, by rw [hfl.2.2.1]; exact hb, hB⟩,
          fun x hx => (hi.good x hx).mono hsub, fun x hx => hsub (hi.sub x hx), hfl.2.2.2,
          fun o ho x hx hid => hsub (hi.offered o ho x hx hid)⟩
      exact (hi₀ _).settle_of subset_rfl
        ((if miss.isEmpty then [] else [.fetch (miss.map Prod.fst)]) ++
          if s.recovering = true ∧ s.asked + cfg.lag + 2 ≤ b.round then [.requestBase] else [])
        fun o ho' => by
        rcases List.mem_append.mp ho' with ho' | ho'
        · split at ho'
          · simp at ho'
          · rw [List.mem_singleton] at ho'; subst ho'; rfl
        · split at ho'
          · rw [List.mem_singleton] at ho'; subst ho'; rfl
          · simp at ho'
    · exact hnil'
  | timer r =>
    simp only [Node.step]
    exact (⟨fun j hj => hsub (hi.known j hj), fun x hx => hsub (hi.pend x hx), hi.rounds,
      fun x hx => (hi.good x hx).mono hsub, fun x hx => hsub (hi.sub x hx), hi.valid,
      fun o ho x hx hid => hsub (hi.offered o ho x hx hid)⟩ :
        Inv cfg { s with fired := insert r s.fired } K' B).settle_of subset_rfl [] (by simp)
  | fetchRequest peer ids =>
    simp only [Node.step]
    refine hnil _ fun o ho => ?_
    obtain ⟨j, -, rfl⟩ := List.mem_map.mp ho
    rfl
  | jump v1 B1 v2 B2 =>
    simp only [Node.step]
    split
    · exact hnil'
    · have hr : received cfg s (.jump v1 B1 v2 B2) = jumpIn cfg s v1 B1 v2 B2 := rfl
      have hmem : ∀ x ∈ jumpIn cfg s v1 B1 v2 B2, x ∈ K' := fun x hx =>
        Or.inr (by rw [hr]; exact hx)
      have hfl := flush_known (cfg := cfg) (K := K')
        (s.pending.length + (jumpIn cfg s v1 B1 v2 B2).length + 1) (st := s.store)
        (pend := jumpIn cfg s v1 B1 v2 B2 ++ s.pending) (fun j hj => hsub (hi.known j hj)) hi.valid
        (fun x hx => by
          rcases List.mem_append.mp hx with hx | hx
          · exact hmem x hx
          · exact hsub (hi.pend x hx))
      dsimp only at hfl ⊢
      generalize flush cfg (s.pending.length + (jumpIn cfg s v1 B1 v2 B2).length + 1) s.store
        (jumpIn cfg s v1 B1 v2 B2 ++ s.pending) = fl at hfl ⊢
      have hi₀ : Inv cfg { s with store := fl.1, pending := fl.2 } K' B :=
        ⟨hfl.1, hfl.2.1, by
          rcases hi.rounds with ⟨h0, hB, hb⟩ | ⟨t, ht, hb, hB⟩
          · exact Or.inl ⟨h0, hB, by rw [hfl.2.2.1]; exact hb⟩
          · exact Or.inr ⟨t, ht, by rw [hfl.2.2.1]; exact hb, hB⟩,
          fun x hx => (hi.good x hx).mono hsub, fun x hx => hsub (hi.sub x hx), hfl.2.2.2,
          fun o ho x hx hid => hsub (hi.offered o ho x hx hid)⟩
      simpa using hi₀.settle_of subset_rfl [] (by simp)
  | restart =>
    simp only [Node.step]
    exact (⟨fun j hj => hsub (hi.known j hj), fun e he => by simp [State.recover] at he,
      hi.rounds, fun x hx => (hi.good x hx).mono hsub, fun x hx => hsub (hi.sub x hx),
      hi.valid, fun o ho => by simp [State.recover] at ho⟩ : Inv cfg s.recover K' B).settle_of
        subset_rfl [.requestBase] (by simp [Output.isFetch])
  | baseRequest peer =>
    simp only [Node.step]
    exact hnil _ (by simp [Output.isFetch])
  | baseOffer peer G bs =>
    simp only [Node.step]
    split
    · rename_i hc
      let s₁ := { s with offers := (peer, G, bs) :: s.offers.filter fun o => o.1 ≠ peer }
      have hi₁ : Inv cfg s₁ K' B :=
        ⟨fun j hj => hsub (hi.known j hj), fun x hx => hsub (hi.pend x hx), hi.rounds,
          fun x hx => (hi.good x hx).mono hsub, fun x hx => hsub (hi.sub x hx), hi.valid,
          fun o ho x hx hid => by
            rcases List.mem_cons.mp ho with rfl | ho
            · refine Or.inl (Or.inr ?_)
              simp only [Set.mem_setOf_eq, delivered, List.flatMap_cons, List.flatMap_nil,
                List.append_nil, List.mem_filter, decide_eq_true_eq]
              exact ⟨hx, hid⟩
            · exact hsub (hi.offered o (List.mem_filter.mp ho).1 x hx hid)⟩
      split
      · rename_i s₂ out hb
        obtain ⟨e, hout, he, hi₂⟩ := hi₁.tryBoot hb
        obtain ⟨bs', ds, gs, hgs, ho, hi'⟩ := hi₂.advance
        refine ⟨[], [], [], e :: bs', ds, gs, by simp, Or.inl ⟨rfl, rfl⟩, hgs, ?_, ?_⟩
        · rw [ho, hout]; simp [built, List.append_assoc]
        · refine (by simpa using hi' :
            Inv cfg _ (K' ∪ {e} ∪ {x | x ∈ bs'}) (B ++ e :: bs')).mono fun x hx => ?_
          rcases hx with (hx | hx) | hx
          · exact Or.inl hx
          · exact Or.inr (by rw [Set.mem_singleton_iff] at hx; subst hx; simp)
          · exact Or.inr (by simp only [Set.mem_setOf_eq] at hx; simp [hx])
      · exact ⟨[], [], [], [], [], [], by simp, Or.inl ⟨rfl, rfl⟩, by simp, by simp [built],
          by simpa only [List.append_nil] using hi₁.mono Set.subset_union_left⟩
    · exact hnil'

omit [Fintype Validator] in
/-- The blocks a step's outputs broadcast: the built ones. -/
theorem broadcasts_shape {xs js : List (Output Validator BlockId Payload)}
    {fs bs : List (BlockId × Block Validator BlockId Payload)} {ds : List (ℕ × Option BlockId)}
    {gs : List ℕ} (hxs : ∀ o ∈ xs, o.isFetch)
    (hjs : js = [] ∧ fs = [] ∨ ∃ B1 v2 B2, js = jumped fs cfg.me B1 v2 B2) :
    broadcasts (xs ++ js ++ built cfg bs ++ ds.map (fun e => .commit e.1 e.2) ++ gs.map .prune) =
      bs := by
  have hx : broadcasts xs = [] := by
    induction xs with
    | nil => rfl
    | cons o xs ih =>
      have ho := hxs o List.mem_cons_self
      have := ih fun o' h' => hxs o' (List.mem_cons_of_mem _ h')
      cases o <;> simp_all [broadcasts, Output.isFetch]
  have hj : broadcasts js = [] := by
    rcases hjs with ⟨rfl, -⟩ | ⟨B1, v2, B2, rfl⟩
    · rfl
    · simp [jumped, broadcasts, List.filterMap_append, List.filterMap_map]
  have hb : broadcasts (built cfg bs) = bs := by
    induction bs with
    | nil => rfl
    | cons e bs ih =>
      simp only [built, List.flatMap_cons] at ih ⊢
      simp only [broadcasts, List.filterMap_append, List.filterMap_cons] at ih ⊢
      simp [ih]
  simp only [broadcasts, List.filterMap_append] at hx hj hb ⊢
  rw [hx, hj, hb]
  simp [List.filterMap_map]

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

omit [Fintype Validator] [DecidableEq Validator] [LinearOrder BlockId] in
theorem persists_jumped (fs : List (BlockId × Block Validator BlockId Payload)) (v1 : Validator)
    (B1 : BlockId) (v2 : Validator) (B2 : BlockId) : persists (jumped fs v1 B1 v2 B2) = fs := by
  simp only [jumped, persists, List.filterMap_append, List.filterMap_map]
  simp

omit [Fintype Validator] [DecidableEq Validator] [LinearOrder BlockId] in
theorem persists_of_isFetch {xs : List (Output Validator BlockId Payload)}
    (h : ∀ o ∈ xs, o.isFetch) : persists xs = [] := by
  induction xs with
  | nil => rfl
  | cons o xs ih =>
    have ho := h o List.mem_cons_self
    have := ih fun o' h' => h o' (List.mem_cons_of_mem _ h')
    cases o <;> simp_all [persists, Output.isFetch]

omit [Fintype Validator] in
/-- The node's own blocks in a step's outputs: the filled ones, then the
built ones. -/
theorem persists_shape {xs js : List (Output Validator BlockId Payload)}
    {fs bs : List (BlockId × Block Validator BlockId Payload)} {ds : List (ℕ × Option BlockId)}
    {gs : List ℕ} (hxs : ∀ o ∈ xs, o.isFetch)
    (hjs : js = [] ∧ fs = [] ∨ ∃ B1 v2 B2, js = jumped fs cfg.me B1 v2 B2) :
    persists (xs ++ js ++ built cfg bs ++ ds.map (fun e => .commit e.1 e.2) ++ gs.map .prune) =
      fs ++ bs := by
  have hj : persists js = fs := by
    rcases hjs with ⟨rfl, rfl⟩ | ⟨B1, v2, B2, rfl⟩
    · rfl
    · exact persists_jumped _ _ _ _ _
  simp only [persists_append, persists_of_isFetch hxs, hj, persists_built, List.nil_append]
  simp [persists, List.filterMap_map]

omit [Fintype Validator] in
/-- What was delivered or offered is identified by its hash. -/
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
  | baseOffer p G bs =>
    simp only [List.mem_filter, decide_eq_true_eq] at hx
    exact hx.2
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
      (K ∪ {x | x ∈ delivered cfg is} ∪ {x | x ∈ derived cfg s is} ∪
        {x | x ∈ persists (Node.run cfg s is).2})
      (B ++ persists (Node.run cfg s is).2)
  | [], s, K, B, hi => by simpa [Node.run, delivered, derived, persists] using hi
  | i :: is, s, K, B, hi => by
    obtain ⟨xs, js, fs, bs, ds, gs, hxs, hjs, -, ho, hi₁⟩ := hi.step i
    have ih := Inv.run is hi₁
    simp only [Node.run]
    rw [persists_append, ho, persists_shape hxs hjs.shape]
    have hK : K ∪ {x | x ∈ delivered cfg [i]} ∪ {x | x ∈ received cfg s i} ∪ {x | x ∈ fs ++ bs} ∪
        {x | x ∈ delivered cfg is} ∪ {x | x ∈ derived cfg (Node.step cfg s i).1 is} ∪
          {x | x ∈ persists (Node.run cfg (Node.step cfg s i).1 is).2} =
        K ∪ {x | x ∈ delivered cfg (i :: is)} ∪ {x | x ∈ derived cfg s (i :: is)} ∪
          {x | x ∈ fs ++ bs ++ persists (Node.run cfg (Node.step cfg s i).1 is).2} := by
      rw [delivered_cons i is]
      simp only [derived]
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
  offered := fun _ h => absurd h (List.not_mem_nil)

end Node

end LeanDag
