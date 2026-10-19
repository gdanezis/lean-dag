import LeanDag.Node.Model.Run
import LeanDag.Node.Helpers.ReadsView
/-!
# One node at a time — the lemmas

A successful build step adds one block at the round above the node's top,
its own, identified by its hash, with accepted references, and valid
under the store's map (`tryBuild_some`); resuming moves the top up with
no block (`tryResume_some`); building, resuming, deciding and collecting
change the parts of the state the claims read only so.
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
  · rename_i r hr
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
/-- An invariant read only from the store, the pending blocks, the top
and the offers carries over to a state that keeps them. -/
theorem Inv.of_eq {s s' : State Validator BlockId Payload}
    {K : Set (BlockId × Block Validator BlockId Payload)}
    {B : List (BlockId × Block Validator BlockId Payload)} (hi : Inv cfg s K B)
    (hst : s'.store = s.store) (hpd : s'.pending = s.pending) (htop : s'.top = s.top)
    (hof : s'.offers = s.offers) : Inv cfg s' K B :=
  ⟨by rw [hst]; exact hi.known, by rw [hpd]; exact hi.pend,
    by rw [hst, htop]; exact hi.rounds, hi.good, hi.sub, by rw [hst]; exact hi.valid,
    by rw [hof]; exact hi.offered⟩

omit [Fintype Validator] in
/-- **Proposing** keeps everything but the proposals, the certificate and
the height last proposed. -/
theorem proposeAt_keeps (s : State Validator BlockId Payload) :
    (proposeAt cfg s).1.store = s.store ∧ (proposeAt cfg s).1.pending = s.pending ∧
      (proposeAt cfg s).1.top = s.top ∧ (proposeAt cfg s).1.own = s.own ∧
      (proposeAt cfg s).1.offers = s.offers ∧ (proposeAt cfg s).1.lo = s.lo ∧
      (proposeAt cfg s).1.requested = s.requested ∧
      (proposeAt cfg s).1.recovering = s.recovering ∧ (proposeAt cfg s).1.fired = s.fired ∧
      (proposeAt cfg s).1.decided = s.decided ∧ (proposeAt cfg s).1.certs = s.certs := by
  unfold proposeAt
  dsimp only
  split <;> exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

omit [Fintype Validator] in
theorem proposeAt_quiet (s : State Validator BlockId Payload) :
    ∀ o ∈ (proposeAt cfg s).2, o.isQuiet := by
  unfold proposeAt
  dsimp only
  split <;> simp [Output.isQuiet]

omit [Fintype Validator] in
/-- **Deciding keeps the invariant** and outputs no block. -/
theorem Inv.decideStep {s : State Validator BlockId Payload}
    {K : Set (BlockId × Block Validator BlockId Payload)}
    {B : List (BlockId × Block Validator BlockId Payload)} (hi : Inv cfg s K B) :
    Out [] (decideStep cfg s).2 ∧ Inv cfg (decideStep cfg s).1 K B := by
  unfold Node.decideStep
  dsimp only
  split
  · rename_i hlt
    generalize hds : Scheme.tryDecide (S := cfg.slots) cfg.p cfg.σ s.store.toRecord
      s.store.view s.lo (decidable cfg s.store.topRound - 1) = ds
    obtain ⟨hst, hpd, htop, -, hof, -⟩ :=
      proposeAt_keeps (cfg := cfg) { s with lo := s.lo + ds.length, decided := s.decided ++ ds }
    exact ⟨(out_quiet (quiet_commits _)).append (out_quiet (proposeAt_quiet _)),
      hi.of_eq hst hpd htop hof⟩
  · exact ⟨⟨rfl, rfl⟩, hi⟩

omit [Fintype Validator] in
/-- **Collecting keeps the invariant** and outputs no block. -/
theorem Inv.collect {s : State Validator BlockId Payload}
    {K : Set (BlockId × Block Validator BlockId Payload)}
    {B : List (BlockId × Block Validator BlockId Payload)} (hi : Inv cfg s K B) :
    Out [] (collect cfg s).2 ∧ Inv cfg (collect cfg s).1 K B := by
  unfold Node.collect
  split
  · rename_i t ht
    dsimp only
    split
    · rename_i hG
      refine ⟨⟨rfl, rfl⟩, ⟨?_, ?_, ?_, hi.good, hi.sub, hi.valid.prune (hG := hG.le),
        hi.offered⟩⟩
      · intro j hj
        have hj' := (Finset.mem_filter.mp hj)
        have hraw := treeMap_getD_filter_of (t := s.store.map)
          (f := fun _ b => decide (min (cfg.per * (min s.lo s.certHeight / cfg.m)) t - cfg.lag ≤
            b.round)) (k := j) (fb := s.store.junk) (by simpa [Store.blk, lookup] using hj'.2)
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
    · exact ⟨⟨rfl, rfl⟩, hi⟩
  · exact ⟨⟨rfl, rfl⟩, hi⟩

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
/-- **Advancing keeps the invariant**, and its own blocks are the built
ones. -/
theorem Inv.advance {s : State Validator BlockId Payload}
    {K : Set (BlockId × Block Validator BlockId Payload)}
    {B : List (BlockId × Block Validator BlockId Payload)} (hi : Inv cfg s K B) :
    ∃ bs, Out bs (advance cfg s).2 ∧ Inv cfg (advance cfg s).1 (K ∪ {x | x ∈ bs}) (B ++ bs) := by
  obtain ⟨bs, hbs, hi₁⟩ := hi.progress (s.store.topRound + 2)
  obtain ⟨hds, hi₂⟩ := hi₁.decideStep
  obtain ⟨hgo, hi₃⟩ := hi₂.collect
  refine ⟨bs, ?_, hi₃.flushAll _⟩
  simp only [Node.advance]
  rw [hbs]
  simpa using ((out_built (cfg := cfg) bs).append hds).append hgo

omit [Fintype Validator] in
/-- **A successful resume**: the top moves up to a round where the store
holds `q` authors, a nonempty set of them, with no block of the node's
own there; the rest of the state the claims read stays. -/
theorem tryResume_some {s s' : State Validator BlockId Payload} (h : tryResume cfg s = some s') :
    ∃ t R, s.top = some t ∧ t < R ∧ cfg.q ≤ (authorsIn s.store.toRecord s.store.ids R).card ∧
      0 < (authorsIn s.store.toRecord s.store.ids R).card ∧
      s'.store = s.store ∧ s'.pending = s.pending ∧ s'.top = some R ∧ s'.own = none ∧
      s'.lo = s.lo ∧ s'.requested = s.requested ∧ s'.offers = s.offers ∧
      s'.fired = insert R s.fired ∧ s'.recovering = false := by
  unfold tryResume at h
  split at h
  · rename_i t hrec htop
    dsimp only at h
    split at h
    · rename_i R hR
      split at h
      · rw [Option.some.injEq] at h
        subst h
        have hm := List.mem_filter.mp (List.max?_mem hR)
        simp only [Bool.and_eq_true, decide_eq_true_eq] at hm
        exact ⟨t, R, htop, by omega, hm.2.1.2, hm.2.2, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
      · cases h
    · cases h
  · cases h

omit [Fintype Validator] in
theorem tryResume_of_idle {s : State Validator BlockId Payload} (h : s.recovering = false) :
    tryResume cfg s = none := by
  unfold tryResume; rw [h]

omit [Fintype Validator] in
theorem settle_of_idle {s : State Validator BlockId Payload} (h : s.recovering = false) :
    settle cfg s = advance cfg s := by
  unfold settle; rw [tryResume_of_idle h]

omit [Fintype Validator] in
/-- **A settle advances**, after a resume or not. -/
theorem settle_cases (s : State Validator BlockId Payload) :
    Node.settle cfg s = advance cfg s ∨ ∃ s₁, tryResume cfg s = some s₁ ∧
      Node.settle cfg s = advance cfg s₁ := by
  unfold Node.settle
  split
  · rename_i s₁ h; exact Or.inr ⟨s₁, h, rfl⟩
  · exact Or.inl rfl

omit [Fintype Validator] in
/-- **A resume keeps the invariant.** -/
theorem Inv.tryResume {s s' : State Validator BlockId Payload}
    {K : Set (BlockId × Block Validator BlockId Payload)}
    {B : List (BlockId × Block Validator BlockId Payload)} (hi : Inv cfg s K B)
    (h : tryResume cfg s = some s') : Inv cfg s' K B := by
  obtain ⟨t, R, htop, htR, -, -, hst, hpd, htop', -, -, -, hof, -, -⟩ := tryResume_some h
  refine ⟨by rw [hst]; exact hi.known, by rw [hpd]; exact hi.pend, ?_, hi.good, hi.sub,
    by rw [hst]; exact hi.valid, by rw [hof]; exact hi.offered⟩
  rcases hi.rounds with ⟨h0, -⟩ | ⟨t', ht', hb, hB⟩
  · rw [htop] at h0; exact absurd h0 (by simp)
  · rw [htop, Option.some.injEq] at ht'
    subst ht'
    exact Or.inr ⟨R, htop', by rw [hst]; omega, hB.mono htR.le⟩

omit [Fintype Validator] in
/-- **Settling keeps the invariant**, and its own blocks are the built
ones. -/
theorem Inv.settle {s : State Validator BlockId Payload}
    {K : Set (BlockId × Block Validator BlockId Payload)}
    {B : List (BlockId × Block Validator BlockId Payload)} (hi : Inv cfg s K B) :
    ∃ bs, Out bs (Node.settle cfg s).2 ∧
      Inv cfg (Node.settle cfg s).1 (K ∪ {x | x ∈ bs}) (B ++ bs) := by
  rcases settle_cases (cfg := cfg) s with h | ⟨s₁, hr, h⟩ <;> rw [h]
  · exact hi.advance
  · exact (hi.tryResume hr).advance

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
/-- The base a bootstrap keeps is part of the attested base. -/
theorem mem_keptBase {l : List (BlockId × Block Validator BlockId Payload)}
    {x : BlockId × Block Validator BlockId Payload} (h : x ∈ keptBase cfg l) : x ∈ l := by
  unfold keptBase at h
  split at h
  · exact h
  · exact List.pwFilter_subset _ h

omit [Fintype Validator] in
/-- The base a bootstrap keeps of a nonempty attested base is nonempty. -/
theorem exists_mem_keptBase {l : List (BlockId × Block Validator BlockId Payload)}
    {x : BlockId × Block Validator BlockId Payload} (hx : x ∈ l) :
    ∃ y, y ∈ keptBase cfg l := by
  unfold keptBase
  split
  · exact ⟨x, hx⟩
  · induction l generalizing x with
    | nil => exact absurd hx List.not_mem_nil
    | cons a l ih =>
      by_cases hl : ∃ y, y ∈ l
      · obtain ⟨y, hy⟩ := hl
        obtain ⟨z, hz⟩ := ih hy
        by_cases hp : ∀ b ∈ l.pwFilter (fun x y => x.2.creator ≠ y.2.creator),
            a.2.creator ≠ b.2.creator
        · exact ⟨z, by rw [List.pwFilter_cons_of_pos hp]; exact List.mem_cons_of_mem _ hz⟩
        · exact ⟨z, by rw [List.pwFilter_cons_of_neg hp]; exact hz⟩
      · have hnil : l = [] := List.eq_nil_iff_forall_not_mem.mpr fun y hy => hl ⟨y, hy⟩
        subst hnil
        exact ⟨a, by simp⟩

omit [Fintype Validator] in
/-- The offered blocks above the horizon a bootstrap takes are offered
blocks, identified by their hash, above it. -/
theorem mem_bootWindow {s : State Validator BlockId Payload} {G : ℕ}
    {x : BlockId × Block Validator BlockId Payload}
    (h : x ∈ (if cfg.limit.isSome then [] else (s.offers.flatMap (·.2.2)).filter (fun e =>
      decide (G < e.2.round ∧ e.1 = cfg.idOf e.2)))) :
    x ∈ s.offers.flatMap (·.2.2) ∧ G < x.2.round ∧ x.1 = cfg.idOf x.2 := by
  split at h
  · exact absurd h List.not_mem_nil
  · obtain ⟨hx, hc⟩ := List.mem_filter.mp h
    simp only [decide_eq_true_eq] at hc
    exact ⟨hx, hc⟩

omit [Fintype Validator] in
/-- **A successful bootstrap**, at a round `G` above the node's top and
its horizon, with a certificate `c` the node can adopt there: the pruned
store takes the attested base, then flushes the offered blocks above `G`
and the pending ones at or above it; the top moves to `G` with no block
of the node's own there; the node takes the certified decisions it
lacks, and its next slot moves up to `c`'s height. -/
theorem tryBoot_some {s s' : State Validator BlockId Payload} {ads : List (ℕ × Option BlockId)}
    (h : tryBoot cfg s = some (s', ads)) :
    ∃ t G c, ∃ hb : s.store.base < G, s.top = some t ∧ t < G ∧ bootRound cfg s t = some G ∧
      certFor cfg s G = some c ∧
      let st₀ := (keptBase cfg (baseAt cfg s G)).foldl (fun st e => accept cfg st e.1 e.2)
        (s.store.prune G hb.le)
      let pend := (if cfg.limit.isSome then [] else (s.offers.flatMap (·.2.2)).filter (fun e =>
        decide (G < e.2.round ∧ e.1 = cfg.idOf e.2))) ++ s.pending.filter fun e => G ≤ e.2.round
      s'.store = (flush cfg (pend.length + 1) st₀ pend).1 ∧
      s'.pending = (flush cfg (pend.length + 1) st₀ pend).2 ∧
      s'.top = some G ∧ s'.own = none ∧ s'.lo = max s.lo c.height ∧
      s'.recovering = s.recovering ∧ s'.offers = [] ∧
      s'.requested = s.requested.filter (fun x => G ≤ x.2.2) ∧ s'.fired = {G} ∧
      ads = c.decisions.drop s.decided.length ∧ s'.decided = s.decided ++ ads ∧
      s'.certs = [] ∧ s'.props = s.props ∧ s'.lastProposed = s.lastProposed ∧
      s'.cert = (if s.certHeight < c.height then some c else s.cert) := by
  unfold tryBoot at h
  split at h
  · rename_i t G ht hG
    split at h
    · rename_i c hc
      split at h
      · rename_i hbase
        dsimp only at h
        rw [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        have hG' : bootRound cfg s t = some G := by rw [ht] at hG; exact hG
        have htG : t < G := by
          have := List.mem_filter.mp (List.max?_mem hG')
          exact (by simpa using this.2 : (t < G ∧ _) ∧ _).1.1
        exact ⟨t, G, c, hbase, ht, htG, hG', hc, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl,
          rfl, rfl, rfl, rfl, rfl, rfl⟩
      · cases h
    · cases h
  · cases h

omit [Fintype Validator] in
/-- **An adoptable certificate**, unfolded. -/
theorem validCert_iff {G : ℕ} {c : Cert Validator BlockId} :
    validCert cfg G c = true ↔ cfg.q ≤ c.signers.length ∧ c.signers.Nodup ∧
      c.decisions.map Prod.fst = List.range c.height ∧ G ≤ cfg.per * (c.height / cfg.m) := by
  simp [validCert, and_assoc]

omit [Fintype Validator] in
/-- The certificate a bootstrap adopts was offered, and is adoptable. -/
theorem certFor_valid {s : State Validator BlockId Payload} {G : ℕ} {c : Cert Validator BlockId}
    (h : certFor cfg s G = some c) : c ∈ s.certs ∧ validCert cfg G c = true :=
  ⟨List.mem_of_find?_eq_some h, List.find?_some h⟩

omit [Fintype Validator] in
/-- **A bootstrap raises the horizon** to its round. -/
theorem boot_base {s s' : State Validator BlockId Payload} {ads : List (ℕ × Option BlockId)}
    (h : tryBoot cfg s = some (s', ads)) : s.store.base < s'.store.base := by
  obtain ⟨t, G, c, hb, -, -, -, -, hst, -⟩ := tryBoot_some h
  rw [hst, flush_base, foldl_base]
  exact hb

omit [Fintype Validator] in
/-- **A bootstrap keeps the invariant**: the new horizon lies at the
node's new top, above its old top, and what it takes from the offers is
known. -/
theorem Inv.tryBoot {s s' : State Validator BlockId Payload}
    {K : Set (BlockId × Block Validator BlockId Payload)}
    {B : List (BlockId × Block Validator BlockId Payload)} {ads : List (ℕ × Option BlockId)}
    (hi : Inv cfg s K B) (h : tryBoot cfg s = some (s', ads)) : Inv cfg s' K B := by
  obtain ⟨t, G, c, hbase, ht, htG, -, -, hst, hpd, htop', -, -, -, hof, -⟩ := tryBoot_some h
  have hfo : ∀ x ∈ s.offers.flatMap (·.2.2), x.1 = cfg.idOf x.2 → x ∈ K := by
    intro x hx hid
    obtain ⟨o, ho, hxo⟩ := List.mem_flatMap.mp hx
    exact hi.offered o ho x hxo hid
  have hkp : ∀ j ∈ (s.store.prune G hbase.le).ids,
      (j, (s.store.prune G hbase.le).map.getD j (s.store.prune G hbase.le).junk) ∈ K := by
    intro j hj
    have hj' := Finset.mem_filter.mp hj
    have hraw := treeMap_getD_filter_of (t := s.store.map)
      (f := fun _ b => decide (G ≤ b.round)) (k := j) (fb := s.store.junk)
      (by simpa [Store.blk, lookup] using hj'.2)
    change (j, (s.store.map.filter _).getD j s.store.junk) ∈ K
    rw [hraw]
    exact hi.known j hj'.1
  have h₀ := foldl_accept_known (cfg := cfg) (keptBase cfg (baseAt cfg s G)) hkp
    (hi.valid.prune (hG := hbase.le)) fun x hx => by
      obtain ⟨hx, hc⟩ := List.mem_filter.mp (mem_keptBase hx)
      simp only [decide_eq_true_eq] at hc
      exact hfo x hx hc.2.1
  have hfl := flush_known (cfg := cfg) (K := K)
    (((if cfg.limit.isSome then [] else (s.offers.flatMap (·.2.2)).filter (fun x =>
      decide (G < x.2.round ∧ x.1 = cfg.idOf x.2))) ++
      s.pending.filter fun x => G ≤ x.2.round).length + 1) h₀.1 h₀.2.2 (pend :=
    (if cfg.limit.isSome then [] else (s.offers.flatMap (·.2.2)).filter (fun x =>
      decide (G < x.2.round ∧ x.1 = cfg.idOf x.2))) ++ s.pending.filter fun x => G ≤ x.2.round)
    (fun x hx => by
      rcases List.mem_append.mp hx with hx | hx
      · obtain ⟨hx, -, hc⟩ := mem_bootWindow hx
        exact hfo x hx hc
      · exact hi.pend x (List.mem_filter.mp hx).1)
  refine ⟨by rw [hst]; exact hfl.1, by rw [hpd]; exact hfl.2.1, Or.inr ⟨G, htop', ?_, ?_⟩,
    hi.good, hi.sub, by rw [hst]; exact hfl.2.2.2,
    by rw [hof]; exact fun o ho => absurd ho (by simp)⟩
  · rw [hst, hfl.2.2.1, h₀.2.1]; exact le_rfl
  · rcases hi.rounds with ⟨h0, -⟩ | ⟨t', ht', -, hB⟩
    · rw [ht] at h0; exact absurd h0 (by simp)
    · rw [ht, Option.some.injEq] at ht'
      subst ht'
      exact hB.mono htG.le

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

omit [Fintype Validator] in
/-- **Trying to bootstrap keeps the invariant**, and its own blocks are
the built ones. -/
theorem Inv.bootFrom {s : State Validator BlockId Payload}
    {K : Set (BlockId × Block Validator BlockId Payload)}
    {B : List (BlockId × Block Validator BlockId Payload)} (hi : Inv cfg s K B) :
    ∃ bs, Out bs (bootFrom cfg s).2 ∧
      Inv cfg (bootFrom cfg s).1 (K ∪ {x | x ∈ bs}) (B ++ bs) := by
  unfold Node.bootFrom
  split
  · rename_i s₂ ads hb
    obtain ⟨bs, ho, hi'⟩ := (hi.tryBoot hb).advance
    exact ⟨bs, by simpa using (out_quiet (quiet_commits ads)).append ho, hi'⟩
  · exact ⟨[], ⟨rfl, rfl⟩, by simpa using hi⟩

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
            refine ⟨rfl, rfl, fun j hj => absurd hj (Finset.notMem_empty j), fun blk _ => ?_⟩
            exact rowValid_congr (fun j hj => absurd hj (Finset.notMem_empty j)) h₂.2.2
          · rw [hB.1, List.nil_append, List.mem_singleton] at hx
            subst hx; simp
        rw [settle_of_idle rfl]
        obtain ⟨bs, ho, hi'⟩ := hi₀.advance
        refine ⟨e :: bs, ?_, ?_⟩
        · exact (out_built (cfg := cfg) [e]).append ho
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
      have hmem : (id, b) ∈ K' := Or.inr (by rw [hd]; exact List.mem_singleton_self _)
      have hfl := flush_known (cfg := cfg) (K := K') (s.pending.length + 1) (st := s.store)
        (pend := (id, b) :: s.pending) (fun j hj => hsub (hi.known j hj)) hi.valid
        (fun x hx => by
          rcases List.mem_cons.mp hx with rfl | hx
          · exact hmem
          · exact hsub (hi.pend x hx))
      dsimp only at hfl ⊢
      generalize flush cfg (s.pending.length + 1) s.store ((id, b) :: s.pending) = fl at hfl ⊢
      generalize charged cfg s id b ++ s.owner = ow
      generalize askable cfg { s with store := fl.1, pending := fl.2, owner := ow } id
        (missing { s with store := fl.1, pending := fl.2, owner := ow } id b) = miss
      let req := s.requested ++ miss.map fun x => (x.1, id, x.2)
      have hi₀ : ∀ a, Inv cfg
          { s with store := fl.1, pending := fl.2, owner := ow, requested := req, asked := a } K' B :=
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
  | restart =>
    simp only [Node.step]
    exact (⟨fun j hj => hsub (hi.known j hj), fun e he => by simp [State.recover] at he,
      hi.rounds, fun x hx => (hi.good x hx).mono hsub, fun x hx => hsub (hi.sub x hx),
      hi.valid, fun o ho => by simp [State.recover] at ho⟩ : Inv cfg s.recover K' B).settle_of
        subset_rfl [.requestBase] (by simp [Output.isQuiet])
  | baseRequest peer =>
    simp only [Node.step]
    exact hnil _ (by simp [Output.isQuiet])
  | proposal peer k ds =>
    simp only [Node.step]
    split
    · have h₁ : Inv cfg (record cfg s peer k ds) K' B := (hi.mono hsub).of_eq rfl rfl rfl rfl
      exact ⟨[], ⟨rfl, rfl⟩, by simpa using h₁⟩
    · exact hnil'
  | certOffer peer c =>
    simp only [Node.step]
    split
    · have h₁ : Inv cfg { s with certs := c :: s.certs } K' B :=
        (hi.mono hsub).of_eq rfl rfl rfl rfl
      exact h₁.bootFrom
    · exact hnil'
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
            · refine Or.inr ?_
              simp only [Set.mem_setOf_eq, delivered, List.flatMap_cons, List.flatMap_nil,
                List.append_nil, List.mem_filter, decide_eq_true_eq]
              exact ⟨hx, hid⟩
            · exact hsub (hi.offered o (List.mem_filter.mp ho).1 x hx hid)⟩
      exact hi₁.bootFrom
    · exact hnil'

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
  rounds := Or.inl ⟨rfl, rfl, rfl⟩
  good := fun _ h => absurd h (List.not_mem_nil)
  sub := fun _ h => absurd h (List.not_mem_nil)
  valid := fun _ h => absurd h (Finset.notMem_empty _)
  offered := fun _ h => absurd h (List.not_mem_nil)

end Node

end LeanDag
