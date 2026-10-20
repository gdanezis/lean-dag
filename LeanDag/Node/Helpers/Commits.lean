import LeanDag.Node.Helpers.Horizon
import LeanDag.Scheme.Loop.Proof
/-!
# A node's decisions are one call of the loop

A record `U` grounds what a node knows, `K` (`Ground`), when a known
block valid over blocks of `U` is the record's block, and a known block
at or below a round `U` reaches is the record's block read alike there.
Then every store along the node's run is a cut of `U` (`IsCut`): its
blocks are blocks of `U`, read as `U` reads them at the store's horizon.

On such a record the decisions a node output so far are nothing, or
`tryDecide` from slot `0` on a view of `U` whose blocks at or above the
store's horizon the store holds (`CommitInv`). A decision step appends
`tryDecide` from the next slot on the store, which reads as a larger
view agreeing with the store from its horizon up (`IsCut.extend`,
`ViewsAbove.of_store`); `Resume` folds the two into one call. Building,
collecting and accepting keep what the view's condition reads
(`CommitInv.keeps`).
-/

namespace LeanDag

namespace Node

open Scheme

variable {Validator BlockId Payload : Type} [Fintype Validator] [DecidableEq Validator]
variable [LinearOrder BlockId]
variable {cfg : Config Validator BlockId Payload}
variable {P : Validity Validator BlockId Payload} {H : Finset Validator}

/-- **A store is a cut of a record**: its blocks are the record's, read as
the record reads them at the store's horizon. -/
def IsCut (U : BlockRecord Validator BlockId Payload P H) (st : Store Validator BlockId Payload) :
    Prop :=
  ∀ j ∈ st.ids, j ∈ U.ids ∧ atBase st.base (U.block j) = st.blk j

/-- **A record reaches round `G`**: `G` is `0`, or the record has a block at
or above it. -/
def Spans (U : BlockRecord Validator BlockId Payload P H) (G : ℕ) : Prop :=
  G = 0 ∨ ∃ j ∈ U.ids, G ≤ (U.block j).round

/-- **A record grounds what a node knew**, at quorum `q`: a known block
valid at `q` over blocks of the record is the record's block, and a known
block at or below a round the record reaches is the record's block, read
alike at that round. -/
structure Ground (U : BlockRecord Validator BlockId Payload P H)
    (K : Set (BlockId × Block Validator BlockId Payload)) (q : ℕ) : Prop where
  real : ∀ x ∈ K, x.2.refs ⊆ U.ids → ValidAt q Clause.none U.block x.2 →
    x.1 ∈ U.ids ∧ U.block x.1 = x.2
  base : ∀ x ∈ K, ∀ G, x.2.round ≤ G → Spans U G →
    x.1 ∈ U.ids ∧ atBase G (U.block x.1) = atBase G x.2

variable {U : BlockRecord Validator BlockId Payload P H}
variable {K : Set (BlockId × Block Validator BlockId Payload)}

section Cut

variable {st : Store Validator BlockId Payload}

omit [Fintype Validator] in
theorem IsCut.round (hc : IsCut U st) {j : BlockId} (hj : j ∈ st.ids) :
    (U.block j).round = (st.blk j).round := by
  rw [← (hc j hj).2, atBase_round]

omit [Fintype Validator] in
theorem IsCut.creator (hc : IsCut U st) {j : BlockId} (hj : j ∈ st.ids) :
    (U.block j).creator = (st.blk j).creator := by
  rw [← (hc j hj).2, atBase_creator]

omit [Fintype Validator] in
/-- Above the horizon, a cut reads its blocks as the record does. -/
theorem IsCut.eq_of_lt (hc : IsCut U st) {j : BlockId} (hj : j ∈ st.ids)
    (hr : st.base < (st.blk j).round) : U.block j = st.blk j := by
  have h := (hc j hj).2
  rwa [atBase_of_lt (by rw [hc.round hj]; exact hr)] at h

omit [Fintype Validator] in
theorem IsCut.insert (hc : IsCut U st) {id : BlockId} {b : Block Validator BlockId Payload}
    {hnew hab hrefs hpred}
    (hb : id ∈ U.ids ∧ atBase st.base (U.block id) = atBase st.base b) :
    IsCut U (st.insert id b hnew hab hrefs hpred) := by
  intro j hj
  change j ∈ Insert.insert id st.ids at hj
  by_cases h : j = id
  · subst h
    refine ⟨hb.1, ?_⟩
    change atBase st.base (U.block j) = lookup (st.map.insert j b) st.junk st.base j
    simp only [lookup, Std.TreeMap.getD_insert_self]
    exact hb.2
  · have hj' := (Finset.mem_insert.mp hj).resolve_left h
    refine ⟨(hc j hj').1, ?_⟩
    change atBase st.base (U.block j) = lookup (st.map.insert id b) st.junk st.base j
    simp only [lookup, treeMap_getD_insert_ne (Ne.symm h)]
    exact (hc j hj').2

omit [Fintype Validator] in
/-- **Validity over the store is validity over the record**, at the
quorum: it reads only the rounds and authors of the references. -/
theorem validAt_of_cut (hc : IsCut U st) {q : ℕ} {id : BlockId}
    {b : Block Validator BlockId Payload} (hnew : id ∉ st.ids) (hrefs : b.refs ⊆ st.ids)
    (hv : rowValid q (Function.update st.blk id b) b) : ValidAt q Clause.none U.block b := by
  have hblk : ∀ j ∈ b.refs, Function.update st.blk id b j = st.blk j := fun j hj =>
    Function.update_of_ne (fun e => hnew (by rw [← e]; exact hrefs hj)) _ _
  refine ⟨fun j hj => ?_, fun h0 => ?_, trivial⟩
  · rw [hc.round (hrefs hj), ← hblk j hj]
    exact hv.predecessor j hj
  · have hcr : creators U.block b = creators (Function.update st.blk id b) b :=
      Finset.image_congr fun j hj => by rw [hblk j hj]; exact hc.creator (hrefs hj)
    rw [hcr]
    exact hv.quorum h0

omit [Fintype Validator] in
/-- **Accepting a known block keeps the store a cut.** -/
theorem IsCut.accept (hg : Ground U K cfg.q) (hc : IsCut U st) (hl : Spans U st.base)
    {id : BlockId} {b : Block Validator BlockId Payload} (hx : (id, b) ∈ K) :
    IsCut U (Node.accept cfg st id b) := by
  unfold Node.accept
  split
  · rename_i h
    refine hc.insert ?_
    by_cases hr : st.base < b.round
    · obtain ⟨h₁, h₂⟩ := hg.real _ hx (fun j hj => (hc j (h.2.2.1 hr hj)).1)
        (validAt_of_cut hc h.1 (h.2.2.1 hr) (h.2.2.2.2 hr))
      exact ⟨h₁, by rw [h₂]⟩
    · exact hg.base _ hx st.base (show b.round ≤ st.base by have := h.2.1; omega) hl
  · exact hc

omit [Fintype Validator] in
theorem IsCut.foldl (hg : Ground U K cfg.q) :
    ∀ (l : List (BlockId × Block Validator BlockId Payload)) {st : Store Validator BlockId Payload},
    IsCut U st → Spans U st.base → (∀ e ∈ l, e ∈ K) →
      IsCut U (l.foldl (fun s e => Node.accept cfg s e.1 e.2) st)
  | [], _, hc, _, _ => hc
  | e :: l, st, hc, hl, hK => by
    rw [List.foldl_cons]
    exact IsCut.foldl hg l (hc.accept hg hl (hK e List.mem_cons_self))
      (by rw [accept_base]; exact hl) fun x hx => hK x (List.mem_cons_of_mem _ hx)

omit [Fintype Validator] in
/-- **Flushing known blocks keeps the store a cut.** -/
theorem IsCut.flush (hg : Ground U K cfg.q) :
    ∀ (fuel : ℕ) {st : Store Validator BlockId Payload}
      (pend : List (BlockId × Block Validator BlockId Payload)),
    IsCut U st → Spans U st.base → (∀ e ∈ pend, e ∈ K) →
      IsCut U (Node.flush cfg fuel st pend).1
  | 0, _, _, hc, _, _ => hc
  | fuel + 1, st, pend, hc, hl, hK => by
    unfold Node.flush
    dsimp only
    split
    · exact hc
    · rw [List.partition_eq_filter_filter]
      have hc₁ := IsCut.foldl hg (pend.filter fun e => ready st e.2) hc hl
        fun e he => hK e (List.mem_filter.mp he).1
      refine IsCut.flush hg fuel _ hc₁ ?_ ?_
      · rw [foldl_base]; exact hl
      · intro e he; exact hK e (List.mem_filter.mp he).1

omit [Fintype Validator] in
theorem IsCut.prune (hc : IsCut U st) {G : ℕ} (hG : st.base ≤ G) : IsCut U (st.prune G hG) := by
  intro j hj
  obtain ⟨hj', hjG⟩ := mem_prune_ids.mp hj
  refine ⟨(hc j hj').1, ?_⟩
  change atBase G (U.block j) = lookup (st.map.filter fun _ b => decide (G ≤ b.round)) st.junk G j
  rw [lookup, treeMap_getD_filter_of (by simpa [Store.blk, lookup] using hjG),
    ← atBase_atBase hG (U.block j), (hc j hj').2]
  exact atBase_atBase hG _

omit [Fintype Validator] in
/-- **Reaching down from a cut**: a block at or above the horizon that a
block of the cut reaches in the record is in the cut. -/
theorem IsCut.down [P.Mechanised] (hc : IsCut U st) {i : BlockId}
    (hr : st.base ≤ (U.block i).round) :
    ∀ {j : BlockId}, j ∈ st.ids → ReachesFrom U.block j i → i ∈ st.ids := by
  intro j hj h
  induction h using Relation.ReflTransGen.head_induction_on with
  | refl => exact hj
  | @head a c hstep hrest ih =>
    have hstep : c ∈ (U.block a).refs := hstep
    have haU := (hc a hj).1
    have hac := U.causal.refs_round a haU c hstep
    have hxc := U.causal.round_le_of_reaches (U.causal.complete a haU c hstep) hrest
    have hlt : st.base < (st.blk a).round := by rw [← hc.round hj]; omega
    have hcs : c ∈ (st.blk a).refs := by rw [← hc.eq_of_lt hj hlt]; exact hstep
    exact ih (st.complete a hj c hcs)

omit [Fintype Validator] in
/-- **A view grown by a cut**: a view whose blocks at or above the horizon
the cut holds grows into one holding exactly the cut's blocks there. -/
theorem IsCut.extend [P.Mechanised] (hc : IsCut U st) (V : U.View)
    (hV : ∀ i ∈ V.ids, st.base ≤ (U.block i).round → i ∈ st.ids) :
    ∃ V' : U.View, V.ids ⊆ V'.ids ∧
      ∀ i, i ∈ V'.ids ∧ st.base ≤ (U.block i).round ↔ i ∈ st.ids := by
  have hsub : ∀ j ∈ st.ids, j ∈ U.ids := fun j hj => (hc j hj).1
  refine ⟨⟨V.ids ∪ st.ids.biUnion (history U), ?_, ?_⟩, Finset.subset_union_left, fun i => ?_⟩
  · exact Finset.union_subset V.subset_ids
      (Finset.biUnion_subset.mpr fun j hj => U.causal.history_subset_ids (hsub j hj))
  · intro i hi x hx
    rcases Finset.mem_union.mp hi with hi | hi
    · exact Finset.mem_union_left _ (V.complete i hi x hx)
    · obtain ⟨j, hj, hij⟩ := Finset.mem_biUnion.mp hi
      refine Finset.mem_union_right _ (Finset.mem_biUnion.mpr ⟨j, hj, ?_⟩)
      exact (mem_history_iff (hsub j hj)).mpr
        (Relation.ReflTransGen.tail ((mem_history_iff (hsub j hj)).mp hij) hx)
  · constructor
    · rintro ⟨hi, hr⟩
      rcases Finset.mem_union.mp hi with hi | hi
      · exact hV i hi hr
      · obtain ⟨j, hj, hij⟩ := Finset.mem_biUnion.mp hi
        exact hc.down hr hj ((mem_history_iff (hsub j hj)).mp hij)
    · intro hi
      refine ⟨Finset.mem_union_right _ (Finset.mem_biUnion.mpr ⟨i, hi,
        (mem_history_iff (hsub i hi)).mpr ReachesFrom.refl⟩), ?_⟩
      rw [hc.round hi]
      exact st.above i hi

end Cut

omit [Fintype Validator] in
/-- A started node's cut reaches its horizon, through a block at or above its top. -/
theorem IsCut.spans {s : State Validator BlockId Payload} (hc : IsCut U s.store)
    (hh : Held cfg s) : Spans U s.store.base := by
  rcases ht : s.top with _ | t
  · exact Or.inl (hh.low ht)
  · obtain ⟨o, hoi, hor⟩ := hh.top t ht
    exact Or.inr ⟨o, (hc o hoi).1, by rw [hc.round hoi]; exact (hh.le_top t ht).trans hor⟩

omit [Fintype Validator] in
theorem IsCut.tryBuild (hg : Ground U K cfg.q) {s s' : State Validator BlockId Payload}
    {out : List (Output Validator BlockId Payload)} (hc : IsCut U s.store) (hh : Held cfg s)
    (h : Node.tryBuild cfg s = some (s', out)) (hb : ∀ e ∈ persists out, e ∈ K) :
    IsCut U s'.store := by
  obtain ⟨r, id, b, hnew, hab, hrefs, hpred, hr, hbr, -, -, hv, hst, -, -, -, hout⟩ :=
    tryBuild_some h
  have hbase : s.store.base < b.round := by have := hh.le_top r hr; omega
  have hx : (id, b) ∈ K := hb _ (by rw [hout, persists_built]; exact List.mem_singleton_self _)
  obtain ⟨h₁, h₂⟩ := hg.real _ hx (fun j hj => (hc j (hrefs hbase hj)).1)
    (validAt_of_cut hc hnew (hrefs hbase) hv)
  rw [hst]
  exact hc.insert ⟨h₁, by rw [h₂]⟩

omit [Fintype Validator] in
/-- **Building known blocks keeps the store a cut.** -/
theorem IsCut.progress (hg : Ground U K cfg.q) :
    ∀ (fuel : ℕ) {s : State Validator BlockId Payload}, IsCut U s.store → Held cfg s →
      (∀ e ∈ persists (Node.progress cfg fuel s).2, e ∈ K) →
      IsCut U (Node.progress cfg fuel s).1.store
  | 0, _, hc, _, _ => hc
  | fuel + 1, s, hc, hh, hb => by
    rcases htb : Node.tryBuild cfg s with _ | ⟨s₁, out⟩
    · simp only [Node.progress, htb]
      exact hc
    · simp only [Node.progress, htb] at hb ⊢
      rw [persists_append] at hb
      exact IsCut.progress hg fuel (hc.tryBuild hg hh htb fun e he => hb e
        (List.mem_append_left _ he)) (hh.tryBuild htb) fun e he => hb e (List.mem_append_right _ he)

omit [Fintype Validator] in
theorem IsCut.collect {s : State Validator BlockId Payload} (hc : IsCut U s.store) :
    IsCut U (Node.collect cfg s).1.store := by
  unfold Node.collect
  split
  · dsimp only
    split
    · rename_i hG
      exact hc.prune hG.le
    · exact hc
  · exact hc

/-! ## The decisions -/

omit [Fintype Validator] in
theorem decidable_mono {R R' : ℕ} (h : R ≤ R') : decidable cfg R ≤ decidable cfg R' := by
  unfold decidable
  exact Nat.mul_le_mul_left _ (Nat.add_le_add_right (Nat.div_le_div_right h) 1)

omit [Fintype Validator] in
theorem commitsOf_append (a b : List (Output Validator BlockId Payload)) :
    commitsOf (a ++ b) = commitsOf a ++ commitsOf b :=
  List.filterMap_append

omit [Fintype Validator] in
theorem commitsOf_built (bs : List (BlockId × Block Validator BlockId Payload)) :
    commitsOf (built cfg bs) = [] := by
  induction bs with
  | nil => rfl
  | cons e bs ih =>
    simp only [built, List.flatMap_cons] at ih ⊢
    rw [commitsOf_append, ih]
    rfl

omit [Fintype Validator] in
theorem commitsOf_map (ds : List (ℕ × Option BlockId)) :
    commitsOf (ds.map fun e => (Output.commit e.1 e.2 : Output Validator BlockId Payload)) =
      ds := by
  induction ds with
  | nil => rfl
  | cons e ds ih => simp only [List.map_cons, commitsOf, List.filterMap_cons] at ih ⊢; rw [ih]

omit [Fintype Validator] in
theorem proposeAt_commits (s : State Validator BlockId Payload) :
    commitsOf (proposeAt cfg s).2 = [] := by
  obtain ⟨-, -, -, -, -, ho⟩ := proposeAt_eq (cfg := cfg) s
  generalize (proposeAt cfg s).2 = out at ho
  induction out with
  | nil => rfl
  | cons o out ih =>
    obtain ⟨k, h, rfl⟩ := ho o (List.mem_cons_self ..)
    exact ih fun o' h' => ho o' (List.mem_cons_of_mem _ h')

omit [Fintype Validator] in
theorem commitsOf_collect (s : State Validator BlockId Payload) :
    commitsOf (Node.collect cfg s).2 = [] :=
  List.filterMap_eq_nil_iff.mpr fun o ho => by
    rcases collect_out s o ho with ⟨_, rfl⟩ | ⟨_, rfl⟩ <;> rfl

omit [Fintype Validator] in
theorem collect_lo (s : State Validator BlockId Payload) : (Node.collect cfg s).1.lo = s.lo := by
  unfold Node.collect
  split
  · dsimp only
    split <;> rfl
  · rfl

omit [Fintype Validator] in
/-- Building outputs only built blocks. -/
theorem progress_built : ∀ (fuel : ℕ) (s : State Validator BlockId Payload),
    ∃ bs, (Node.progress cfg fuel s).2 = built cfg bs
  | 0, _ => ⟨[], rfl⟩
  | fuel + 1, s => by
    unfold Node.progress
    split
    · rename_i s₁ out h
      obtain ⟨r, id, b, -, -, -, -, -, -, -, -, -, -, -, -, -, hout⟩ := tryBuild_some h
      obtain ⟨bs, hbs⟩ := progress_built fuel s₁
      exact ⟨(id, b) :: bs, by simp only [hout, hbs, built, List.flatMap_cons,
        List.flatMap_nil, List.append_nil]⟩
    · exact ⟨[], rfl⟩

variable [P.Mechanised]

variable (cfg) in
/-- **The decisions so far are one call of the loop**: nothing, or
`tryDecide` from slot `0` on a view whose blocks at or above the horizon
the store holds, scanned no further than the store allows; and the next
slot is the one after them. -/
def CommitInv (U : BlockRecord Validator BlockId Payload P H) (s : State Validator BlockId Payload)
    (cs : List (ℕ × Option BlockId)) : Prop :=
  s.lo = cs.length ∧ (cs = [] ∨ ∃ (V : U.View) (N : ℕ),
    (∀ i ∈ V.ids, s.store.base ≤ (U.block i).round → i ∈ s.store.ids) ∧
    N + 1 ≤ decidable cfg s.store.topRound ∧
    cs = tryDecide (S := cfg.slots) cfg.p boundedSel U V 0 N)

variable {q f : ℕ} [P.Quorate q]

omit [Fintype Validator] in
/-- The invariant survives a change that keeps the store and the next slot. -/
theorem CommitInv.keeps {s s' : State Validator BlockId Payload} {cs : List (ℕ × Option BlockId)}
    (h : CommitInv cfg U s cs) (hlo : s'.lo = s.lo) (hk : Keeps s.store s'.store)
    (hc : IsCut U s.store) : CommitInv cfg U s' cs := by
  refine ⟨hlo.trans h.1, ?_⟩
  rcases h.2 with h0 | ⟨V, N, hV, hN, hcs⟩
  · exact Or.inl h0
  · refine Or.inr ⟨V, N, fun i hi hr => ?_, hN.trans (decidable_mono hk.2.2), hcs⟩
    have hi' := hV i hi (hk.1.trans hr)
    exact hk.2.1 i hi' (by rw [← hc.round hi']; exact hr)

/-- **A decision step keeps the invariant.** -/
theorem CommitInv.decideStep (hσ : cfg.σ = boundedSel) (ht : cfg.p.Tolerates H f q)
    {s : State Validator BlockId Payload} {cs : List (ℕ × Option BlockId)}
    (h : CommitInv cfg U s cs) (hc : IsCut U s.store) (hh : Held cfg s) :
    CommitInv cfg U (Node.decideStep cfg s).1 (cs ++ commitsOf (Node.decideStep cfg s).2) := by
  letI := cfg.slots
  have hw : 2 ≤ cfg.p.waveLength := by
    rcases ht.2.2 with ⟨-, hw, -⟩ | ⟨-, hw, -⟩ | ⟨-, hw, -⟩ | ⟨-, hw, -⟩ <;> omega
  -- the store decides as a view of `U` grown from any view the invariant allows
  have hgrow : ∀ V : U.View, (∀ i ∈ V.ids, s.store.base ≤ (U.block i).round → i ∈ s.store.ids) →
      ∃ V' : U.View, V.ids ⊆ V'.ids ∧
        (∀ i ∈ V'.ids, s.store.base ≤ (U.block i).round → i ∈ s.store.ids) ∧
        ∀ N, tryDecide cfg.p cfg.σ s.store.toRecord s.store.view s.lo N =
          tryDecide cfg.p boundedSel U V' s.lo N := by
    intro V hV
    obtain ⟨V', hVV, hiff⟩ := hc.extend V hV
    refine ⟨V', hVV, fun i hi hr => (hiff i).mp ⟨hi, hr⟩, fun N => ?_⟩
    rw [hσ]
    exact (ViewsAbove.of_store hiff fun i hi => (hc i hi).2).tryDecide_eq cfg.p hw N hh.horizon
  have hempty : ∀ i ∈ (⟨∅, Finset.empty_subset _,
      fun _ h => absurd h (Finset.notMem_empty _)⟩ : U.View).ids,
      s.store.base ≤ (U.block i).round → i ∈ s.store.ids :=
    fun i hi => absurd hi (Finset.notMem_empty i)
  unfold Node.decideStep
  dsimp only
  split
  · rename_i hlt
    rw [commitsOf_append, commitsOf_map, proposeAt_commits, List.append_nil]
    refine CommitInv.keeps (hlo := (proposeAt_keeps _).2.2.2.2.2.1)
      (hk := by rw [(proposeAt_keeps _).1]; exact Keeps.refl _) (hc := hc) ?_
    refine ⟨?_, Or.inr ?_⟩
    · change s.lo + _ = _
      rw [List.length_append, h.1]
    rcases h.2 with h0 | ⟨V, N, hV, hN, hcs⟩
    · subst h0
      obtain ⟨V', -, hV', hT⟩ := hgrow _ hempty
      have hlo : s.lo = 0 := h.1
      refine ⟨V', decidable cfg s.store.topRound - 1, hV',
        by change _ ≤ decidable cfg s.store.topRound; omega, ?_⟩
      rw [List.nil_append, hT, hlo]
    · obtain ⟨V', hVV, hV', hT⟩ := hgrow V hV
      refine ⟨V', decidable cfg s.store.topRound - 1, hV',
        by change _ ≤ decidable cfg s.store.topRound; omega, ?_⟩
      rw [hT, h.1, hcs]
      have := Loop.resume _ _ _ P q H f cfg.p boundedSel U V V' 0 N
        (decidable cfg s.store.topRound - 1) ht hVV (by omega)
      rw [Nat.zero_add] at this
      exact this
  · rw [proposeAt_commits, List.append_nil]
    exact CommitInv.keeps (hlo := (proposeAt_keeps _).2.2.2.2.2.1)
      (hk := by rw [(proposeAt_keeps _).1]; exact Keeps.refl _) (hc := hc) h

theorem CommitInv.advance (hg : Ground U K cfg.q) (hσ : cfg.σ = boundedSel)
    (ht : cfg.p.Tolerates H f q) {s : State Validator BlockId Payload}
    {cs : List (ℕ × Option BlockId)} (h : CommitInv cfg U s cs) (hc : IsCut U s.store)
    (hh : Held cfg s) (hp : ∀ e ∈ s.pending, e ∈ K)
    (hb : ∀ e ∈ persists (Node.advance cfg s).2, e ∈ K) :
    CommitInv cfg U (Node.advance cfg s).1 (cs ++ commitsOf (Node.advance cfg s).2) ∧
      IsCut U (Node.advance cfg s).1.store := by
  obtain ⟨bs, hbs⟩ := progress_built (cfg := cfg) (s.store.topRound + 2) s
  obtain ⟨hg₁, hlo₁⟩ := Grows.progress (cfg := cfg) (s.store.topRound + 2) s
  have hb₁ := progress_base (cfg := cfg) (s.store.topRound + 2) s
  have hp₁ := (progress_pending (cfg := cfg) (s.store.topRound + 2) s).1
  simp only [Node.advance] at hb ⊢
  rw [persists_append, persists_append] at hb
  have hc₁ := IsCut.progress hg _ hc hh fun e he => hb e
    (List.mem_append_left _ (List.mem_append_left _ he))
  have hh₁ := Held.progress (s.store.topRound + 2) hh
  generalize Node.progress cfg (s.store.topRound + 2) s = r at hbs hg₁ hlo₁ hb₁ hp₁ hc₁ hh₁ ⊢
  have h₁ : CommitInv cfg U r.1 cs := h.keeps hlo₁ (hg₁.keeps hb₁) hc
  have hd := decideStep_store (cfg := cfg) r.1
  have hdp := (decideStep_pending (cfg := cfg) r.1).1
  have h₂ := h₁.decideStep hσ ht hc₁ hh₁
  have hc₂ : IsCut U (Node.decideStep cfg r.1).1.store := by rw [hd]; exact hc₁
  have hh₂ := hh₁.decideStep
  obtain ⟨hh₃, hk₃⟩ := Held.collect hh₂
  have h₃ := h₂.keeps (collect_lo _) hk₃ hc₂
  have hc₃ := hc₂.collect (cfg := cfg)
  have hco := commitsOf_collect (cfg := cfg) (Node.decideStep cfg r.1).1
  have hcp := (collect_sub (cfg := cfg) (Node.decideStep cfg r.1).1).1
  generalize Node.collect cfg (Node.decideStep cfg r.1).1 = g at hh₃ h₃ hc₃ hco hcp ⊢
  have hgp : ∀ e ∈ g.1.pending, e ∈ K := fun e he => hp e (by
    have := hcp e he; rwa [hdp, hp₁] at this)
  have hc₄ := IsCut.flush hg (g.1.pending.length + 1) g.1.pending hc₃ (hc₃.spans hh₃) hgp
  have hk₄ := (Grows.flush (cfg := cfg) (g.1.pending.length + 1) g.1.store g.1.pending).keeps
    (flush_base _ _ _)
  refine ⟨?_, hc₄⟩
  have hcs : commitsOf (r.2 ++ (Node.decideStep cfg r.1).2 ++ g.2) =
      commitsOf (Node.decideStep cfg r.1).2 := by
    rw [commitsOf_append, commitsOf_append, hbs, commitsOf_built, hco, List.nil_append,
      List.append_nil]
  rw [hcs]
  exact h₃.keeps rfl hk₄ hc₃

/-- **Settling keeps the invariant, and the store a cut.** -/
theorem CommitInv.settle (hg : Ground U K cfg.q) (hσ : cfg.σ = boundedSel)
    (ht : cfg.p.Tolerates H f q) {s : State Validator BlockId Payload}
    {cs : List (ℕ × Option BlockId)} (h : CommitInv cfg U s cs) (hc : IsCut U s.store)
    (hh : Held cfg s) (hp : ∀ e ∈ s.pending, e ∈ K)
    (hb : ∀ e ∈ persists (Node.settle cfg s).2, e ∈ K) :
    CommitInv cfg U (Node.settle cfg s).1 (cs ++ commitsOf (Node.settle cfg s).2) ∧
      IsCut U (Node.settle cfg s).1.store := by
  rcases settle_cases (cfg := cfg) s with he | ⟨s₁, hj, he⟩ <;> rw [he] at hb ⊢
  · exact h.advance hg hσ ht hc hh hp hb
  · obtain ⟨-, -, -, -, -, -, hst, hpd, -, -, hlo, -⟩ := tryResume_some hj
    have h₁ : CommitInv cfg U s₁ cs := h.keeps hlo (by rw [hst]; exact Keeps.refl _) hc
    exact h₁.advance hg hσ ht (by rw [hst]; exact hc) (hh.tryResume hj) (by rw [hpd]; exact hp) hb

/-- **A step keeps the invariant, and the store a cut.** -/
theorem CommitInv.step (hg : Ground U K cfg.q) (hσ : cfg.σ = boundedSel)
    (ht : cfg.p.Tolerates H f q) {s : State Validator BlockId Payload}
    {cs : List (ℕ × Option BlockId)} (i : Input Validator BlockId Payload)
    (h : CommitInv cfg U s cs) (hc : IsCut U s.store) (hh : Held cfg s)
    (hp : ∀ e ∈ s.pending, e ∈ K) (hd : ∀ e ∈ delivered cfg [i], e ∈ K)
    (hb : ∀ e ∈ persists (Node.step cfg s i).2, e ∈ K) (hno : ¬ i.isOffer) :
    CommitInv cfg U (Node.step cfg s i).1 (cs ++ commitsOf (Node.step cfg s i).2) ∧
      IsCut U (Node.step cfg s i).1.store := by
  -- a step that settles a state `s₀`, after outputs without decisions
  have hset : ∀ (s₀ : State Validator BlockId Payload) (pre : List (Output Validator BlockId Payload)),
      CommitInv cfg U s₀ cs → IsCut U s₀.store → Held cfg s₀ → (∀ e ∈ s₀.pending, e ∈ K) →
      commitsOf pre = [] →
      Node.step cfg s i = ((Node.settle cfg s₀).1, pre ++ (Node.settle cfg s₀).2) →
      CommitInv cfg U (Node.step cfg s i).1 (cs ++ commitsOf (Node.step cfg s i).2) ∧
        IsCut U (Node.step cfg s i).1.store := by
    intro s₀ pre h₀ hc₀ hh₀ hp₀ hpre he
    rw [he] at hb ⊢
    rw [persists_append] at hb
    rw [commitsOf_append, hpre, List.nil_append]
    exact h₀.settle hg hσ ht hc₀ hh₀ hp₀ fun e he => hb e (List.mem_append_right _ he)
  have hsame : Node.step cfg s i = (s, []) →
      CommitInv cfg U (Node.step cfg s i).1 (cs ++ commitsOf (Node.step cfg s i).2) ∧
        IsCut U (Node.step cfg s i).1.store := by
    intro he; rw [he]; exact ⟨by simpa [commitsOf] using h, hc⟩
  cases i with
  | start =>
    by_cases h₁ : s.top = none ∧ cfg.Admissible
    · by_cases h₂ : cfg.idOf cfg.genesis ∉ s.store.ids ∧ s.store.base ≤ cfg.genesis.round ∧
          rowValid cfg.q (Function.update s.store.blk (cfg.idOf cfg.genesis) cfg.genesis)
            cfg.genesis
      · let st := s.store.insert _ _ h₂.1 h₂.2.1 (fun _ => Finset.empty_subset _)
          (fun _ j hj => absurd hj (Finset.notMem_empty j))
        have h0 := hh.low h₁.1
        have hx : (cfg.idOf cfg.genesis, cfg.genesis) ∈ K :=
          hb _ (by simp only [Node.step, dif_pos h₂, if_pos h₁]; simp [persists])
        have hcst : IsCut U st := hc.insert (hg.base _ hx s.store.base
          (by simp [Config.genesis]) (Or.inl h0))
        let gid := cfg.idOf cfg.genesis
        have hh₀ : Held cfg
            { { s with store := st, top := some 0, own := some gid } with
            owner := slotted cfg [(gid, cfg.genesis)] ++ s.owner, recovering := false } := by
          refine ⟨fun t ht => ⟨_, Finset.mem_insert_self _ _, ?_⟩, hh.horizon,
            fun ht => absurd ht (by simp), fun t _ => ?_, hh.junk⟩
          · simp only [Option.some.injEq] at ht
            simp only [st, Store.blk, Store.insert, lookup, Std.TreeMap.getD_insert_self,
              atBase_round]
            exact ht.ge
          · change s.store.base ≤ t
            omega
        have hk : Keeps s.store st := (Grows.insert s.store).keeps rfl
        exact hset { { s with store := st, top := some 0, own := some gid } with
            owner := slotted cfg [(gid, cfg.genesis)] ++ s.owner, recovering := false }
          (built cfg [(cfg.idOf cfg.genesis, cfg.genesis)]) (h.keeps rfl hk hc) hcst hh₀ hp
          (commitsOf_built _) (by simp only [Node.step, dif_pos h₂, if_pos h₁]; rfl)
      · exact hsame (by simp only [Node.step, dif_neg h₂, if_pos h₁])
    · exact hsame (by simp only [Node.step, if_neg h₁])
  | deliver id b =>
    by_cases hA : Admits cfg s id b
    · let s₁ := afterFlush (cfg := cfg) s id b
      let miss := askable cfg s₁ id (missing s₁ id b)
      have hx : (id, b) ∈ K := hd _ (by simp [delivered, hA.1])
      have hg₁ := Grows.flush (cfg := cfg) (s.pending.length + 1) s.store ((id, b) :: s.pending)
      have hb₁ := flush_base (cfg := cfg) (s.pending.length + 1) s.store ((id, b) :: s.pending)
      have hpend : ∀ e ∈ (id, b) :: s.pending, e ∈ K := fun e he => by
        rcases List.mem_cons.mp he with rfl | he
        · exact hx
        · exact hp e he
      have hc₁ : IsCut U s₁.store :=
        IsCut.flush hg _ _ hc (hc.spans hh) hpend
      let s₂ := { s₁ with requested := s₁.requested ++ miss.map fun (x : BlockId × ℕ) => (x.1, id, x.2) }
      refine hset { s₂ with asked := askedAfter (cfg := cfg) s b }
        ((if miss.isEmpty then [] else [.fetch b.creator s.store.base (miss.map Prod.fst)]) ++ askOut (cfg := cfg) s b)
        (h.keeps rfl (hg₁.keeps hb₁) hc) hc₁ (hh.grow hg₁ hb₁ rfl le_rfl)
        (fun e he => hpend e (flush_pending_sub _ _ _ e he))
        (by rw [commitsOf_append]; unfold askOut; split <;> split <;> rfl) (step_deliver hA)
    · have h' : ¬ (id = cfg.idOf b ∧ b.creator ≠ cfg.me ∧ s.store.base ≤ b.round ∧
          id ∉ s.store.ids ∧ id ∉ s.pending.map Prod.fst ∧ kept cfg s id b) := hA
      exact hsame (by simp only [Node.step, if_neg h'])
  | timer r =>
    exact hset { s with fired := insert r s.fired } [] h hc
      (hh.grow (Grows.refl _) rfl rfl le_rfl) hp rfl (by simp only [Node.step]; rfl)
  | fetchRequest peer G ids =>
    rw [show Node.step cfg s (.fetchRequest peer G ids) = (s, answer s peer G ids) from rfl]
    have : commitsOf (answer s peer G ids) = [] := by
      unfold answer commitsOf
      rw [List.filterMap_map]
      exact List.filterMap_eq_nil_iff.mpr fun _ _ => rfl
    rw [this, List.append_nil]
    exact ⟨h, hc⟩
  | restart =>
    exact hset s.recover [.requestBase] (h.keeps rfl (Keeps.refl _) hc) hc
      (hh.grow (Grows.refl _) rfl rfl le_rfl) (fun e he => by simp [State.recover] at he) rfl
      (by simp only [Node.step]; rfl)
  | baseOffer p G bs => exact absurd trivial hno
  | certOffer p c ds => exact absurd trivial hno
  | announced p c =>
    rcases announced_cases (cfg := cfg) s p c with ⟨-, -, he⟩ | he | he
    · exact hset { s with cert := some c, props := above (some c) s.props } []
        (h.keeps rfl (Keeps.refl _) hc) hc (hh.grow (Grows.refl _) rfl rfl le_rfl) hp rfl
        (by rw [he]; rfl)
    · rw [he]; exact ⟨by simpa [commitsOf] using h, hc⟩
    · exact hsame he
  | proposal p k kh =>
    rw [step_proposal]
    split
    · obtain ⟨n, hn⟩ := seek_eq (cfg := cfg) (record cfg s p k kh) k kh
      rw [commitsOf_requests fun o ho => Or.inl (seek_out (cfg := cfg) _ k kh o ho), hn,
        List.append_nil]
      exact ⟨h.keeps rfl (Keeps.refl _) hc, hc⟩
    · exact ⟨by simpa [commitsOf] using h, hc⟩
  | decisionRequest p lo =>
    rw [step_decisionRequest, commitsOf_requests fun o ho => Or.inr (by
      split at ho
      · exact ⟨p, serveFrom_out s p lo o ho⟩
      · simp at ho), List.append_nil]
    exact ⟨h, hc⟩
  | baseRequest peer =>
    rw [show Node.step cfg s (.baseRequest peer) = (s, .serveBase peer s.store.base
      s.store.window :: s.cert.toList.map (fun c => .serveCert peer c
        (s.decided.drop (s.lo - c.height)).reverse)) from rfl]
    refine ⟨?_, hc⟩
    cases hcert : s.cert <;> simpa [commitsOf] using h

/-- **A run keeps the invariant**, at a record grounding what the node knew. -/
theorem CommitInv.run (hg : Ground U K cfg.q) (hσ : cfg.σ = boundedSel)
    (ht : cfg.p.Tolerates H f q) :
    ∀ (is : List (Input Validator BlockId Payload)) {s : State Validator BlockId Payload}
      {cs : List (ℕ × Option BlockId)}, CommitInv cfg U s cs → IsCut U s.store → Held cfg s →
      (∀ e ∈ s.pending, e ∈ K) → (∀ e ∈ delivered cfg is, e ∈ K) →
      (∀ e ∈ persists (Node.run cfg s is).2, e ∈ K) →
      (∀ i ∈ is, ¬ i.isOffer) →
      CommitInv cfg U (Node.run cfg s is).1 (cs ++ commitsOf (Node.run cfg s is).2)
  | [], s, cs, h, _, _, _, _, _, _ => by simpa [Node.run, commitsOf] using h
  | i :: is, s, cs, h, hc, hh, hp, hd, hb, hno => by
    simp only [Node.run] at hb ⊢
    rw [persists_append] at hb
    rw [delivered_cons] at hd
    obtain ⟨h₁, hc₁⟩ := h.step hg hσ ht i hc hh hp (fun e he => hd e (List.mem_append_left _ he))
      (fun e he => hb e (List.mem_append_left _ he))
      (hno i List.mem_cons_self)
    have hp₁ : ∀ e ∈ (Node.step cfg s i).1.pending, e ∈ K := fun e he => by
      rcases (step_sub s i).1 e he with he | ⟨hi, hA⟩ | hi
      · exact hp e he
      · refine hd e (List.mem_append_left _ ?_)
        rw [hi]
        simp only [delivered, List.flatMap_cons, List.flatMap_nil, List.append_nil, if_pos hA.1]
        exact List.mem_singleton.mpr rfl
      · exact absurd hi (hno i List.mem_cons_self)
    have := CommitInv.run hg hσ ht is h₁ hc₁ (hh.step i) hp₁
      (fun e he => hd e (List.mem_append_right _ he))
      (fun e he => hb e (List.mem_append_right _ he)) fun x hx => hno x (List.mem_cons_of_mem _ hx)
    rw [commitsOf_append, ← List.append_assoc]
    exact this

end Node

end LeanDag
