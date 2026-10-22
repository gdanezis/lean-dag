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
      have hc₁ := IsCut.foldl hg (pend.filter fun e => ready cfg st e) hc hl
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
theorem tryDecide_length_le {P : Validity Validator BlockId Payload} {H : Finset Validator}
    {p : Scheme.Params} {σ : Scheme.VoteSel Validator BlockId Payload P H} [S : Slots Validator]
    {U : BlockRecord Validator BlockId Payload P H} {V : U.View} {lo N : ℕ} (hlo : lo ≤ N + 1) :
    (Scheme.tryDecide p σ U V lo N).length ≤ N + 1 - lo := by
  rw [Scheme.tryDecide_eq hlo, List.length_map]
  exact (List.takeWhile_sublist _).length_le.trans (by simp)

omit [Fintype Validator] in
theorem tryBuild_recovering {s s' : State Validator BlockId Payload}
    {out : List (Output Validator BlockId Payload)} (h : tryBuild cfg s = some (s', out)) :
    s'.recovering = true → s.recovering = true := by
  unfold tryBuild at h
  split at h
  · dsimp only at h
    split at h
    · split at h
      · rw [Option.some.injEq, Prod.mk.injEq] at h; rw [← h.1]
        intro hr; simp only [Bool.and_eq_true] at hr; exact hr.1
      · cases h
    · cases h
  · cases h

omit [Fintype Validator] in
theorem progress_recovering : ∀ (fuel : ℕ) (s : State Validator BlockId Payload),
    (Node.progress cfg fuel s).1.recovering = true → s.recovering = true
  | 0, _ => id
  | fuel + 1, s => by
    unfold Node.progress
    split
    · rename_i s₁ out hb
      exact fun h => tryBuild_recovering hb (progress_recovering fuel s₁ h)
    · exact id

omit [Fintype Validator] in
theorem collect_recovering (s : State Validator BlockId Payload) :
    (Node.collect cfg s).1.recovering = s.recovering := by
  unfold Node.collect
  split
  · dsimp only; split <;> rfl
  · rfl

omit [Fintype Validator] [DecidableEq Validator] in
/-- A record that reaches a round reaches every round below it. -/
theorem Spans.mono {G G' : ℕ} (h : Spans U G) (hle : G' ≤ G) : Spans U G' := by
  rcases h with rfl | ⟨j, hj, hjr⟩
  · exact Or.inl (by omega)
  · exact Or.inr ⟨j, hj, hle.trans hjr⟩

variable (cfg U) in
/-- **The record reaches the round of every slot the node decided.** -/
def SpansDecided (s : State Validator BlockId Payload) : Prop :=
  ∀ k < s.lo, Spans U (cfg.slots.slotRound k)

omit [Fintype Validator] in
/-- A slot among those at rounds at most `R` lies at a round at most `R`. -/
theorem slotRound_le_of_decidable {k R : ℕ} (hk : k < decidable cfg R) :
    cfg.slots.slotRound k ≤ R := by
  change cfg.per * (k / cfg.m) ≤ R
  unfold decidable at hk
  have h₁ : k / cfg.m ≤ R / cfg.per := by
    have := (Nat.div_lt_iff_lt_mul cfg.m_pos).mpr (by rw [Nat.mul_comm]; exact hk)
    omega
  exact (Nat.mul_le_mul_left _ h₁).trans (Nat.mul_div_le _ _)

omit [Fintype Validator] in
/-- A slot at a round the store's top reaches is reached by the record. -/
theorem IsCut.spans_slot {st : Store Validator BlockId Payload} (hc : IsCut U st) {k : ℕ}
    (hk : k < decidable cfg st.topRound) : Spans U (cfg.slots.slotRound k) := by
  have hkr : cfg.slots.slotRound k ≤ st.topRound := slotRound_le_of_decidable hk
  rcases st.ids.eq_empty_or_nonempty with he | ⟨j, hj⟩
  · have : st.topRound = 0 := by unfold Store.topRound; rw [he]; rfl
    exact Or.inl (by omega)
  · obtain ⟨i, hi, hmax⟩ := Finset.exists_max_image st.ids (fun i => (st.blk i).round) ⟨j, hj⟩
    have htop : st.topRound = (st.blk i).round :=
      le_antisymm (Finset.sup_le fun i' hi' => hmax i' hi')
        (Finset.le_sup (f := fun i => (st.blk i).round) hi)
    exact Or.inr ⟨i, (hc i hi).1, by rw [hc.round hi, ← htop]; exact hkr⟩

omit [Fintype Validator] in
/-- A pass decides only slots at rounds its store reaches. -/
theorem decideStep_lo_le (s : State Validator BlockId Payload) :
    (Node.decideStep cfg s).1.lo ≤ max s.lo (decidable cfg s.store.topRound) := by
  unfold Node.decideStep
  dsimp only
  split
  · rename_i hlt
    generalize hds : Scheme.tryDecide (S := cfg.slots) cfg.p cfg.σ s.store.toRecord
      s.store.view s.lo (decidable cfg s.store.topRound - 1) = ds
    have hlen : ds.length ≤ decidable cfg s.store.topRound - 1 + 1 - s.lo := by
      rw [← hds]; exact tryDecide_length_le (S := cfg.slots) (by omega)
    rw [(proposeAt_keeps _).2.2.2.2.2.1]
    change s.lo + ds.length ≤ _
    omega
  · rw [(proposeAt_keeps _).2.2.2.2.2.1]; exact le_max_left _ _

omit [Fintype Validator] in
/-- **Deciding keeps the record reaching the decided slots**: a pass
decides slots at rounds its store, a cut, reaches. -/
theorem SpansDecided.decideStep {s : State Validator BlockId Payload} (h : SpansDecided cfg U s)
    (hc : IsCut U s.store) : SpansDecided cfg U (Node.decideStep cfg s).1 := by
  intro k hk
  by_cases hks : k < s.lo
  · exact h k hks
  · have := decideStep_lo_le (cfg := cfg) s
    exact hc.spans_slot (by omega)

omit [Fintype Validator] in
/-- **A started node's cut reaches its horizon**, through a block at or
above its top, or, while it recovers, the round of a slot it decided,
which the record reaches. -/
theorem IsCut.spans {s : State Validator BlockId Payload} (hc : IsCut U s.store)
    (hh : Held cfg s) (hr : s.recovering = true → SpansDecided cfg U s) : Spans U s.store.base := by
  rcases ht : s.top with _ | t
  · exact Or.inl (hh.low ht)
  · rcases hh.top t ht with ⟨o, hoi, hor⟩ | ⟨hrec, k, hk, hkt⟩
    · exact Or.inr ⟨o, (hc o hoi).1, by rw [hc.round hoi]; exact (hh.le_top t ht).trans hor⟩
    · exact (hr hrec k hk).mono ((hh.le_top t ht).trans hkt)

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

omit [Fintype Validator] [P.Mechanised] in
/-- **A pass from a cut keeps the store a cut.** -/
theorem IsCut.advanceStore (hg : Ground U K cfg.q) {s : State Validator BlockId Payload}
    (hc : IsCut U s.store) (hh : Held cfg s) (hr : s.recovering = true → SpansDecided cfg U s)
    (hp : ∀ e ∈ s.pending, e ∈ K)
    (hb : ∀ e ∈ persists (Node.advance cfg s).2, e ∈ K) : IsCut U (Node.advance cfg s).1.store ∧
      ((Node.advance cfg s).1.recovering = true → SpansDecided cfg U (Node.advance cfg s).1) := by
  have hp₁ := (progress_pending (cfg := cfg) (s.store.topRound + 2) s).1
  simp only [Node.advance] at hb ⊢
  rw [persists_append, persists_append] at hb
  have hc₁ := IsCut.progress hg _ hc hh fun e he => hb e
    (List.mem_append_left _ (List.mem_append_left _ he))
  have hh₁ := Held.progress (s.store.topRound + 2) hh
  have hlo₁ := (Grows.progress (cfg := cfg) (s.store.topRound + 2) s).2
  have hrc₁ := progress_recovering (cfg := cfg) (s.store.topRound + 2) s
  generalize Node.progress cfg (s.store.topRound + 2) s = r at hp₁ hc₁ hh₁ hlo₁ hrc₁ ⊢
  have hr₁ : r.1.recovering = true → SpansDecided cfg U r.1 := fun h k hk =>
    hr (hrc₁ h) k (hlo₁ ▸ hk)
  have hd := decideStep_store (cfg := cfg) r.1
  have hdp := (decideStep_pending (cfg := cfg) r.1).1
  have hc₂ : IsCut U (Node.decideStep cfg r.1).1.store := by rw [hd]; exact hc₁
  have hr₂ : (Node.decideStep cfg r.1).1.recovering = true →
      SpansDecided cfg U (Node.decideStep cfg r.1).1 := fun h =>
    SpansDecided.decideStep (hr₁ (by rw [← decideStep_recovering]; exact h)) hc₁
  obtain ⟨hh₃, -⟩ := Held.collect hh₁.decideStep
  have hc₃ := hc₂.collect (cfg := cfg)
  have hcp := (collect_sub (cfg := cfg) (Node.decideStep cfg r.1).1).1
  have hr₃ : (Node.collect cfg (Node.decideStep cfg r.1).1).1.recovering = true →
      SpansDecided cfg U (Node.collect cfg (Node.decideStep cfg r.1).1).1 := fun h k hk =>
    hr₂ (by rw [← collect_recovering]; exact h) k (by rw [← collect_lo]; exact hk)
  generalize Node.collect cfg (Node.decideStep cfg r.1).1 = g at hh₃ hc₃ hcp hr₃ ⊢
  have hgp : ∀ e ∈ g.1.pending, e ∈ K := fun e he => hp e (by
    have := hcp e he; rwa [hdp, hp₁] at this)
  exact ⟨IsCut.flush hg (g.1.pending.length + 1) g.1.pending hc₃ (hc₃.spans hh₃ hr₃) hgp, hr₃⟩

omit [Fintype Validator] in
/-- The decisions under the invariant number at most the slots at rounds
the store's top reaches. -/
theorem CommitInv.lo_le {s : State Validator BlockId Payload} {cs : List (ℕ × Option BlockId)}
    (h : CommitInv cfg U s cs) : s.lo = 0 ∨ s.lo ≤ decidable cfg s.store.topRound := by
  rcases h.2 with h0 | ⟨V, N, -, hN, hcs⟩
  · left; rw [h.1, h0]; rfl
  · right
    have hlen : cs.length ≤ N + 1 := by
      rw [hcs]
      have := tryDecide_length_le (S := cfg.slots) (p := cfg.p) (σ := boundedSel) (U := U)
        (V := V) (lo := 0) (N := N) (by omega)
      omega
    rw [h.1]; omega

omit [Fintype Validator] in
/-- **Under the invariant the record reaches each decided slot**, the
decisions reading the store. -/
theorem CommitInv.reaches {s : State Validator BlockId Payload} {cs : List (ℕ × Option BlockId)}
    (h : CommitInv cfg U s cs) (hc : IsCut U s.store) : SpansDecided cfg U s := fun k hk => by
  rcases h.lo_le with h0 | hle
  · omega
  · exact hc.spans_slot (by omega)

omit [Fintype Validator] in
/-- **Under the invariant the store's top round reaches the node's top.** -/
theorem CommitInv.top_le {s : State Validator BlockId Payload} {cs : List (ℕ × Option BlockId)}
    (h : CommitInv cfg U s cs) (hh : Held cfg s) : ∀ t, s.top = some t → t ≤ s.store.topRound := by
  intro t ht
  rcases hh.top t ht with ⟨o, hoi, hor⟩ | ⟨-, k, hk, hkt⟩
  · exact hor.trans (Finset.le_sup (f := fun i => (s.store.blk i).round) hoi)
  · rcases h.lo_le with h0 | hle
    · omega
    · exact hkt.trans (slotRound_le_of_decidable (by omega))

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
  have h₃ := h₂.keeps (collect_lo _) (hk₃ (h₂.top_le hh₂)) hc₂
  have hc₃ := hc₂.collect (cfg := cfg)
  have hco := commitsOf_collect (cfg := cfg) (Node.decideStep cfg r.1).1
  have hcp := (collect_sub (cfg := cfg) (Node.decideStep cfg r.1).1).1
  generalize Node.collect cfg (Node.decideStep cfg r.1).1 = g at hh₃ h₃ hc₃ hco hcp ⊢
  have hgp : ∀ e ∈ g.1.pending, e ∈ K := fun e he => hp e (by
    have := hcp e he; rwa [hdp, hp₁] at this)
  have hc₄ := IsCut.flush hg (g.1.pending.length + 1) g.1.pending hc₃
    (hc₃.spans hh₃ fun _ => h₃.reaches hc₃) hgp
  have hk₄ := (Grows.flush (cfg := cfg) (g.1.pending.length + 1) g.1.store g.1.pending).keeps
    (flush_base _ _ _)
  refine ⟨?_, hc₄⟩
  have hcs : commitsOf (r.2 ++ (Node.decideStep cfg r.1).2 ++ g.2) =
      commitsOf (Node.decideStep cfg r.1).2 := by
    rw [commitsOf_append, commitsOf_append, hbs, commitsOf_built, hco, List.nil_append,
      List.append_nil]
  rw [hcs]
  exact h₃.keeps rfl hk₄ hc₃

/-- **The passes keep the invariant, and the store a cut.** -/
theorem CommitInv.quiesce (hg : Ground U K cfg.q) (hσ : cfg.σ = boundedSel)
    (ht : cfg.p.Tolerates H f q) : ∀ (n : ℕ) {s : State Validator BlockId Payload}
    {cs : List (ℕ × Option BlockId)}, CommitInv cfg U s cs → IsCut U s.store → Held cfg s →
    (∀ e ∈ s.pending, e ∈ K) → (∀ e ∈ persists (Node.quiesce cfg n s).2, e ∈ K) →
    CommitInv cfg U (Node.quiesce cfg n s).1 (cs ++ commitsOf (Node.quiesce cfg n s).2) ∧
      IsCut U (Node.quiesce cfg n s).1.store
  | 0, s, cs, h, hc, _, _, _ => by
    simp only [Node.quiesce, commitsOf, List.filterMap_nil, List.append_nil]; exact ⟨h, hc⟩
  | n + 1, s, cs, h, hc, hh, hp, hb => by
    rcases quiesce_succ_cases (cfg := cfg) n s with he | he <;> rw [he] at hb ⊢
    · exact h.advance hg hσ ht hc hh hp hb
    · rw [persists_append] at hb
      obtain ⟨h₁, hc₁⟩ := h.advance hg hσ ht hc hh hp fun e he => hb e (List.mem_append_left _ he)
      have := CommitInv.quiesce hg hσ ht n h₁ hc₁ hh.advance
        (fun e he => hp e ((advance_sub (cfg := cfg) s).1 e he))
        fun e he => hb e (List.mem_append_right _ he)
      rw [commitsOf_append, ← List.append_assoc]; exact this

/-- **Settling keeps the invariant, and the store a cut.** -/
theorem CommitInv.settle (hg : Ground U K cfg.q) (hσ : cfg.σ = boundedSel)
    (ht : cfg.p.Tolerates H f q) {s : State Validator BlockId Payload}
    {cs : List (ℕ × Option BlockId)} (h : CommitInv cfg U s cs) (hc : IsCut U s.store)
    (hh : Held cfg s) (hp : ∀ e ∈ s.pending, e ∈ K)
    (hb : ∀ e ∈ persists (Node.settle cfg s).2, e ∈ K) :
    CommitInv cfg U (Node.settle cfg s).1 (cs ++ commitsOf (Node.settle cfg s).2) ∧
      IsCut U (Node.settle cfg s).1.store := by
  rcases settle_cases (cfg := cfg) s with he | ⟨s₁, hj, he⟩ <;> rw [he] at hb ⊢
  · exact CommitInv.quiesce hg hσ ht _ h hc hh hp hb
  · obtain ⟨-, -, -, -, -, hst, hpd, -, -, hlo, -⟩ := tryResume_some hj
    have h₁ : CommitInv cfg U s₁ cs := h.keeps hlo (by rw [hst]; exact Keeps.refl _) hc
    exact CommitInv.quiesce hg hσ ht _ h₁ (by rw [hst]; exact hc) (hh.tryResume hj)
      (by rw [hpd]; exact hp) hb

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
            recovering := false } := by
          refine ⟨fun t ht => Or.inl ⟨_, Finset.mem_insert_self _ _, ?_⟩, hh.horizon,
            fun ht => absurd ht (by simp), fun t _ => ?_, hh.junk⟩
          · simp only [Option.some.injEq] at ht
            simp only [st, Store.blk, Store.insert, lookup, Std.TreeMap.getD_insert_self,
              atBase_round]
            exact ht.ge
          · change s.store.base ≤ t
            omega
        have hk : Keeps s.store st := (Grows.insert s.store).keeps rfl
        exact hset { { s with store := st, top := some 0, own := some gid } with
            recovering := false }
          (built cfg [(cfg.idOf cfg.genesis, cfg.genesis)]) (h.keeps rfl hk hc) hcst hh₀ hp
          (commitsOf_built _) (by simp only [Node.step, dif_pos h₂, if_pos h₁]; rfl)
      · exact hsame (by simp only [Node.step, dif_neg h₂, if_pos h₁])
    · exact hsame (by simp only [Node.step, if_neg h₁])
  | deliver id b =>
    by_cases hA : Admits cfg s id b
    · let s₁ := afterFlush (cfg := cfg) s id b
      let miss := missing s₁ id b
      have hx : (id, b) ∈ K := hd _ (by simp [delivered, hA.1])
      have hg₁ := Grows.flush (cfg := cfg) (s.pending.length + 1) s.store ((id, b) :: s.pending)
      have hb₁ := flush_base (cfg := cfg) (s.pending.length + 1) s.store ((id, b) :: s.pending)
      have hpend : ∀ e ∈ (id, b) :: s.pending, e ∈ K := fun e he => by
        rcases List.mem_cons.mp he with rfl | he
        · exact hx
        · exact hp e he
      have hc₁ : IsCut U s₁.store :=
        IsCut.flush hg _ _ hc (hc.spans hh fun _ => h.reaches hc) hpend
      let s₂ := { s₁ with requested := s₁.requested ++ miss.map fun (x : BlockId × ℕ) => (x.1, id, x.2) }
      refine hset { s₂ with asked := askedAfter (cfg := cfg) s b }
        (evidence s id b ++
          (if miss.isEmpty then [] else [.fetch b.creator s.store.base (miss.map Prod.fst)]) ++
          askOut (cfg := cfg) s b)
        (h.keeps rfl (hg₁.keeps hb₁) hc) hc₁ (hh.grow hg₁ hb₁ rfl le_rfl (fun hr => hr))
        (fun e he => hpend e (flush_pending_sub _ _ _ e he))
        (by
          rw [commitsOf_append, commitsOf_append, commitsOf_evidence]; unfold askOut
          split <;> split <;> rfl) (step_deliver hA)
    · rcases step_deliver_not (cfg := cfg) hA with he | ⟨a, he⟩
      · exact hsame he
      · rw [he]
        have h₁ := h.keeps (s' := { s with asked := a, recovering := true }) rfl (Keeps.refl _) hc
        exact ⟨by simpa [commitsOf] using h₁, hc⟩
  | timer r =>
    exact hset (timerState cfg s r) (timerOut cfg s r) h hc
      (hh.grow (Grows.refl _) rfl rfl le_rfl (timerState_recovering r)) hp (commitsOf_timerOut s r)
      (step_timer_eq s r)
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
  | baseOffer p G => exact absurd trivial hno
  | certOffer p c ds => exact absurd trivial hno
  | announced p c =>
    rcases announced_cases (cfg := cfg) s p c with ⟨-, -, he⟩ | he | he
    · exact hset { s with cert := some c, props := above (some c) s.props } []
        (h.keeps rfl (Keeps.refl _) hc) hc (hh.grow (Grows.refl _) rfl rfl le_rfl) hp rfl
        (by rw [he]; rfl)
    · rw [he]; exact ⟨by simpa [commitsOf] using h, hc⟩
    · exact hsame he
  | proposal p k kh =>
    by_cases hpm : p ≠ cfg.me
    · exact hset (record cfg s p k kh) ([] : List (Output Validator BlockId Payload))
        (by exact h.keeps rfl (Keeps.refl _) hc) (by exact hc)
        (by exact hh.grow (Grows.refl _) rfl rfl le_rfl) (by exact hp)
        rfl
        (by rw [step_proposal, if_pos hpm])
    · rw [step_proposal, if_neg hpm]; exact ⟨by simpa [commitsOf] using h, hc⟩
  | decisionRequest p lo =>
    rw [step_decisionRequest, commitsOf_requests fun o ho => Or.inr (by
      split at ho
      · exact ⟨p, serveFrom_out s p lo o ho⟩
      · simp at ho), List.append_nil]
    exact ⟨h, hc⟩
  | baseRequest peer =>
    rw [commitsOf_baseRequest, List.append_nil, step_baseRequest_state]
    exact ⟨h, hc⟩

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
