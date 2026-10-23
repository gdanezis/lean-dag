import LeanDag.Node.Helpers.Held
import LeanDag.Node.Helpers.Decided
import LeanDag.Scheme.Loop.Proof
/-!
# A node's decisions are one call of the loop

A record `U` grounds what a node knows, `K` (`Ground`), when a known
block valid over blocks of `U` is the record's block. Then every disk
along the node's run is a cut of `U` (`IsCut`): its blocks are blocks of
`U`, read as `U` reads them.

On such a record the decisions a node output so far are nothing, or
`tryDecide` from slot `0` on a view of `U` whose blocks the disk holds
(`CommitInv`). A decision step appends `tryDecide` from the next slot on
the disk, which reads as the view of `U` holding exactly the disk's
blocks (`IsCut.extend`, `ViewsAbove.of_store`), and the scheme's
`Loop.resume` folds the two calls into one. Building and accepting keep
what the view's condition reads (`CommitInv.keeps`).
-/

namespace LeanDag

namespace Node

open Scheme

variable {Validator BlockId Payload : Type} [Fintype Validator] [DecidableEq Validator]
variable [LinearOrder BlockId]
variable {cfg : Config Validator BlockId Payload}
variable {P : Validity Validator BlockId Payload} {H : Finset Validator}

/-- **A store is a cut of a record**: its blocks are the record's, read as
the record reads them. -/
def IsCut (U : BlockRecord Validator BlockId Payload P H) (st : Store Validator BlockId Payload) :
    Prop :=
  ∀ j ∈ st.ids, j ∈ U.ids ∧ U.block j = st.blk j

/-- **A record grounds what a node knew**, at quorum `q`: a known block
valid at `q` over blocks of the record is the record's block. -/
structure Ground (U : BlockRecord Validator BlockId Payload P H)
    (K : Set (BlockId × Block Validator BlockId Payload)) (q : ℕ) : Prop where
  real : ∀ x ∈ K, x.2.refs ⊆ U.ids → ValidAt q Clause.none U.block x.2 →
    x.1 ∈ U.ids ∧ U.block x.1 = x.2

variable {U : BlockRecord Validator BlockId Payload P H}
variable {K : Set (BlockId × Block Validator BlockId Payload)}

section Cut

variable {st : Store Validator BlockId Payload}

omit [Fintype Validator] [DecidableEq Validator] in
/-- A cut reads its blocks as the record does. -/
theorem IsCut.eq (hc : IsCut U st) {j : BlockId} (hj : j ∈ st.ids) : U.block j = st.blk j :=
  (hc j hj).2

omit [Fintype Validator] [DecidableEq Validator] in
theorem IsCut.round (hc : IsCut U st) {j : BlockId} (hj : j ∈ st.ids) :
    (U.block j).round = (st.blk j).round := by
  rw [hc.eq hj]

omit [Fintype Validator] [DecidableEq Validator] in
theorem IsCut.creator (hc : IsCut U st) {j : BlockId} (hj : j ∈ st.ids) :
    (U.block j).creator = (st.blk j).creator := by
  rw [hc.eq hj]

omit [Fintype Validator] [DecidableEq Validator] in
theorem IsCut.insert (hc : IsCut U st) {id : BlockId} {b : Block Validator BlockId Payload}
    {hnew hrefs hpred} (hb : id ∈ U.ids ∧ U.block id = b) :
    IsCut U (st.insert id b hnew hrefs hpred) := by
  intro j hj
  rw [Store.insert_ids] at hj
  by_cases h : j = id
  · subst h
    refine ⟨hb.1, ?_⟩
    change U.block j = (st.map.insert j b).getD j st.junk
    simp only [Std.TreeMap.getD_insert_self]
    exact hb.2
  · have hj' := (Finset.mem_insert.mp hj).resolve_left h
    refine ⟨(hc j hj').1, ?_⟩
    change U.block j = (st.map.insert id b).getD j st.junk
    rw [treeMap_getD_insert_ne (Ne.symm h)]
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
theorem IsCut.accept (hg : Ground U K cfg.q) (hc : IsCut U st)
    {id : BlockId} {b : Block Validator BlockId Payload} (hx : (id, b) ∈ K) :
    IsCut U (acceptOn cfg st id b) := by
  unfold acceptOn
  split
  · rename_i h
    obtain ⟨h₁, h₂⟩ := hg.real _ hx (fun j hj => (hc j (h.2.1 hj)).1)
      (validAt_of_cut hc h.1 h.2.1 h.2.2.2)
    exact hc.insert ⟨h₁, h₂⟩
  · exact hc

omit [Fintype Validator] in
theorem IsCut.foldl (hg : Ground U K cfg.q) :
    ∀ (l : List (BlockId × Block Validator BlockId Payload)) {st : Store Validator BlockId Payload},
    IsCut U st → (∀ e ∈ l, e ∈ K) →
      IsCut U (l.foldl (fun s e => acceptOn cfg s e.1 e.2) st)
  | [], _, hc, _ => hc
  | e :: l, st, hc, hK => by
    rw [List.foldl_cons]
    exact IsCut.foldl hg l (hc.accept hg (hK e List.mem_cons_self))
      fun x hx => hK x (List.mem_cons_of_mem _ hx)

omit [Fintype Validator] in
/-- **Flushing known blocks keeps the store a cut.** -/
theorem IsCut.flush (hg : Ground U K cfg.q) :
    ∀ (fuel : ℕ) {st : Store Validator BlockId Payload}
      (pend : List (BlockId × Block Validator BlockId Payload)),
    IsCut U st → (∀ e ∈ pend, e ∈ K) → IsCut U (flushOn cfg fuel st pend).1
  | 0, _, _, hc, _ => hc
  | fuel + 1, st, pend, hc, hK => by
    unfold flushOn
    dsimp only
    split
    · exact hc
    · rw [List.partition_eq_filter_filter]
      have hc₁ := IsCut.foldl hg (pend.filter fun e => readyOn cfg st e) hc
        fun e he => hK e (List.mem_filter.mp he).1
      exact IsCut.flush hg fuel _ hc₁ fun e he => hK e (List.mem_filter.mp he).1

omit [Fintype Validator] [DecidableEq Validator] in
/-- **Reaching down from a cut**: a block that a block of the cut reaches
in the record is in the cut. -/
theorem IsCut.down (hc : IsCut U st) {i : BlockId} :
    ∀ {j : BlockId}, j ∈ st.ids → ReachesFrom U.block j i → i ∈ st.ids := by
  intro j hj h
  induction h using Relation.ReflTransGen.head_induction_on with
  | refl => exact hj
  | @head a c hstep hrest ih =>
    have hstep : c ∈ (U.block a).refs := hstep
    have hcs : c ∈ (st.blk a).refs := by rw [← hc.eq hj]; exact hstep
    exact ih (st.complete a hj c hcs)

omit [Fintype Validator] [DecidableEq Validator] in
/-- **A view grown by a cut**: a view whose blocks the cut holds grows into
the view holding exactly the cut's blocks. -/
theorem IsCut.extend (hc : IsCut U st) (V : U.View) (hV : ∀ i ∈ V.ids, i ∈ st.ids) :
    ∃ V' : U.View, V.ids ⊆ V'.ids ∧ ∀ i, i ∈ V'.ids ↔ i ∈ st.ids := by
  refine ⟨⟨st.ids, fun j hj => (hc j hj).1, fun i hi j hj => ?_⟩, fun i hi => hV i hi,
    fun i => Iff.rfl⟩
  rw [hc.eq hi] at hj
  exact st.complete i hi j hj

end Cut

omit [Fintype Validator] in
theorem tryDecide_length_le {P : Validity Validator BlockId Payload} {H : Finset Validator}
    {p : Scheme.Params} {σ : Scheme.VoteSel Validator BlockId Payload P H} [S : Slots Validator]
    {U : BlockRecord Validator BlockId Payload P H} {V : U.View} {lo N : ℕ} (hlo : lo ≤ N + 1) :
    (Scheme.tryDecide p σ U V lo N).length ≤ N + 1 - lo := by
  rw [Scheme.tryDecide_eq hlo, List.length_map]
  exact (List.takeWhile_sublist _).length_le.trans (by simp)

omit [Fintype Validator] in
/-- A pass decides only slots at rounds its disk reaches. -/
theorem decideStep_lo_le (s : State Validator BlockId Payload) :
    (Node.decideStep cfg s).1.lo ≤ max s.lo (decidable cfg s.disk.topRound) := by
  unfold Node.decideStep
  dsimp only
  split
  · rename_i hlt
    obtain ⟨hlt, -⟩ := hlt
    generalize hds : Scheme.tryDecide (S := cfg.slots) cfg.p cfg.σ
      (s.memory.window (cfg.slots.slotRound s.lo)) (s.memory.windowView (cfg.slots.slotRound s.lo))
      s.lo (decidable cfg s.disk.topRound - 1) = ds
    have hlen : ds.length ≤ decidable cfg s.disk.topRound - 1 + 1 - s.lo := by
      rw [← hds]; exact tryDecide_length_le (S := cfg.slots) (by omega)
    rw [release_lo]
    change s.lo + ds.length ≤ _
    omega
  · exact le_max_left _ _

omit [Fintype Validator] in
theorem IsCut.tryBuild (hg : Ground U K cfg.q) {s s' : State Validator BlockId Payload}
    {out : List (Output Validator BlockId Payload)} (hc : IsCut U s.disk)
    (h : Node.tryBuild cfg s = some (s', out)) (hb : ∀ e ∈ persists out, e ∈ K) :
    IsCut U s'.disk := by
  obtain ⟨r, id, b, hnew, hrefs, hpred, -, -, -, -, hv, hst, -, -, -, hout⟩ := tryBuild_some h
  have hx : (id, b) ∈ K := hb _ (by rw [hout, persists_built]; exact List.mem_singleton_self _)
  obtain ⟨h₁, h₂⟩ := hg.real _ hx (fun j hj => (hc j (hrefs hj)).1)
    (validAt_of_cut hc hnew hrefs hv)
  rw [hst]
  exact hc.insert ⟨h₁, h₂⟩

omit [Fintype Validator] in
/-- **Building known blocks keeps the disk a cut.** -/
theorem IsCut.progress (hg : Ground U K cfg.q) :
    ∀ (fuel : ℕ) {s : State Validator BlockId Payload}, IsCut U s.disk →
      (∀ e ∈ persists (Node.progress cfg fuel s).2, e ∈ K) →
      IsCut U (Node.progress cfg fuel s).1.disk
  | 0, _, hc, _ => hc
  | fuel + 1, s, hc, hb => by
    rcases htb : Node.tryBuild cfg s with _ | ⟨s₁, out⟩
    · simp only [Node.progress, htb]
      exact hc
    · simp only [Node.progress, htb] at hb ⊢
      rw [persists_append] at hb
      exact IsCut.progress hg fuel (hc.tryBuild hg htb fun e he => hb e
        (List.mem_append_left _ he)) fun e he => hb e (List.mem_append_right _ he)

omit [Fintype Validator] in
/-- **A pass from a cut keeps the disk a cut.** -/
theorem IsCut.advanceStore (hg : Ground U K cfg.q) {s : State Validator BlockId Payload}
    (hc : IsCut U s.disk) (hp : ∀ e ∈ s.pending, e ∈ K)
    (hb : ∀ e ∈ persists (Node.advance cfg s).2, e ∈ K) : IsCut U (Node.advance cfg s).1.disk := by
  have hp₁ := progress_pending (cfg := cfg) (s.disk.topRound + 2) s
  rw [advance_snd, persists_append, persists_arm, List.append_nil] at hb
  rw [advance_disk]
  simp only [Node.pass, flush_disk] at hb ⊢
  rw [persists_append] at hb
  have hc₁ := IsCut.progress hg _ hc fun e he => hb e (List.mem_append_left _ he)
  generalize Node.progress cfg (s.disk.topRound + 2) s = r at hp₁ hc₁ ⊢
  have hc₂ : IsCut U (Node.decideStep cfg r.1).1.disk := by
    rw [decideStep_disk]; exact hc₁
  have hgp : ∀ e ∈ (Node.decideStep cfg r.1).1.pending, e ∈ K := by
    rw [decideStep_pending (cfg := cfg) r.1, hp₁]; exact hp
  exact IsCut.flush hg _ _ hc₂ hgp

/-! ## The decisions -/

omit [Fintype Validator] in
theorem decidable_mono {R R' : ℕ} (h : R ≤ R') : decidable cfg R ≤ decidable cfg R' := by
  unfold decidable
  exact Nat.mul_le_mul_left _ (Nat.add_le_add_right (Nat.div_le_div_right h) 1)

omit [Fintype Validator] in
/-- Building outputs only built blocks. -/
theorem progress_built : ∀ (fuel : ℕ) (s : State Validator BlockId Payload),
    ∃ bs, (Node.progress cfg fuel s).2 = built cfg bs
  | 0, _ => ⟨[], rfl⟩
  | fuel + 1, s => by
    unfold Node.progress
    split
    · rename_i s₁ out h
      obtain ⟨r, id, b, -, -, -, -, -, -, -, -, -, -, -, -, hout⟩ := tryBuild_some h
      obtain ⟨bs, hbs⟩ := progress_built fuel s₁
      exact ⟨(id, b) :: bs, by simp only [hout, hbs, built, List.flatMap_cons,
        List.flatMap_nil, List.append_nil]⟩
    · exact ⟨[], rfl⟩

variable [P.Mechanised]

variable (cfg) in
/-- **The decisions so far are one call of the loop**: nothing, or
`tryDecide` from slot `0` on a view whose blocks the disk holds, scanned
no further than the disk allows; and the next slot is the one after
them. -/
def CommitInv (U : BlockRecord Validator BlockId Payload P H) (s : State Validator BlockId Payload)
    (cs : List (ℕ × Option BlockId)) : Prop :=
  s.lo = cs.length ∧ (cs = [] ∨ ∃ (V : U.View) (N : ℕ),
    (∀ i ∈ V.ids, i ∈ s.disk.ids) ∧
    N + 1 ≤ decidable cfg s.disk.topRound ∧
    cs = tryDecide (S := cfg.slots) cfg.p boundedSel U V 0 N)

variable {q f : ℕ} [P.Quorate q]

omit [Fintype Validator] in
/-- The invariant survives a change that keeps the disk and the next slot. -/
theorem CommitInv.keeps {s s' : State Validator BlockId Payload} {cs : List (ℕ × Option BlockId)}
    (h : CommitInv cfg U s cs) (hlo : s'.lo = s.lo) (hk : Keeps s.disk s'.disk) :
    CommitInv cfg U s' cs := by
  refine ⟨hlo.trans h.1, ?_⟩
  rcases h.2 with h0 | ⟨V, N, hV, hN, hcs⟩
  · exact Or.inl h0
  · exact Or.inr ⟨V, N, fun i hi => hk.1 (hV i hi), hN.trans (decidable_mono hk.2.2), hcs⟩

/-- **A decision step keeps the invariant.** -/
theorem CommitInv.decideStep (hσ : cfg.σ = boundedSel) (ht : cfg.p.Tolerates H f q)
    {s : State Validator BlockId Payload} {cs : List (ℕ × Option BlockId)}
    (h : CommitInv cfg U s cs) (hc : IsCut U s.disk) :
    CommitInv cfg U (Node.decideStep cfg s).1 (cs ++ commitsOf (Node.decideStep cfg s).2) := by
  letI := cfg.slots
  have hw : 2 ≤ cfg.p.waveLength := by
    rcases ht.2.2 with ⟨-, hw, -⟩ | ⟨-, hw, -⟩ | ⟨-, hw, -⟩ | ⟨-, hw, -⟩ <;> omega
  -- the disk decides as a view of `U` grown from any view the invariant allows
  have hgrow : ∀ V : U.View, (∀ i ∈ V.ids, i ∈ s.disk.ids) →
      ∃ V' : U.View, V.ids ⊆ V'.ids ∧ (∀ i ∈ V'.ids, i ∈ s.disk.ids) ∧
        ∀ N, tryDecide cfg.p boundedSel s.disk.toRecord s.disk.view s.lo N =
          tryDecide cfg.p boundedSel U V' s.lo N := by
    intro V hV
    obtain ⟨V', hVV, hiff⟩ := hc.extend V hV
    refine ⟨V', hVV, fun i hi => (hiff i).mp hi, fun N => ?_⟩
    exact (ViewsAbove.of_store hiff fun i hi => hc.eq hi).tryDecide_eq cfg.p hw N
      (Nat.zero_le _)
  have hempty : ∀ i ∈ (⟨∅, Finset.empty_subset _,
      fun _ h => absurd h (Finset.notMem_empty _)⟩ : U.View).ids, i ∈ s.disk.ids :=
    fun i hi => absurd hi (Finset.notMem_empty i)
  unfold Node.decideStep
  dsimp only
  split
  · rename_i hlt
    obtain ⟨hlt, hfl, -⟩ := hlt
    rw [commitsOf_map, tryDecide_memory hσ hw s hfl]
    unfold CommitInv
    simp only [release_lo, release_disk]
    refine ⟨?_, Or.inr ?_⟩
    · change s.lo + _ = _
      rw [List.length_append, h.1]
    rcases h.2 with h0 | ⟨V, N, hV, hN, hcs⟩
    · subst h0
      obtain ⟨V', -, hV', hT⟩ := hgrow _ hempty
      have hlo : s.lo = 0 := h.1
      refine ⟨V', decidable cfg s.disk.topRound - 1, hV',
        by change _ ≤ decidable cfg s.disk.topRound; omega, ?_⟩
      rw [List.nil_append, hT, hlo]
    · obtain ⟨V', hVV, hV', hT⟩ := hgrow V hV
      refine ⟨V', decidable cfg s.disk.topRound - 1, hV',
        by change _ ≤ decidable cfg s.disk.topRound; omega, ?_⟩
      rw [hT, h.1, hcs]
      have := Loop.resume _ _ _ P q H f cfg.p boundedSel U V V' 0 N
        (decidable cfg s.disk.topRound - 1) ht hVV (by omega)
      rw [Nat.zero_add] at this
      exact this
  · rw [show commitsOf ([] : List (Output Validator BlockId Payload)) = [] from rfl,
      List.append_nil]
    exact h

/-- **A pass keeps the invariant, and the disk a cut.** -/
theorem CommitInv.advance (hg : Ground U K cfg.q) (hσ : cfg.σ = boundedSel)
    (ht : cfg.p.Tolerates H f q) {s : State Validator BlockId Payload}
    {cs : List (ℕ × Option BlockId)} (h : CommitInv cfg U s cs) (hc : IsCut U s.disk)
    (hp : ∀ e ∈ s.pending, e ∈ K) (hb : ∀ e ∈ persists (Node.advance cfg s).2, e ∈ K) :
    CommitInv cfg U (Node.advance cfg s).1 (cs ++ commitsOf (Node.advance cfg s).2) ∧
      IsCut U (Node.advance cfg s).1.disk := by
  have hcut := IsCut.advanceStore hg hc hp hb
  obtain ⟨bs, hbs⟩ := progress_built (cfg := cfg) (s.disk.topRound + 2) s
  obtain ⟨hg₁, hlo₁⟩ := Grows.progress (cfg := cfg) (s.disk.topRound + 2) s
  rw [advance_snd, persists_append, persists_arm, List.append_nil] at hb
  rw [advance_snd, commitsOf_append, commitsOf_arm, List.append_nil]
  refine ⟨CommitInv.keeps ?_ (advance_lo s) (by rw [advance_disk]; exact Keeps.refl _), hcut⟩
  rw [advance_disk] at hcut
  simp only [Node.pass] at hb hcut ⊢
  rw [persists_append] at hb
  have hc₁ := IsCut.progress hg _ hc fun e he => hb e (List.mem_append_left _ he)
  generalize Node.progress cfg (s.disk.topRound + 2) s = r at hbs hg₁ hlo₁ hc₁ hcut ⊢
  have h₁ : CommitInv cfg U r.1 cs := h.keeps hlo₁ hg₁.keeps
  have h₂ := h₁.decideStep hσ ht hc₁
  have hk := (Grows.flush (cfg := cfg) ((Node.decideStep cfg r.1).1.pending.length + 1)
    (Node.decideStep cfg r.1).1.disk (Node.decideStep cfg r.1).1.pending).keeps
  rw [commitsOf_append, hbs, commitsOf_built, List.nil_append]
  exact h₂.keeps (flush_lo _ _) (by rw [flush_disk]; exact hk)

/-- **The passes keep the invariant, and the disk a cut.** -/
theorem CommitInv.quiesce (hg : Ground U K cfg.q) (hσ : cfg.σ = boundedSel)
    (ht : cfg.p.Tolerates H f q) : ∀ (n : ℕ) {s : State Validator BlockId Payload}
    {cs : List (ℕ × Option BlockId)}, CommitInv cfg U s cs → IsCut U s.disk →
    (∀ e ∈ s.pending, e ∈ K) → (∀ e ∈ persists (Node.quiesce cfg n s).2, e ∈ K) →
    CommitInv cfg U (Node.quiesce cfg n s).1 (cs ++ commitsOf (Node.quiesce cfg n s).2) ∧
      IsCut U (Node.quiesce cfg n s).1.disk
  | 0, s, cs, h, hc, _, _ => by
    simp only [Node.quiesce, commitsOf, List.filterMap_nil, List.append_nil]; exact ⟨h, hc⟩
  | n + 1, s, cs, h, hc, hp, hb => by
    rcases quiesce_succ_cases (cfg := cfg) n s with he | he <;> rw [he] at hb ⊢
    · exact h.advance hg hσ ht hc hp hb
    · rw [persists_append] at hb
      obtain ⟨h₁, hc₁⟩ := h.advance hg hσ ht hc hp fun e he => hb e (List.mem_append_left _ he)
      have := CommitInv.quiesce hg hσ ht n h₁ hc₁
        (fun e he => hp e (advance_sub (cfg := cfg) s e he))
        fun e he => hb e (List.mem_append_right _ he)
      rw [commitsOf_append, ← List.append_assoc]; exact this

/-- **Settling keeps the invariant, and the disk a cut.** -/
theorem CommitInv.settle (hg : Ground U K cfg.q) (hσ : cfg.σ = boundedSel)
    (ht : cfg.p.Tolerates H f q) {s : State Validator BlockId Payload}
    {cs : List (ℕ × Option BlockId)} (h : CommitInv cfg U s cs) (hc : IsCut U s.disk)
    (hp : ∀ e ∈ s.pending, e ∈ K) (hb : ∀ e ∈ persists (Node.settle cfg s).2, e ∈ K) :
    CommitInv cfg U (Node.settle cfg s).1 (cs ++ commitsOf (Node.settle cfg s).2) ∧
      IsCut U (Node.settle cfg s).1.disk :=
  CommitInv.quiesce hg hσ ht (passes cfg s) h hc hp hb

/-- **A step keeps the invariant, and the disk a cut.** -/
theorem CommitInv.step (hg : Ground U K cfg.q) (hσ : cfg.σ = boundedSel)
    (ht : cfg.p.Tolerates H f q) {s : State Validator BlockId Payload}
    {cs : List (ℕ × Option BlockId)} (i : Input Validator BlockId Payload)
    (h : CommitInv cfg U s cs) (hc : IsCut U s.disk)
    (hp : ∀ e ∈ s.pending, e ∈ K) (hd : ∀ e ∈ delivered cfg [i], e ∈ K)
    (hb : ∀ e ∈ persists (Node.step cfg s i).2, e ∈ K) :
    CommitInv cfg U (Node.step cfg s i).1 (cs ++ commitsOf (Node.step cfg s i).2) ∧
      IsCut U (Node.step cfg s i).1.disk := by
  -- a step that settles a state `s₀`, after outputs without decisions
  have hset : ∀ (s₀ : State Validator BlockId Payload)
      (pre : List (Output Validator BlockId Payload)),
      CommitInv cfg U s₀ cs → IsCut U s₀.disk → (∀ e ∈ s₀.pending, e ∈ K) →
      commitsOf pre = [] →
      Node.step cfg s i = ((Node.settle cfg s₀).1, pre ++ (Node.settle cfg s₀).2) →
      CommitInv cfg U (Node.step cfg s i).1 (cs ++ commitsOf (Node.step cfg s i).2) ∧
        IsCut U (Node.step cfg s i).1.disk := by
    intro s₀ pre h₀ hc₀ hp₀ hpre he
    rw [he] at hb ⊢
    rw [persists_append] at hb
    rw [commitsOf_append, hpre, List.nil_append]
    exact h₀.settle hg hσ ht hc₀ hp₀ fun e he => hb e (List.mem_append_right _ he)
  have hsame : Node.step cfg s i = (s, []) →
      CommitInv cfg U (Node.step cfg s i).1 (cs ++ commitsOf (Node.step cfg s i).2) ∧
        IsCut U (Node.step cfg s i).1.disk := by
    intro he; rw [he]; exact ⟨by simpa [commitsOf] using h, hc⟩
  cases i with
  | start =>
    by_cases h₁ : s.top = none ∧ cfg.Admissible
    · by_cases h₂ : cfg.idOf cfg.genesis ∉ s.disk.ids ∧
          rowValid cfg.q (Function.update s.disk.blk (cfg.idOf cfg.genesis) cfg.genesis)
            cfg.genesis
      · let st := s.disk.insert (cfg.idOf cfg.genesis) cfg.genesis h₂.1
          (fun _ hj => absurd hj (Finset.notMem_empty _))
          (fun j hj => absurd hj (Finset.notMem_empty j))
        have hx : (cfg.idOf cfg.genesis, cfg.genesis) ∈ K :=
          hb _ (by simp only [Node.step, dif_pos h₂, if_pos h₁]; simp [persists])
        have hnil : cfg.genesis.refs ⊆ s.disk.ids := fun _ hj => absurd hj (Finset.notMem_empty _)
        obtain ⟨hU₁, hU₂⟩ := hg.real _ hx (fun _ hj => absurd hj (Finset.notMem_empty _))
          (validAt_of_cut hc h₂.1 hnil h₂.2)
        have hcst : IsCut U st := hc.insert ⟨hU₁, hU₂⟩
        let gid := cfg.idOf cfg.genesis
        have hk : Keeps s.disk st := (Grows.insert s.disk).keeps
        exact hset { keep s (cfg.idOf cfg.genesis) cfg.genesis h₂.1
            (fun _ hj => absurd hj (Finset.notMem_empty _))
            (fun j hj => absurd hj (Finset.notMem_empty j)) with
            top := some 0, own := some gid, recovering := false }
          (built cfg [(cfg.idOf cfg.genesis, cfg.genesis)]) (h.keeps rfl hk) hcst hp
          (commitsOf_built _) (by simp only [Node.step, dif_pos h₂, if_pos h₁]; rfl)
      · exact hsame (by simp only [Node.step, dif_neg h₂, if_pos h₁])
    · exact hsame (by simp only [Node.step, if_neg h₁])
  | deliver id b =>
    by_cases hA : Admits cfg s id b
    · let s₁ := afterFlush (cfg := cfg) s id b
      let miss := missing s₁ b
      have hx : (id, b) ∈ K := hd _ (by simp [delivered, hA.1])
      have hg₁ := Grows.flush (cfg := cfg) (s.pending.length + 1) s.disk ((id, b) :: s.pending)
      have hpend : ∀ e ∈ (id, b) :: s.pending, e ∈ K := fun e he => by
        rcases List.mem_cons.mp he with rfl | he
        · exact hx
        · exact hp e he
      have hc₁ : IsCut U s₁.disk := by rw [afterFlush_disk]; exact IsCut.flush hg _ _ hc hpend
      exact hset s₁
        (if miss.isEmpty then [] else [.fetch b.creator (s.top.getD 0) miss])
        (h.keeps (afterFlush_lo _ _ _) (by rw [afterFlush_disk]; exact hg₁.keeps)) hc₁
        (fun e he => hpend e (flush_pending_sub _ _ _ e (by rwa [afterFlush_pending] at he)))
        (by split <;> rfl) (step_deliver hA)
    · exact hsame (step_deliver_not hA)
  | timer r =>
    rw [persists_step_timer] at hb
    rw [step_timer_fst, commitsOf_step_timer]
    exact (h.keeps (s' := { s with fired := fire s r, recovering := false }) rfl
      (Keeps.refl _)).settle hg hσ ht hc hp hb
  | fetchRequest peer r ids =>
    rw [show Node.step cfg s (.fetchRequest peer r ids) = (s, answer cfg s peer r ids) from rfl]
    have : commitsOf (answer cfg s peer r ids) = [] := by
      unfold answer commitsOf
      rw [List.filterMap_map]
      exact List.filterMap_eq_nil_iff.mpr fun _ _ => rfl
    rw [this, List.append_nil]
    exact ⟨h, hc⟩
  | restart =>
    rw [persists_step_restart] at hb
    rw [step_restart_fst, commitsOf_step_restart]
    exact (h.keeps (s' := { s with recovering := true }) rfl (Keeps.refl _)).settle
      hg hσ ht hc hp hb

/-- **A run keeps the invariant**, at a record grounding what the node knew. -/
theorem CommitInv.run (hg : Ground U K cfg.q) (hσ : cfg.σ = boundedSel)
    (ht : cfg.p.Tolerates H f q) :
    ∀ (is : List (Input Validator BlockId Payload)) {s : State Validator BlockId Payload}
      {cs : List (ℕ × Option BlockId)}, CommitInv cfg U s cs → IsCut U s.disk →
      (∀ e ∈ s.pending, e ∈ K) → (∀ e ∈ delivered cfg is, e ∈ K) →
      (∀ e ∈ persists (Node.run cfg s is).2, e ∈ K) →
      CommitInv cfg U (Node.run cfg s is).1 (cs ++ commitsOf (Node.run cfg s is).2)
  | [], s, cs, h, _, _, _, _ => by simpa [Node.run, commitsOf] using h
  | i :: is, s, cs, h, hc, hp, hd, hb => by
    simp only [Node.run] at hb ⊢
    rw [persists_append] at hb
    rw [delivered_cons] at hd
    obtain ⟨h₁, hc₁⟩ := h.step hg hσ ht i hc hp (fun e he => hd e (List.mem_append_left _ he))
      (fun e he => hb e (List.mem_append_left _ he))
    have hp₁ : ∀ e ∈ (Node.step cfg s i).1.pending, e ∈ K := fun e he => by
      rcases step_sub s i e he with he | ⟨hi, hA⟩
      · exact hp e he
      · refine hd e (List.mem_append_left _ ?_)
        rw [hi]
        simp only [delivered, List.flatMap_cons, List.flatMap_nil, List.append_nil, if_pos hA.1]
        exact List.mem_singleton.mpr rfl
    have := CommitInv.run hg hσ ht is h₁ hc₁ hp₁
      (fun e he => hd e (List.mem_append_right _ he))
      (fun e he => hb e (List.mem_append_right _ he))
    rw [commitsOf_append, ← List.append_assoc]
    exact this

end Node

end LeanDag
