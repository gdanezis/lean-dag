import LeanDag.Node.Helpers.Held
import LeanDag.Node.Helpers.Decided
import LeanDag.Scheme.Loop.Proof
/-!
# A node's decisions are one call of the loop

A store takes in only good blocks from `K` (`Grounds`) when a known new
block valid over it, with its references held, is good once the store's
blocks are (`AllGood`); accepting, building and passes keep the disk good
(`AllGood.accept`, `AllGood.advanceStore`). A record `U` grounds what a node
knows, `K` (`Ground`), when a known block valid over blocks of `U` is the
record's block; then the store takes in only blocks of `U`
(`Ground.grounds`), and every disk along the node's run is a cut of `U`
(`IsCut`): its blocks are blocks of `U`, read as `U` reads them.

On such a record the decisions of a node that does not drop output so far
are nothing, or
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

/-- **Every block of a store is good**, as accepted. -/
def AllGood (Good : BlockId → Block Validator BlockId Payload → Prop)
    (st : Store Validator BlockId Payload) : Prop :=
  ∀ j ∈ st.ids, Good j (st.full j)

variable (cfg) in
/-- **A store takes in only good blocks from `K`**: a known new block whose
references the store holds and that is valid over it is good, when the
store's blocks are. -/
def Grounds (Good : BlockId → Block Validator BlockId Payload → Prop)
    (K : Set (BlockId × Block Validator BlockId Payload)) : Prop :=
  ∀ st : Store Validator BlockId Payload, AllGood Good st → ∀ x ∈ K, x.1 ∉ st.ids →
    x.2.refs ⊆ st.ids → rowValid cfg.q cfg.xp (Function.update st.blk x.1 x.2) x.2 → Good x.1 x.2

/-- **A store is a cut of a record**: its blocks, as accepted, are the
record's. -/
def IsCut (U : BlockRecord Validator BlockId Payload P H) (st : Store Validator BlockId Payload) :
    Prop :=
  AllGood (fun j b => j ∈ U.ids ∧ U.block j = b) st

/-- **A record grounds what a node knew**, at quorum `q`: a known block
valid at `q` over blocks of the record is the record's block. -/
structure Ground (U : BlockRecord Validator BlockId Payload P H)
    (K : Set (BlockId × Block Validator BlockId Payload)) (q : ℕ) : Prop where
  real : ∀ x ∈ K, x.2.refs ⊆ U.ids → ValidAt q Clause.none U.block x.2 →
    x.1 ∈ U.ids ∧ U.block x.1 = x.2

variable {U : BlockRecord Validator BlockId Payload P H}
variable {K : Set (BlockId × Block Validator BlockId Payload)}
variable {Good : BlockId → Block Validator BlockId Payload → Prop}

section Cut

variable {st : Store Validator BlockId Payload}

omit [Fintype Validator] [DecidableEq Validator] in
/-- A cut holds its blocks as the record does. -/
theorem IsCut.eq (hc : IsCut U st) {j : BlockId} (hj : j ∈ st.ids) : U.block j = st.full j :=
  (hc j hj).2

omit [Fintype Validator] [DecidableEq Validator] in
/-- A cut reads a block it keeps with its references as the record does. -/
theorem IsCut.eq_blk (hc : IsCut U st) {j : BlockId} (hj : j ∈ st.ids)
    (hk : st.kept[j]? = none) : U.block j = st.blk j := by
  rw [hc.eq hj, st.full_of_kept_none hk]

omit [Fintype Validator] [DecidableEq Validator] in
theorem IsCut.round (hc : IsCut U st) {j : BlockId} (hj : j ∈ st.ids) :
    (U.block j).round = (st.blk j).round := by
  rw [hc.eq hj]; exact (st.full_fields j).1

omit [Fintype Validator] [DecidableEq Validator] in
theorem IsCut.creator (hc : IsCut U st) {j : BlockId} (hj : j ∈ st.ids) :
    (U.block j).creator = (st.blk j).creator := by
  rw [hc.eq hj]; exact (st.full_fields j).2.1

omit [Fintype Validator] [DecidableEq Validator] in
theorem AllGood.insert (hc : AllGood Good st) {id : BlockId} {b : Block Validator BlockId Payload}
    {hnew hrefs hpred} (hb : Good id b) : AllGood Good (st.insert id b hnew hrefs hpred) := by
  intro j hj
  rw [Store.insert_ids] at hj
  rw [Store.full_insert]
  by_cases h : j = id
  · subst h
    rw [if_pos rfl]
    exact hb
  · rw [if_neg h]
    exact hc j ((Finset.mem_insert.mp hj).resolve_left h)

omit [Fintype Validator] [DecidableEq Validator] in
/-- Keeping blocks without their references keeps the store good. -/
theorem AllGood.restrips {F : ℕ} {st' : Store Validator BlockId Payload} (hc : AllGood Good st)
    (h : Store.Restrips F st st') : AllGood Good st' := by
  intro j hj
  rw [h.full]
  exact hc j (h.ids ▸ hj)

omit [Fintype Validator] in
theorem AllGood.shrinks {st' : Store Validator BlockId Payload} (hc : AllGood Good st)
    (h : Store.Shrinks st st') : AllGood Good st' := by
  intro j hj
  rw [h.full j hj]
  exact hc j (h.ids hj)

omit [Fintype Validator] in
/-- **Validity over the store is validity over the record**, at the
quorum: it reads only the rounds and authors of the references. -/
theorem validAt_of_cut (hc : IsCut U st) {q : ℕ} {E : Exposure Validator BlockId Payload}
    {id : BlockId} {b : Block Validator BlockId Payload} (hnew : id ∉ st.ids)
    (hrefs : b.refs ⊆ st.ids) (hv : rowValid q E (Function.update st.blk id b) b) :
    ValidAt q Clause.none U.block b := by
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
/-- **A record grounding what a node knew takes in its blocks.** -/
theorem Ground.grounds (hg : Ground U K cfg.q) :
    Grounds cfg (fun j b => j ∈ U.ids ∧ U.block j = b) K :=
  fun _ hc x hx hnew hrefs hv =>
    hg.real x hx (fun j hj => (hc j (hrefs hj)).1) (validAt_of_cut hc hnew hrefs hv)

omit [Fintype Validator] in
/-- **Accepting a known block keeps the store good.** -/
theorem AllGood.accept (hg : Grounds cfg Good K) (hc : AllGood Good st)
    {id : BlockId} {b : Block Validator BlockId Payload} (hx : (id, b) ∈ K) :
    AllGood Good (acceptOn cfg st id b) := by
  unfold acceptOn
  split
  · rename_i h
    exact hc.insert (hg st hc _ hx h.1 h.2.1 h.2.2.2)
  · exact hc

omit [Fintype Validator] in
theorem AllGood.foldl (hg : Grounds cfg Good K) :
    ∀ (l : List (BlockId × Block Validator BlockId Payload)) {st : Store Validator BlockId Payload},
    AllGood Good st → (∀ e ∈ l, e ∈ K) →
      AllGood Good (l.foldl (fun s e => acceptOn cfg s e.1 e.2) st)
  | [], _, hc, _ => hc
  | e :: l, st, hc, hK => by
    rw [List.foldl_cons]
    exact AllGood.foldl hg l (hc.accept hg (hK e List.mem_cons_self))
      fun x hx => hK x (List.mem_cons_of_mem _ hx)

omit [Fintype Validator] in
/-- **Accepting known syncs' blocks keeps the store good.** -/
theorem AllGood.flushSyncs (hg : Grounds cfg Good K) (fuel : ℕ)
    {s : State Validator BlockId Payload} (hc : AllGood Good s.disk)
    (hK : ∀ e ∈ s.syncs, e.2.1 ∈ K) : AllGood Good (Node.flushSyncs cfg fuel s).disk := by
  obtain ⟨L, hL, hd⟩ := (flushSyncs_eq (cfg := cfg) fuel s).1
  rw [hd]
  refine AllGood.foldl hg L hc fun e he => ?_
  obtain ⟨x, hx, rfl⟩ := List.mem_map.mp (hL e he)
  exact hK x hx

omit [Fintype Validator] in
/-- **A receipt of known blocks keeps the store good**, and the syncs'
blocks known. -/
theorem Received.good (hg : Grounds cfg Good K) {inp : Input Validator BlockId Payload}
    {s s₁ : State Validator BlockId Payload} (hr : Received cfg inp s s₁)
    (hc : AllGood Good s.disk) (hp : ∀ e ∈ s.syncs, e.2.1 ∈ K)
    (hd : ∀ e ∈ delivered cfg [inp], e ∈ K) :
    AllGood Good s₁.disk ∧ ∀ e ∈ s₁.syncs, e.2.1 ∈ K := by
  obtain ⟨L, hL, hdk⟩ := hr.disk
  refine ⟨by
    rw [hdk]
    refine AllGood.foldl hg L hc fun e he => ?_
    rcases hL e he with h | h
    · obtain ⟨x, hx, rfl⟩ := List.mem_map.mp h; exact hp x hx
    · exact hd e h, fun e he => ?_⟩
  rcases hr.syncs e he with h | h
  · obtain ⟨x, hx, hxe⟩ := List.mem_map.mp h; rw [← hxe]; exact hp x hx
  · exact hd _ h

omit [Fintype Validator] [DecidableEq Validator] in
/-- **Reaching down from a cut**: a block that a block of the cut reaches
in the record is in the cut, when the cut's blocks as accepted are closed
under references. -/
theorem IsCut.down (hc : IsCut U st) (hcl : st.FullClosed) {i : BlockId} :
    ∀ {j : BlockId}, j ∈ st.ids → ReachesFrom U.block j i → i ∈ st.ids := by
  intro j hj h
  induction h using Relation.ReflTransGen.head_induction_on with
  | refl => exact hj
  | @head a c hstep hrest ih =>
    have hstep : c ∈ (U.block a).refs := hstep
    have hcs : c ∈ (st.full a).refs := by rw [← hc.eq hj]; exact hstep
    exact ih (hcl a hj c hcs).1

omit [Fintype Validator] in
/-- **Reaching down from a cut, from a round up**: a block at or above `R`
that a block of the cut reaches in the record is in the cut, when the cut
keeps every block from `R` up with its references. -/
theorem IsCut.down_above [P.Mechanised] (hc : IsCut U st) {R : ℕ}
    (hk : ∀ a ∈ st.ids, R ≤ (st.blk a).round → st.kept[a]? = none) {i : BlockId}
    (hiR : R ≤ (U.block i).round) :
    ∀ {j : BlockId}, j ∈ st.ids → ReachesFrom U.block j i → i ∈ st.ids := by
  intro j hj h
  induction h using Relation.ReflTransGen.head_induction_on with
  | refl => exact hj
  | @head a c hstep hrest ih =>
    have hstep : c ∈ (U.block a).refs := hstep
    have hai : R ≤ (st.blk a).round := by
      rw [← hc.round hj]
      exact hiR.trans (round_le_of_reaches (hc a hj).1 (Relation.ReflTransGen.head hstep hrest))
    have hcs : c ∈ (st.blk a).refs := by rw [← hc.eq_blk hj (hk a hj hai)]; exact hstep
    exact ih (st.complete a hj c hcs)

omit [Fintype Validator] [DecidableEq Validator] in
/-- **A view grown by a cut**: a view whose blocks the cut holds grows into
the view holding exactly the cut's blocks, when the cut's blocks as
accepted are closed under references. -/
theorem IsCut.extend (hc : IsCut U st) (hcl : st.FullClosed) (V : U.View)
    (hV : ∀ i ∈ V.ids, i ∈ st.ids) :
    ∃ V' : U.View, V.ids ⊆ V'.ids ∧ ∀ i, i ∈ V'.ids ↔ i ∈ st.ids := by
  refine ⟨⟨st.ids, fun j hj => (hc j hj).1, fun i hi j hj => ?_⟩, fun i hi => hV i hi,
    fun i => Iff.rfl⟩
  rw [hc.eq hi] at hj
  exact (hcl i hi j hj).1

/-- **The histories of a cut's blocks**, as a view of the record. -/
def IsCut.histView [P.Mechanised] (hc : IsCut U st) : U.View :=
  U.historiesView st.ids fun i hi => (hc i hi).1

omit [Fintype Validator] in
/-- **The histories of a cut's blocks agree with it from `R` up**, when the
cut keeps every block from `R` up with its references. -/
theorem IsCut.viewsAbove [P.Mechanised] (hc : IsCut U st) {R : ℕ}
    (hk : ∀ a ∈ st.ids, R ≤ (st.blk a).round → st.kept[a]? = none) :
    ViewsAbove R boundedSel boundedSel st.view hc.histView := by
  refine ViewsAbove.of_boundedSel (fun i hi _ => ?_) (fun i hi hR => ?_)
    (fun i hi _ => hc.round hi) (fun i hi _ => hc.creator hi) (fun i hi hR => ?_)
  · exact Finset.mem_biUnion.mpr ⟨i, hi, mem_history_self⟩
  · obtain ⟨a, ha, hia⟩ := Finset.mem_biUnion.mp hi
    have hiS := hc.down_above hk hR ha ((mem_history_iff (hc a ha).1).mp hia)
    exact ⟨hiS, by change R ≤ (st.blk i).round; rw [← hc.round hiS]; exact hR⟩
  · change (U.block i).refs = (st.blk i).refs
    rw [hc.eq_blk hi (hk i hi (le_of_lt hR))]

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
    rw [drop_lo, release_lo]
    change s.lo + ds.length ≤ _
    omega
  · exact le_max_left _ _

omit [Fintype Validator] in
theorem AllGood.tryBuild (hg : Grounds cfg Good K) {s s' : State Validator BlockId Payload}
    {out : List (Output Validator BlockId Payload)} (hc : AllGood Good s.disk)
    (h : Node.tryBuild cfg s = some (s', out)) (hb : ∀ e ∈ persists out, e ∈ K) :
    AllGood Good s'.disk := by
  obtain ⟨r, id, b, hnew, hrefs, hpred, -, -, -, -, hv, hst, -, -, -, hout⟩ := tryBuild_some h
  have hx : (id, b) ∈ K := hb _ (by rw [hout, persists_built]; exact List.mem_singleton_self _)
  exact (hc.insert (hg _ hc _ hx hnew hrefs hv)).restrips hst

omit [Fintype Validator] in
/-- **Building known blocks keeps the disk good.** -/
theorem AllGood.progress (hg : Grounds cfg Good K) :
    ∀ (fuel : ℕ) {s : State Validator BlockId Payload}, AllGood Good s.disk →
      (∀ e ∈ persists (Node.progress cfg fuel s).2, e ∈ K) →
      AllGood Good (Node.progress cfg fuel s).1.disk
  | 0, _, hc, _ => hc
  | fuel + 1, s, hc, hb => by
    rcases htb : Node.tryBuild cfg s with _ | ⟨s₁, out⟩
    · simp only [Node.progress, htb]
      exact hc
    · simp only [Node.progress, htb] at hb ⊢
      rw [persists_append] at hb
      exact AllGood.progress hg fuel (hc.tryBuild hg htb fun e he => hb e
        (List.mem_append_left _ he)) fun e he => hb e (List.mem_append_right _ he)

omit [Fintype Validator] in
/-- **A pass keeps the disk good.** -/
theorem AllGood.advanceStore (hg : Grounds cfg Good K) {s : State Validator BlockId Payload}
    (hc : AllGood Good s.disk) (hp : ∀ e ∈ s.syncs, e.2.1 ∈ K)
    (hb : ∀ e ∈ persists (Node.advance cfg s).2, e ∈ K) :
    AllGood Good (Node.advance cfg s).1.disk := by
  have hp₁ := progress_syncs (cfg := cfg) (s.disk.topRound + 2) s
  rw [advance_snd, persists_append, persists_arm, List.append_nil] at hb
  rw [advance_disk]
  simp only [Node.pass] at hb ⊢
  rw [persists_append] at hb
  have hc₁ := AllGood.progress hg _ hc fun e he => hb e (List.mem_append_left _ he)
  generalize Node.progress cfg (s.disk.topRound + 2) s = r at hp₁ hc₁ ⊢
  have hc₂ : AllGood Good (Node.decideStep cfg r.1).1.disk := hc₁.shrinks (decideStep_shrinks _)
  have hgp : ∀ e ∈ (Node.decideStep cfg r.1).1.syncs, e.2.1 ∈ K := by
    rw [decideStep_syncs (cfg := cfg) r.1, hp₁]; exact hp
  exact AllGood.flushSyncs hg _ hc₂ hgp

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
    (h : CommitInv cfg U s cs) (hc : IsCut U s.disk) (hcl : s.disk.FullClosed)
    (hd : cfg.drops = false) :
    CommitInv cfg U (Node.decideStep cfg s).1 (cs ++ commitsOf (Node.decideStep cfg s).2) := by
  letI := cfg.slots
  have hw : 2 ≤ cfg.p.waveLength := by
    rcases ht.2.2 with ⟨-, hw, -⟩ | ⟨-, hw, -⟩ | ⟨-, hw, -⟩ | ⟨-, hw, -⟩ <;> omega
  -- the disk decides as a view of `U` grown from any view the invariant allows
  have hgrow : s.floor ≤ cfg.slots.slotRound s.lo → ∀ V : U.View, (∀ i ∈ V.ids, i ∈ s.disk.ids) →
      ∃ V' : U.View, V.ids ⊆ V'.ids ∧ (∀ i ∈ V'.ids, i ∈ s.disk.ids) ∧
        ∀ N, tryDecide cfg.p boundedSel s.disk.toRecord s.disk.view s.lo N =
          tryDecide cfg.p boundedSel U V' s.lo N := by
    intro hfl V hV
    obtain ⟨V', hVV, hiff⟩ := hc.extend hcl V hV
    refine ⟨V', hVV, fun i hi => (hiff i).mp hi, fun N => ?_⟩
    exact (ViewsAbove.of_storeAbove (cfg.slots.slotRound s.lo) hiff
      (fun i hi => ⟨hc.round hi, hc.creator hi⟩)
      (fun i hi hR => hc.eq_blk hi (by
        by_contra hk
        have := s.low i hk
        omega))).tryDecide_eq cfg.p hw N le_rfl
  have hempty : ∀ i ∈ (⟨∅, Finset.empty_subset _,
      fun _ h => absurd h (Finset.notMem_empty _)⟩ : U.View).ids, i ∈ s.disk.ids :=
    fun i hi => absurd hi (Finset.notMem_empty i)
  unfold Node.decideStep
  dsimp only
  split
  · rename_i hlt
    obtain ⟨hlt, hfl, -⟩ := hlt
    rw [commitsOf_map, tryDecide_memory hσ hw s hfl, drop_of_false _ hd]
    unfold CommitInv
    simp only [release_lo, release_ids, release_topRound]
    refine ⟨?_, Or.inr ?_⟩
    · change s.lo + _ = _
      rw [List.length_append, h.1]
    rcases h.2 with h0 | ⟨V, N, hV, hN, hcs⟩
    · subst h0
      obtain ⟨V', -, hV', hT⟩ := hgrow hfl _ hempty
      have hlo : s.lo = 0 := h.1
      refine ⟨V', decidable cfg s.disk.topRound - 1, hV',
        by change _ ≤ decidable cfg s.disk.topRound; omega, ?_⟩
      rw [List.nil_append, hT, hlo]
    · obtain ⟨V', hVV, hV', hT⟩ := hgrow hfl V hV
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
    (hdr : cfg.drops = false) (ht : cfg.p.Tolerates H f q) {s : State Validator BlockId Payload}
    {cs : List (ℕ × Option BlockId)} (h : CommitInv cfg U s cs) (hc : IsCut U s.disk)
    (hcl : s.disk.FullClosed)
    (hp : ∀ e ∈ s.syncs, e.2.1 ∈ K) (hb : ∀ e ∈ persists (Node.advance cfg s).2, e ∈ K) :
    CommitInv cfg U (Node.advance cfg s).1 (cs ++ commitsOf (Node.advance cfg s).2) ∧
      IsCut U (Node.advance cfg s).1.disk := by
  have hcut := AllGood.advanceStore hg.grounds hc hp hb
  obtain ⟨bs, hbs⟩ := progress_built (cfg := cfg) (s.disk.topRound + 2) s
  obtain ⟨hg₁, hlo₁⟩ := Grows.progress (cfg := cfg) (s.disk.topRound + 2) s
  rw [advance_snd, persists_append, persists_arm, List.append_nil] at hb
  rw [advance_snd, commitsOf_append, commitsOf_arm, List.append_nil]
  refine ⟨CommitInv.keeps ?_ (advance_lo s) (by rw [advance_disk]; exact Keeps.refl _), hcut⟩
  rw [advance_disk] at hcut
  simp only [Node.pass] at hb hcut ⊢
  rw [persists_append] at hb
  have hc₁ := AllGood.progress hg.grounds _ hc fun e he => hb e (List.mem_append_left _ he)
  have hcl₁ := closed_progress (cfg := cfg) (s.disk.topRound + 2) s hcl
  generalize Node.progress cfg (s.disk.topRound + 2) s = r at hbs hg₁ hlo₁ hc₁ hcut hcl₁ ⊢
  have h₁ : CommitInv cfg U r.1 cs := h.keeps hlo₁ hg₁.keeps
  have h₂ := h₁.decideStep hσ ht hc₁ hcl₁ hdr
  have hk := (Grows.flushSyncs (cfg := cfg) ((Node.decideStep cfg r.1).1.syncs.length + 1)
    (Node.decideStep cfg r.1).1).keeps
  rw [commitsOf_append, hbs, commitsOf_built, List.nil_append]
  exact h₂.keeps (flushSyncs_lo _ _) hk

/-- **The passes keep the invariant, and the disk a cut.** -/
theorem CommitInv.quiesce (hg : Ground U K cfg.q) (hσ : cfg.σ = boundedSel)
    (hdr : cfg.drops = false) (ht : cfg.p.Tolerates H f q) :
    ∀ (n : ℕ) {s : State Validator BlockId Payload} {cs : List (ℕ × Option BlockId)},
    CommitInv cfg U s cs → IsCut U s.disk → s.disk.FullClosed →
    (∀ e ∈ s.syncs, e.2.1 ∈ K) → (∀ e ∈ persists (Node.quiesce cfg n s).2, e ∈ K) →
    CommitInv cfg U (Node.quiesce cfg n s).1 (cs ++ commitsOf (Node.quiesce cfg n s).2) ∧
      IsCut U (Node.quiesce cfg n s).1.disk
  | 0, s, cs, h, hc, _, _, _ => by
    simp only [Node.quiesce, commitsOf, List.filterMap_nil, List.append_nil]; exact ⟨h, hc⟩
  | n + 1, s, cs, h, hc, hcl, hp, hb => by
    rcases quiesce_succ_cases (cfg := cfg) n s with he | he <;> rw [he] at hb ⊢
    · exact h.advance hg hσ hdr ht hc hcl hp hb
    · rw [persists_append] at hb
      obtain ⟨h₁, hc₁⟩ := h.advance hg hσ hdr ht hc hcl hp
        fun e he => hb e (List.mem_append_left _ he)
      have := CommitInv.quiesce hg hσ hdr ht n h₁ hc₁ (closed_advance s hdr hcl)
        (fun e he => hp e (advance_sub (cfg := cfg) s e he))
        fun e he => hb e (List.mem_append_right _ he)
      rw [commitsOf_append, ← List.append_assoc]; exact this

/-- **Settling keeps the invariant, and the disk a cut.** -/
theorem CommitInv.settle (hg : Ground U K cfg.q) (hσ : cfg.σ = boundedSel)
    (hdr : cfg.drops = false) (ht : cfg.p.Tolerates H f q) {s : State Validator BlockId Payload}
    {cs : List (ℕ × Option BlockId)} (h : CommitInv cfg U s cs) (hc : IsCut U s.disk)
    (hcl : s.disk.FullClosed)
    (hp : ∀ e ∈ s.syncs, e.2.1 ∈ K) (hb : ∀ e ∈ persists (Node.settle cfg s).2, e ∈ K) :
    CommitInv cfg U (Node.settle cfg s).1 (cs ++ commitsOf (Node.settle cfg s).2) ∧
      IsCut U (Node.settle cfg s).1.disk :=
  CommitInv.quiesce hg hσ hdr ht (passes cfg s) h hc hcl hp hb

/-- **A step keeps the invariant, and the disk a cut.** -/
theorem CommitInv.step (hg : Ground U K cfg.q) (hσ : cfg.σ = boundedSel)
    (hdr : cfg.drops = false) (ht : cfg.p.Tolerates H f q) {s : State Validator BlockId Payload}
    {cs : List (ℕ × Option BlockId)} (i : Input Validator BlockId Payload)
    (h : CommitInv cfg U s cs) (hc : IsCut U s.disk) (hcl : s.disk.FullClosed)
    (hp : ∀ e ∈ s.syncs, e.2.1 ∈ K) (hd : ∀ e ∈ delivered cfg [i], e ∈ K)
    (hb : ∀ e ∈ persists (Node.step cfg s i).2, e ∈ K) :
    CommitInv cfg U (Node.step cfg s i).1 (cs ++ commitsOf (Node.step cfg s i).2) ∧
      IsCut U (Node.step cfg s i).1.disk := by
  -- a step that settles a state `s₀`, after outputs without decisions
  have hset : ∀ (s₀ : State Validator BlockId Payload)
      (pre : List (Output Validator BlockId Payload)),
      CommitInv cfg U s₀ cs → IsCut U s₀.disk → s₀.disk.FullClosed →
      (∀ e ∈ s₀.syncs, e.2.1 ∈ K) → commitsOf pre = [] →
      Node.step cfg s i = ((Node.settle cfg s₀).1, pre ++ (Node.settle cfg s₀).2) →
      CommitInv cfg U (Node.step cfg s i).1 (cs ++ commitsOf (Node.step cfg s i).2) ∧
        IsCut U (Node.step cfg s i).1.disk := by
    intro s₀ pre h₀ hc₀ hcl₀ hp₀ hpre he
    rw [he] at hb ⊢
    rw [persists_append] at hb
    rw [commitsOf_append, hpre, List.nil_append]
    exact h₀.settle hg hσ hdr ht hc₀ hcl₀ hp₀ fun e he => hb e (List.mem_append_right _ he)
  have hsame : Node.step cfg s i = (s, []) →
      CommitInv cfg U (Node.step cfg s i).1 (cs ++ commitsOf (Node.step cfg s i).2) ∧
        IsCut U (Node.step cfg s i).1.disk := by
    intro he; rw [he]; exact ⟨by simpa [commitsOf] using h, hc⟩
  cases i with
  | start =>
    by_cases h₁ : s.top = none ∧ cfg.Admissible
    · by_cases h₂ : cfg.idOf cfg.genesis ∉ s.disk.ids ∧
          rowValid cfg.q cfg.xp (Function.update s.disk.blk (cfg.idOf cfg.genesis) cfg.genesis)
            cfg.genesis
      · let st := s.disk.insert (cfg.idOf cfg.genesis) cfg.genesis h₂.1
          (fun _ hj => absurd hj (Finset.notMem_empty _))
          (fun j hj => absurd hj (Finset.notMem_empty j))
        have hx : (cfg.idOf cfg.genesis, cfg.genesis) ∈ K :=
          hb _ (by simp only [Node.step, dif_pos h₂, if_pos h₁]; simp [persists])
        have hnil : cfg.genesis.refs ⊆ s.disk.ids := fun _ hj => absurd hj (Finset.notMem_empty _)
        obtain ⟨hU₁, hU₂⟩ := hg.real _ hx (fun _ hj => absurd hj (Finset.notMem_empty _))
          (validAt_of_cut hc h₂.1 hnil h₂.2)
        have hcst : IsCut U st := AllGood.insert hc ⟨hU₁, hU₂⟩
        let gid := cfg.idOf cfg.genesis
        have hk : Keeps s.disk st := (Grows.insert s.disk).keeps
        exact hset { keep s (cfg.idOf cfg.genesis) cfg.genesis h₂.1
            (fun _ hj => absurd hj (Finset.notMem_empty _))
            (fun j hj => absurd hj (Finset.notMem_empty j)) with
            top := some 0, own := some gid, recovering := false }
          (built cfg [(cfg.idOf cfg.genesis, cfg.genesis)]) (h.keeps rfl hk) hcst
          (hcl.insert (hrefs := fun _ hj => absurd hj (Finset.notMem_empty _))
            (hpred := fun j hj => absurd hj (Finset.notMem_empty j))) hp
          (commitsOf_built _) (by simp only [Node.step, dif_pos h₂, if_pos h₁]; rfl)
      · exact hsame (by simp only [Node.step, dif_neg h₂, if_pos h₁])
    · exact hsame (by simp only [Node.step, if_neg h₁])
  | deliver u id b =>
    rcases step_receipt (cfg := cfg) (s := s) (Or.inl ⟨u, id, b, rfl⟩) with
      he | ⟨s₁, pre, hr, hpre, he⟩
    · exact hsame he
    · obtain ⟨L, hL, hdk⟩ := hr.disk
      have hLK : ∀ e ∈ L, e ∈ K := fun e he => by
        rcases hL e he with h | h
        · obtain ⟨x, hx, rfl⟩ := List.mem_map.mp h; exact hp x hx
        · exact hd e h
      have hc₁ : IsCut U s₁.disk := by rw [hdk]; exact AllGood.foldl hg.grounds L hc hLK
      refine hset s₁ pre (h.keeps hr.lo hr.grows.keeps) hc₁
        (by rw [hdk]; exact closed_foldl _ _ hcl) (fun e he => ?_)
        (List.filterMap_eq_nil_iff.mpr fun o ho => ?_) he
      · rcases hr.syncs e he with h | h
        · obtain ⟨x, hx, hxe⟩ := List.mem_map.mp h; rw [← hxe]; exact hp x hx
        · exact hd _ h
      · obtain ⟨_, _, _, _, rfl⟩ := hpre o ho; rfl
  | stream u L =>
    rcases step_receipt (cfg := cfg) (s := s) (Or.inr ⟨u, L, rfl⟩) with he | ⟨s₁, pre, hr, hpre, he⟩
    · exact hsame he
    · obtain ⟨L', hL, hdk⟩ := hr.disk
      have hLK : ∀ e ∈ L', e ∈ K := fun e he => by
        rcases hL e he with h | h
        · obtain ⟨x, hx, rfl⟩ := List.mem_map.mp h; exact hp x hx
        · exact hd e h
      have hc₁ : IsCut U s₁.disk := by rw [hdk]; exact AllGood.foldl hg.grounds L' hc hLK
      refine hset s₁ pre (h.keeps hr.lo hr.grows.keeps) hc₁
        (by rw [hdk]; exact closed_foldl _ _ hcl) (fun e he => ?_)
        (List.filterMap_eq_nil_iff.mpr fun o ho => ?_) he
      · rcases hr.syncs e he with h | h
        · obtain ⟨x, hx, hxe⟩ := List.mem_map.mp h; rw [← hxe]; exact hp x hx
        · exact hd _ h
      · obtain ⟨_, _, _, _, rfl⟩ := hpre o ho; rfl
  | timer r =>
    rw [persists_step_timer] at hb
    rw [step_timer_fst, commitsOf_step_timer]
    exact (h.keeps (s' := { s with fired := fire s r, recovering := false }) rfl
      (Keeps.refl _)).settle hg hσ hdr ht hc hcl hp hb
  | syncRequest peer t fr ids =>
    have he : (Node.step cfg s (.syncRequest peer t fr ids)).1 = s := rfl
    have hc' : commitsOf (Node.step cfg s (.syncRequest peer t fr ids)).2 = [] := by
      simp only [Node.step]; split <;> rfl
    rw [he, hc', List.append_nil]
    exact ⟨h, hc⟩
  | ask peer r =>
    have he : (Node.step cfg s (.ask peer r)).1 = s := rfl
    have hc' : commitsOf (Node.step cfg s (.ask peer r)).2 = [] := by
      simp only [Node.step]; split <;> (try split) <;> rfl
    rw [he, hc', List.append_nil]
    exact ⟨h, hc⟩
  | restart =>
    rw [persists_step_restart] at hb
    rw [step_restart_fst, commitsOf_step_restart]
    exact (h.keeps (s' := { s with recovering := true }) rfl (Keeps.refl _)).settle
      hg hσ hdr ht hc hcl hp hb
  | askProof peer k =>
    have hc' : commitsOf (Node.step cfg s (.askProof peer k)).2 = [] := by
      simp only [Node.step]; split <;> (try split) <;> rfl
    rw [step_askProof_fst, hc', List.append_nil]
    exact ⟨h, hc⟩
  | proof u k L => exact hsame (step_proof_of_false hdr s u k L)

/-- **A run keeps the invariant**, at a record grounding what the node knew. -/
theorem CommitInv.run (hg : Ground U K cfg.q) (hσ : cfg.σ = boundedSel)
    (hdr : cfg.drops = false) (ht : cfg.p.Tolerates H f q) :
    ∀ (is : List (Input Validator BlockId Payload)) {s : State Validator BlockId Payload}
      {cs : List (ℕ × Option BlockId)}, CommitInv cfg U s cs → IsCut U s.disk →
      s.disk.FullClosed →
      (∀ e ∈ s.syncs, e.2.1 ∈ K) → (∀ e ∈ delivered cfg is, e ∈ K) →
      (∀ e ∈ persists (Node.run cfg s is).2, e ∈ K) →
      CommitInv cfg U (Node.run cfg s is).1 (cs ++ commitsOf (Node.run cfg s is).2)
  | [], s, cs, h, _, _, _, _, _ => by simpa [Node.run, commitsOf] using h
  | i :: is, s, cs, h, hc, hcl, hp, hd, hb => by
    simp only [Node.run] at hb ⊢
    rw [persists_append] at hb
    rw [delivered_cons] at hd
    obtain ⟨h₁, hc₁⟩ := h.step hg hσ hdr ht i hc hcl hp
      (fun e he => hd e (List.mem_append_left _ he))
      (fun e he => hb e (List.mem_append_left _ he))
    have hp₁ : ∀ e ∈ (Node.step cfg s i).1.syncs, e.2.1 ∈ K := fun e he => by
      rcases step_syncs s i e he with h | h
      · obtain ⟨x, hx, hxe⟩ := List.mem_map.mp h; rw [← hxe]; exact hp x hx
      · exact hd _ (List.mem_append_left _ h)
    have := CommitInv.run hg hσ hdr ht is h₁ hc₁ (closed_step s i hdr hcl) hp₁
      (fun e he => hd e (List.mem_append_right _ he))
      (fun e he => hb e (List.mem_append_right _ he))
    rw [commitsOf_append, ← List.append_assoc]
    exact this

end Node

end LeanDag
