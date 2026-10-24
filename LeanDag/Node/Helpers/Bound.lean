import LeanDag.Node.Helpers.SyncInv
/-!
# The blocks a node holds a round

`docs/validator.md` §3.4, V13. Two blocks of an author other than the
node at one round on its disk convict the author (`Caught`), and at most
two blocks of such an author at one round are referenced by no block of
the disk (`Loose`). A step adds at most one such unreferenced block of an
author, and none of a convicted author, since it takes a block of an
author only in the author's own name, as an announcement or the block of
the author's sync, and the other blocks of a piece taken in are
referenced by blocks taken in with them (`Tame.step`).
-/

namespace LeanDag

namespace Node

variable {Validator BlockId Payload : Type} [Fintype Validator] [DecidableEq Validator]
variable [LinearOrder BlockId]

variable (cfg : Config Validator BlockId Payload)

/-- **Twins convict**: two blocks of an author other than the node at one
round on the disk convict the author. -/
def Caught (s : State Validator BlockId Payload) : Prop :=
  ∀ i ∈ s.disk.ids, ∀ j ∈ s.disk.ids, i ≠ j →
    (s.disk.blk i).creator = (s.disk.blk j).creator →
    (s.disk.blk i).round = (s.disk.blk j).round → (s.disk.blk i).creator ≠ cfg.me →
    (s.disk.blk i).creator ∈ s.detected

variable {cfg} in
/-- The blocks of `X` at round `k` on a store that no block of it
references. -/
def unrefAt (st : Store Validator BlockId Payload) (X : Validator) (k : ℕ) : Finset BlockId :=
  st.ids.filter fun i =>
    (st.blk i).creator = X ∧ (st.blk i).round = k ∧ ∀ j ∈ st.ids, i ∉ (st.blk j).refs

/-- **Two loose blocks**: at most two blocks of an author other than the
node at one round on the disk are referenced by no block of it. -/
def Loose (s : State Validator BlockId Payload) : Prop :=
  ∀ X, X ≠ cfg.me → ∀ k, (unrefAt s.disk X k).card ≤ 2

/-- **A tame state**: twins convict, and two loose blocks. -/
def Tame (s : State Validator BlockId Payload) : Prop :=
  Caught cfg s ∧ Loose cfg s

variable {cfg} in
/-- **The syncs are with peers not convicted.** -/
def Free (s : State Validator BlockId Payload) : Prop :=
  ∀ e ∈ s.syncs, e.1 ∉ s.detected

variable {cfg}

omit [Fintype Validator] in
/-- An author not convicted, other than the node, has at most one block a
round on the disk of a state where twins convict. -/
theorem Caught.card_le_one {s : State Validator BlockId Payload} (h : Caught cfg s)
    {X : Validator} (hX : X ∉ s.detected) (hme : X ≠ cfg.me) (k : ℕ) :
    (s.disk.ids.filter fun i => (s.disk.blk i).creator = X ∧ (s.disk.blk i).round = k).card ≤ 1 :=
    by
  refine Finset.card_le_one.mpr fun a ha b hb => ?_
  by_contra hab
  obtain ⟨ha, hac, har⟩ := Finset.mem_filter.mp ha
  obtain ⟨hb, hbc, hbr⟩ := Finset.mem_filter.mp hb
  exact hX (hac ▸ h a ha b hb hab (hac.trans hbc.symm) (har.trans hbr.symm) (hac ▸ hme))

omit [Fintype Validator] in
/-- **Loose blocks after growth**: if the new blocks of the grown disk
that no block references number at most one for each author, and none for
a convicted author, two loose blocks stay two. -/
theorem Loose.of_new {s s' : State Validator BlockId Payload} (hg : Grows s.disk s'.disk)
    (hc : Caught cfg s) (hl : Loose cfg s)
    (hnew : ∀ X, X ≠ cfg.me → ∀ k,
      ((unrefAt s'.disk X k).filter (· ∉ s.disk.ids)).card ≤ 1 ∧
        (X ∈ s.detected → ∀ i ∈ unrefAt s'.disk X k, i ∈ s.disk.ids)) :
    Loose cfg s' := by
  intro X hme k
  set U := unrefAt s'.disk X k
  have hold : U.filter (· ∈ s.disk.ids) ⊆ unrefAt s.disk X k := by
    intro i hi
    obtain ⟨hiU, his⟩ := Finset.mem_filter.mp hi
    obtain ⟨-, hic, hir, hiu⟩ := Finset.mem_filter.mp hiU
    rw [hg.2.2 i his] at hic hir
    refine Finset.mem_filter.mpr ⟨his, hic, hir, fun j hj => ?_⟩
    rw [← hg.2.2 j hj]
    exact hiu j (hg.1 hj)
  have hsplit := Finset.card_filter_add_card_filter_not (s := U) (· ∈ s.disk.ids)
  by_cases hX : X ∈ s.detected
  · have hall : U.filter (· ∈ s.disk.ids) = U :=
      Finset.filter_true_of_mem fun i hi => (hnew X hme k).2 hX i hi
    rw [← hall]
    exact (Finset.card_le_card hold).trans (hl X hme k)
  · have h₁ : (unrefAt s.disk X k).card ≤ 1 :=
      (Finset.card_le_card (Finset.monotone_filter_right _ fun i _ h => ⟨h.1, h.2.1⟩)).trans
        (hc.card_le_one hX hme k)
    have h₂ : (U.filter (· ∉ s.disk.ids)).card ≤ 1 := (hnew X hme k).1
    have h₃ := Finset.card_le_card hold
    omega

omit [Fintype Validator] in
/-- **Accepting a block keeps twins convicting.** -/
theorem Caught.accept {s : State Validator BlockId Payload} (h : Caught cfg s) (id : BlockId)
    (b : Block Validator BlockId Payload) : Caught cfg (Node.accept cfg s id b) := by
  unfold Node.accept
  split
  · rename_i hc
    dsimp only
    simp only [keep_disk]
    have hd := s.mirrors.checks_pick.mp hc.2
    set st' := s.disk.insert id b hc.1 hd.1 hd.2.1 with hst'
    have hg : Grows s.disk st' := Grows.insert s.disk
    have hk : st'.blk id = b := by rw [hst', Store.insert_blk, if_pos rfl]
    -- a new block with an old twin is convicted by the twin
    have hnew : ∀ j ∈ s.disk.ids, (s.disk.blk j).creator = b.creator →
        (s.disk.blk j).round = b.round → b.creator ∈ named (evidenceOf cfg s.disk id b) := by
      intro j hj hjc hjr
      have hjS : j ∈ (s.disk.atRound b.round).filter fun i => (s.disk.blk i).creator = b.creator :=
        Finset.mem_filter.mpr ⟨Store.mem_atRound.mpr ⟨hj, hjr⟩, hjc⟩
      cases ht : twinOf s.disk b with
      | none =>
        unfold twinOf at ht
        rw [Scheme.leastOf_eq_none ht] at hjS
        exact absurd hjS (Finset.notMem_empty _)
      | some i =>
        have hi := Finset.mem_filter.mp (mem_of_leastOf ht)
        rw [Store.mem_atRound] at hi
        refine Finset.mem_image.mpr ⟨(b.creator, i, id), Finset.mem_filter.mpr
          ⟨Finset.mem_union_left _ ?_, fun e => hc.1 (by simp only at e; exact e ▸ hi.1.1)⟩, rfl⟩
        simp [ht]
    intro i hi j hj hij hcr hrd hme
    change i ∈ st'.ids at hi
    change j ∈ st'.ids at hj
    change (st'.blk i).creator = (st'.blk j).creator at hcr
    change (st'.blk i).round = (st'.blk j).round at hrd
    change (st'.blk i).creator ≠ cfg.me at hme
    change (st'.blk i).creator ∈ s.detected ∪ named (evidenceOf cfg s.disk id b)
    rw [hst', Store.insert_ids] at hi hj
    by_cases hi' : i = id
    · have hj' : j ∈ s.disk.ids :=
        (Finset.mem_insert.mp hj).resolve_left fun e => hij (hi'.trans e.symm)
      rw [hi', hk, hg.2.2 j hj'] at hcr hrd
      rw [hi', hk]
      exact Finset.mem_union_right _ (hnew j hj' hcr.symm hrd.symm)
    · have hi'' : i ∈ s.disk.ids := (Finset.mem_insert.mp hi).resolve_left hi'
      by_cases hj' : j = id
      · rw [hj', hk, hg.2.2 i hi''] at hcr hrd
        rw [hg.2.2 i hi'', hcr]
        exact Finset.mem_union_right _ (hnew i hi'' hcr hrd)
      · have hj'' : j ∈ s.disk.ids := (Finset.mem_insert.mp hj).resolve_left hj'
        rw [hg.2.2 i hi'', hg.2.2 j hj''] at hcr hrd
        rw [hg.2.2 i hi''] at hme ⊢
        exact Finset.mem_union_left _ (h i hi'' j hj'' hij hcr hrd hme)
  · exact h

omit [Fintype Validator] in
theorem Caught.absorb {s : State Validator BlockId Payload} (h : Caught cfg s) :
    ∀ L : List (BlockId × Block Validator BlockId Payload), Caught cfg (Node.absorb cfg s L)
  | [] => h
  | x :: L => by
    unfold Node.absorb
    rw [List.foldl_cons]
    exact (h.accept x.1 x.2).absorb L

omit [Fintype Validator] in
theorem Caught.of_same {s s' : State Validator BlockId Payload} (h : Caught cfg s)
    (hd : s'.disk = s.disk) (hdet : s.detected ⊆ s'.detected) : Caught cfg s' := by
  intro i hi j hj hij hc hr hme
  rw [hd] at hi hj hc hr hme ⊢
  exact hdet (h i hi j hj hij hc hr hme)

omit [Fintype Validator] in
theorem Tame.of_same {s s' : State Validator BlockId Payload} (h : Tame cfg s)
    (hd : s'.disk = s.disk) (hdet : s.detected ⊆ s'.detected) : Tame cfg s' :=
  ⟨h.1.of_same hd hdet, fun X hX k => by rw [hd]; exact h.2 X hX k⟩

omit [Fintype Validator] in
/-- **A block new after taking blocks in** is one of them, as taken. -/
theorem foldl_new {i : BlockId} : ∀ (L : List (BlockId × Block Validator BlockId Payload))
    (st : Store Validator BlockId Payload),
    i ∈ (L.foldl (fun s e => acceptOn cfg s e.1 e.2) st).ids → i ∉ st.ids →
    ∃ e ∈ L, e.1 = i ∧ (L.foldl (fun s e => acceptOn cfg s e.1 e.2) st).blk i = e.2
  | [], _, h, hn => absurd h hn
  | x :: L, st, h, hn => by
    rw [List.foldl_cons] at h ⊢
    by_cases h₁ : i ∈ (acceptOn cfg st x.1 x.2).ids
    · have hx : i = x.1 ∧ (acceptOn cfg st x.1 x.2).blk i = x.2 := by
        unfold acceptOn at h₁ ⊢
        split at h₁
        · rename_i hc
          rw [dif_pos hc, Store.insert_blk]
          rw [Store.insert_ids] at h₁
          have : i = x.1 := (Finset.mem_insert.mp h₁).resolve_right hn
          exact ⟨this, if_pos this⟩
        · exact absurd h₁ hn
      refine ⟨x, List.mem_cons_self, hx.1.symm, ?_⟩
      rw [(Grows.foldl (cfg := cfg) L _).2.2 i h₁, hx.2]
    · obtain ⟨e, he, h₂⟩ := foldl_new L _ h h₁
      exact ⟨e, List.mem_cons_of_mem _ he, h₂⟩

omit [Fintype Validator] in
/-- **A tame state grown**: the new blocks of the grown disk that no block
references, other than the node's, are by authors not convicted, at most
one for each. -/
theorem Tame.grow {s s' : State Validator BlockId Payload} (h : Tame cfg s)
    (hg : Grows s.disk s'.disk) (hc : Caught cfg s')
    (hnew : ∀ i ∈ s'.disk.ids, i ∉ s.disk.ids → (∀ j ∈ s'.disk.ids, i ∉ (s'.disk.blk j).refs) →
      (s'.disk.blk i).creator ≠ cfg.me → (s'.disk.blk i).creator ∉ s.detected ∧
        ∀ i' ∈ s'.disk.ids, i' ∉ s.disk.ids → (∀ j ∈ s'.disk.ids, i' ∉ (s'.disk.blk j).refs) →
          (s'.disk.blk i').creator = (s'.disk.blk i).creator → i' = i) :
    Tame cfg s' := by
  refine ⟨hc, Loose.of_new hg h.1 h.2 fun X hme k => ⟨?_, fun hX i hi => ?_⟩⟩
  · refine Finset.card_le_one.mpr fun a ha b hb => ?_
    obtain ⟨ha, han⟩ := Finset.mem_filter.mp ha
    obtain ⟨hb, hbn⟩ := Finset.mem_filter.mp hb
    obtain ⟨ha', hac, -, hau⟩ := Finset.mem_filter.mp ha
    obtain ⟨hb', hbc, -, hbu⟩ := Finset.mem_filter.mp hb
    exact ((hnew a ha' han hau (hac ▸ hme)).2 b hb' hbn hbu (hbc.trans hac.symm)).symm
  · obtain ⟨hi', hic, -, hiu⟩ := Finset.mem_filter.mp hi
    by_contra hin
    exact (hnew i hi' hin hiu (hic ▸ hme)).1 (hic ▸ hX)

omit [Fintype Validator] in
/-- **Taking blocks in, at most one of each author other than the node and
none of a convicted author**, keeps a state tame. -/
theorem Tame.absorb {s : State Validator BlockId Payload} (h : Tame cfg s)
    {L : List (BlockId × Block Validator BlockId Payload)}
    (hone : ∀ e ∈ L, ∀ e' ∈ L, e.2.creator = e'.2.creator → e.2.creator ≠ cfg.me → e.1 = e'.1)
    (hdet : ∀ e ∈ L, e.2.creator ≠ cfg.me → e.2.creator ∉ s.detected) :
    Tame cfg (Node.absorb cfg s L) := by
  have hd : (Node.absorb cfg s L).disk = L.foldl (fun st e => acceptOn cfg st e.1 e.2) s.disk :=
    absorb_disk _ _
  refine h.grow (Grows.absorb s L) (h.1.absorb L) fun i hi hin _ hme => ?_
  rw [hd] at hi hme ⊢
  obtain ⟨e, he, rfl, hb⟩ := foldl_new L s.disk hi hin
  rw [hb] at hme ⊢
  refine ⟨hdet e he hme, fun i' hi' hin' _ hc => ?_⟩
  obtain ⟨e', he', rfl, hb'⟩ := foldl_new L s.disk hi' hin'
  rw [hb'] at hc
  exact hone e' he' e he hc (hc ▸ hme)

/-! ## Settling -/

variable (cfg) in
/-- **A tame state with free syncs of their shape.** -/
def Steady (s : State Validator BlockId Payload) : Prop :=
  Tame cfg s ∧ Free s ∧ SyncsOn s

omit [Fintype Validator] in
theorem Steady.of_same {s s' : State Validator BlockId Payload} (h : Steady cfg s)
    (hd : s'.disk = s.disk) (hdet : s'.detected = s.detected) (hs : s'.syncs = s.syncs) :
    Steady cfg s' :=
  ⟨h.1.of_same hd hdet.symm.subset, fun e he => by rw [hdet]; exact h.2.1 e (hs ▸ he),
    ⟨by rw [hs]; exact h.2.2.1, fun e he => h.2.2.2 e (hs ▸ he)⟩⟩

omit [Fintype Validator] in
/-- **The node's own block added** keeps the state steady. -/
theorem Steady.own {s s' : State Validator BlockId Payload} (h : Steady cfg s) {id : BlockId}
    {b : Block Validator BlockId Payload} {hnew hrefs hpred}
    (hd : s'.disk = s.disk.insert id b hnew hrefs hpred) (hbc : b.creator = cfg.me)
    (hdet : s'.detected = s.detected) (hs : s'.syncs = s.syncs) : Steady cfg s' := by
  have hg : Grows s.disk s'.disk := hd ▸ Grows.insert s.disk
  have hk : ∀ i ∈ s'.disk.ids, (s'.disk.blk i).creator ≠ cfg.me → i ∈ s.disk.ids ∧
      s'.disk.blk i = s.disk.blk i := by
    intro i hi hme
    rw [hd, Store.insert_ids] at hi
    rw [hd, Store.insert_blk] at hme ⊢
    by_cases hid : i = id
    · rw [if_pos hid] at hme; exact absurd hbc hme
    · rw [if_neg hid]; exact ⟨(Finset.mem_insert.mp hi).resolve_left hid, rfl⟩
  refine ⟨⟨fun i hi j hj hij hc hr hme => ?_, fun X hX k => ?_⟩,
    fun e he => by rw [hdet]; exact h.2.1 e (hs ▸ he),
    ⟨by rw [hs]; exact h.2.2.1, fun e he => h.2.2.2 e (hs ▸ he)⟩⟩
  · obtain ⟨hi', hbi⟩ := hk i hi hme
    obtain ⟨hj', hbj⟩ := hk j hj (hc ▸ hme)
    rw [hbi, hbj] at hc hr
    rw [hbi] at hme ⊢
    rw [hdet]
    exact h.1.1 i hi' j hj' hij hc hr hme
  · refine (Finset.card_le_card fun i hi => ?_).trans (h.1.2 X hX k)
    obtain ⟨hi', hic, hir, hiu⟩ := Finset.mem_filter.mp hi
    obtain ⟨hi'', hbi⟩ := hk i hi' (hic ▸ hX)
    rw [hbi] at hic hir
    exact Finset.mem_filter.mpr ⟨hi'', hic, hir, fun j hj => by
      rw [← hg.2.2 j hj]; exact hiu j (hg.1 hj)⟩

omit [Fintype Validator] in
theorem Steady.tryBuild {s s' : State Validator BlockId Payload}
    {out : List (Output Validator BlockId Payload)} (h : Steady cfg s)
    (hb : Node.tryBuild cfg s = some (s', out)) : Steady cfg s' := by
  obtain ⟨_, _, _, _, _, _, -, -, hbc, -, -, hd, -, hs, -, -⟩ := tryBuild_some hb
  exact h.own hd hbc (tryBuild_detected hb).1 hs

omit [Fintype Validator] in
theorem Steady.progress : ∀ (fuel : ℕ) {s : State Validator BlockId Payload}, Steady cfg s →
    Steady cfg (Node.progress cfg fuel s).1
  | 0, _, h => h
  | fuel + 1, s, h => by
    unfold Node.progress
    split
    · rename_i s₁ out hb
      exact Steady.progress fuel (h.tryBuild hb)
    · exact h

omit [Fintype Validator] in
theorem Steady.decideStep {s : State Validator BlockId Payload} (h : Steady cfg s) :
    Steady cfg (Node.decideStep cfg s).1 := by
  refine h.of_same (decideStep_disk s) ?_ (decideStep_syncs s)
  unfold Node.decideStep
  dsimp only
  split
  · simp
  · rfl

omit [Fintype Validator] in
theorem Steady.tidy {s : State Validator BlockId Payload} (h : Tame cfg s) (hs : SyncsOn s) :
    Steady cfg (Node.tidy s) := by
  refine ⟨h.of_same (tidy_eq _).1 (tidy_eq _).2.2.2.2.2.2.2.2.2.1.symm.subset, fun e he => ?_,
    hs.sublist List.filter_sublist⟩
  have := (List.mem_filter.mp he).2
  simp only [decide_eq_true_eq] at this
  exact this.2

omit [Fintype Validator] in
theorem Steady.flushSyncs : ∀ (fuel : ℕ) {s : State Validator BlockId Payload}, Steady cfg s →
    Steady cfg (Node.flushSyncs cfg fuel s)
  | 0, _, h => h
  | fuel + 1, s, h => by
    unfold Node.flushSyncs
    dsimp only
    split
    · exact h
    · refine Steady.flushSyncs fuel (Steady.tidy ?_ ((h.2.2.sublist (Thins.absorb (cfg := cfg) s
        _).sub)))
      have hmem : ∀ e ∈ (s.syncs.partition fun e => ready cfg s e.2.1).1.map (·.2.1),
          ∃ x ∈ s.syncs, x.2.1 = e := fun e he => by
        obtain ⟨x, hx, rfl⟩ := List.mem_map.mp he
        rw [List.partition_eq_filter_filter] at hx
        exact ⟨x, List.mem_of_mem_filter hx, rfl⟩
      refine h.1.absorb (fun e he e' he' hc _ => ?_) (fun e he _ => ?_)
      · obtain ⟨x, hx, rfl⟩ := hmem e he
        obtain ⟨x', hx', rfl⟩ := hmem e' he'
        rw [(h.2.2.2 x hx).2, (h.2.2.2 x' hx').2] at hc
        rw [h.2.2.eq hx hx' hc]
      · obtain ⟨x, hx, rfl⟩ := hmem e he
        rw [(h.2.2.2 x hx).2]
        exact h.2.1 x hx

omit [Fintype Validator] in
theorem Steady.advance {s : State Validator BlockId Payload} (h : Steady cfg s) :
    Steady cfg (Node.advance cfg s).1 := by
  obtain ⟨a, ha⟩ := arm_eq (cfg := cfg) (Node.pass cfg s).1
  have hp : Steady cfg (Node.pass cfg s).1 :=
    Steady.flushSyncs _ (Steady.decideStep (Steady.progress _ h))
  unfold Node.advance
  dsimp only
  rw [ha]
  exact hp.of_same rfl rfl rfl

omit [Fintype Validator] in
theorem Steady.settle {s : State Validator BlockId Payload} (h : Steady cfg s) :
    Steady cfg (Node.settle cfg s).1 :=
  (quiesce_rel (P := Steady cfg) (R := fun _ _ _ => True) (fun _ => trivial)
    (fun _ _ _ _ _ _ _ => trivial) (fun _ hs => ⟨trivial, hs.advance⟩) _ s h).2

/-! ## A step -/

omit [Fintype Validator] [DecidableEq Validator] in
/-- **The walk through a piece from a held block**, on a store reading as a
block map the piece agrees with: what it met is held, and is the block or
a reference the piece gives a block it met. -/
theorem pieceAt_held {g : BlockId → Block Validator BlockId Payload}
    {L : List (BlockId × Block Validator BlockId Payload)} {t : BlockId}
    {st : Store Validator BlockId Payload} (hst : ReadsAs g st) (hL : ∀ e ∈ L, e.2 = g e.1)
    (ht : t ∈ st.ids) : ∀ k,
    (∀ y ∈ (pieceAt L t k).1, y = t ∨ ∃ z ∈ (pieceAt L t k).2, y ∈ pieceRefs L z) ∧
    (∀ x ∈ (pieceAt L t k).2, x ∈ st.ids ∧ (x = t ∨ ∃ z ∈ (pieceAt L t k).2, x ∈ pieceRefs L z))
  | 0 => ⟨fun y hy => Or.inl (List.mem_singleton.mp hy), fun _ h => absurd h List.not_mem_nil⟩
  | k + 1 => by
    obtain ⟨h₁, h₂⟩ := pieceAt_held hst hL ht k
    rw [pieceAt_succ]
    set w := pieceAt L t k
    unfold pieceLevel
    dsimp only
    set front := (w.1.filter fun x => decide (x ∈ L.map Prod.fst) && decide (x ∉ w.2)).dedup
    have hfront : ∀ x ∈ front, x ∈ w.1 ∧ x ∈ L.map Prod.fst := by
      intro x hx
      have := List.mem_filter.mp (List.mem_dedup.mp hx)
      simp only [Bool.and_eq_true, decide_eq_true_eq] at this
      exact ⟨this.1, this.2.1⟩
    -- a reference the piece gives a held block is held
    have href : ∀ z ∈ w.2, ∀ y ∈ pieceRefs L z, y ∈ st.ids := by
      intro z hz y hy
      have hzL : z ∈ L.map Prod.fst := by
        unfold pieceRefs at hy
        cases hf : L.find? (fun e => decide (e.1 = z)) with
        | none => rw [hf] at hy; exact absurd hy List.not_mem_nil
        | some e =>
          have := List.find?_some hf
          simp only [decide_eq_true_eq] at this
          exact this ▸ List.mem_map_of_mem (List.mem_of_find?_eq_some hf)
      have hzs := (h₂ z hz).1
      have hy' := (pieceRefs_of_map L hL hzL).mp hy
      rw [← hst z hzs] at hy'
      exact st.complete z hzs y hy'
    refine ⟨fun y hy => ?_, fun x hx => ?_⟩
    · obtain ⟨z, hz, hyz⟩ := List.mem_flatMap.mp hy
      exact Or.inr ⟨z, List.mem_append_right _ hz, hyz⟩
    · rcases List.mem_append.mp hx with hx | hx
      · obtain ⟨hxs, ho⟩ := h₂ x hx
        refine ⟨hxs, ho.imp_right fun ⟨z, hz, hxz⟩ => ⟨z, List.mem_append_left _ hz, hxz⟩⟩
      · rcases h₁ x (hfront x hx).1 with rfl | ⟨z, hz, hxz⟩
        · exact ⟨ht, Or.inl rfl⟩
        · exact ⟨href z hz x hxz, Or.inr ⟨z, List.mem_append_left _ hz, hxz⟩⟩

omit [Fintype Validator] in
/-- **A piece taken in header first, read on a store reading as a block map
the piece agrees with**: each new block other than the sync's block is
referenced by a block of the store. -/
theorem takeIn_referenced {g : BlockId → Block Validator BlockId Payload}
    {s : State Validator BlockId Payload} {t : BlockId × Block Validator BlockId Payload}
    {L : List (BlockId × Block Validator BlockId Payload)}
    (hst : ReadsAs g (Node.absorb cfg s (inHistory cfg t L)).disk)
    (hL : ∀ e ∈ hashed cfg L, g e.1 = e.2)
    (ht : t.1 ∈ (Node.absorb cfg s (inHistory cfg t L)).disk.ids)
    {i : BlockId} (hi : i ∈ (Node.absorb cfg s (inHistory cfg t L)).disk.ids)
    (hin : i ∉ s.disk.ids) (hit : i ≠ t.1) :
    ∃ z ∈ (Node.absorb cfg s (inHistory cfg t L)).disk.ids,
      i ∈ ((Node.absorb cfg s (inHistory cfg t L)).disk.blk z).refs := by
  set st := (Node.absorb cfg s (inHistory cfg t L)).disk
  have hd : st = (inHistory cfg t L).foldl (fun st e => acceptOn cfg st e.1 e.2) s.disk :=
    absorb_disk _ _
  rw [hd] at hi
  obtain ⟨e, he, rfl, -⟩ := foldl_new _ s.disk hi hin
  have hf := ((mem_inHistory L).mp he).2.2
  have hL' : ∀ e ∈ hashed cfg L, e.2 = g e.1 := fun e he => (hL e he).symm
  rcases (pieceAt_held hst hL' ht _).2 e.1 hf with ⟨-, het | ⟨z, hz, hez⟩⟩
  · exact absurd het hit
  · have hzs := ((pieceAt_held hst hL' ht _).2 z hz).1
    have hzL : z ∈ (hashed cfg L).map Prod.fst := by
      unfold pieceRefs at hez
      cases hf : (hashed cfg L).find? (fun e => decide (e.1 = z)) with
      | none => rw [hf] at hez; exact absurd hez List.not_mem_nil
      | some e =>
        have := List.find?_some hf
        simp only [decide_eq_true_eq] at this
        exact this ▸ List.mem_map_of_mem (List.mem_of_find?_eq_some hf)
    refine ⟨z, hzs, ?_⟩
    rw [hst z hzs]
    exact (pieceRefs_of_map _ hL' hzL).mp hez

omit [Fintype Validator] in
/-- **A piece taken in header first keeps the state steady**, on a store
reading as a block map that the piece and the sync's block agree with. -/
theorem Steady.takeIn {g : BlockId → Block Validator BlockId Payload}
    {s : State Validator BlockId Payload} (h : Steady cfg s) {u : Validator}
    {t : BlockId × Block Validator BlockId Payload} {A : List BlockId} (he : (u, t, A) ∈ s.syncs)
    {L : List (BlockId × Block Validator BlockId Payload)}
    (hst : ReadsAs g (Node.takeIn cfg s t (inHistory cfg t L)).disk)
    (hL : ∀ e ∈ hashed cfg L, g e.1 = e.2) (ht : g t.1 = t.2) :
    Steady cfg (Node.takeIn cfg s t (inHistory cfg t L)) := by
  unfold Node.takeIn at hst ⊢
  split
  · rename_i hc
    rw [if_pos hc] at hst
    have hst' : ReadsAs g (Node.absorb cfg s (inHistory cfg t L)).disk := hst
    refine Steady.tidy (h.1.grow (Grows.absorb s _) (h.1.1.absorb _) fun i hi hin hiu _ => ?_)
      (h.2.2.sublist (Thins.absorb (cfg := cfg) s _).sub)
    -- the only new block no block references is the sync's block
    have hone : ∀ i ∈ (Node.absorb cfg s (inHistory cfg t L)).disk.ids, i ∉ s.disk.ids →
        (∀ j ∈ (Node.absorb cfg s (inHistory cfg t L)).disk.ids,
          i ∉ ((Node.absorb cfg s (inHistory cfg t L)).disk.blk j).refs) → i = t.1 := by
      intro i hi hin hiu
      by_contra hit
      obtain ⟨z, hz, hiz⟩ := takeIn_referenced hst' hL hc.2 hi hin hit
      exact hiu z hz hiz
    obtain rfl := hone i hi hin hiu
    have hb : (Node.absorb cfg s (inHistory cfg t L)).disk.blk t.1 = t.2 := by
      rw [hst' t.1 hi, ht]
    rw [hb, (h.2.2.2 _ he).2]
    exact ⟨h.2.1 _ he, fun i' hi' hin' hiu' _ => hone i' hi' hin' hiu'⟩
  · exact h

/-- **A step keeps the state steady**, on a disk after it reading as a block
map that what the step is given and the syncs' blocks agree with. -/
theorem Steady.step {g : BlockId → Block Validator BlockId Payload}
    {s : State Validator BlockId Payload} (h : Steady cfg s) (inp : Input Validator BlockId Payload)
    (hR : ReadsAs g (Node.step cfg s inp).1.disk)
    (hP : ∀ e ∈ delivered cfg [inp], g e.1 = e.2)
    (hS : ∀ e ∈ s.syncs, g e.2.1.1 = e.2.1.2) : Steady cfg (Node.step cfg s inp).1 := by
  cases inp with
  | start =>
    rw [step_start_eq]
    split_ifs with h₁ h₂
    · exact Steady.settle (h.own (hrefs := fun _ hj => absurd hj (Finset.notMem_empty _))
        (hpred := fun j hj => absurd hj (Finset.notMem_empty j)) keep_disk rfl rfl rfl)
    · exact h
    · exact h
  | deliver u id b =>
    rw [step_deliver_eq]
    split_ifs with hg hr hc
    · refine Steady.settle (Steady.tidy ?_ (h.2.2.sublist (Thins.accept (cfg := cfg) s id b).sub))
      have hT := h.1.absorb (L := [(id, b)])
        (fun e he e' he' _ _ => by
          rw [List.mem_singleton] at he he'; rw [he, he'])
        (fun e he _ => by
          rw [List.mem_singleton] at he; rw [he, hg.2.1]; exact hg.2.2.2.1)
      exact hT
    · refine Steady.settle ⟨h.1.of_same rfl subset_rfl, fun e he => ?_, h.2.2.fresh hg.2.1⟩
      rcases List.mem_cons.mp he with rfl | he
      · exact hg.2.2.2.1
      · exact h.2.1 e (List.mem_of_mem_filter he)
    · exact h
    · exact h
  | stream u L =>
    have hL : ∀ e ∈ hashed cfg L, g e.1 = e.2 := fun e he =>
      hP e (by simpa [delivered, hashed] using he)
    cases hf : s.syncs.find? fun e => decide (e.1 = u) with
    | none =>
      have : Node.step cfg s (.stream u L) = (s, []) := by simp only [Node.step, hf]
      rw [this]; exact h
    | some e =>
      have he := List.mem_of_find?_eq_some hf
      have hp := List.find?_some hf
      simp only [decide_eq_true_eq] at hp
      obtain ⟨w, t, A⟩ := e
      simp only at hp
      subst hp
      have ht := hS _ he
      rcases step_stream_cases (cfg := cfg) h.2.2 he L with ⟨-, hs⟩ | ⟨-, hs⟩
      · rw [hs] at hR ⊢
        exact Steady.settle (h.takeIn he (hR.of_grows (Grows.settle _)) hL ht)
      · set s₁ := Node.takeIn cfg s t (inHistory cfg t L) with hs₁
        set s₂ : State Validator BlockId Payload := { s₁ with
          syncs := s₁.syncs.map fun x =>
            if x.1 = w then (w, t, (A ++ missingIn s₁ (t :: inHistory cfg t L)).dedup) else x }
          with hs₂
        have hs' : (Node.step cfg s (.stream w L)).1 = (Node.settle cfg s₂).1 := by rw [hs]
        rw [hs'] at hR ⊢
        have hg : Grows s₁.disk (Node.settle cfg s₂).1.disk := Grows.settle s₂
        have h₁ := h.takeIn he (hR.of_grows hg) hL ht
        refine Steady.settle ⟨h₁.1.of_same rfl subset_rfl, fun x hx => ?_,
          h.2.2.extend (Thins.takeIn (cfg := cfg) s t _).sub he⟩
        obtain ⟨x', hx', hxe⟩ := List.mem_map.mp hx
        rw [← hxe]
        split
        · rename_i hxu
          rw [← hxu]; exact h₁.2.1 x' hx'
        · exact h₁.2.1 x' hx'
  | timer r =>
    rw [step_timer_fst]
    exact Steady.settle (h.of_same rfl rfl rfl)
  | syncRequest peer t fr ids => exact h
  | ask peer r => exact h
  | restart =>
    rw [step_restart_fst]
    exact Steady.settle (h.of_same rfl rfl rfl)

/-! ## Along a trace -/

section Trace

variable {cfg : Config Validator BlockId Payload} {H : Finset Validator}
variable {tr : Trace Validator BlockId Payload}

/-- **An honest node is steady** before every event, with an injective
hash. -/
theorem steady_before (hinj : Converge.HashInjective cfg H tr) {v : Validator} (hv : v ∈ H) :
    ∀ i, Steady (cfg.at v) (stateBefore cfg tr i v)
  | 0 => by
    have hd : (stateBefore cfg tr 0 v).disk.ids = ∅ := by
      simp [stateBefore, inputsBefore, run, State.init, Store.empty]
    have hs : (stateBefore cfg tr 0 v).syncs = [] := by
      simp [stateBefore, inputsBefore, run, State.init]
    refine ⟨⟨fun i hi => by rw [hd] at hi; exact absurd hi (Finset.notMem_empty _),
      fun X _ k => ?_⟩, fun e he => by rw [hs] at he; exact absurd he List.not_mem_nil,
      Converge.syncsOn_before v 0⟩
    have : unrefAt (stateBefore cfg tr 0 v).disk X k = ∅ := by
      unfold unrefAt; rw [hd]; rfl
    rw [this]; exact Nat.zero_le _
  | i + 1 => by
    by_cases he : ∃ inp, tr[i]? = some (v, inp)
    · obtain ⟨inp, hi⟩ := he
      have hR := Converge.reads_before hinj hv (i + 1)
      rw [Converge.step_before hi] at hR ⊢
      exact (steady_before hinj hv i).step inp hR
        (fun x hx => Converge.gT_of_known hinj (Or.inl ⟨i, v, inp, hi, hv, hx⟩))
        (Converge.pend_before hinj hv i)
    · rw [Converge.same_before fun inp h => he ⟨inp, h⟩]; exact steady_before hinj hv i

end Trace

end Node

end LeanDag
