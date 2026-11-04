import LeanDag.Node.Helpers.Bound
import LeanDag.Node.Helpers.Wait
/-!
# The blocks a node that drops holds a round

`docs/validator.md` §3.4, V13 with dropping. Above its floor a node that
drops checks every block it keeps, and a block referencing one lies a round
above it, so dropping and stripping below the floor leave the references of
the blocks above it as they were (`blk_refs_above`). Counting only stored
references, at most two blocks of an author other than the node at one round
above the floor are referenced by no block of the disk (`LooseAbove`): a part
of a step that keeps the disk from its new floor up adds at most one such
block of an author a round, and none of a convicted author
(`LooseAbove.of_rises`). Of a piece taken in, every block other than the
sync's is referenced a round above (`pieceAt_held_above`,
`SteadyAbove.takeIn`); of the blocks a decision on a proof brings, those of
convicted authors stay only when referenced (`TameAbove.decideOn`). So an
honest node that drops stays steady above its floor (`steadyAbove_before`).
A block a node builds is its block on its memory's references, its own
among them only when held in memory (`tryBuild_block`).
-/

namespace LeanDag

namespace Node

variable {Validator BlockId Payload : Type} [Fintype Validator] [DecidableEq Validator]
variable [LinearOrder BlockId]
variable {cfg : Config Validator BlockId Payload}

/-- The blocks of `X` at round `k` on a store that no block of it references
among its stored references. -/
def looseAt (st : Store Validator BlockId Payload) (X : Validator) (k : ℕ) : Finset BlockId :=
  st.ids.filter fun i =>
    (st.full i).creator = X ∧ (st.full i).round = k ∧ ∀ j ∈ st.ids, i ∉ (st.blk j).refs

variable (cfg) in
/-- **Two loose blocks above the floor**: at most two blocks of an author
other than the node at one round above the floor are referenced by no block
of the disk. -/
def LooseAbove (s : State Validator BlockId Payload) : Prop :=
  ∀ X, X ≠ cfg.me → ∀ k, s.floor < k → (looseAt s.disk X k).card ≤ 2

variable (cfg) in
/-- **A tame state above the floor**: twins convict, and two loose blocks
above the floor. -/
def TameAbove (s : State Validator BlockId Payload) : Prop :=
  Caught cfg s ∧ LooseAbove cfg s

variable (cfg) in
/-- **A steady state above the floor**: tame above the floor, with free
syncs of their shape. -/
def SteadyAbove (s : State Validator BlockId Payload) : Prop :=
  TameAbove cfg s ∧ Free s ∧ SyncsOn s

omit [Fintype Validator] [DecidableEq Validator] in
/-- **A block at or above the floor keeps its references**: its stored
references are its references as accepted. -/
theorem blk_refs_above {s : State Validator BlockId Payload} {j : BlockId}
    (hj : s.floor ≤ (s.disk.blk j).round) : (s.disk.blk j).refs = (s.disk.full j).refs := by
  have hkn : s.disk.kept[j]? = none := by
    by_contra hk
    have := s.low j hk
    omega
  rw [s.disk.full_of_kept_none hkn]

omit [Fintype Validator] in
/-- **Two loose blocks above the floor stay two** across a part of a step
that raises the floor, keeps the disk from the new floor up and the blocks it
keeps as they were, and adds at most one loose block of an author a round
above the new floor, and none of a convicted author. -/
theorem LooseAbove.of_rises {s s' : State Validator BlockId Payload} (hl : LooseAbove cfg s)
    (hc : Caught cfg s) (hf : s.floor ≤ s'.floor)
    (hk : KeepsFrom cfg.drops s'.floor s.disk s'.disk)
    (hfull : ∀ i ∈ s.disk.ids, i ∈ s'.disk.ids → s'.disk.full i = s.disk.full i)
    (hnew : ∀ X, X ≠ cfg.me → ∀ k, s'.floor < k →
      ((looseAt s'.disk X k).filter (· ∉ s.disk.ids)).card ≤ 1 ∧
        (X ∈ s.detected → ∀ i ∈ looseAt s'.disk X k, i ∈ s.disk.ids)) :
    LooseAbove cfg s' := by
  intro X hme k hkF
  set U := looseAt s'.disk X k
  have hold : U.filter (· ∈ s.disk.ids) ⊆ looseAt s.disk X k := by
    intro i hi
    obtain ⟨hiU, his⟩ := Finset.mem_filter.mp hi
    obtain ⟨hi', hic, hir, hiu⟩ := Finset.mem_filter.mp hiU
    rw [hfull i his hi'] at hic hir
    refine Finset.mem_filter.mpr ⟨his, hic, hir, fun j hj hij => ?_⟩
    -- a block referencing `i` lies a round above it, above the floor, and stays
    have hp : (s.disk.blk i).round + 1 = (s.disk.blk j).round := s.disk.pred j hj i hij
    have hir' : (s.disk.blk i).round = k := by rw [← (s.disk.full_fields i).1]; exact hir
    obtain ⟨hj', hfj⟩ := hk j hj (Or.inr (by omega))
    have hjr : (s'.disk.blk j).round = (s.disk.blk j).round := by
      rw [← (s'.disk.full_fields j).1, hfj, (s.disk.full_fields j).1]
    refine hiu j hj' ?_
    rw [blk_refs_above (s := s') (by omega), hfj, ← blk_refs_above (s := s) (by omega)]
    exact hij
  have hsplit := Finset.card_filter_add_card_filter_not (s := U) (· ∈ s.disk.ids)
  by_cases hX : X ∈ s.detected
  · have hall : U.filter (· ∈ s.disk.ids) = U :=
      Finset.filter_true_of_mem fun i hi => (hnew X hme k hkF).2 hX i hi
    rw [← hall]
    exact (Finset.card_le_card hold).trans (hl X hme k (hf.trans_lt hkF))
  · have h₁ : (looseAt s.disk X k).card ≤ 1 :=
      (Finset.card_le_card (Finset.monotone_filter_right _ fun i _ h => ⟨h.1, h.2.1⟩)).trans
        (hc.card_le_one hX hme k)
    have h₂ : (U.filter (· ∉ s.disk.ids)).card ≤ 1 := (hnew X hme k hkF).1
    have h₃ := Finset.card_le_card hold
    omega

omit [Fintype Validator] in
/-- **Letting go of blocks keeps twins convicting.** -/
theorem Caught.shrinks {s s' : State Validator BlockId Payload} (h : Caught cfg s)
    (hd : Store.Shrinks s.disk s'.disk) (hdet : s.detected ⊆ s'.detected) : Caught cfg s' := by
  intro i hi j hj hij hc hr hme
  rw [hd.full i hi, hd.full j hj] at hc hr
  rw [hd.full i hi] at hme ⊢
  exact hdet (h i (hd.ids hi) j (hd.ids hj) hij hc hr hme)

omit [Fintype Validator] in
/-- **A part of a step adding no block** keeps a state tame above the floor,
when it keeps the disk from its new floor up. -/
theorem TameAbove.of_shrinks {s s' : State Validator BlockId Payload} (h : TameAbove cfg s)
    (hd : Store.Shrinks s.disk s'.disk) (hf : s.floor ≤ s'.floor)
    (hk : KeepsFrom cfg.drops s'.floor s.disk s'.disk) (hdet : s.detected ⊆ s'.detected) :
    TameAbove cfg s' := by
  refine ⟨h.1.shrinks hd hdet, h.2.of_rises h.1 hf hk (fun i _ hi => hd.full i hi)
    fun X _ k _ => ⟨?_, fun _ i hi => hd.ids (Finset.mem_filter.mp hi).1⟩⟩
  rw [Finset.card_le_one]
  intro a ha
  exact absurd (hd.ids (Finset.mem_filter.mp (Finset.mem_filter.mp ha).1).1)
    (Finset.mem_filter.mp ha).2

omit [Fintype Validator] [DecidableEq Validator] in
theorem shrinks_refl (st : Store Validator BlockId Payload) : Store.Shrinks st st :=
  ⟨subset_rfl, fun _ _ => rfl, fun _ _ => ⟨rfl, rfl, rfl⟩⟩

omit [Fintype Validator] in
theorem SteadyAbove.of_shrinks {s s' : State Validator BlockId Payload}
    (h : SteadyAbove cfg s) (hd : Store.Shrinks s.disk s'.disk) (hf : s.floor ≤ s'.floor)
    (hk : KeepsFrom cfg.drops s'.floor s.disk s'.disk) (hdet : s'.detected = s.detected)
    (hs : s'.syncs = s.syncs) : SteadyAbove cfg s' :=
  ⟨h.1.of_shrinks hd hf hk hdet.symm.subset, fun e he => by rw [hdet]; exact h.2.1 e (hs ▸ he),
    ⟨by rw [hs]; exact h.2.2.1, fun e he => h.2.2.2 e (hs ▸ he)⟩⟩

omit [Fintype Validator] in
/-- **The node's own block added** keeps a state steady above the floor. -/
theorem SteadyAbove.own {s s' : State Validator BlockId Payload} (h : SteadyAbove cfg s)
    {id : BlockId} {b : Block Validator BlockId Payload} {hnew hrefs hpred} {F : ℕ}
    (hd : Store.Restrips F (s.disk.insert id b hnew hrefs hpred) s'.disk)
    (hf : s.floor ≤ s'.floor) (hbc : b.creator = cfg.me)
    (hdet : s'.detected = s.detected) (hs : s'.syncs = s.syncs) : SteadyAbove cfg s' := by
  have hg : Grows s.disk s'.disk := (Grows.insert s.disk).trans (Grows.of_restrips hd)
  have hk : ∀ i ∈ s'.disk.ids, (s'.disk.full i).creator ≠ cfg.me → i ∈ s.disk.ids ∧
      s'.disk.full i = s.disk.full i := by
    intro i hi hme
    rw [hd.ids, Store.insert_ids] at hi
    rw [hd.full, Store.full_insert] at hme ⊢
    by_cases hid : i = id
    · rw [if_pos hid] at hme; exact absurd hbc hme
    · rw [if_neg hid]; exact ⟨(Finset.mem_insert.mp hi).resolve_left hid, rfl⟩
  have hc : Caught cfg s' := fun i hi j hj hij hc hr hme => by
    obtain ⟨hi', hbi⟩ := hk i hi hme
    obtain ⟨hj', hbj⟩ := hk j hj (hc ▸ hme)
    rw [hbi, hbj] at hc hr
    rw [hbi] at hme ⊢
    rw [hdet]
    exact h.1.1 i hi' j hj' hij hc hr hme
  refine ⟨⟨hc, h.1.2.of_rises h.1.1 hf (KeepsFrom.of_grows hg) (fun i hi _ => hg.2.2 i hi)
    fun X hX k _ => ⟨?_, fun _ i hi => ?_⟩⟩, fun e he => by rw [hdet]; exact h.2.1 e (hs ▸ he),
    ⟨by rw [hs]; exact h.2.2.1, fun e he => h.2.2.2 e (hs ▸ he)⟩⟩
  · rw [Finset.card_le_one]
    intro a ha
    obtain ⟨ha', han⟩ := Finset.mem_filter.mp ha
    obtain ⟨ha'', hac, -⟩ := Finset.mem_filter.mp ha'
    exact absurd (hk a ha'' (hac ▸ hX)).1 han
  · obtain ⟨hi', hic, -⟩ := Finset.mem_filter.mp hi
    exact (hk i hi' (hic ▸ hX)).1

omit [Fintype Validator] in
theorem SteadyAbove.tryBuild {s s' : State Validator BlockId Payload}
    {out : List (Output Validator BlockId Payload)} (h : SteadyAbove cfg s)
    (hb : Node.tryBuild cfg s = some (s', out)) : SteadyAbove cfg s' := by
  obtain ⟨_, _, _, _, _, _, -, -, hbc, -, -, hd, -, hs, -, -⟩ := tryBuild_some hb
  exact h.own hd (by rw [tryBuild_floor hb]; exact le_max_left _ _) hbc (tryBuild_detected hb).1 hs

omit [Fintype Validator] in
theorem SteadyAbove.progress : ∀ (fuel : ℕ) {s : State Validator BlockId Payload},
    SteadyAbove cfg s → SteadyAbove cfg (Node.progress cfg fuel s).1
  | 0, _, h => h
  | fuel + 1, s, h => by
    unfold Node.progress
    split
    · rename_i s₁ out hb
      exact SteadyAbove.progress fuel (h.tryBuild hb)
    · exact h

omit [Fintype Validator] in
theorem SteadyAbove.decideStep {s : State Validator BlockId Payload} (h : SteadyAbove cfg s) :
    SteadyAbove cfg (Node.decideStep cfg s).1 := by
  have hr := diskRises_decideStep (cfg := cfg) s
  refine h.of_shrinks (decideStep_shrinks s) hr.1.1 hr.2 ?_ (decideStep_syncs s)
  unfold Node.decideStep
  dsimp only
  split
  · simp
  · rfl

omit [Fintype Validator] in
theorem SteadyAbove.tidy {s : State Validator BlockId Payload} (h : TameAbove cfg s)
    (hs : SyncsOn s) : SteadyAbove cfg (Node.tidy s) := by
  refine ⟨h.of_shrinks (by rw [(tidy_eq s).1]; exact shrinks_refl _) le_rfl
    (by rw [(tidy_eq s).1]; exact fun _ hj _ => ⟨hj, rfl⟩)
    (tidy_eq _).2.2.2.2.2.2.2.2.2.1.symm.subset, fun e he => ?_,
    hs.sublist List.filter_sublist⟩
  have := (List.mem_filter.mp he).2
  simp only [decide_eq_true_eq] at this
  exact this.2

omit [Fintype Validator] in
/-- **Taking blocks in, at most one of each author other than the node and
none of a convicted author**, keeps a state tame above the floor. -/
theorem TameAbove.absorb {s : State Validator BlockId Payload} (h : TameAbove cfg s)
    {L : List (BlockId × Block Validator BlockId Payload)}
    (hone : ∀ e ∈ L, ∀ e' ∈ L, e.2.creator = e'.2.creator → e.2.creator ≠ cfg.me → e.1 = e'.1)
    (hdet : ∀ e ∈ L, e.2.creator ≠ cfg.me → e.2.creator ∉ s.detected) :
    TameAbove cfg (Node.absorb cfg s L) := by
  have hd : (Node.absorb cfg s L).disk =
      L.foldl (fun st e => acceptOn cfg s.floor st e.1 e.2) s.disk := absorb_disk _ _
  have hg := Grows.absorb (cfg := cfg) s L
  refine ⟨h.1.absorb L, h.2.of_rises h.1 (absorb_rest (cfg := cfg) s L).1.ge
    (KeepsFrom.of_grows hg) (fun i hi _ => hg.2.2 i hi) fun X hX k _ => ⟨?_, fun hXd i hi => ?_⟩⟩
  · rw [Finset.card_le_one]
    intro a ha b hb
    obtain ⟨ha', han⟩ := Finset.mem_filter.mp ha
    obtain ⟨hb', hbn⟩ := Finset.mem_filter.mp hb
    obtain ⟨ha'', hac, -⟩ := Finset.mem_filter.mp ha'
    obtain ⟨hb'', hbc, -⟩ := Finset.mem_filter.mp hb'
    rw [hd] at ha'' hb'' hac hbc
    obtain ⟨e, he, rfl, heb⟩ := foldl_new L s.disk ha'' han
    obtain ⟨e', he', rfl, heb'⟩ := foldl_new L s.disk hb'' hbn
    rw [heb] at hac
    rw [heb'] at hbc
    exact hone e he e' he' (hac.trans hbc.symm) (hac ▸ hX)
  · obtain ⟨hi', hic, -⟩ := Finset.mem_filter.mp hi
    by_contra hin
    rw [hd] at hi' hic
    obtain ⟨e, he, rfl, heb⟩ := foldl_new L s.disk hi' hin
    rw [heb] at hic
    exact hdet e he (hic ▸ hX) (hic ▸ hXd)

omit [Fintype Validator] in
theorem SteadyAbove.flushSyncs : ∀ (fuel : ℕ) {s : State Validator BlockId Payload},
    SteadyAbove cfg s → SteadyAbove cfg (Node.flushSyncs cfg fuel s)
  | 0, _, h => h
  | fuel + 1, s, h => by
    unfold Node.flushSyncs
    dsimp only
    split
    · exact h
    · refine SteadyAbove.flushSyncs fuel (SteadyAbove.tidy ?_ ((h.2.2.sublist
        (Thins.absorb (cfg := cfg) s _).sub)))
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
theorem SteadyAbove.advance {s : State Validator BlockId Payload} (h : SteadyAbove cfg s) :
    SteadyAbove cfg (Node.advance cfg s).1 := by
  obtain ⟨a, ha⟩ := arm_eq (cfg := cfg) (Node.pass cfg s).1
  have hp : SteadyAbove cfg (Node.pass cfg s).1 :=
    SteadyAbove.flushSyncs _ (SteadyAbove.decideStep (SteadyAbove.progress _ h))
  unfold Node.advance
  dsimp only
  rw [ha]
  exact hp.of_shrinks (shrinks_refl _) le_rfl (fun _ hj _ => ⟨hj, rfl⟩) rfl rfl

omit [Fintype Validator] in
theorem SteadyAbove.settle {s : State Validator BlockId Payload} (h : SteadyAbove cfg s) :
    SteadyAbove cfg (Node.settle cfg s).1 :=
  quiesce_ind (P := SteadyAbove cfg) (fun _ hs => hs.advance) _ s h

/-! ## Taking a piece in, and deciding on a proof -/

omit [Fintype Validator] in
/-- **The walk through a piece from a held block**, on a store reading as a
block map the piece agrees with, valid from `F` up, of a piece at or above
the round below `F`: what it met is held, and is the block or a reference
the piece gives a block it met. -/
theorem pieceAt_held_above {q : ℕ} {E : Exposure Validator BlockId Payload}
    {g : BlockId → Block Validator BlockId Payload}
    {L : List (BlockId × Block Validator BlockId Payload)} {t : BlockId}
    {st : Store Validator BlockId Payload} {F : ℕ} (hst : ReadsAs g st)
    (hab : UpperValid q E F st) (hL : ∀ e ∈ L, e.2 = g e.1)
    (hcut : ∀ e ∈ L, F ≤ e.2.round + 1) (ht : t ∈ st.ids) : ∀ k,
    (∀ y ∈ (pieceAt L t k).1, y = t ∨ ∃ z ∈ (pieceAt L t k).2, y ∈ pieceRefs L z) ∧
    (∀ x ∈ (pieceAt L t k).2, x ∈ st.ids ∧ (x = t ∨ ∃ z ∈ (pieceAt L t k).2, x ∈ pieceRefs L z))
  | 0 => ⟨fun y hy => Or.inl (List.mem_singleton.mp hy), fun _ h => absurd h List.not_mem_nil⟩
  | k + 1 => by
    obtain ⟨h₁, h₂⟩ := pieceAt_held_above hst hab hL hcut ht k
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
    -- a reference the piece gives a held block is held: from the floor up by
    -- validity, and below it the piece holds no block a round lower
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
      obtain ⟨hy', hyL, hyr⟩ := (pieceRefs_of_map L hL hzL).mp hy
      by_cases hzF : F ≤ (st.blk z).round
      · rw [← hst z hzs] at hy'
        exact (hab z hzs hzF).1 hy'
      · exfalso
        obtain ⟨e, he, hez⟩ := List.mem_map.mp hzL
        obtain ⟨e', he', hey⟩ := List.mem_map.mp hyL
        have hc₁ := hcut e he
        have hc₂ := hcut e' he'
        rw [hL e he, hez] at hc₁
        rw [hL e' he', hey] at hc₂
        have hzr : (st.blk z).round = (g z).round := by
          rw [← (st.full_fields z).1, hst z hzs]
        omega
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
/-- **A piece taken in header first keeps a state steady above the floor**,
from a disk valid from the floor up and reading as a block map the piece and
the sync's block agree with, of a piece at or above the round below the
floor: every new block other than the sync's block is referenced a round
above. -/
theorem SteadyAbove.takeIn {g : BlockId → Block Validator BlockId Payload}
    {s : State Validator BlockId Payload} (h : SteadyAbove cfg s)
    (hab : UpperValid cfg.q cfg.xp s.floor s.disk) (hR : ReadsAs g s.disk) {u : Validator}
    {t : BlockId × Block Validator BlockId Payload} {A : List BlockId} (he : (u, t, A) ∈ s.syncs)
    {L : List (BlockId × Block Validator BlockId Payload)}
    (hL : ∀ e ∈ hashed cfg L, g e.1 = e.2) (ht : g t.1 = t.2)
    (hcut : ∀ e ∈ L, s.floor ≤ e.2.round + 1) :
    SteadyAbove cfg (Node.takeIn cfg s t (inHistory cfg t L)) := by
  unfold Node.takeIn
  split
  · rename_i hc
    refine SteadyAbove.tidy ?_ (h.2.2.sublist (Thins.absorb (cfg := cfg) s _).sub)
    set X := Node.absorb cfg s (inHistory cfg t L) with hX
    have hd : X.disk =
        (inHistory cfg t L).foldl (fun st e => acceptOn cfg s.floor st e.1 e.2) s.disk :=
      absorb_disk _ _
    have hg := Grows.absorb (cfg := cfg) s (inHistory cfg t L)
    have hXf : X.floor = s.floor := (absorb_rest (cfg := cfg) s _).1
    have hRX : ReadsAs g X.disk := by
      rw [hd]
      exact ReadsAs.foldl _ hR fun e he => hL e ((mem_inHistory L).mp he).1
    have habX : UpperValid cfg.q cfg.xp s.floor X.disk := by
      have := hab.absorb (inHistory cfg t L); rwa [hXf] at this
    have hL' : ∀ e ∈ hashed cfg L, e.2 = g e.1 := fun e he => (hL e he).symm
    have hcut' : ∀ e ∈ hashed cfg L, s.floor ≤ e.2.round + 1 := fun e he =>
      hcut e ((mem_hashed L).mp he).1
    -- every new block other than the sync's block, above the floor, is referenced
    have href : ∀ i ∈ X.disk.ids, i ∉ s.disk.ids → i ≠ t.1 → s.floor < (X.disk.blk i).round →
        ∃ z ∈ X.disk.ids, i ∈ (X.disk.blk z).refs := by
      intro i hi hin hit hiF
      have hi' := hi
      rw [hd] at hi'
      obtain ⟨e, he, rfl, -⟩ := foldl_new _ s.disk hi' hin
      have hf := ((mem_inHistory L).mp he).2.2
      have hw := pieceAt_held_above hRX habX hL' hcut' hc ((hashed cfg L).length + 1)
      rcases (hw.2 e.1 hf).2 with het | ⟨z, hz, hez⟩
      · exact absurd het hit
      · have hzs := (hw.2 z hz).1
        have hzL : z ∈ (hashed cfg L).map Prod.fst := by
          unfold pieceRefs at hez
          cases hf' : (hashed cfg L).find? (fun e => decide (e.1 = z)) with
          | none => rw [hf'] at hez; exact absurd hez List.not_mem_nil
          | some e' =>
            have := List.find?_some hf'
            simp only [decide_eq_true_eq] at this
            exact this ▸ List.mem_map_of_mem (List.mem_of_find?_eq_some hf')
        obtain ⟨hez', -, hr⟩ := (pieceRefs_of_map _ hL' hzL).mp hez
        have hzr : (X.disk.blk z).round = (X.disk.blk e.1).round + 1 := by
          rw [← (X.disk.full_fields z).1, ← (X.disk.full_fields e.1).1, hRX z hzs, hRX e.1 hi]
          exact hr.symm
        refine ⟨z, hzs, ?_⟩
        rw [blk_refs_above (s := X) (by rw [hXf]; omega), hRX z hzs]
        exact hez'
    refine ⟨h.1.1.absorb _, h.1.2.of_rises h.1.1 hXf.ge (KeepsFrom.of_grows hg)
      (fun i hi _ => hg.2.2 i hi) fun Y hY k hk => ⟨?_, fun hYd i hi => ?_⟩⟩
    · refine Finset.card_le_one.mpr fun a ha b hb => ?_
      obtain ⟨ha', han⟩ := Finset.mem_filter.mp ha
      obtain ⟨hb', hbn⟩ := Finset.mem_filter.mp hb
      obtain ⟨ha'', -, har, hau⟩ := Finset.mem_filter.mp ha'
      obtain ⟨hb'', -, hbr, hbu⟩ := Finset.mem_filter.mp hb'
      have hat : a = t.1 := by
        by_contra hat
        obtain ⟨z, hz, haz⟩ := href a ha'' han hat (by
          rw [← (X.disk.full_fields a).1, har]; rw [hXf] at hk; exact hk)
        exact hau z hz haz
      have hbt : b = t.1 := by
        by_contra hbt
        obtain ⟨z, hz, hbz⟩ := href b hb'' hbn hbt (by
          rw [← (X.disk.full_fields b).1, hbr]; rw [hXf] at hk; exact hk)
        exact hbu z hz hbz
      rw [hat, hbt]
    · obtain ⟨hi', hic, hir, hiu⟩ := Finset.mem_filter.mp hi
      by_contra hin
      have hit : i = t.1 := by
        by_contra hit
        obtain ⟨z, hz, hiz⟩ := href i hi' hin hit (by
          rw [← (X.disk.full_fields i).1, hir]; rw [hXf] at hk; exact hk)
        exact hiu z hz hiz
      subst hit
      rw [hRX _ hi', ht, (h.2.2.2 _ he).2] at hic
      exact h.2.1 _ he (hic ▸ hYd)
  · exact h

omit [Fintype Validator] in
/-- **Deciding on a proof keeps a state tame above the floor**, at a node
that drops: of the blocks it took in above the floor, those of convicted
authors stay only when referenced (`eraseAll_referenced`), and twins
convict the others. -/
theorem TameAbove.decideOn (hdr : cfg.drops = true) {s : State Validator BlockId Payload}
    (h : TameAbove cfg s) (k : ℕ) (d : Option BlockId)
    (L : List (BlockId × Block Validator BlockId Payload)) :
    TameAbove cfg (Node.decideOn cfg s k d L) := by
  set s₁ : State Validator BlockId Payload :=
    { s with
      lo := k + 1
      decided := (k, d) :: s.decided
      proofs := (k, hashed cfg L) :: s.proofs } with hs₁
  set l := (hashed cfg L).mergeSort fun x y => decide (x.2.round ≤ y.2.round) with hl
  set X := Node.absorb cfg (Node.release cfg s₁) l with hX
  set l' := spareSet cfg s X with hl'
  have e : Node.decideOn cfg s k d L = letGo X l' := rfl
  have hr := diskRises_decideOn (cfg := cfg) s k d L
  have hgr := Grows.decideOn (cfg := cfg) s k d L
  rw [e] at hr hgr ⊢
  have hsh := letGo_disk X l'
  have hcX : Caught cfg X :=
    (Caught.of_same (s := s₁) h.1 (release_disk s₁) (by rw [release_detected])).absorb l
  have hdX : s.detected ⊆ X.detected := by
    have := (absorb_rest (cfg := cfg) (Node.release cfg s₁) l).2.2.2.2.2.2.2.2.2
    rwa [release_detected] at this
  -- a new block of a convicted author above the floor that stays is referenced
  have hnd : l'.Nodup := (List.mergeSort_perm _ _).nodup_iff.mpr (Finset.sort_nodup _ _)
  have hpw : l'.Pairwise fun x y => (X.disk.blk y).round ≤ (X.disk.blk x).round :=
    (List.pairwise_mergeSort
      (fun a b c h₁ h₂ => by simp only [decide_eq_true_eq] at *; omega)
      (fun a b => by simp only [Bool.or_eq_true, decide_eq_true_eq]; omega) _).imp
      (fun h => by simpa using h)
  have hconv : ∀ i ∈ (letGo X l').disk.ids, i ∉ s.disk.ids →
      X.floor < ((letGo X l').disk.blk i).round →
      ((letGo X l').disk.blk i).creator ∈ X.detected →
      ∃ z ∈ (letGo X l').disk.ids, i ∈ ((letGo X l').disk.blk z).refs := by
    intro i hi hin hiF hic
    have hiX := hsh.ids hi
    rw [(hsh.fields i hi).1] at hiF
    rw [(hsh.fields i hi).2.1] at hic
    have hil : i ∈ l' := List.mem_mergeSort.mpr ((Finset.mem_sort _).mpr
      (Finset.mem_filter.mpr ⟨Finset.mem_sdiff.mpr ⟨hiX, hin⟩, hdr, hiF, hic⟩))
    exact X.disk.eraseAll_referenced l' hnd (fun x hx => (mem_spareSet hx).1) hpw i hil hi
  refine ⟨hcX.shrinks hsh subset_rfl, h.2.of_rises h.1 hr.1.1 hr.2
    (fun i hi hi' => hgr.2.2 i hi) fun Y hY k' hk' => ⟨?_, fun hYd i hi => ?_⟩⟩
  · refine Finset.card_le_one.mpr fun a ha b hb => ?_
    obtain ⟨ha', han⟩ := Finset.mem_filter.mp ha
    obtain ⟨hb', hbn⟩ := Finset.mem_filter.mp hb
    obtain ⟨ha'', hac, har, hau⟩ := Finset.mem_filter.mp ha'
    obtain ⟨hb'', hbc, hbr, hbu⟩ := Finset.mem_filter.mp hb'
    have hYX : Y ∉ X.detected := fun hYX => by
      obtain ⟨z, hz, haz⟩ := hconv a ha'' han
        (by rw [← ((letGo X l').disk.full_fields a).1, har]; exact hk')
        (by rw [← ((letGo X l').disk.full_fields a).2.1, hac]; exact hYX)
      exact hau z hz haz
    rw [hsh.full a ha''] at hac har
    rw [hsh.full b hb''] at hbc hbr
    exact Finset.card_le_one.mp (hcX.card_le_one hYX hY k')
      a (Finset.mem_filter.mpr ⟨hsh.ids ha'', hac, har⟩) b
      (Finset.mem_filter.mpr ⟨hsh.ids hb'', hbc, hbr⟩)
  · obtain ⟨hi', hic, hir, hiu⟩ := Finset.mem_filter.mp hi
    by_contra hin
    obtain ⟨z, hz, hiz⟩ := hconv i hi' hin
      (by rw [← ((letGo X l').disk.full_fields i).1, hir]; exact hk')
      (by rw [← ((letGo X l').disk.full_fields i).2.1, hic]; exact hdX hYd)
    exact hiu z hz hiz

/-! ## A step -/

/-- **A step keeps a node that drops steady above the floor**, from a disk
valid from the floor up and reading as a block map that what the step is
given and the syncs' blocks agree with. -/
theorem SteadyAbove.step {g : BlockId → Block Validator BlockId Payload}
    {s : State Validator BlockId Payload} (h : SteadyAbove cfg s) (hdr : cfg.drops = true)
    (hab : UpperValid cfg.q cfg.xp s.floor s.disk) (hR : ReadsAs g s.disk)
    (inp : Input Validator BlockId Payload) (hP : ∀ e ∈ delivered cfg [inp], g e.1 = e.2)
    (hS : ∀ e ∈ s.syncs, g e.2.1.1 = e.2.1.2) : SteadyAbove cfg (Node.step cfg s inp).1 := by
  cases inp with
  | start =>
    rw [step_start_eq]
    split_ifs with h₁ h₂
    · exact SteadyAbove.settle (h.own (hrefs := fun _ hj => absurd hj (Finset.notMem_empty _))
        (hpred := fun j hj => absurd hj (Finset.notMem_empty j)) (Store.Restrips.refl _ 0) le_rfl
        rfl rfl rfl)
    · exact h
    · exact h
  | deliver u id b =>
    rw [step_deliver_eq]
    split_ifs with hg hr hc
    · refine SteadyAbove.settle
        (SteadyAbove.tidy ?_ (h.2.2.sublist (Thins.accept (cfg := cfg) s id b).sub))
      exact h.1.absorb (L := [(id, b)])
        (fun e he e' he' _ _ => by
          rw [List.mem_singleton] at he he'; rw [he, he'])
        (fun e he _ => by
          rw [List.mem_singleton] at he; rw [he, hg.2.1]; exact hg.2.2.2.1)
    · refine SteadyAbove.settle ⟨h.1.of_shrinks (shrinks_refl _) le_rfl
        (fun _ hj _ => ⟨hj, rfl⟩) subset_rfl, fun e he => ?_, h.2.2.fresh hg.2.1⟩
      rcases List.mem_cons.mp he with rfl | he
      · exact hg.2.2.2.1
      · exact h.2.1 e (List.mem_of_mem_filter he)
    · exact h
    · exact h
  | stream u L =>
    have hL : ∀ e ∈ hashed cfg (aboveCut cfg s L), g e.1 = e.2 := fun e he => by
      obtain ⟨heL, heh⟩ := (mem_hashed _).mp he
      exact hP e (by simpa [delivered, hashed] using ⟨(List.mem_filter.mp heL).1, heh⟩)
    have hcut : ∀ e ∈ aboveCut cfg s L, s.floor ≤ e.2.round + 1 := fun e he => by
      have := of_decide_eq_true (List.mem_filter.mp he).2
      unfold cutOf at this
      rw [if_pos hdr] at this
      omega
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
      · rw [hs]
        exact SteadyAbove.settle (h.takeIn hab hR he hL ht hcut)
      · set s₁ := Node.takeIn cfg s t (inHistory cfg t (aboveCut cfg s L)) with hs₁
        have hs' : (Node.step cfg s (.stream w L)).1 = (Node.settle cfg { s₁ with
            syncs := s₁.syncs.map fun x => if x.1 = w then
              (w, t, (A ++ missingIn cfg s₁ (t :: inHistory cfg t (aboveCut cfg s L))).dedup)
              else x }).1 := by rw [hs]
        rw [hs']
        have h₁ := h.takeIn hab hR he hL ht hcut
        refine SteadyAbove.settle ⟨h₁.1.of_shrinks (shrinks_refl _) le_rfl
          (fun _ hj _ => ⟨hj, rfl⟩) subset_rfl, fun x hx => ?_,
          h.2.2.extend (Thins.takeIn (cfg := cfg) s t _).sub he⟩
        obtain ⟨x', hx', hxe⟩ := List.mem_map.mp hx
        rw [← hxe]
        split
        · rename_i hxu
          rw [← hxu]; exact h₁.2.1 x' hx'
        · exact h₁.2.1 x' hx'
  | timer r =>
    rw [step_timer_fst]
    exact SteadyAbove.settle (h.of_shrinks (shrinks_refl _) le_rfl (fun _ hj _ => ⟨hj, rfl⟩)
      rfl rfl)
  | syncRequest peer t fr ids => exact h
  | ask peer r => exact h
  | restart =>
    rw [step_restart_fst]
    exact SteadyAbove.settle (h.of_shrinks (shrinks_refl _) le_rfl (fun _ hj _ => ⟨hj, rfl⟩)
      rfl rfl)
  | askProof peer k => exact h
  | proof u k L =>
    simp only [Node.step]
    split
    · split
      · rename_i d _
        refine SteadyAbove.settle (SteadyAbove.tidy (h.1.decideOn hdr k d L)
          (h.2.2.sublist ?_))
        rw [(decideOn_rest (cfg := cfg) s k d L).1]
      · exact h
    · exact h

/-! ## Along a trace -/

section Trace

variable {cfg : Config Validator BlockId Payload} {H : Finset Validator}
variable {tr : Trace Validator BlockId Payload}

/-- **An honest node that drops is steady above its floor** before every
event, with an injective hash. -/
theorem steadyAbove_before (hinj : Converge.HashInjective cfg H tr) (hdr : cfg.drops = true)
    {v : Validator} (hv : v ∈ H) : ∀ i, SteadyAbove (cfg.at v) (stateBefore cfg tr i v)
  | 0 => by
    have hd : (stateBefore cfg tr 0 v).disk.ids = ∅ := by
      simp [stateBefore, inputsBefore, run, State.init, Store.empty]
    have hs : (stateBefore cfg tr 0 v).syncs = [] := by
      simp [stateBefore, inputsBefore, run, State.init]
    refine ⟨⟨fun i hi => by rw [hd] at hi; exact absurd hi (Finset.notMem_empty _),
      fun X _ k _ => ?_⟩, fun e he => by rw [hs] at he; exact absurd he List.not_mem_nil,
      Converge.syncsOn_before v 0⟩
    have : looseAt (stateBefore cfg tr 0 v).disk X k = ∅ := by
      unfold looseAt; rw [hd]; rfl
    rw [this]; exact Nat.zero_le _
  | i + 1 => by
    by_cases he : ∃ inp, tr[i]? = some (v, inp)
    · obtain ⟨inp, hi⟩ := he
      rw [Converge.step_before hi]
      exact (steadyAbove_before hinj hdr hv i).step hdr
        (Converge.inv_before (cfg := cfg) (tr := tr) i v).above (Converge.reads_before hinj hv i)
        inp (fun x hx => Converge.gT_of_known hinj (Or.inl ⟨i, v, inp, hi, hv, hx⟩))
        (Converge.pend_before hinj hv i)
    · rw [Converge.same_before fun inp h => he ⟨inp, h⟩]; exact steadyAbove_before hinj hdr hv i

end Trace

/-! ## The block a node builds -/

omit [Fintype Validator] in
/-- **A block the node builds** is its block on its memory's references
above some round, those of the round and, if any, its own block there, which
its memory then holds. -/
theorem tryBuild_block {s s' : State Validator BlockId Payload}
    {out : List (Output Validator BlockId Payload)} (hown : OwnTop cfg s)
    (hfl : s.floor ≤ floorOf cfg s) (h : tryBuild cfg s = some (s', out)) :
    ∃ r o, (∀ j, o = some j → j ∈ s.memory.ids ∧ (s.memory.blk j).creator = cfg.me) ∧
      out = built cfg [(cfg.idOf (blockOn cfg s.memory r (refsAt cfg s.memory r o s.evidence)
        s.evidence), blockOn cfg s.memory r (refsAt cfg s.memory r o s.evidence) s.evidence)] := by
  have hab : ∀ r o, buildAbove cfg s r o = some (s', out) →
      (∀ j, o = some j → j ∈ s.memory.ids ∧ (s.memory.blk j).creator = cfg.me) →
      ∃ r o, (∀ j, o = some j → j ∈ s.memory.ids ∧ (s.memory.blk j).creator = cfg.me) ∧
        out = built cfg [(cfg.idOf (blockOn cfg s.memory r (refsAt cfg s.memory r o s.evidence)
          s.evidence), blockOn cfg s.memory r (refsAt cfg s.memory r o s.evidence)
            s.evidence)] := by
    intro r o hb ho
    refine ⟨r, o, ho, ?_⟩
    unfold buildAbove at hb
    dsimp only at hb
    split at hb
    · split at hb
      · rw [Option.some.injEq, Prod.mk.injEq] at hb
        rw [← hb.2]
        simp [built, blockOn]
      · cases hb
    · cases hb
  have hnone : ∀ j, (none : Option BlockId) = some j →
      j ∈ s.memory.ids ∧ (s.memory.blk j).creator = cfg.me := fun _ h => by cases h
  unfold tryBuild at h
  split at h
  · rename_i t ht
    -- off the drop branch, the node's own block at its top lies at or above its floor
    have hown' : ¬ (cfg.drops = true ∧ t < s.floor) → ∀ j, s.own = some j →
        j ∈ s.memory.ids ∧ (s.memory.blk j).creator = cfg.me := by
      intro hnd j hj
      obtain ⟨j', hj', hjd, hjr, hjc⟩ := hown t ht
      rw [hj, Option.some.injEq] at hj'
      subst hj'
      have hFt : s.floor ≤ t := by
        cases hd : cfg.drops
        · have := floorOf_le_top (cfg := cfg) hd s
          rw [ht] at this
          simp only [Option.getD_some] at this
          omega
        · by_contra hlt
          exact hnd ⟨hd, by omega⟩
      have hjm := s.mirrors.mem_of hjd (by rw [hjr]; exact hFt)
      exact ⟨hjm, by rw [s.mirrors.creator hjm]; exact hjc⟩
    split at h
    · dsimp only at h
      split at h
      · exact hab _ _ h hnone
      · cases h
    · rename_i hnd
      split at h
      · dsimp only at h
        split at h
        · split at h
          · exact hab _ _ h hnone
          · cases h
        · split at h
          · exact hab _ _ h (hown' hnd)
          · cases h
      · exact hab _ _ h (hown' hnd)
  · cases h

end Node

end LeanDag
