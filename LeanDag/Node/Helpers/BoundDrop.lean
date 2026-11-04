import LeanDag.Node.Helpers.Bound
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
(`LooseAbove.of_rises`).
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

end Node

end LeanDag
