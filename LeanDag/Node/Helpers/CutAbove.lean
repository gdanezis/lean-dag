import LeanDag.Node.Helpers.CutVerdict
import LeanDag.Node.Helpers.Agree
/-!
# Honest disks are cuts of the record padded below each round

`docs/dos-bounds.md` §5, Phase 3.2, step 4. A block of a store is read as a
record reads it from `G` up (`CutAbove`) when, at or above `G`, it is a block
of the record at the same round and author, and above `G` the record's block.
The invariant reads no block below `G`, so it holds of a disk that drops
blocks below its cut or never held them.

* **The padded record takes in what the honest nodes knew** (`grounds_padded`):
  a known block valid over a disk read as the record padded below `G` reads
  it from `G` up, with its references held, is real down to `G`.
* **The disk's blocks from `G` up, with the synthetic blocks below**
  (`storeView`), are a view of the padded record agreeing with the disk from
  `G` up (`viewsAbove_store`), so a decision step from such a disk outputs,
  for every slot of round `G` or `G + 1`, a verdict on the padded record
  (`decidesWell_padded`).
* **A proof of known blocks** builds a store read as the padded record reads
  it (`proofStore_good`), so the verdict it gives is a verdict on that
  record (`verdict_proof`). A known block at or below `G` is read so too
  (`cutAbove_known`), which covers the blocks a node takes in without their
  references below its new cut.
* **Along a run** (`cutAbove_before`), every honest disk whose next
  undecided slot's round is at most `G + 1` is read as the record padded
  below `G` reads it from `G` up, and every decision of a slot of round `G`
  or `G + 1` is a verdict on that record.
-/

namespace LeanDag

namespace Node

open Scheme

variable {Validator BlockId Payload : Type} [Fintype Validator] [DecidableEq Validator]
variable [LinearOrder BlockId]

variable {P : Validity Validator BlockId Payload} {H : Finset Validator}

/-- **A block of a store read as the record reads it from `G` up**: at or
above `G`, a block of the record at the same round and author, and above `G`
the record's block. -/
def CutAbove (U : BlockRecord Validator BlockId Payload P H) (G : ℕ) (j : BlockId)
    (b : Block Validator BlockId Payload) : Prop :=
  G ≤ b.round → j ∈ U.ids ∧ (U.block j).round = b.round ∧ (U.block j).creator = b.creator ∧
    (G < b.round → U.block j = b)

variable {cfg : Config Validator BlockId Payload} {tr : Trace Validator BlockId Payload}
variable (hinj : HashInjective cfg H tr) (hauth : Authentic cfg H tr) [Infinite BlockId]
variable (hq : cfg.q ≤ Fintype.card Validator)

/-- A synthetic block lies below `G`. -/
theorem round_fresh_lt {G : ℕ} {x : Validator × ℕ} (hx : x.2 < G) :
    (padBlk cfg H tr G (fresh cfg H tr x)).round < G := by
  rw [padBlk_fresh]; exact hx

include hinj hauth hq in
/-- A block read as the padded record reads it from `G` up is known and real
down to `G`. -/
theorem CutAbove.mem_globalCutIds {G : ℕ} {j : BlockId} {b : Block Validator BlockId Payload}
    (h : CutAbove (padded hinj hauth hq G) G j b) (hG : G ≤ b.round) :
    j ∈ globalCutIds cfg H tr G := by
  obtain ⟨hj, hr, -⟩ := h hG
  rcases mem_paddedIds.mp hj with hj | ⟨x, hx, rfl⟩
  · exact hj
  · have : (padBlk cfg H tr G (fresh cfg H tr x)).round < G := round_fresh_lt hx
    change (padBlk cfg H tr G (fresh cfg H tr x)).round = b.round at hr
    omega

include hinj hauth hq in
/-- **The padded record takes in what the honest nodes knew**, from `G` up. -/
theorem grounds_padded (G : ℕ) (v : Validator) :
    Grounds (cfg.at v) (CutAbove (padded hinj hauth hq G) G) (knownAll cfg H tr) := by
  intro st hc x hx hnew hrefs hv hG
  have hxk := mem_knownIds hx
  have hcx := content_of_known hinj hx
  have hblk : ∀ j ∈ x.2.refs, Function.update st.blk x.1 x.2 j = st.blk j := fun j hj =>
    Function.update_of_ne (fun e => hnew (by rw [← e]; exact hrefs hj)) _ _
  -- the references lie one round below, read alike by the padded record
  have hpred : ∀ j ∈ x.2.refs, (st.blk j).round + 1 = x.2.round := fun j hj => by
    rw [← hblk j hj]; exact hv.predecessor j hj
  have hreal : RealDown cfg H tr G x.1 := by
    by_cases hle : x.2.round ≤ G
    · exact .base (by rw [hcx]; exact hle)
    · have hjG : ∀ j ∈ x.2.refs, G ≤ (st.full j).round := fun j hj => by
        have := hpred j hj; rw [(st.full_fields j).1]; omega
      have hjc : ∀ j ∈ x.2.refs, j ∈ globalCutIds cfg H tr G := fun j hj =>
        CutAbove.mem_globalCutIds hinj hauth hq (hc j (hrefs hj)) (hjG j hj)
      have hfields : ∀ j ∈ x.2.refs, (content cfg H tr j).round = (st.blk j).round ∧
          (content cfg H tr j).creator = (st.blk j).creator := fun j hj => by
        obtain ⟨hjk, -, -⟩ := mem_globalCutIds.mp (hjc j hj)
        obtain ⟨-, hr, hcr, -⟩ := hc j (hrefs hj) (hjG j hj)
        have hf := padBlk_known_fields (G := G) hjk
        have hs := st.full_fields j
        exact ⟨hf.1.symm.trans (hr.trans hs.1), hf.2.1.symm.trans (hcr.trans hs.2.1)⟩
      refine .intro (by rw [hcx]; omega) (by rw [hcx]; exact fun j hj =>
          (mem_globalCutIds.mp (hjc j hj)).1) ⟨fun j hj => ?_, fun h0 => ?_, trivial⟩
        (by rw [hcx]; exact fun j hj => (mem_globalCutIds.mp (hjc j hj)).2.2)
      · rw [hcx] at hj ⊢
        rw [(hfields j hj).1]
        exact hpred j hj
      · have hcr : creators (content cfg H tr) x.2 =
            creators (Function.update st.blk x.1 x.2) x.2 :=
          Finset.image_congr fun j hj => by rw [hblk j hj]; exact (hfields j hj).2
        rw [hcx] at h0 ⊢
        rw [hcr]
        exact hv.quorum h0
  have hf := padBlk_known_fields (G := G) hxk
  refine ⟨mem_paddedIds.mpr (Or.inl (mem_globalCutIds.mpr ⟨hxk, by rw [hcx]; exact hG, hreal⟩)),
    hf.1.trans (by rw [hcx]), hf.2.1.trans (by rw [hcx]), fun hlt => ?_⟩
  change padBlk cfg H tr G x.1 = x.2
  rw [padBlk_of_lt hxk (by rw [hcx]; exact hlt), hcx]

include hinj hauth hq in
/-- **The histories of the disk's blocks from `G` up**, in the record padded
below `G`, as a view of it. -/
noncomputable def storeView (G : ℕ) (st : Store Validator BlockId Payload)
    (hc : AllGood (CutAbove (padded hinj hauth hq G) G) st) :
    (padded hinj hauth hq G).View :=
  (padded hinj hauth hq G).historiesView (st.ids.filter fun i => G ≤ (st.full i).round)
    fun i hi => (hc i (Finset.mem_filter.mp hi).1 (Finset.mem_filter.mp hi).2).1

/-- **A record path from the disk, from a round `R ≥ G` up, stays on the disk**,
when the disk keeps every block from `R` up with its references. -/
theorem cutAbove_down (G : ℕ) {st : Store Validator BlockId Payload}
    (hc : AllGood (CutAbove (padded hinj hauth hq G) G) st) {R : ℕ} (hGR : G ≤ R)
    (hk : ∀ a ∈ st.ids, R ≤ (st.blk a).round → st.kept[a]? = none) {i : BlockId}
    (hiR : R ≤ ((padded hinj hauth hq G).block i).round) :
    ∀ {j : BlockId}, j ∈ st.ids → G ≤ (st.full j).round →
      ReachesFrom (padded hinj hauth hq G).block j i → i ∈ st.ids ∧ G ≤ (st.full i).round := by
  intro j hj hjG h
  induction h using Relation.ReflTransGen.head_induction_on with
  | refl => exact ⟨hj, hjG⟩
  | @head a c hstep hrest ih =>
    have hstep : c ∈ ((padded hinj hauth hq G).block a).refs := hstep
    obtain ⟨haU, har, -, hab⟩ := hc a hj hjG
    have hca := round_le_of_reaches haU (Relation.ReflTransGen.head hstep hrest)
    have hci := round_le_of_reaches ((padded hinj hauth hq G).complete a haU c hstep) hrest
    have hcr := ((padded hinj hauth hq G).valid a haU).predecessor c hstep
    have hGa : G < (st.full a).round := by rw [← har]; omega
    have hka : st.kept[a]? = none := hk a hj (by rw [← (st.full_fields a).1]; omega)
    have hcs : c ∈ (st.blk a).refs := by
      rw [← st.full_of_kept_none hka, ← hab hGa]; exact hstep
    have hcst := st.complete a hj c hcs
    have hcG : G ≤ (st.full c).round := by
      obtain ⟨-, hcr', -, -⟩ := hc c hcst (by
        have := st.pred a hj c hcs
        change (st.blk c).round + 1 = (st.blk a).round at this
        rw [(st.full_fields c).1]; rw [(st.full_fields a).1] at hGa; omega)
      rw [← hcr']; omega
    exact ih hcst hcG

/-- **The store view agrees with the store from `R ≥ G` up**, when the store
keeps every block from `R` up with its references. -/
theorem viewsAbove_store (G : ℕ) (st : Store Validator BlockId Payload)
    (hc : AllGood (CutAbove (padded hinj hauth hq G) G) st) {R : ℕ} (hGR : G ≤ R)
    (hk : ∀ i ∈ st.ids, R ≤ (st.blk i).round → st.kept[i]? = none) :
    ViewsAbove R boundedSel boundedSel st.view (storeView hinj hauth hq G st hc) := by
  have hround : ∀ i, (st.toRecord.block i).round = (st.full i).round :=
    fun i => (st.full_fields i).1.symm
  refine ViewsAbove.of_boundedSel (fun i hi hR => ?_) (fun i hi hR => ?_)
    (fun i hi hR => ?_) (fun i hi hR => ?_) (fun i hi hR => ?_)
  · rw [hround] at hR
    exact Finset.mem_biUnion.mpr ⟨i, Finset.mem_filter.mpr ⟨hi, by omega⟩, mem_history_self⟩
  · obtain ⟨a, ha, hia⟩ := Finset.mem_biUnion.mp hi
    obtain ⟨has, haG⟩ := Finset.mem_filter.mp ha
    have haU := (hc a has haG).1
    obtain ⟨his, hiG⟩ := cutAbove_down hinj hauth hq G hc hGR hk hR has haG
      ((mem_history_iff haU).mp hia)
    refine ⟨his, ?_⟩
    rw [hround, ← (hc i his hiG).2.1]
    exact hR
  · rw [hround] at hR ⊢
    exact (hc i hi (by omega)).2.1
  · rw [hround] at hR
    rw [(hc i hi (by omega)).2.2.1]
    exact (st.full_fields i).2.1
  · change R < (st.blk i).round at hR
    have hlt : G < (st.full i).round := by rw [(st.full_fields i).1]; omega
    change (padBlk cfg H tr G i).refs = (st.blk i).refs
    have := (hc i hi hlt.le).2.2.2 hlt
    change padBlk cfg H tr G i = st.full i at this
    rw [this, st.full_of_kept_none (hk i hi hR.le)]

include hinj hauth hq in
/-- **A known block at or below `G` is read as the padded record reads it.** -/
theorem cutAbove_known {G : ℕ} {x : BlockId × Block Validator BlockId Payload}
    (hx : x ∈ knownAll cfg H tr) (hle : x.2.round ≤ G) :
    CutAbove (padded hinj hauth hq G) G x.1 x.2 := by
  intro hG
  have hxk := mem_knownIds hx
  have hcx := content_of_known hinj hx
  have hf := padBlk_known_fields (G := G) hxk
  exact ⟨mem_paddedIds.mpr (Or.inl (mem_globalCutIds.mpr ⟨hxk, by rw [hcx]; exact hG,
    .base (by rw [hcx]; exact hle)⟩)), hf.1.trans (by rw [hcx]), hf.2.1.trans (by rw [hcx]),
    fun hlt => absurd hlt (by omega)⟩

include hinj hauth hq in
/-- **The store a proof of known blocks builds is read as the padded record
reads it**, from a `G` at or above the round below the slot's, and keeps
blocks without their references only at that round. -/
theorem proofStore_good (v : Validator) {G k : ℕ} (hk : cfg.slots.slotRound k ≤ G + 1)
    {L : List (BlockId × Block Validator BlockId Payload)}
    (hL : ∀ e ∈ hashed (cfg.at v) L, e ∈ knownAll cfg H tr) :
    AllGood (CutAbove (padded hinj hauth hq G) G) (proofStore (cfg.at v) k L) ∧
      ∀ i, (proofStore (cfg.at v) k L).kept[i]? ≠ none →
        ((proofStore (cfg.at v) k L).blk i).round + 1 = cfg.slots.slotRound k := by
  have hstep : ∀ (st : Store Validator BlockId Payload)
      (e : BlockId × Block Validator BlockId Payload),
      e ∈ knownAll cfg H tr → AllGood (CutAbove (padded hinj hauth hq G) G) st →
      (∀ i, st.kept[i]? ≠ none → (st.blk i).round + 1 = cfg.slots.slotRound k) →
      AllGood (CutAbove (padded hinj hauth hq G) G) (proofStep (cfg.at v) k st e) ∧
        ∀ i, (proofStep (cfg.at v) k st e).kept[i]? ≠ none →
          ((proofStep (cfg.at v) k st e).blk i).round + 1 = cfg.slots.slotRound k := by
    intro st e he hc hkp
    unfold proofStep
    split
    · rename_i hnew
      split
      · rename_i hr
        refine ⟨fun j hj => ?_, fun i hi => ?_⟩
        · rw [Store.base_ids] at hj
          rw [Store.full_base]
          split
          · rename_i hje; subst hje
            have hr' : e.2.round + 1 = cfg.slots.slotRound k := hr
            exact cutAbove_known hinj hauth hq he (by omega)
          · rename_i hje; exact hc j ((Finset.mem_insert.mp hj).resolve_left hje)
        · have hk' : (st.base e.1 e.2 hnew).kept = st.kept.insert e.1 e.2.refs := rfl
          rw [hk', Std.TreeMap.getElem?_insert] at hi
          rw [Store.base_blk]
          by_cases h : i = e.1
          · rw [if_pos h]; exact hr
          · have hc' : ¬ compare e.1 i = Ordering.eq := fun e' => h (compare_eq_iff_eq.mp e').symm
            simp only [hc', if_false] at hi
            rw [if_neg h]; exact hkp i hi
      · split
        · rename_i _ h'
          refine ⟨hc.insert (grounds_padded hinj hauth hq G v st hc e he hnew h'.2.1 h'.2.2.2),
            fun i hi => ?_⟩
          have hi' : st.kept[i]? ≠ none := hi
          have hie : i ≠ e.1 := fun h' => hi' (by rw [h']; exact Store.kept_none_of_notMem st hnew)
          rw [Store.insert_blk, if_neg hie]
          exact hkp i hi'
        · exact ⟨hc, hkp⟩
    · exact ⟨hc, hkp⟩
  have hfold : ∀ (l : List (BlockId × Block Validator BlockId Payload))
      (st : Store Validator BlockId Payload), (∀ e ∈ l, e ∈ knownAll cfg H tr) →
      AllGood (CutAbove (padded hinj hauth hq G) G) st →
      (∀ i, st.kept[i]? ≠ none → (st.blk i).round + 1 = cfg.slots.slotRound k) →
      AllGood (CutAbove (padded hinj hauth hq G) G) (l.foldl (proofStep (cfg.at v) k) st) ∧
        ∀ i, (l.foldl (proofStep (cfg.at v) k) st).kept[i]? ≠ none →
          ((l.foldl (proofStep (cfg.at v) k) st).blk i).round + 1 = cfg.slots.slotRound k := by
    intro l
    induction l with
    | nil => exact fun _ _ hc hkp => ⟨hc, hkp⟩
    | cons e l ih =>
      intro st hl hc hkp
      obtain ⟨hc₁, hkp₁⟩ := hstep st e (hl e List.mem_cons_self) hc hkp
      exact ih _ (fun x hx => hl x (List.mem_cons_of_mem _ hx)) hc₁ hkp₁
  exact hfold _ _ hL (fun j hj => absurd hj (Finset.notMem_empty j))
    fun i hi => absurd (by simp [Store.empty]) hi

include hinj hauth hq in
/-- **The verdict a proof of known blocks gives is a verdict on the record
padded below `G`**, for `G` from the round below the slot's to the slot's. -/
theorem verdict_proof (hσ : cfg.σ = boundedSel) (hadm : cfg.Admissible)
    (hf : Hᶜ.card ≤ cfg.f) (G : ℕ) (v : Validator) {k : ℕ}
    {L : List (BlockId × Block Validator BlockId Payload)} {d : Option BlockId}
    (hv : verdictOn (cfg.at v) k L = some d)
    (hL : ∀ e ∈ hashed (cfg.at v) L, e ∈ knownAll cfg H tr)
    (hk : cfg.slots.slotRound k ≤ G + 1) (hGk : G ≤ cfg.slots.slotRound k) :
    Verdict (cfg.at v) (padded hinj hauth hq G) (k, d) := by
  letI := cfg.slots
  haveI : Validity.Quorate (ValidAt (Validator := Validator) (BlockId := BlockId)
      (Payload := Payload) cfg.q Clause.none) cfg.q :=
    Validity.Quorate.of_validAt hadm.2.2.2.1 fun _ _ => Iff.rfl
  have ht : cfg.p.Tolerates H cfg.f cfg.q := ⟨hf, hadm.2.2.2.2, hadm.1⟩
  have hw : 2 ≤ cfg.p.waveLength := by
    rcases ht.2.2 with ⟨-, hw, -⟩ | ⟨-, hw, -⟩ | ⟨-, hw, -⟩ | ⟨-, hw, -⟩ <;> omega
  obtain ⟨hl, -, hcv, -⟩ := coveredLaws (boundedSel (P := ValidAt (Validator := Validator)
    (BlockId := BlockId) (Payload := Payload) cfg.q Clause.none) (honest := H)) ht
  obtain ⟨hc, hkp⟩ := proofStore_good hinj hauth hq v hk hL
  set st := proofStore (cfg.at v) k L with hst
  set N := max k (decidable (cfg.at v) st.topRound - 1)
  have hv' :
      ((tryDecide cfg.p boundedSel st.toRecord st.view k N).head?).map Prod.snd = some d := by
    rw [← hσ]; exact hv
  obtain ⟨e, he, hed⟩ := Option.map_eq_some_iff.mp hv'
  have hmem := List.mem_of_mem_head? he
  have hlo : k ≤ N + 1 := (le_max_left _ _).trans (Nat.le_succ _)
  have he1 : e.1 = k := by
    obtain ⟨hmap, -⟩ := tryDecide_sound (σ := boundedSel) (U := st.toRecord) (V := st.view) hl hcv
      hlo
    obtain ⟨x, l, hxl⟩ := List.exists_cons_of_ne_nil (List.ne_nil_of_mem hmem)
    rw [hxl, List.head?_cons, Option.some.injEq] at he
    subst he
    have := congrArg List.head? hmap
    rw [hxl] at this
    simp only [List.map_cons, List.head?_cons, List.length_cons, List.range'_succ,
      Option.some.injEq] at this
    exact this
  refine ⟨storeView hinj hauth hq G st hc,
    (viewsAbove_store hinj hauth hq G st hc (R := max G (cfg.slots.slotRound k))
      (le_max_left _ _) fun i hi hR => ?_).decided_of_mem cfg.p hw hl hcv
      (lo := k) hlo (max_le hGk le_rfl) ((Prod.ext he1.symm hed.symm : (k, d) = e) ▸ hmem)⟩
  by_contra hkept
  have := hkp i hkept
  have := le_max_right G (cfg.slots.slotRound k)
  omega

include hinj hauth hq in
/-- **A decision step from a disk read as the padded record reads it from `G`
up, while the next undecided slot's round is at most `G + 1`,** outputs, for
every slot of round `G` or `G + 1`, a verdict on that record. -/
theorem decidesWell_padded (hσ : cfg.σ = boundedSel) (hadm : cfg.Admissible)
    (hf : Hᶜ.card ≤ cfg.f) (G : ℕ) (v : Validator) :
    DecidesWell (cfg.at v) (CutAbove (padded hinj hauth hq G) G)
      (fun n => cfg.slots.slotRound n ≤ G + 1)
      (fun e => cfg.slots.slotRound e.1 ≤ G + 1 → G ≤ cfg.slots.slotRound e.1 →
        Verdict (cfg.at v) (padded hinj hauth hq G) e) := by
  letI := cfg.slots
  haveI : Validity.Quorate (ValidAt (Validator := Validator) (BlockId := BlockId)
      (Payload := Payload) cfg.q Clause.none) cfg.q :=
    Validity.Quorate.of_validAt hadm.2.2.2.1 fun _ _ => Iff.rfl
  have ht : cfg.p.Tolerates H cfg.f cfg.q := ⟨hf, hadm.2.2.2.2, hadm.1⟩
  have hw : 2 ≤ cfg.p.waveLength := by
    rcases ht.2.2 with ⟨-, hw, -⟩ | ⟨-, hw, -⟩ | ⟨-, hw, -⟩ | ⟨-, hw, -⟩ <;> omega
  obtain ⟨hl, -, hcv, -⟩ := coveredLaws (boundedSel (P := ValidAt (Validator := Validator)
    (BlockId := BlockId) (Payload := Payload) cfg.q Clause.none) (honest := H)) ht
  intro s hc e he hke hGe
  unfold Node.decideStep at he
  dsimp only at he
  split at he
  · rename_i hlt
    obtain ⟨hlt, hfl, -⟩ := hlt
    rw [commitsOf_map, tryDecide_memory (cfg := cfg.at v) hσ hw s hfl] at he
    have hfl' : s.floor ≤ cfg.slots.slotRound s.lo := hfl
    have hlo := (tryDecide_sound (p := (cfg.at v).p) (σ := boundedSel) (S := (cfg.at v).slots)
      hl hcv
      (U := s.disk.toRecord) (V := s.disk.view) (lo := s.lo)
      (N := decidable (cfg.at v) s.disk.topRound - 1) (by omega)).1
    have hle : s.lo ≤ e.1 := by
      have := List.mem_map_of_mem (f := Prod.fst) he
      rw [hlo, List.mem_range'_1] at this
      exact this.1
    have hc' := hc ((cfg.slots.mono hle).trans hke)
    refine ⟨storeView hinj hauth hq G s.disk hc',
      (viewsAbove_store hinj hauth hq G s.disk hc' (R := max G (cfg.slots.slotRound s.lo))
        (le_max_left _ _) fun i hi hR => ?_).decided_of_mem cfg.p hw hl hcv
        (lo := s.lo) (by omega) (max_le hGe (cfg.slots.mono hle)) he⟩
    by_contra hk
    have := s.low i hk
    have := le_max_right G (cfg.slots.slotRound s.lo)
    omega
  · simp [commitsOf] at he

section Run

variable (hσ : cfg.σ = boundedSel) (hadm : cfg.Admissible) (hf : Hᶜ.card ≤ cfg.f)
include hinj hauth hq hσ hadm hf

/-- **Every honest disk whose next undecided slot's round is at most `G + 1`
is read as the record padded below `G` reads it from `G` up, and every
decision of a slot of round `G` or `G + 1` is a verdict on that record**,
before every event of the trace. -/
theorem cutAbove_before (G t : ℕ) : ∀ v ∈ H,
    (cfg.slots.slotRound (stateBefore cfg tr t v).lo ≤ G + 1 →
      AllGood (CutAbove (padded hinj hauth hq G) G) (stateBefore cfg tr t v).disk) ∧
      ∀ e ∈ commitsOf (run (cfg.at v) (State.init (cfg.at v)) (inputsBefore tr t v)).2,
        cfg.slots.slotRound e.1 ≤ G + 1 → G ≤ cfg.slots.slotRound e.1 →
          Verdict (cfg.at v) (padded hinj hauth hq G) e := by
  have hK : ∀ v ∈ H, ∀ x ∈ knownOf cfg tr v, x ∈ knownAll cfg H tr :=
    fun v hv x hx => ⟨v, hv, hx⟩
  induction t using Nat.strong_induction_on with
  | _ t ih =>
  intro v hv
  rcases t with _ | t
  · refine ⟨fun _ j hj => absurd hj (Finset.notMem_empty j), fun e he => ?_⟩
    simp [inputsBefore, run, commitsOf] at he
  · rcases hj : tr[t]? with _ | ⟨w, inp⟩
    · have hL : tr.length ≤ t := List.getElem?_eq_none_iff.mp hj
      have h₁ : inputsBefore tr (t + 1) v = inputsBefore tr t v := by
        rw [inputsBefore_of_le (by omega), inputsBefore_of_le hL]
      have := ih t (by omega) v hv
      unfold stateBefore at this ⊢
      rw [h₁]
      exact this
    · by_cases hw : w = v
      · subst hw
        obtain ⟨hc, hv₀⟩ := ih t (by omega) w hv
        have hi := Converge.inv_before (cfg := cfg) (tr := tr) t w
        obtain ⟨hd, hb⟩ := event_knownOf (cfg := cfg) hj
        obtain ⟨hc', hv'⟩ := AllGood.step (cfg := cfg.at w)
          (C := fun n => cfg.slots.slotRound n ≤ G + 1)
          (fun _ _ h h' => (cfg.slots.mono h).trans h')
          (fun _ n hn x hx hr => cutAbove_known hinj hauth hq hx
            (by change x.2.round < cfg.slots.slotRound n at hr; omega))
          (grounds_padded hinj hauth hq G w) (decidesWell_padded hinj hauth hq hσ hadm hf G w)
          (fun _ k L d hvd hL hk hGk => verdict_proof hinj hauth hq hσ hadm hf G w hvd hL hk hGk)
          inp hc (hi.floor.trans (floorOf_le _))
          (fun e he => hK w hv _ (knownBefore_knownOf (hi.pend e he)))
          (fun e he => hK w hv e (hd e he))
          (fun e he => hK w hv e (hb e he))
        refine ⟨by rw [stateBefore_succ hj, if_pos rfl]; exact hc', fun e he => ?_⟩
        rw [inputsBefore_succ hj, if_pos rfl, run_append_single, commitsOf_append] at he
        rcases List.mem_append.mp he with he | he
        · exact hv₀ e he
        · exact hv' e he
      · have h₁ : inputsBefore tr (t + 1) v = inputsBefore tr t v := by
          rw [inputsBefore_succ hj, if_neg hw, List.append_nil]
        have := ih t (by omega) v hv
        unfold stateBefore at this ⊢
        rw [h₁]
        exact this

end Run

end Node

end LeanDag
