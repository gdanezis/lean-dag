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
  `G` up (`viewsAbove_store`), so a decision step outputs, for every slot from
  round `G` up, a verdict on the padded record (`decidesWell_padded`).
* **Along a run** (`cutAbove_before`), every honest disk is read as the record
  padded below `G` reads it from `G` up, and every decision of a slot from
  round `G` up is a verdict on that record.
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
/-- **The disk's blocks from `G` up, with the synthetic blocks below**, as a
view of the record padded below `G`. -/
noncomputable def storeView (G : ℕ) (st : Store Validator BlockId Payload)
    (hc : AllGood (CutAbove (padded hinj hauth hq G) G) st) :
    (padded hinj hauth hq G).View where
  ids := st.ids.filter (fun i => G ≤ (st.full i).round) ∪
    (Finset.range G).biUnion (ladder cfg H tr)
  subset_ids := by
    intro x hx
    rcases Finset.mem_union.mp hx with hx | hx
    · obtain ⟨hxs, hxG⟩ := Finset.mem_filter.mp hx
      exact (hc x hxs hxG).1
    · obtain ⟨v, r, hr, rfl⟩ := mem_ladder_range hx
      exact mem_paddedIds.mpr (Or.inr ⟨(v, r), hr, rfl⟩)
  complete := by
    intro i hi x hx
    change x ∈ (padBlk cfg H tr G i).refs at hx
    rcases Finset.mem_union.mp hi with hi | hi
    · obtain ⟨his, hiG⟩ := Finset.mem_filter.mp hi
      obtain ⟨-, hr, -, hblk⟩ := hc i his hiG
      rcases Nat.lt_or_ge G (st.full i).round with hlt | hle
      · have hb' : padBlk cfg H tr G i = st.full i := hblk hlt
        rw [hb'] at hx
        obtain ⟨hxs, hxr⟩ := st.full_refs i his x hx
        rw [← (st.full_fields x).1, ← (st.full_fields i).1] at hxr
        exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hxs, by omega⟩)
      · have hik := (mem_globalCutIds.mp
          (CutAbove.mem_globalCutIds hinj hauth hq (hc i his) hiG)).1
        have hf := (padBlk_known_fields (G := G) hik).1
        change (padBlk cfg H tr G i).round = (st.full i).round at hr
        rw [padBlk_known hik, if_pos (by omega)] at hx
        dsimp only at hx
        split at hx
        · exact absurd hx (Finset.notMem_empty x)
        · exact Finset.mem_union_right _ (ladder_sub_range (by omega) hx)
    · obtain ⟨v, r, hr, rfl⟩ := mem_ladder_range hi
      rw [padBlk_fresh] at hx
      simp only [synth] at hx
      split at hx
      · exact absurd hx (Finset.notMem_empty x)
      · exact Finset.mem_union_right _ (ladder_sub_range (by omega) hx)

/-- **The store view agrees with the store from `R ≥ G` up**, when the store
keeps every block above `R` with its references. -/
theorem viewsAbove_store (G : ℕ) (st : Store Validator BlockId Payload)
    (hc : AllGood (CutAbove (padded hinj hauth hq G) G) st) {R : ℕ} (hGR : G ≤ R)
    (hk : ∀ i ∈ st.ids, R < (st.blk i).round → st.kept[i]? = none) :
    ViewsAbove R boundedSel boundedSel st.view (storeView hinj hauth hq G st hc) := by
  have hround : ∀ i, (st.toRecord.block i).round = (st.full i).round :=
    fun i => (st.full_fields i).1.symm
  refine ViewsAbove.of_boundedSel (fun i hi hR => ?_) (fun i hi hR => ?_)
    (fun i hi hR => ?_) (fun i hi hR => ?_) (fun i hi hR => ?_)
  · rw [hround] at hR
    exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hi, by omega⟩)
  · rcases Finset.mem_union.mp hi with hi | hi
    · obtain ⟨his, -⟩ := Finset.mem_filter.mp hi
      refine ⟨his, ?_⟩
      rw [hround]
      have := (hc i his (by
        obtain ⟨-, hiG⟩ := Finset.mem_filter.mp hi; exact hiG)).2.1
      change R ≤ (padBlk cfg H tr G i).round at hR
      change (padBlk cfg H tr G i).round = _ at this
      omega
    · obtain ⟨v, r, hr, rfl⟩ := mem_ladder_range hi
      have : (padBlk cfg H tr G (fresh cfg H tr (v, r))).round < G := round_fresh_lt hr
      change R ≤ (padBlk cfg H tr G (fresh cfg H tr (v, r))).round at hR
      omega
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
    rw [this, st.full_of_kept_none (hk i hi hR)]

include hinj hauth hq in
/-- **A decision step from a disk read as the padded record reads it from `G`
up** outputs, for every slot from round `G` up, a verdict on that record. -/
theorem decidesWell_padded (hσ : cfg.σ = boundedSel) (hadm : cfg.Admissible)
    (hf : Hᶜ.card ≤ cfg.f) (G : ℕ) (v : Validator) :
    DecidesWell (cfg.at v) (CutAbove (padded hinj hauth hq G) G)
      (fun e => G ≤ cfg.slots.slotRound e.1 → Verdict (cfg.at v) (padded hinj hauth hq G) e) := by
  letI := cfg.slots
  haveI : Validity.Quorate (ValidAt (Validator := Validator) (BlockId := BlockId)
      (Payload := Payload) cfg.q Clause.none) cfg.q :=
    Validity.Quorate.of_validAt hadm.2.2.2.1 fun _ _ => Iff.rfl
  have ht : cfg.p.Tolerates H cfg.f cfg.q := ⟨hf, hadm.2.2.2.2, hadm.1⟩
  have hw : 2 ≤ cfg.p.waveLength := by
    rcases ht.2.2 with ⟨-, hw, -⟩ | ⟨-, hw, -⟩ | ⟨-, hw, -⟩ | ⟨-, hw, -⟩ <;> omega
  obtain ⟨hl, -, hcv, -⟩ := coveredLaws (boundedSel (P := ValidAt (Validator := Validator)
    (BlockId := BlockId) (Payload := Payload) cfg.q Clause.none) (honest := H)) ht
  intro s hc e he hGe
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
    have hke : s.lo ≤ e.1 := by
      have := List.mem_map_of_mem (f := Prod.fst) he
      rw [hlo, List.mem_range'_1] at this
      exact this.1
    refine ⟨storeView hinj hauth hq G s.disk hc,
      (viewsAbove_store hinj hauth hq G s.disk hc (R := max G (cfg.slots.slotRound s.lo))
        (le_max_left _ _) fun i hi hR => ?_).decided_of_mem cfg.p hw hl hcv
        (lo := s.lo) (by omega) (max_le hGe (cfg.slots.mono hke)) he⟩
    by_contra hk
    have := s.low i hk
    have := le_max_right G (cfg.slots.slotRound s.lo)
    omega
  · simp [commitsOf] at he

section Run

variable (hσ : cfg.σ = boundedSel) (hadm : cfg.Admissible) (hf : Hᶜ.card ≤ cfg.f)
include hinj hauth hq hσ hadm hf

/-- **Every honest disk is read as the record padded below `G` reads it from
`G` up, and every decision of a slot from round `G` up is a verdict on that
record**, before every event of the trace. -/
theorem cutAbove_before (G t : ℕ) : ∀ v ∈ H,
    AllGood (CutAbove (padded hinj hauth hq G) G) (stateBefore cfg tr t v).disk ∧
      ∀ e ∈ commitsOf (run (cfg.at v) (State.init (cfg.at v)) (inputsBefore tr t v)).2,
        G ≤ cfg.slots.slotRound e.1 → Verdict (cfg.at v) (padded hinj hauth hq G) e := by
  have hK : ∀ v ∈ H, ∀ x ∈ knownOf cfg tr v, x ∈ knownAll cfg H tr :=
    fun v hv x hx => ⟨v, hv, hx⟩
  induction t using Nat.strong_induction_on with
  | _ t ih =>
  intro v hv
  rcases t with _ | t
  · refine ⟨fun j hj => absurd hj (Finset.notMem_empty j), fun e he => ?_⟩
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
        obtain ⟨hc', hv'⟩ := AllGood.step (cfg := cfg.at w) (grounds_padded hinj hauth hq G w)
          (decidesWell_padded hinj hauth hq hσ hadm hf G w) inp hc
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
