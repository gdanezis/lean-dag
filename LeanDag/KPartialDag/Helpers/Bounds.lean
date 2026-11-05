import LeanDag.KPartialDag.Model.Bounds
import LeanDag.KPartialDag.Helpers.Order
import Mathlib.Order.Interval.Finset.Nat
/-!
# Bands of rounds — helpers

`docs/kpartial.md` §10. Anchoring read on `H` grows with `H`
(`AnchoredIn.mono`), and a block anchored at round `ρ + K` or above is
anchored on the blocks of `H` at round `ρ` or above, since its derivation
reads only blocks above it and their histories to depth `K`
(`AnchoredIn.band`). So the available sub-DAG, the indirect test and the
fetch test above round `ρ + K` read only that band (`availIn_band_iff`,
`linkedIn_band_iff`, `fetchedIn_band_iff`), and so does a decision of a slot
at round `ρ + K − 1` or above (`nodeDecided_band_iff`). A node holding the
blocks of `T` over a run and the available sub-DAG above round `ρ` decides
every slot at round `ρ + K − 1` or above up to the run's end
(`nodeDecided_of_run_band`). The entry slots of a ledger from slot `s` on
read the verdicts and outputs of the slots `D` rounds below `s` and above
(`entersIn_resume`). A block referencing a quorum is valid, and its
obligation lies in the `K` rounds below it (`validAt_of_quorum`,
`obliged_band`). Without equivocation a round holds at most `n` blocks
(`card_between_le`). With no condition on equivocation, one layer of a
history holds at most `|C|` correct blocks and `f` Byzantine blocks per block
of the layer above (`card_layers_le`, `card_historyUpto_le`); every Byzantine
block of the available sub-DAG hangs at most `K` rounds below a root, a
correct or anchored block, through Byzantine blocks (`exists_root`); a round
holds at most `|C|(f + 1) + 1` roots (`card_anchored_le`, `card_roots_le`);
and so the available sub-DAG holds at most
`|C| + (|C|(f + 1) + 1)(1 + f + ⋯ + f^K)` blocks per round
(`card_avail_round_le`).
-/

namespace LeanDag

namespace KPartialDag

variable {Validator : Type*} [Fintype Validator] [DecidableEq Validator] [F : Faults Validator]
variable {BlockId : Type*} [DecidableEq BlockId] {Payload : Type*}
variable {U : KRecord Validator BlockId Payload} {K : ℕ} {H : Finset BlockId} {A : BlockId}

omit [DecidableEq BlockId] in
theorem mem_band {ρ : ℕ} {b : BlockId} : b ∈ Band U H ρ ↔ b ∈ H ∧ ρ ≤ (U.block b).round :=
  Finset.mem_filter

omit [DecidableEq BlockId] in
theorem band_subset {ρ : ℕ} : Band U H ρ ⊆ H := Finset.filter_subset _ _

/-- Anchoring read on `H` grows with `H`. -/
theorem AnchoredIn.mono {H' : Finset BlockId} (hsub : H ⊆ H') {y : BlockId}
    (h : AnchoredIn U K H A y) : AnchoredIn U K H' A y := by
  induction h with
  | anchor h => exact AnchoredIn.anchor (h.trans hsub)
  | referenced S y _ hz href hcard hx ih =>
    exact AnchoredIn.referenced S y ih hz href hcard (hx.trans hsub)

/-- The available sub-DAG read on `H` grows with `H`. -/
theorem availIn_mono {H' : Finset BlockId} (hsub : H ⊆ H') {z : BlockId}
    (hz : z ∈ AvailIn U K H A) : z ∈ AvailIn U K H' A := by
  obtain ⟨y, hy, hzy⟩ := hz
  exact ⟨y, hy.mono hsub, hzy⟩

/-- A history to depth `K` of a block at round `ρ + K` or above, held in
`H`, is held in the band of `H` from `ρ`. -/
theorem historyUpto_subset_band (hH : H ⊆ U.ids) {ρ : ℕ} {x : BlockId}
    (hx : historyUpto U K x ⊆ H) (hρ : ρ + K ≤ (U.block x).round) :
    historyUpto U K x ⊆ Band U H ρ := by
  have hxi : x ∈ U.ids := hH (hx mem_historyUpto_self)
  intro w hw
  have := (round_of_mem_historyUpto K hxi hw).2
  exact mem_band.mpr ⟨hx hw, by omega⟩

/-- **A block anchored at round `ρ + K` or above is anchored on the band of
`H` from `ρ`.** -/
theorem AnchoredIn.band (hH : H ⊆ U.ids) {ρ : ℕ} {y : BlockId} (h : AnchoredIn U K H A y) :
    ρ + K ≤ (U.block y).round → AnchoredIn U K (Band U H ρ) A y := by
  induction h with
  | anchor h => exact fun hρ => AnchoredIn.anchor (historyUpto_subset_band hH h hρ)
  | @referenced x S y hy hz href hcard hx ih =>
    intro hρ
    have hup : ∀ z ∈ S, ρ + K ≤ (U.block (y z)).round := fun z hzS => by
      have hyz : y z ∈ U.ids := hH ((hy z hzS).window mem_historyUpto_self)
      have hzi : z ∈ U.ids := hH ((hy z hzS).window (hz z hzS))
      have := (U.valid z hzi).predecessor x (href z hzS)
      have := (round_of_mem_historyUpto K hyz (hz z hzS)).1
      omega
    exact AnchoredIn.referenced S y (fun z hzS => ih z hzS (hup z hzS)) hz href hcard
      (historyUpto_subset_band hH hx hρ)

/-- **The available sub-DAG above round `ρ + K` is read on the band from
`ρ`.** -/
theorem availIn_band_iff (hH : H ⊆ U.ids) {ρ : ℕ} {z : BlockId}
    (hz : ρ + K ≤ (U.block z).round) : z ∈ AvailIn U K (Band U H ρ) A ↔ z ∈ AvailIn U K H A := by
  refine ⟨availIn_mono band_subset, fun ⟨y, hy, hzy⟩ => ⟨y, hy.band hH ?_, hzy⟩⟩
  have hyi : y ∈ U.ids := hH (hy.window mem_historyUpto_self)
  have := (round_of_mem_historyUpto K hyi hzy).1
  omega

/-- **The indirect test for a slot at round `r`, with `ρ + K ≤ r + 1`, is
read on the band from `ρ`.** -/
theorem linkedIn_band_iff (hH : H ⊆ U.ids) {ρ r : ℕ} (hr : ρ + K ≤ r + 1) {L : BlockId} :
    LinkedIn U K (Band U H ρ) A L r ↔ LinkedIn U K H A L r := by
  have hHb : Band U H ρ ⊆ U.ids := band_subset.trans hH
  constructor
  · rintro ⟨C, hC, hCr, hrefs, hv⟩
    exact ⟨C, availIn_mono band_subset hC, hCr, fun j hj => availIn_mono band_subset (hrefs j hj),
      hv⟩
  · rintro ⟨C, hC, hCr, hrefs, hv⟩
    have hCi : C ∈ U.ids := hH (availIn_subset_held hC)
    refine ⟨C, (availIn_band_iff hH (by omega)).mpr hC, hCr, fun j hj => ?_, hv⟩
    have := (U.valid C hCi).predecessor j hj
    exact (availIn_band_iff hH (by omega)).mpr (hrefs j hj)

/-- **The fetch test down to `ρ'`, with `ρ + K ≤ ρ'`, below an anchor at round
`ρ + K` or above, is read on the band from `ρ`.** -/
theorem fetchedIn_band_iff (hH : H ⊆ U.ids) {ρ ρ' : ℕ} (hA : ρ + K ≤ (U.block A).round)
    (hρ : ρ + K ≤ ρ') : FetchedIn U K (Band U H ρ) A ρ' ↔ FetchedIn U K H A ρ' := by
  constructor
  · rintro ⟨hwin, hall⟩
    refine ⟨hwin.trans band_subset, fun S x hS href hcard => ?_⟩
    refine (hall S x (fun z hzS => ⟨(availIn_band_iff hH (by have := (hS z hzS).2; omega)).mpr
      (hS z hzS).1, (hS z hzS).2⟩) href hcard).trans band_subset
  · rintro ⟨hwin, hall⟩
    refine ⟨historyUpto_subset_band hH hwin hA, fun S x hS href hcard => ?_⟩
    obtain ⟨c, hc⟩ : (creatorsOf U.block S).Nonempty := Finset.card_pos.mp (by omega)
    obtain ⟨z, hzS, -⟩ := mem_creatorsOf.mp hc
    have hzi : z ∈ U.ids := hH (availIn_subset_held (availIn_mono band_subset (hS z hzS).1))
    have := (U.valid z hzi).predecessor x (href z hzS)
    have := (hS z hzS).2
    exact historyUpto_subset_band hH
      (hall S x (fun z hzS => ⟨availIn_mono band_subset (hS z hzS).1, (hS z hzS).2⟩) href hcard)
      (by omega)

/-- Blocks of the record at round `ρ + 1` or above are held with their
references in the band from `ρ` exactly when they are in `H`. -/
theorem heldWithRefs_band {ρ : ℕ} {s : Finset BlockId}
    (hs : ∀ b ∈ s, b ∈ U.ids ∧ ρ + 1 ≤ (U.block b).round) :
    heldWithRefs U (Band U H ρ) s = heldWithRefs U H s := by
  refine Finset.filter_congr fun b hb => ?_
  obtain ⟨hbi, hbr⟩ := hs b hb
  simp only [mem_band]
  constructor
  · rintro ⟨⟨hbH, -⟩, hrefs⟩
    exact ⟨hbH, fun j hj => (hrefs j hj).1⟩
  · rintro ⟨hbH, hrefs⟩
    refine ⟨⟨hbH, by omega⟩, fun j hj => ⟨hrefs j hj, ?_⟩⟩
    have := (U.valid b hbi).predecessor j hj
    omega

/-- A block of the available sub-DAG below a block of the record lies at or
below it. -/
theorem AnchoredBelow.round_le (hA : A ∈ U.ids) {y : BlockId} (h : AnchoredBelow U K A y) :
    (U.block y).round ≤ (U.block A).round := by
  induction h with
  | anchor => exact le_rfl
  | @referenced x S y hy hz href hcard ih =>
    obtain ⟨c, hc⟩ : (creatorsOf U.block S).Nonempty := Finset.card_pos.mp (by omega)
    obtain ⟨z, hzS, -⟩ := mem_creatorsOf.mp hc
    have hyz := (hy z hzS).mem hA
    have hzi := historyUpto_subset_ids K hyz (hz z hzS)
    have := (U.valid z hzi).predecessor x (href z hzS)
    have := (round_of_mem_historyUpto K hyz (hz z hzS)).1
    have := ih z hzS
    omega

/-- What a leader outputs lies at or below it. -/
theorem round_le_of_mem_outIn {D : ℕ} {L b : BlockId} (hL : L ∈ U.ids)
    (hb : b ∈ OutIn U K H D L) : (U.block b).round ≤ (U.block L).round := by
  obtain ⟨y, hy, hby⟩ := availIn_subset hb.1
  have := (round_of_mem_historyUpto K (hy.mem hL) hby).1
  have := hy.round_le hL
  omega

/-! ## Building -/

omit [DecidableEq BlockId] in
/-- **A block referencing a quorum of distinct authors of the round below is
valid.** -/
theorem validAt_of_quorum {Q : Finset BlockId} {r : ℕ} {b : Block Validator BlockId Payload}
    (hQ : ∀ x ∈ Q, (U.block x).round = r) (hd : ∀ x ∈ Q, ∀ y ∈ Q,
      (U.block x).creator = (U.block y).creator → x = y)
    (hq : quorumCard Validator ≤ (creatorsOf U.block Q).card) (hbr : b.round = r + 1)
    (hbQ : b.refs = Q) : KValid Validator BlockId Payload U.block b where
  predecessor := fun i hi => by rw [hbr, hQ i (hbQ ▸ hi)]
  quorum := fun _ => by unfold creators; rw [hbQ]; exact hq
  clause := fun i hi j hj h => hd i (hbQ ▸ hi) j (hbQ ▸ hj) h

/-- **The obligation of a block referencing round-`r` blocks lies in the band
from `r − K`.** -/
theorem obliged_band {Q : Finset BlockId} {r : ℕ} {b : Block Validator BlockId Payload}
    (hQ : ∀ x ∈ Q, x ∈ U.ids ∧ (U.block x).round = r) (hbQ : b.refs = Q)
    (hwin : ∀ x ∈ Q, historyUpto U K x ⊆ H) : Obliged U K (Band U H (r - K)) b := by
  intro x hx w hw
  rw [hbQ] at hx
  have := (round_of_mem_historyUpto K (hQ x hx).1 hw).2
  have := (hQ x hx).2
  exact mem_band.mpr ⟨hwin x hx hw, by omega⟩

/-! ## Counting -/

omit [DecidableEq BlockId] in
/-- **Without equivocation, the record holds at most `n` blocks per round.** -/
theorem card_between_le {lo hi : ℕ} (hE : EquivFree U lo hi) :
    (Between U lo hi).card ≤ (hi + 1 - lo) * Fintype.card Validator := by
  classical
  have hsub : Between U lo hi ⊆ (Finset.Icc lo hi).biUnion (blocksAt U) := by
    intro b hb
    obtain ⟨hbi, h1, h2⟩ := Finset.mem_filter.mp hb
    exact Finset.mem_biUnion.mpr ⟨_, Finset.mem_Icc.mpr ⟨h1, h2⟩, mem_blocksAt.mpr ⟨hbi, rfl⟩⟩
  refine (Finset.card_le_card hsub).trans ?_
  refine (Finset.card_biUnion_le_card_mul _ _ (Fintype.card Validator) fun ρ hρ => ?_).trans
    (by rw [Nat.card_Icc])
  obtain ⟨h1, h2⟩ := Finset.mem_Icc.mp hρ
  refine Finset.card_le_card_of_injOn (fun b => (U.block b).creator)
    (fun _ _ => Finset.mem_coe.mpr (Finset.mem_univ _)) fun i hi j hj hij => ?_
  obtain ⟨hii, hir⟩ := mem_blocksAt.mp hi
  obtain ⟨hji, hjr⟩ := mem_blocksAt.mp hj
  exact hE i hii j hji (by omega) (by omega) (by rw [hir, hjr]) hij

/-- A history to depth `K` of a block of the record lies in its `K + 1`
rounds. -/
theorem historyUpto_subset_between {x : BlockId} (hx : x ∈ U.ids) :
    historyUpto U K x ⊆ Between U ((U.block x).round - K) (U.block x).round := by
  intro w hw
  have := round_of_mem_historyUpto K hx hw
  exact Finset.mem_filter.mpr ⟨historyUpto_subset_ids K hx hw, by omega, this.1⟩

/-! ## Counting with equivocation -/

/-- The blocks `d` references below the blocks of `s`. -/
def layers (U : KRecord Validator BlockId Payload) (s : Finset BlockId) : ℕ → Finset BlockId
  | 0 => s
  | d + 1 => (layers U s d).biUnion fun w => (U.block w).refs

/-- The Byzantine blocks reached from `r` by `s` references, each to a
Byzantine block. -/
def byzLayers (U : KRecord Validator BlockId Payload) (r : BlockId) : ℕ → Finset BlockId
  | 0 => {r}
  | s + 1 => (byzLayers U r s).biUnion fun w =>
      (U.block w).refs.filter fun j => (U.block j).creator ∉ (Correct : Finset Validator)

theorem layers_mono {s t : Finset BlockId} (h : s ⊆ t) :
    ∀ d, layers U s d ⊆ layers U t d
  | 0 => h
  | d + 1 => Finset.biUnion_subset_biUnion_of_subset_left _ (layers_mono h d)

theorem layers_ref {x j : BlockId} (hj : j ∈ (U.block x).refs) :
    ∀ d, layers U {j} d ⊆ layers U {x} (d + 1)
  | 0 => by
    intro w hw
    rw [Finset.mem_singleton.mp hw]
    exact Finset.mem_biUnion.mpr ⟨x, Finset.mem_singleton_self x, hj⟩
  | d + 1 => Finset.biUnion_subset_biUnion_of_subset_left _ (layers_ref hj d)

/-- A history to depth `K` lies in its first `K + 1` layers. -/
theorem historyUpto_subset_layers : ∀ (K : ℕ) (x : BlockId),
    historyUpto U K x ⊆ (Finset.range (K + 1)).biUnion (layers U {x})
  | 0, x => by
    intro w hw
    rw [historyUpto_zero] at hw
    exact Finset.mem_biUnion.mpr ⟨0, by simp, hw⟩
  | K + 1, x => by
    intro w hw
    rcases mem_historyUpto_succ.mp hw with rfl | ⟨j, hj, hwj⟩
    · exact Finset.mem_biUnion.mpr ⟨0, by simp, Finset.mem_singleton_self _⟩
    · obtain ⟨d, hd, hwd⟩ := Finset.mem_biUnion.mp (historyUpto_subset_layers K j hwj)
      exact Finset.mem_biUnion.mpr ⟨d + 1, by simp at hd ⊢; omega, layers_ref hj d hwd⟩

theorem layers_round {x : BlockId} (hx : x ∈ U.ids) :
    ∀ d, ∀ w ∈ layers U {x} d, w ∈ U.ids ∧ (U.block w).round + d = (U.block x).round
  | 0, w, hw => by rw [Finset.mem_singleton.mp hw]; exact ⟨hx, rfl⟩
  | d + 1, w, hw => by
    obtain ⟨p, hp, hwp⟩ := Finset.mem_biUnion.mp hw
    obtain ⟨hpi, hpr⟩ := layers_round hx d p hp
    have := (U.valid p hpi).predecessor w hwp
    exact ⟨U.complete p hpi w hwp, by omega⟩

omit [DecidableEq BlockId] in
/-- A block references at most `f` Byzantine blocks. -/
theorem card_byz_refs_le {w : BlockId} (hw : w ∈ U.ids) :
    ((U.block w).refs.filter fun j => (U.block j).creator ∉ (Correct : Finset Validator)).card ≤
      F.f := by
  refine le_trans (Finset.card_le_card_of_injOn (fun j => (U.block j).creator)
    (fun j hj => ?_) fun i hi j hj hij => ?_) F.card_byzantine
  · have := (Finset.mem_filter.mp (Finset.mem_coe.mp hj)).2
    exact Finset.mem_coe.mpr (by simpa [mem_correct] using this)
  · exact (U.valid w hw).clause i (Finset.mem_filter.mp (Finset.mem_coe.mp hi)).1 j
      (Finset.mem_filter.mp (Finset.mem_coe.mp hj)).1 hij

omit [DecidableEq BlockId] in
/-- Blocks of correct authors at one round number at most `|C|`. -/
theorem card_correct_round_le {ρ : ℕ} {X : Finset BlockId}
    (hX : ∀ x ∈ X, x ∈ U.ids ∧ (U.block x).round = ρ ∧
      (U.block x).creator ∈ (Correct : Finset Validator)) :
    X.card ≤ (Correct : Finset Validator).card :=
  Finset.card_le_card_of_injOn (fun x => (U.block x).creator)
    (fun x hx => Finset.mem_coe.mpr (hX x (Finset.mem_coe.mp hx)).2.2) fun i hi j hj hij =>
      U.eq_of_creator_eq (hX i hi).1 (hX j hj).1 (hX i hi).2.2 rfl hij.symm
        ((hX i hi).2.1.trans (hX j hj).2.1.symm)

/-- **One layer of a history**: at most `|C|` blocks of correct authors, and
at most `f` Byzantine blocks per block of the layer above. -/
theorem card_layers_le {x : BlockId} (hx : x ∈ U.ids) :
    ∀ d, (layers U {x} d).card ≤ layerBound (Correct : Finset Validator).card F.f d
  | 0 => by simp [layers, layerBound]
  | d + 1 => by
    classical
    have hsplit := Finset.card_filter_add_card_filter_not (s := layers U {x} (d + 1))
      (fun w => (U.block w).creator ∈ (Correct : Finset Validator))
    have hc : ((layers U {x} (d + 1)).filter
        fun w => (U.block w).creator ∈ (Correct : Finset Validator)).card ≤
        (Correct : Finset Validator).card := by
      refine card_correct_round_le (U := U) (ρ := (U.block x).round - (d + 1)) fun w hw => ?_
      obtain ⟨hwl, hwc⟩ := Finset.mem_filter.mp hw
      obtain ⟨hwi, hwr⟩ := layers_round hx (d + 1) w hwl
      exact ⟨hwi, by omega, hwc⟩
    have hb : ((layers U {x} (d + 1)).filter
        fun w => (U.block w).creator ∉ (Correct : Finset Validator)).card ≤
        (layers U {x} d).card * F.f := by
      refine (Finset.card_le_card fun w hw => ?_).trans
        (Finset.card_biUnion_le_card_mul _ _ _ fun p hp =>
          card_byz_refs_le (layers_round hx d p hp).1)
      obtain ⟨hwl, hwc⟩ := Finset.mem_filter.mp hw
      obtain ⟨p, hp, hwp⟩ := Finset.mem_biUnion.mp hwl
      exact Finset.mem_biUnion.mpr ⟨p, hp, Finset.mem_filter.mpr ⟨hwp, hwc⟩⟩
    have ih := card_layers_le hx d
    have : (layers U {x} d).card * F.f ≤ F.f * layerBound (Correct : Finset Validator).card F.f d :=
      by rw [mul_comm]; exact Nat.mul_le_mul_left _ ih
    simp only [layerBound]
    omega

/-- **A history to depth `K` holds at most `N_0 + ⋯ + N_K` blocks**, with
`N_0 = 1` and `N_{d+1} = |C| + f · N_d`, with no condition on
equivocation. -/
theorem card_historyUpto_le (K : ℕ) {x : BlockId} (hx : x ∈ U.ids) :
    (historyUpto U K x).card ≤
      ∑ d ∈ Finset.range (K + 1), layerBound (Correct : Finset Validator).card F.f d :=
  (Finset.card_le_card (historyUpto_subset_layers K x)).trans
    (Finset.card_biUnion_le.trans (Finset.sum_le_sum fun d _ => card_layers_le hx d))

theorem byzLayers_subset_ids {r : BlockId} (hr : r ∈ U.ids) : ∀ s, ∀ w ∈ byzLayers U r s,
    w ∈ U.ids ∧ (U.block w).round + s = (U.block r).round
  | 0, w, hw => by rw [Finset.mem_singleton.mp hw]; exact ⟨hr, rfl⟩
  | s + 1, w, hw => by
    obtain ⟨p, hp, hwp⟩ := Finset.mem_biUnion.mp hw
    obtain ⟨hpi, hpr⟩ := byzLayers_subset_ids hr s p hp
    have hwp' := (Finset.mem_filter.mp hwp).1
    have := (U.valid p hpi).predecessor w hwp'
    exact ⟨U.complete p hpi w hwp', by omega⟩

/-- At most `f^s` Byzantine blocks are reached from a block by `s` references
through Byzantine blocks. -/
theorem card_byzLayers_le {r : BlockId} (hr : r ∈ U.ids) :
    ∀ s, (byzLayers U r s).card ≤ F.f ^ s
  | 0 => by simp [byzLayers]
  | s + 1 => by
    refine (Finset.card_biUnion_le_card_mul _ _ _ fun p hp =>
      card_byz_refs_le (byzLayers_subset_ids hr s p hp).1).trans ?_
    rw [pow_succ]
    exact Nat.mul_le_mul_right _ (card_byzLayers_le hr s)

/-- A block of a history to depth `K`, other than its top, is referenced by a
block of that history. -/
theorem exists_parent : ∀ (K : ℕ) {y z : BlockId}, z ∈ historyUpto U K y → z ≠ y →
    ∃ p ∈ historyUpto U K y, z ∈ (U.block p).refs
  | 0, y, z, hz, hne => by
    rw [historyUpto_zero, Finset.mem_singleton] at hz; exact absurd hz hne
  | K + 1, y, z, hz, hne => by
    rcases mem_historyUpto_succ.mp hz with h | ⟨j, hj, hzj⟩
    · exact absurd h hne
    by_cases hzj' : z = j
    · exact ⟨y, mem_historyUpto_self, hzj' ▸ hj⟩
    · obtain ⟨p, hp, hzp⟩ := exists_parent K hzj hzj'
      exact ⟨p, mem_historyUpto_succ.mpr (Or.inr ⟨j, hj, hp⟩), hzp⟩

/-- **Every Byzantine block of a history below an anchored block hangs below a
root**: a block of a correct author or an anchored block, at most as many
rounds above it as the history's top, reached through Byzantine blocks. -/
theorem exists_root (hA : A ∈ U.ids) {y : BlockId} (hy : AnchoredBelow U K A y) :
    ∀ d z, z ∈ historyUpto U K y → (U.block y).round = (U.block z).round + d →
      (U.block z).creator ∉ (Correct : Finset Validator) →
      ∃ s r, s ≤ d ∧ r ∈ U.ids ∧ (U.block r).round = (U.block z).round + s ∧
        ((U.block r).creator ∈ (Correct : Finset Validator) ∨ AnchoredBelow U K A r) ∧
        z ∈ byzLayers U r s := by
  classical
  have hyi := hy.mem hA
  intro d
  induction d using Nat.strong_induction_on with
  | _ d ih =>
    intro z hz hdr hzc
    by_cases hzy : z = y
    · subst hzy
      exact ⟨0, z, Nat.zero_le _, hyi, rfl, Or.inr hy, Finset.mem_singleton_self _⟩
    obtain ⟨p, hp, hzp⟩ := exists_parent K hz hzy
    have hpi := historyUpto_subset_ids K hyi hp
    have hpr := (U.valid p hpi).predecessor z hzp
    have hpy := (round_of_mem_historyUpto K hyi hp).1
    by_cases hroot : (U.block p).creator ∈ (Correct : Finset Validator) ∨ AnchoredBelow U K A p
    · exact ⟨1, p, by omega, hpi, by omega, hroot, Finset.mem_biUnion.mpr
        ⟨p, Finset.mem_singleton_self _, Finset.mem_filter.mpr ⟨hzp, hzc⟩⟩⟩
    · push Not at hroot
      obtain ⟨s, r, hs, hri, hrr, hrt, hpr'⟩ := ih (d - 1) (by omega) p hp (by omega) hroot.1
      exact ⟨s + 1, r, by omega, hri, by omega, hrt, Finset.mem_biUnion.mpr
        ⟨p, hpr', Finset.mem_filter.mpr ⟨hzp, hzc⟩⟩⟩

/-- **One round holds at most `|C| · |B|` anchored blocks of authors in `B`
besides the anchor**: each has a correct referencer one round up, which has
one block there and references one block per author. -/
theorem card_anchored_le (hA : A ∈ U.ids) {ρ : ℕ} {B : Finset Validator} {X : Finset BlockId}
    (hX : ∀ x ∈ X, AnchoredBelow U K A x ∧ (U.block x).round = ρ ∧ x ≠ A ∧
      (U.block x).creator ∈ B) :
    X.card ≤ (Correct : Finset Validator).card * B.card := by
  classical
  have hex : ∀ x ∈ X, ∃ z, z ∈ U.ids ∧ (U.block z).creator ∈ (Correct : Finset Validator) ∧
      x ∈ (U.block z).refs := by
    intro x hx
    obtain ⟨hxa, -, hxA, -⟩ := hX x hx
    cases hxa with
    | anchor => exact absurd rfl hxA
    | referenced S y hy hz href hcard =>
      obtain ⟨c, hc, hcC⟩ := exists_correct_of_card hcard
      obtain ⟨z, hzS, hzc⟩ := mem_creatorsOf.mp hc
      exact ⟨z, historyUpto_subset_ids K ((hy z hzS).mem hA) (hz z hzS), hzc ▸ hcC, href z hzS⟩
  choose! zf hzf using hex
  have hcard : X.card ≤ ((Correct : Finset Validator) ×ˢ B).card :=
    Finset.card_le_card_of_injOn (fun x => ((U.block (zf x)).creator, (U.block x).creator))
      (fun x hx => Finset.mem_coe.mpr (Finset.mem_product.mpr ⟨(hzf x hx).2.1, (hX x hx).2.2.2⟩))
      fun x hx x' hx' hxx => by
        obtain ⟨hz, hzC, hxz⟩ := hzf x hx
        obtain ⟨hz', -, hxz'⟩ := hzf x' hx'
        obtain ⟨h1, h2⟩ := Prod.mk.inj hxx
        have hr := (U.valid _ hz).predecessor x hxz
        have hr' := (U.valid _ hz').predecessor x' hxz'
        have hzz : zf x = zf x' := U.eq_of_creator_eq hz hz' hzC rfl h1.symm
          (by have := (hX x hx).2.1; have := (hX x' hx').2.1; omega)
        rw [← hzz] at hxz'
        exact (U.valid _ hz).clause x hxz x' hxz' h2
  rwa [Finset.card_product] at hcard

/-- One round holds at most `|C|(f + 1) + 1` roots: blocks of correct authors,
and anchored blocks. -/
theorem card_roots_le (hA : A ∈ U.ids) {ρ : ℕ} {X : Finset BlockId}
    (hX : ∀ x ∈ X, x ∈ U.ids ∧ (U.block x).round = ρ ∧
      ((U.block x).creator ∈ (Correct : Finset Validator) ∨ AnchoredBelow U K A x)) :
    X.card ≤ (Correct : Finset Validator).card * (F.f + 1) + 1 := by
  classical
  have hsplit := Finset.card_filter_add_card_filter_not (s := X)
    (fun x => (U.block x).creator ∈ (Correct : Finset Validator))
  have hc := card_correct_round_le (U := U) (ρ := ρ) (X := X.filter
    fun x => (U.block x).creator ∈ (Correct : Finset Validator)) fun x hx => by
      obtain ⟨hxX, hxc⟩ := Finset.mem_filter.mp hx
      exact ⟨(hX x hxX).1, (hX x hxX).2.1, hxc⟩
  have h1 := Finset.pred_card_le_card_erase (s := X.filter
    fun x => (U.block x).creator ∉ (Correct : Finset Validator)) (a := A)
  have hb := card_anchored_le hA (ρ := ρ) (B := F.byzantine) (X := (X.filter
    fun x => (U.block x).creator ∉ (Correct : Finset Validator)).erase A) fun x hx => by
      obtain ⟨hxA, hxf⟩ := Finset.mem_erase.mp hx
      obtain ⟨hxX, hxc⟩ := Finset.mem_filter.mp hxf
      obtain ⟨-, hxr, hxa⟩ := hX x hxX
      exact ⟨hxa.resolve_left hxc, hxr, hxA, by simpa [mem_correct] using hxc⟩
  have := Nat.mul_le_mul_left (Correct : Finset Validator).card F.card_byzantine
  rw [Nat.mul_add, Nat.mul_one]
  omega

/-- **The available sub-DAG holds at most `|C| + (|C|(f + 1) + 1)(1 + f + ⋯ +
f^K)` blocks per round**, with no condition on equivocation: its correct
blocks number at most `|C|`, and each Byzantine block hangs at most `K`
rounds below a root through Byzantine blocks. -/
theorem card_avail_round_le (hA : A ∈ U.ids) {ρ : ℕ} {Z : Finset BlockId}
    (hZ : ∀ z ∈ Z, z ∈ Avail U K A ∧ (U.block z).round = ρ) :
    Z.card ≤ (Correct : Finset Validator).card +
      ((Correct : Finset Validator).card * (F.f + 1) + 1) *
        ∑ s ∈ Finset.range (K + 1), F.f ^ s := by
  classical
  have hsplit := Finset.card_filter_add_card_filter_not (s := Z)
    (fun z => (U.block z).creator ∈ (Correct : Finset Validator))
  have hc := card_correct_round_le (U := U) (ρ := ρ) (X := Z.filter
    fun z => (U.block z).creator ∈ (Correct : Finset Validator)) fun z hz => by
      obtain ⟨hzZ, hzc⟩ := Finset.mem_filter.mp hz
      obtain ⟨⟨y, hy, hzy⟩, hzr⟩ := hZ z hzZ
      exact ⟨historyUpto_subset_ids K (hy.mem hA) hzy, hzr, hzc⟩
  let R : ℕ → Finset BlockId := fun t => U.ids.filter fun r => (U.block r).round = t ∧
    ((U.block r).creator ∈ (Correct : Finset Validator) ∨ AnchoredBelow U K A r)
  have hsub : Z.filter (fun z => (U.block z).creator ∉ (Correct : Finset Validator)) ⊆
      (Finset.range (K + 1)).biUnion fun s => (R (ρ + s)).biUnion fun r => byzLayers U r s := by
    intro z hz
    obtain ⟨hzZ, hzc⟩ := Finset.mem_filter.mp hz
    obtain ⟨⟨y, hy, hzy⟩, hzr⟩ := hZ z hzZ
    have hyz := round_of_mem_historyUpto K (hy.mem hA) hzy
    obtain ⟨s, r, hs, hri, hrr, hrt, hzr'⟩ := exists_root hA hy
      ((U.block y).round - (U.block z).round) z hzy (by omega) hzc
    exact Finset.mem_biUnion.mpr ⟨s, Finset.mem_range.mpr (by omega),
      Finset.mem_biUnion.mpr ⟨r, Finset.mem_filter.mpr ⟨hri, by omega, hrt⟩, hzr'⟩⟩
  have hb : (Z.filter fun z => (U.block z).creator ∉ (Correct : Finset Validator)).card ≤
      ((Correct : Finset Validator).card * (F.f + 1) + 1) *
        ∑ s ∈ Finset.range (K + 1), F.f ^ s := by
    refine (Finset.card_le_card hsub).trans (Finset.card_biUnion_le.trans ?_)
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun s _ => (Finset.card_biUnion_le_card_mul _ _ _ fun r hr =>
      card_byzLayers_le (Finset.mem_filter.mp hr).1 s).trans (Nat.mul_le_mul_right _ ?_)
    exact card_roots_le hA fun x hx => by
      obtain ⟨hxi, hxr, hxt⟩ := Finset.mem_filter.mp hx
      exact ⟨hxi, hxr, hxt⟩
  omega

variable [S : Slots Validator]

/-! ## Decisions read a band -/

/-- One direction of the band: a decision on `H` is one on the band. -/
theorem nodeDecided_band (hH : H ⊆ U.ids) {ρ i : ℕ} {v : Option BlockId}
    (h : NodeDecided U K H i v) :
    ρ ≤ S.slotRound i → ρ + K ≤ S.slotRound i + 1 → NodeDecided U K (Band U H ρ) i v := by
  induction h with
  | @directCommit k L hL hc =>
    intro h1 h2
    refine NodeDecided.directCommit hL ?_
    rw [heldWithRefs_band fun b hb => by
      obtain ⟨hbi, hbr, -⟩ := mem_certificatesAt.mp hb
      exact ⟨hbi, by omega⟩]
    exact hc
  | @directSkip k hs =>
    intro h1 h2
    refine NodeDecided.directSkip ?_
    rw [heldWithRefs_band fun b hb => by
      obtain ⟨hbi, hbr⟩ := mem_blocksAt.mp (Finset.mem_filter.mp hb).1
      exact ⟨hbi, by omega⟩]
    exact hs
  | @indirectCommit k j A L hkj helig hj hmid hL hlink ihj ihm =>
    intro h1 h2
    have hkj' := S.mono hkj.le
    exact NodeDecided.indirectCommit hkj helig (ihj (by omega) (by omega))
      (fun m h3 h4 h5 => ihm m h3 h4 h5 (by have := S.mono h3.le; omega)
        (by have := S.mono h3.le; omega)) hL ((linkedIn_band_iff hH h2).mpr hlink)
  | @indirectSkip k j A hkj helig hj hmid hf hnone ihj ihm =>
    intro h1 h2
    have hkj' := S.mono hkj.le
    have hA := (hj.certified hH).1
    have hAr : ρ + K ≤ (U.block A).round := by
      rw [hA.2.1]; have := eligibleAt_iff.mp helig; omega
    exact NodeDecided.indirectSkip hkj helig (ihj (by omega) (by omega))
      (fun m h3 h4 h5 => ihm m h3 h4 h5 (by have := S.mono h3.le; omega)
        (by have := S.mono h3.le; omega))
      ((fetchedIn_band_iff hH hAr (by omega)).mpr hf)
      fun L hL hl => hnone L hL ((linkedIn_band_iff hH h2).mp hl)

/-- The other direction: a decision on the band is one on `H`. -/
theorem nodeDecided_of_band (hH : H ⊆ U.ids) {ρ i : ℕ} {v : Option BlockId}
    (h : NodeDecided U K (Band U H ρ) i v) :
    ρ ≤ S.slotRound i → ρ + K ≤ S.slotRound i + 1 → NodeDecided U K H i v := by
  have hHb : Band U H ρ ⊆ U.ids := band_subset.trans hH
  induction h with
  | @directCommit k L hL hc =>
    intro h1 h2
    refine NodeDecided.directCommit hL ?_
    rw [← heldWithRefs_band (ρ := ρ) fun b hb => by
      obtain ⟨hbi, hbr, -⟩ := mem_certificatesAt.mp hb
      exact ⟨hbi, by omega⟩]
    exact hc
  | @directSkip k hs =>
    intro h1 h2
    refine NodeDecided.directSkip ?_
    rw [← heldWithRefs_band (ρ := ρ) fun b hb => by
      obtain ⟨hbi, hbr⟩ := mem_blocksAt.mp (Finset.mem_filter.mp hb).1
      exact ⟨hbi, by omega⟩]
    exact hs
  | @indirectCommit k j A L hkj helig hj hmid hL hlink ihj ihm =>
    intro h1 h2
    have hkj' := S.mono hkj.le
    exact NodeDecided.indirectCommit hkj helig (ihj (by omega) (by omega))
      (fun m h3 h4 h5 => ihm m h3 h4 h5 (by have := S.mono h3.le; omega)
        (by have := S.mono h3.le; omega)) hL ((linkedIn_band_iff hH h2).mp hlink)
  | @indirectSkip k j A hkj helig hj hmid hf hnone ihj ihm =>
    intro h1 h2
    have hkj' := S.mono hkj.le
    have hA := (hj.certified hHb).1
    have hAr : ρ + K ≤ (U.block A).round := by
      rw [hA.2.1]; have := eligibleAt_iff.mp helig; omega
    exact NodeDecided.indirectSkip hkj helig (ihj (by omega) (by omega))
      (fun m h3 h4 h5 => ihm m h3 h4 h5 (by have := S.mono h3.le; omega)
        (by have := S.mono h3.le; omega))
      ((fetchedIn_band_iff hH hAr (by omega)).mp hf)
      fun L hL hl => hnone L hL ((linkedIn_band_iff hH h2).mpr hl)

/-- **A decision of a slot at round `ρ + K − 1` or above, and not below `ρ`,
reads only the band from `ρ`.** -/
theorem nodeDecided_band_iff (hH : H ⊆ U.ids) {ρ i : ℕ} {v : Option BlockId}
    (h1 : ρ ≤ S.slotRound i) (h2 : ρ + K ≤ S.slotRound i + 1) :
    NodeDecided U K (Band U H ρ) i v ↔ NodeDecided U K H i v :=
  ⟨fun h => nodeDecided_of_band hH h h1 h2, fun h => nodeDecided_band hH h h1 h2⟩

/-- **Progress from a band**: on a responsive run, a node holding the blocks
of `T` over the run with their references, and the available sub-DAG below
every certified leader up to the run's end from round `ρ` up, decides every
slot up to the run's end at round `ρ + K − 1` or above, and not below `ρ`. -/
theorem nodeDecided_of_run_band {T : Finset Validator}
    (hcard : quorumCard Validator ≤ T.card) (hH : H ⊆ U.ids)
    {b c ρ : ℕ} (hc : 0 < c) (hspan : ∀ b i, i < b → EligibleAt (S := S) 2 i (b + c - 1))
    (hresp : ∀ j, b ≤ j → j ≤ b + c - 1 → Responds U T j)
    (hW : WithRefs U T (S.slotRound b) (S.slotRound (b + c - 1) + 2) ⊆ ↑H)
    (hav : ∀ z ∈ AvailBelow U K (b + c - 1), ρ ≤ (U.block z).round → z ∈ H) :
    ∀ i, i < b + c → ρ ≤ S.slotRound i → ρ + K ≤ S.slotRound i + 1 →
      ∃ v, NodeDecided U K H i v := by
  classical
  let H' := H ∪ U.ids.filter (· ∈ AvailBelow U K (b + c - 1))
  have hH' : H' ⊆ U.ids := Finset.union_subset hH (Finset.filter_subset _ _)
  have hheld : WithRefs U T (S.slotRound b) (S.slotRound (b + c - 1) + 2) ∪
      AvailBelow U K (b + c - 1) ⊆ ↑H' := by
    rintro z (hz | hz)
    · exact Finset.mem_union_left _ (hW hz)
    · obtain ⟨j, L, hj, hL, hC, hzL⟩ := hz
      exact Finset.mem_union_right _
        (Finset.mem_filter.mpr ⟨avail_subset_ids hL.1 hzL, ⟨j, L, hj, hL, hC, hzL⟩⟩)
  have heq : Band U H' ρ = Band U H ρ := by
    ext z
    simp only [mem_band, H', Finset.mem_union, Finset.mem_filter]
    constructor
    · rintro ⟨hz | ⟨-, hz⟩, hρ⟩
      · exact ⟨hz, hρ⟩
      · exact ⟨hav z hz hρ, hρ⟩
    · rintro ⟨hz, hρ⟩
      exact ⟨Or.inl hz, hρ⟩
  intro i hi h1 h2
  obtain ⟨v, hv⟩ := nodeDecided_of_run hcard hH' hc hspan hresp hheld i hi
  have := nodeDecided_band hH' hv h1 h2
  rw [heq] at this
  exact ⟨v, nodeDecided_of_band hH this h1 h2⟩

/-! ## Resuming the ledger -/

/-- One direction of resuming: entry slots from `s` on carry over between two
nodes that agree on the verdicts of the slots `D` rounds below `s` and above,
and have fetched those slots' leaders down to `D` rounds below `s`. -/
theorem entersIn_resume {D : ℕ} {H₁ H₂ : Finset BlockId} (hH₁ : H₁ ⊆ U.ids)
    (hH₂ : H₂ ⊆ U.ids) {g₁ g₂ : ℕ → Option BlockId} {s m : ℕ}
    (hg₁ : ∀ j L, g₁ j = some L → IsLeaderBlock U j L)
    (hg₂ : ∀ j L, g₂ j = some L → IsLeaderBlock U j L)
    (hagree : ∀ j, j < m → S.slotRound s ≤ S.slotRound j + D → g₁ j = g₂ j)
    (hf₁ : ∀ j L, j < m → S.slotRound s ≤ S.slotRound j + D → g₁ j = some L →
      FetchedIn U K H₁ L (S.slotRound s - D))
    (hf₂ : ∀ j L, j < m → S.slotRound s ≤ S.slotRound j + D → g₂ j = some L →
      FetchedIn U K H₂ L (S.slotRound s - D))
    {b : BlockId} {k : ℕ} (hsk : s ≤ k) (hkm : k < m) :
    EntersIn U K H₁ D g₁ b k → EntersIn U K H₂ D g₂ b k := by
  rintro ⟨⟨L, hL, hb⟩, hmin⟩
  have hLk := hg₁ k L hL
  have hσ : S.slotRound s ≤ S.slotRound k := S.mono hsk
  have hbL := hb.2
  rw [hLk.2.1] at hbL
  have hrange : S.slotRound s ≤ S.slotRound k + D := by omega
  have hL₂ : g₂ k = some L := (hagree k hkm hrange).symm.trans hL
  refine ⟨⟨L, hL₂, avail_subset_availIn hH₂ (hf₂ k L hkm hrange hL₂) (outIn_subset hb).1
    (by omega), hb.2⟩, fun j hj L' hL' hb' => ?_⟩
  by_cases hjr : S.slotRound s ≤ S.slotRound j + D
  · have hL'₁ : g₁ j = some L' := (hagree j (by omega) hjr).trans hL'
    exact hmin j hj L' hL'₁ ⟨avail_subset_availIn hH₁ (hf₁ j L' (by omega) hjr hL'₁)
      (outIn_subset hb').1 (by omega), hb'.2⟩
  · have hjL := hg₂ j L' hL'
    have := round_le_of_mem_outIn hjL.1 hb'
    rw [hjL.2.1] at this
    omega

end KPartialDag

end LeanDag
