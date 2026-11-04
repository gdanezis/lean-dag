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
(`card_between_le`); in general the history to depth `K` holds at most
`1 + n + ⋯ + n^K` blocks (`card_historyUpto_le`), a round holds at most
`|C| · n` anchored blocks besides the anchor (`card_anchored_le`), and so the
available sub-DAG holds a bounded number of blocks per round
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

/-- **A history to depth `K` holds at most `1 + n + ⋯ + n^K` blocks**, with no
condition on equivocation: a block references at most one block per
author. -/
theorem card_historyUpto_le : ∀ (K : ℕ) {x : BlockId}, x ∈ U.ids →
    (historyUpto U K x).card ≤ ∑ d ∈ Finset.range (K + 1), Fintype.card Validator ^ d
  | 0, x, _ => by simp
  | K + 1, x, hx => by
    classical
    have hrefs : (U.block x).refs.card ≤ Fintype.card Validator :=
      Finset.card_le_card_of_injOn (fun b => (U.block b).creator)
        (fun _ _ => Finset.mem_coe.mpr (Finset.mem_univ _))
        fun i hi j hj hij => (U.valid x hx).clause i hi j hj hij
    have hbu : ((U.block x).refs.biUnion (historyUpto U K)).card ≤
        (U.block x).refs.card * ∑ d ∈ Finset.range (K + 1), Fintype.card Validator ^ d :=
      Finset.card_biUnion_le_card_mul _ _ _ fun y hy =>
        card_historyUpto_le K (U.complete x hx y hy)
    rw [historyUpto_succ, Finset.sum_range_succ', pow_zero]
    refine (Finset.card_insert_le _ _).trans (Nat.add_le_add_right (hbu.trans ?_) 1)
    calc (U.block x).refs.card * ∑ d ∈ Finset.range (K + 1), Fintype.card Validator ^ d
        ≤ Fintype.card Validator * ∑ d ∈ Finset.range (K + 1), Fintype.card Validator ^ d :=
          Nat.mul_le_mul_right _ hrefs
      _ = ∑ d ∈ Finset.range (K + 1), Fintype.card Validator ^ (d + 1) := by
          rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun d _ => (pow_succ' _ _).symm

/-- **One round holds at most `|C| · n` anchored blocks besides the anchor**:
each has a correct referencer one round up, which has one block there and
references one block per author. -/
theorem card_anchored_le (hA : A ∈ U.ids) {ρ : ℕ} {X : Finset BlockId}
    (hX : ∀ x ∈ X, AnchoredBelow U K A x ∧ (U.block x).round = ρ ∧ x ≠ A) :
    X.card ≤ (Correct : Finset Validator).card * Fintype.card Validator := by
  classical
  have hex : ∀ x ∈ X, ∃ z, z ∈ U.ids ∧ (U.block z).creator ∈ (Correct : Finset Validator) ∧
      x ∈ (U.block z).refs := by
    intro x hx
    obtain ⟨hxa, -, hxA⟩ := hX x hx
    cases hxa with
    | anchor => exact absurd rfl hxA
    | referenced S y hy hz href hcard =>
      obtain ⟨c, hc, hcC⟩ := exists_correct_of_card hcard
      obtain ⟨z, hzS, hzc⟩ := mem_creatorsOf.mp hc
      exact ⟨z, historyUpto_subset_ids K ((hy z hzS).mem hA) (hz z hzS), hzc ▸ hcC, href z hzS⟩
  choose! zf hzf using hex
  have hcard : X.card ≤ ((Correct : Finset Validator) ×ˢ (Finset.univ : Finset Validator)).card :=
    Finset.card_le_card_of_injOn (fun x => ((U.block (zf x)).creator, (U.block x).creator))
      (fun x hx => Finset.mem_coe.mpr (Finset.mem_product.mpr ⟨(hzf x hx).2.1, Finset.mem_univ _⟩))
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
  rwa [Finset.card_product, Finset.card_univ] at hcard

/-- **The available sub-DAG holds a bounded number of blocks per round**, with
no condition on equivocation: those of round `ρ` lie in the histories to depth
`K` of anchored blocks of rounds `ρ` to `ρ + K`. -/
theorem card_avail_round_le (hA : A ∈ U.ids) {ρ : ℕ} {Z : Finset BlockId}
    (hZ : ∀ z ∈ Z, z ∈ Avail U K A ∧ (U.block z).round = ρ) :
    Z.card ≤ (K + 1) * ((Correct : Finset Validator).card * Fintype.card Validator + 1) *
      ∑ d ∈ Finset.range (K + 1), Fintype.card Validator ^ d := by
  classical
  let Y : ℕ → Finset BlockId := fun t =>
    U.ids.filter fun y => AnchoredBelow U K A y ∧ (U.block y).round = t
  have hsub : Z ⊆
      (Finset.range (K + 1)).biUnion fun t => (Y (ρ + t)).biUnion (historyUpto U K) := by
    intro z hz
    obtain ⟨⟨y, hy, hzy⟩, hzr⟩ := hZ z hz
    have hyi := hy.mem hA
    have := round_of_mem_historyUpto K hyi hzy
    refine Finset.mem_biUnion.mpr ⟨(U.block y).round - ρ, Finset.mem_range.mpr (by omega), ?_⟩
    exact Finset.mem_biUnion.mpr ⟨y, Finset.mem_filter.mpr ⟨hyi, hy, by omega⟩, hzy⟩
  have hY : ∀ t, (Y t).card ≤ (Correct : Finset Validator).card * Fintype.card Validator + 1 := by
    intro t
    have h1 := Finset.pred_card_le_card_erase (s := Y t) (a := A)
    have h2 := card_anchored_le hA (X := (Y t).erase A) (ρ := t) fun x hx => by
      obtain ⟨hxA, hxY⟩ := Finset.mem_erase.mp hx
      obtain ⟨-, hxa, hxr⟩ := Finset.mem_filter.mp hxY
      exact ⟨hxa, hxr, hxA⟩
    omega
  refine (Finset.card_le_card hsub).trans ?_
  refine (Finset.card_biUnion_le_card_mul _ _
    (((Correct : Finset Validator).card * Fintype.card Validator + 1) *
      ∑ d ∈ Finset.range (K + 1), Fintype.card Validator ^ d) fun t _ => ?_).trans
    (by rw [Finset.card_range, mul_assoc])
  exact (Finset.card_biUnion_le_card_mul _ _ _ fun y hy =>
    card_historyUpto_le K (Finset.mem_filter.mp hy).1).trans (Nat.mul_le_mul_right _ (hY _))

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

/-- **Progress from a band**: after synchrony, a node holding the blocks of
`T` over a run with their references, and the available sub-DAG below every
certified leader up to the run's end from round `ρ` up, decides every slot
up to the run's end at round `ρ + K − 1` or above, and not below `ρ`. -/
theorem nodeDecided_of_run_band {T : Finset Validator} {R : ℕ}
    (hcard : quorumCard Validator ≤ T.card) (hs : SynchronisedOn U T R) (hH : H ⊆ U.ids)
    {b c ρ : ℕ} (hc : 0 < c) (hspan : ∀ b i, i < b → EligibleAt (S := S) 2 i (b + c - 1))
    (hR : R ≤ S.slotRound b) (hrun : ∀ i, i < c → S.leader (b + i) ∈ T)
    (hpop : ∀ r, S.slotRound b ≤ r → r ≤ S.slotRound (b + c - 1) + 2 → PopulatedOn U T r)
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
  obtain ⟨v, hv⟩ := nodeDecided_of_run hcard hs hH' hc hspan hR hrun hpop hheld i hi
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
