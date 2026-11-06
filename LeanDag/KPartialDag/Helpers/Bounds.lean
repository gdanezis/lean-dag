import LeanDag.KPartialDag.Model.Bounds
import LeanDag.KPartialDag.Helpers.Order
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Data.Fintype.Option
/-!
# Bands of rounds — helpers

`docs/kpartial.md` §10. Decisions read a band of rounds
(`nodeDecided_band_iff`), the counts of a history and of a round of the
available sub-DAG (`card_historyUpto_le`, `card_avail_round_le`), and
resuming the ledger (`entersIn_resume`).
-/

namespace LeanDag

namespace KPartialDag

variable {Validator : Type*} [Fintype Validator] [DecidableEq Validator] [F : Faults Validator]
variable [Cr : Crashes Validator]
variable {BlockId : Type*} [LinearOrder BlockId] {Payload : Type*}
variable {U : KRecord Validator BlockId Payload} {K : ℕ} {H : Finset BlockId} {A : BlockId}
variable {p : Scheme.Params}

omit [LinearOrder BlockId] in
theorem mem_band {ρ : ℕ} {b : BlockId} : b ∈ Band U H ρ ↔ b ∈ H ∧ ρ ≤ (U.block b).round :=
  Finset.mem_filter

omit [LinearOrder BlockId] in
theorem band_subset {ρ : ℕ} : Band U H ρ ⊆ H := Finset.filter_subset _ _

/-- Anchoring read on `H` grows with `H`. -/
theorem AnchoredIn.mono {H' : Finset BlockId} (hsub : H ⊆ H') {y : BlockId} {d : ℕ}
    (h : AnchoredIn U K H A y d) : AnchoredIn U K H' A y d := by
  induction h with
  | anchor h => exact AnchoredIn.anchor (h.trans hsub)
  | referenced S y d _ hz href hcard hx ih =>
    exact AnchoredIn.referenced S y d ih hz href hcard (hx.trans hsub)
  | reached S m y d y' d' _ hz _ hmz hm href hcard hc hx ih ih' =>
    exact AnchoredIn.reached S m y d y' d' ih hz ih' hmz hm href hcard hc (hx.trans hsub)

/-- The available sub-DAG read on `H` grows with `H`. -/
theorem availIn_mono {H' : Finset BlockId} (hsub : H ⊆ H') {z : BlockId}
    (hz : z ∈ AvailIn U K H A) : z ∈ AvailIn U K H' A := by
  obtain ⟨y, d, hy, hzy⟩ := hz
  exact ⟨y, d, hy.mono hsub, hzy⟩

/-- A history to depth `d` of a block at round `ρ + d` or above, held in
`H`, is held in the band of `H` from `ρ`. -/
theorem historyUpto_subset_band (hH : H ⊆ U.ids) {ρ d : ℕ} {x : BlockId}
    (hx : historyUpto U d x ⊆ H) (hρ : ρ + d ≤ (U.block x).round) :
    historyUpto U d x ⊆ Band U H ρ := by
  have hxi : x ∈ U.ids := hH (hx mem_historyUpto_self)
  intro w hw
  have := (round_of_mem_historyUpto d hxi hw).2
  exact mem_band.mpr ⟨hx hw, by omega⟩

/-- **An anchor point at round `ρ + K` or above is an anchor point on the band
of `H` from `ρ`.** -/
theorem AnchoredIn.band (hH : H ⊆ U.ids) {ρ : ℕ} {y : BlockId} {d : ℕ}
    (h : AnchoredIn U K H A y d) :
    ρ + K ≤ (U.block y).round → AnchoredIn U K (Band U H ρ) A y d := by
  induction h with
  | anchor h => exact fun hρ => AnchoredIn.anchor (historyUpto_subset_band hH h hρ)
  | @referenced x S y d hy hz href hcard hx ih =>
    intro hρ
    have hup : ∀ z ∈ S, ρ + K ≤ (U.block (y z)).round := fun z hzS => by
      have hyz : y z ∈ U.ids := hH ((hy z hzS).window mem_historyUpto_self)
      have hzi : z ∈ U.ids := hH ((hy z hzS).window (hz z hzS))
      have := (U.valid z hzi).predecessor x (href z hzS)
      have := (round_of_mem_historyUpto _ hyz (hz z hzS)).1
      omega
    exact AnchoredIn.referenced S y d (fun z hzS => ih z hzS (hup z hzS)) hz href hcard
      (historyUpto_subset_band hH hx hρ)
  | @reached x S m y d y' d' hy hz hy' hmz hm href hcard hc hx ih ih' =>
    intro hρ
    have hup : ∀ z ∈ S, ρ + K ≤ (U.block (y z)).round ∧ ρ + K ≤ (U.block (y' z)).round :=
      fun z hzS => by
        have hyz : y z ∈ U.ids := hH ((hy z hzS).window mem_historyUpto_self)
        have hyz' : y' z ∈ U.ids := hH ((hy' z hzS).window mem_historyUpto_self)
        have hzi : z ∈ U.ids := hH ((hy z hzS).window (hz z hzS))
        have hmi : m z ∈ U.ids := hH ((hy' z hzS).window (hmz z hzS))
        have := (U.valid (m z) hmi).predecessor x (href z hzS)
        have := (U.valid z hzi).predecessor (m z) (hm z hzS)
        have := (round_of_mem_historyUpto _ hyz (hz z hzS)).1
        have := (round_of_mem_historyUpto _ hyz' (hmz z hzS)).1
        omega
    exact AnchoredIn.reached S m y d y' d' (fun z hzS => ih z hzS (hup z hzS).1) hz
      (fun z hzS => ih' z hzS (hup z hzS).2) hmz hm href hcard hc
      (historyUpto_subset_band hH hx (by omega))

/-- **The available sub-DAG above round `ρ + K` is read on the band from
`ρ`.** -/
theorem availIn_band_iff (hH : H ⊆ U.ids) {ρ : ℕ} {z : BlockId}
    (hz : ρ + K ≤ (U.block z).round) : z ∈ AvailIn U K (Band U H ρ) A ↔ z ∈ AvailIn U K H A := by
  refine ⟨availIn_mono band_subset, fun ⟨y, d, hy, hzy⟩ => ⟨y, d, hy.band hH ?_, hzy⟩⟩
  have hyi : y ∈ U.ids := hH (hy.window mem_historyUpto_self)
  have := (round_of_mem_historyUpto d hyi hzy).1
  omega

/-- **The indirect test for a slot at round `r`, with `ρ + K ≤ r + 1`, is
read on the band from `ρ`**, at a row. -/
theorem linkedIn_band_iff (hH : H ⊆ U.ids) (hrow : Row Validator p) {ρ r : ℕ}
    (hr : ρ + K ≤ r + 1) {L : BlockId} :
    LinkedIn p U K (Band U H ρ) A L r ↔ LinkedIn p U K H A L r := by
  constructor
  · rintro ⟨X, hX, hXn⟩
    exact ⟨X, fun C hC => ⟨availIn_mono band_subset (hX C hC).1, (hX C hC).2.1,
      fun hv j hj => availIn_mono band_subset ((hX C hC).2.2 hv j hj)⟩, hXn⟩
  · rintro ⟨X, hX, hXn⟩
    refine ⟨X, fun C hC => ?_, hXn⟩
    obtain ⟨hCa, hCc, hrefs⟩ := hX C hC
    have hCi : C ∈ U.ids := hH (availIn_subset_held hCa)
    have hCr := hCc.1
    have hw : 2 ≤ p.waveLength := by rcases hrow with ⟨-, h, -⟩ | ⟨-, h, -⟩ <;> omega
    refine ⟨(availIn_band_iff hH (by omega)).mpr hCa, hCc, fun hv j hj => ?_⟩
    have := (U.valid C hCi).predecessor j hj
    have := (row_wave hrow).2 hv
    exact (availIn_band_iff hH (by omega)).mpr (hrefs hv j hj)

/-- **The fetch test down to `ρ'`, with `ρ + K ≤ ρ'`, below an anchor at round
`ρ + K` or above, is read on the band from `ρ`.** -/
theorem fetchedIn_band_iff (hH : H ⊆ U.ids) {ρ ρ' : ℕ} (hA : ρ + K ≤ (U.block A).round)
    (hρ : ρ + K ≤ ρ') : FetchedIn U K (Band U H ρ) A ρ' ↔ FetchedIn U K H A ρ' := by
  have up : ∀ {z : BlockId}, ρ' < (U.block z).round →
      (z ∈ AvailIn U K (Band U H ρ) A ↔ z ∈ AvailIn U K H A) := fun h =>
    availIn_band_iff hH (by omega)
  constructor
  · rintro ⟨hwin, hall, hall₂⟩
    refine ⟨hwin.trans band_subset, fun S x hS href hcard => ?_,
      fun S m x hS hm href hcard hc => ?_⟩
    · exact (hall S x (fun z hzS => ⟨(up (hS z hzS).2).mpr (hS z hzS).1, (hS z hzS).2⟩) href
        hcard).trans band_subset
    · refine (hall₂ S m x (fun z hzS => ⟨?_, (up (hS z hzS).2.2).mpr (hS z hzS).2.1,
        (hS z hzS).2.2⟩) hm href hcard hc).trans band_subset
      have hzi : z ∈ U.ids := hH (availIn_subset_held (hS z hzS).1)
      have := (U.valid z hzi).predecessor (m z) (hm z hzS)
      exact (availIn_band_iff hH (by have := (hS z hzS).2.2; omega)).mpr (hS z hzS).1
  · rintro ⟨hwin, hall, hall₂⟩
    refine ⟨historyUpto_subset_band hH hwin hA, fun S x hS href hcard => ?_,
      fun S m x hS hm href hcard hc => ?_⟩
    · obtain ⟨c, hc⟩ : (creatorsOf U.block S).Nonempty := Finset.card_pos.mp (by omega)
      obtain ⟨z, hzS, -⟩ := mem_creatorsOf.mp hc
      have hzi : z ∈ U.ids := hH (availIn_subset_held (availIn_mono band_subset (hS z hzS).1))
      have := (U.valid z hzi).predecessor x (href z hzS)
      have := (hS z hzS).2
      exact historyUpto_subset_band hH
        (hall S x (fun z hzS => ⟨availIn_mono band_subset (hS z hzS).1, (hS z hzS).2⟩) href hcard)
        (by omega)
    · obtain ⟨c, hcm⟩ : (creatorsOf U.block S).Nonempty := Finset.card_pos.mp (by omega)
      obtain ⟨z, hzS, -⟩ := mem_creatorsOf.mp hcm
      have hmi : m z ∈ U.ids := hH (availIn_subset_held (availIn_mono band_subset (hS z hzS).2.1))
      have := (U.valid (m z) hmi).predecessor x (href z hzS)
      have := (hS z hzS).2.2
      exact historyUpto_subset_band hH
        (hall₂ S m x (fun z hzS => ⟨availIn_mono band_subset (hS z hzS).1,
          availIn_mono band_subset (hS z hzS).2.1, (hS z hzS).2.2⟩) hm href hcard hc)
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

/-- An anchor point below a block of the record lies at or below it. -/
theorem AnchoredBelow.round_le (hA : A ∈ U.ids) {y : BlockId} {d : ℕ}
    (h : AnchoredBelow U K A y d) : (U.block y).round ≤ (U.block A).round := by
  induction h with
  | anchor => exact le_rfl
  | @referenced x S y d hy hz href hcard ih =>
    obtain ⟨z, hzS⟩ := nonempty_of_creatorsOf_card_pos (by omega : 0 < (creatorsOf U.block S).card)
    have hyz := (hy z hzS).mem hA
    have hzi := historyUpto_subset_ids _ hyz (hz z hzS)
    have := (U.valid z hzi).predecessor x (href z hzS)
    have := (round_of_mem_historyUpto _ hyz (hz z hzS)).1
    have := ih z hzS
    omega
  | @reached x S m y d y' d' hy hz hy' hmz hm href hcard hc ih ih' =>
    obtain ⟨z, hzS⟩ := nonempty_of_creatorsOf_card_pos (by omega : 0 < (creatorsOf U.block S).card)
    have hyz := (hy' z hzS).mem hA
    have hmi := historyUpto_subset_ids _ hyz (hmz z hzS)
    have := (U.valid (m z) hmi).predecessor x (href z hzS)
    have := (round_of_mem_historyUpto _ hyz (hmz z hzS)).1
    have := ih' z hzS
    omega

/-- What a leader outputs lies at or below it. -/
theorem round_le_of_mem_outIn {D : ℕ} {L b : BlockId} (hL : L ∈ U.ids)
    (hb : b ∈ OutIn U K H D L) : (U.block b).round ≤ (U.block L).round := by
  obtain ⟨y, d, hy, hby⟩ := availIn_subset hb.1
  have := (round_of_mem_historyUpto d (hy.mem hL) hby).1
  have := hy.round_le hL
  omega

/-! ## Building -/

omit [LinearOrder BlockId] in
/-- **A block referencing a quorum of distinct authors of the round below is
valid.** -/
theorem validAt_of_quorum {Q : Finset BlockId} {r : ℕ} {b : Block Validator BlockId Payload}
    (hQ : ∀ x ∈ Q, (U.block x).round = r) (hd : ∀ x ∈ Q, ∀ y ∈ Q,
      (U.block x).creator = (U.block y).creator → x = y)
    (hq : kQuorum Validator ≤ (creatorsOf U.block Q).card) (hbr : b.round = r + 1)
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

omit [LinearOrder BlockId] in
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

omit [LinearOrder BlockId] in
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

omit [LinearOrder BlockId] in
/-- Blocks at one round number at most `|C|` besides their Byzantine ones. -/
theorem card_round_le {ρ : ℕ} {X : Finset BlockId}
    (hX : ∀ x ∈ X, x ∈ U.ids ∧ (U.block x).round = ρ) :
    X.card ≤ (Correct : Finset Validator).card +
      (X.filter fun x => (U.block x).creator ∉ (Correct : Finset Validator)).card := by
  have hsplit := Finset.card_filter_add_card_filter_not (s := X)
    (fun x => (U.block x).creator ∈ (Correct : Finset Validator))
  have hc : (X.filter fun x => (U.block x).creator ∈ (Correct : Finset Validator)).card ≤
      (Correct : Finset Validator).card :=
    Finset.card_le_card_of_injOn (fun x => (U.block x).creator)
      (fun x hx => Finset.mem_coe.mpr (Finset.mem_filter.mp hx).2) fun i hi j hj hij => by
        obtain ⟨hiX, hic⟩ := Finset.mem_filter.mp hi
        obtain ⟨hjX, -⟩ := Finset.mem_filter.mp hj
        exact U.eq_of_creator_eq (hX i hiX).1 (hX j hjX).1 hic rfl hij.symm
          ((hX i hiX).2.trans (hX j hjX).2.symm)
  omega

/-- **One layer of a history**: at most `|C|` blocks of correct authors, and
at most `f` Byzantine blocks per block of the layer above. -/
theorem card_layers_le {x : BlockId} (hx : x ∈ U.ids) :
    ∀ d, (layers U {x} d).card ≤ layerBound (Correct : Finset Validator).card F.f d
  | 0 => by simp [layers, layerBound]
  | d + 1 => by
    classical
    have hc := card_round_le (U := U) (ρ := (U.block x).round - (d + 1)) fun w hw => by
      obtain ⟨hwi, hwr⟩ := layers_round hx (d + 1) w hw
      exact ⟨hwi, by omega⟩
    have hb : ((layers U {x} (d + 1)).filter
        fun w => (U.block w).creator ∉ (Correct : Finset Validator)).card ≤
        (layers U {x} d).card * F.f := by
      rw [layers, Finset.filter_biUnion]
      exact Finset.card_biUnion_le_card_mul _ _ _ fun p hp =>
        card_byz_refs_le (layers_round hx d p hp).1
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

theorem byzLayers_subset_layers {r : BlockId} : ∀ s, byzLayers U r s ⊆ layers U {r} s
  | 0 => subset_rfl
  | s + 1 => (Finset.biUnion_mono fun _ _ => Finset.filter_subset _ _).trans
      (Finset.biUnion_subset_biUnion_of_subset_left _ (byzLayers_subset_layers s))

/-- At most `f^s` Byzantine blocks are reached from a block by `s` references
through Byzantine blocks. -/
theorem card_byzLayers_le {r : BlockId} (hr : r ∈ U.ids) :
    ∀ s, (byzLayers U r s).card ≤ F.f ^ s
  | 0 => by simp [byzLayers]
  | s + 1 => by
    refine (Finset.card_biUnion_le_card_mul _ _ _ fun p hp =>
      card_byz_refs_le (layers_round hr s p (byzLayers_subset_layers s hp)).1).trans ?_
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

/-- **Every Byzantine block of a history below an anchor point hangs below a
root**: a block of a correct author or an anchor point, at most as many
rounds above it as the history's top, reached through Byzantine blocks. -/
theorem exists_root (hA : A ∈ U.ids) {y : BlockId} {e : ℕ} (hy : AnchoredBelow U K A y e) :
    ∀ d z, z ∈ historyUpto U e y → (U.block y).round = (U.block z).round + d →
      (U.block z).creator ∉ (Correct : Finset Validator) →
      ∃ s r, s ≤ d ∧ r ∈ U.ids ∧ (U.block r).round = (U.block z).round + s ∧
        ((U.block r).creator ∈ (Correct : Finset Validator) ∨ ∃ d', AnchoredBelow U K A r d') ∧
        z ∈ byzLayers U r s := by
  classical
  have hyi := hy.mem hA
  intro d
  induction d using Nat.strong_induction_on with
  | _ d ih =>
    intro z hz hdr hzc
    by_cases hzy : z = y
    · subst hzy
      exact ⟨0, z, Nat.zero_le _, hyi, rfl, Or.inr ⟨e, hy⟩, Finset.mem_singleton_self _⟩
    obtain ⟨p, hp, hzp⟩ := exists_parent e hz hzy
    have hpi := historyUpto_subset_ids e hyi hp
    have hpr := (U.valid p hpi).predecessor z hzp
    have hpy := (round_of_mem_historyUpto e hyi hp).1
    by_cases hroot : (U.block p).creator ∈ (Correct : Finset Validator) ∨
        ∃ d', AnchoredBelow U K A p d'
    · exact ⟨1, p, by omega, hpi, by omega, hroot, Finset.mem_biUnion.mpr
        ⟨p, Finset.mem_singleton_self _, Finset.mem_filter.mpr ⟨hzp, hzc⟩⟩⟩
    · push Not at hroot
      obtain ⟨s, r, hs, hri, hrr, hrt, hpr'⟩ := ih (d - 1) (by omega) p hp (by omega) hroot.1
      exact ⟨s + 1, r, by omega, hri, by omega, hrt, Finset.mem_biUnion.mpr
        ⟨p, hpr', Finset.mem_filter.mpr ⟨hzp, hzc⟩⟩⟩

/-- The tags of the ways a correct block anchors a block: by reference, and,
when validators may crash for good, through a block of each author. -/
def reachTags : Finset (Option Validator) :=
  if 1 ≤ Cr.c then Finset.univ else {none}

theorem card_reachTags : (reachTags (Validator := Validator)).card = reachWidth Validator := by
  unfold reachTags reachWidth
  split <;> simp [Fintype.card_option]; omega

/-- **One round holds at most `|C| · w · |B|` anchor points of authors in `B`
besides the anchor**, `w` the reach width: each has a correct referencer
one round up, or one reaching it through a block two rounds up, which has
one block there and references one block per author. -/
theorem card_anchored_le (hA : A ∈ U.ids) {ρ : ℕ} {B : Finset Validator} {X : Finset BlockId}
    (hX : ∀ x ∈ X, (∃ d, AnchoredBelow U K A x d) ∧ (U.block x).round = ρ ∧ x ≠ A ∧
      (U.block x).creator ∈ B) :
    X.card ≤ (Correct : Finset Validator).card * reachWidth Validator * B.card := by
  classical
  have hex : ∀ x ∈ X, ∃ w, w ∈ U.ids ∧ (U.block w).creator ∈ (Correct : Finset Validator) ∧
      ∃ t : Option BlockId, (t = none ∧ x ∈ (U.block w).refs) ∨
        ∃ v, t = some v ∧ v ∈ (U.block w).refs ∧ x ∈ (U.block v).refs ∧ 1 ≤ Cr.c := by
    intro x hx
    obtain ⟨⟨d, hxa⟩, -, hxA, -⟩ := hX x hx
    rcases hxa.eq_or_referenced with ⟨h, -⟩ | ⟨w, hw, hwc, hxw, -⟩ | ⟨w, hw, hwc, v, hv, hxv, -, hc⟩
    · exact absurd h hxA
    · exact ⟨w, avail_subset_ids hA hw, hwc, none, Or.inl ⟨rfl, hxw⟩⟩
    · exact ⟨w, avail_subset_ids hA hw, hwc, some v, Or.inr ⟨v, rfl, hv, hxv, hc⟩⟩
  choose! wf hwf using hex
  choose! tf htf using fun x hx => (hwf x hx).2.2
  have hround : ∀ {b c : BlockId}, b ∈ U.ids → c ∈ (U.block b).refs →
      (U.block c).round + 1 = (U.block b).round := fun hb hc =>
    by have := (U.valid _ hb).predecessor _ hc; omega
  have hcard : X.card ≤ (((Correct : Finset Validator) ×ˢ reachTags (Validator := Validator)) ×ˢ
      B).card := by
    refine Finset.card_le_card_of_injOn
      (fun x => (((U.block (wf x)).creator, (tf x).map fun v => (U.block v).creator),
        (U.block x).creator)) (fun x hx => ?_) fun x hx x' hx' hxx => ?_
    · refine Finset.mem_coe.mpr (Finset.mem_product.mpr ⟨Finset.mem_product.mpr
        ⟨(hwf x hx).2.1, ?_⟩, (hX x hx).2.2.2⟩)
      unfold reachTags
      rcases htf x hx with ⟨h, -⟩ | ⟨v, h, -, -, hc⟩
      · split <;> simp [h]
      · simp [h, hc]
    · obtain ⟨hw, hwC, -⟩ := hwf x hx
      obtain ⟨hw', -, -⟩ := hwf x' hx'
      simp only [Prod.mk.injEq] at hxx
      obtain ⟨⟨h1, h2⟩, h3⟩ := hxx
      have hxr := (hX x hx).2.1
      have hxr' := (hX x' hx').2.1
      rcases htf x hx with ⟨ht, hxw⟩ | ⟨v, ht, hvw, hxv, -⟩ <;>
        rcases htf x' hx' with ⟨ht', hxw'⟩ | ⟨v', ht', hvw', hxv', -⟩ <;>
        simp only [ht, ht', Option.map_none, Option.map_some, reduceCtorEq,
          Option.some.injEq] at h2
      · have hww : wf x = wf x' := U.eq_of_creator_eq hw hw' hwC rfl h1.symm
          (by have := hround hw hxw; have := hround hw' hxw'; omega)
        rw [← hww] at hxw'
        exact (U.valid _ hw).clause x hxw x' hxw' h3
      · have hv := U.complete _ hw _ hvw
        have hww : wf x = wf x' := U.eq_of_creator_eq hw hw' hwC rfl h1.symm
          (by have := hround hw hvw; have := hround hv hxv; have := hround hw' hvw'
              have := hround (U.complete _ hw' _ hvw') hxv'; omega)
        rw [← hww] at hvw'
        have hvv : v = v' := (U.valid _ hw).clause v hvw v' hvw' h2
        subst hvv
        exact (U.valid _ hv).clause x hxv x' hxv' h3
  rwa [Finset.card_product, Finset.card_product, card_reachTags] at hcard

/-- One round holds at most `|C|(w f + 1) + 1` roots, `w` the reach width:
blocks of correct authors, and anchor points. -/
theorem card_roots_le (hA : A ∈ U.ids) {ρ : ℕ} {X : Finset BlockId}
    (hX : ∀ x ∈ X, x ∈ U.ids ∧ (U.block x).round = ρ ∧
      ((U.block x).creator ∈ (Correct : Finset Validator) ∨ ∃ d, AnchoredBelow U K A x d)) :
    X.card ≤ (Correct : Finset Validator).card * (reachWidth Validator * F.f + 1) + 1 := by
  classical
  have hc := card_round_le (U := U) fun x hx => ⟨(hX x hx).1, (hX x hx).2.1⟩
  have h1 := Finset.pred_card_le_card_erase (s := X.filter
    fun x => (U.block x).creator ∉ (Correct : Finset Validator)) (a := A)
  have hb := card_anchored_le hA (ρ := ρ) (B := F.byzantine) (X := (X.filter
    fun x => (U.block x).creator ∉ (Correct : Finset Validator)).erase A) fun x hx => by
      obtain ⟨hxA, hxf⟩ := Finset.mem_erase.mp hx
      obtain ⟨hxX, hxc⟩ := Finset.mem_filter.mp hxf
      obtain ⟨-, hxr, hxa⟩ := hX x hxX
      exact ⟨hxa.resolve_left hxc, hxr, hxA, by simpa [mem_correct] using hxc⟩
  have := Nat.mul_le_mul_left ((Correct : Finset Validator).card * reachWidth Validator)
    F.card_byzantine
  rw [Nat.mul_add, Nat.mul_one, ← Nat.mul_assoc]
  omega

/-- **The available sub-DAG holds at most `|C| + (|C|(w f + 1) + 1)(1 + f + ⋯ +
f^K)` blocks per round**, `w` the reach width, with no condition on
equivocation: its correct blocks number at most `|C|`, and each Byzantine
block hangs at most `K` rounds below a root through Byzantine blocks. -/
theorem card_avail_round_le (hA : A ∈ U.ids) {ρ : ℕ} {Z : Finset BlockId}
    (hZ : ∀ z ∈ Z, z ∈ Avail U K A ∧ (U.block z).round = ρ) :
    Z.card ≤ (Correct : Finset Validator).card +
      ((Correct : Finset Validator).card * (reachWidth Validator * F.f + 1) + 1) *
        ∑ s ∈ Finset.range (K + 1), F.f ^ s := by
  classical
  have hc := card_round_le (U := U) fun z hz => ⟨avail_subset_ids hA (hZ z hz).1, (hZ z hz).2⟩
  let R : ℕ → Finset BlockId := fun t => U.ids.filter fun r => (U.block r).round = t ∧
    ((U.block r).creator ∈ (Correct : Finset Validator) ∨ ∃ d, AnchoredBelow U K A r d)
  have hsub : Z.filter (fun z => (U.block z).creator ∉ (Correct : Finset Validator)) ⊆
      (Finset.range (K + 1)).biUnion fun s => (R (ρ + s)).biUnion fun r => byzLayers U r s := by
    intro z hz
    obtain ⟨hzZ, hzc⟩ := Finset.mem_filter.mp hz
    obtain ⟨⟨y, e, hy, hzy⟩, hzr⟩ := hZ z hzZ
    have hyz := round_of_mem_historyUpto e (hy.mem hA) hzy
    have hek := hy.le
    obtain ⟨s, r, hs, hri, hrr, hrt, hzr'⟩ := exists_root hA hy
      ((U.block y).round - (U.block z).round) z hzy (by omega) hzc
    exact Finset.mem_biUnion.mpr ⟨s, Finset.mem_range.mpr (by omega),
      Finset.mem_biUnion.mpr ⟨r, Finset.mem_filter.mpr ⟨hri, by omega, hrt⟩, hzr'⟩⟩
  have hb : (Z.filter fun z => (U.block z).creator ∉ (Correct : Finset Validator)).card ≤
      ((Correct : Finset Validator).card * (reachWidth Validator * F.f + 1) + 1) *
        ∑ s ∈ Finset.range (K + 1), F.f ^ s := by
    refine (Finset.card_le_card hsub).trans (Finset.card_biUnion_le.trans ?_)
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun s _ => (Finset.card_biUnion_le_card_mul _ _ _ fun r hr =>
      card_byzLayers_le (Finset.mem_filter.mp hr).1 s).trans (Nat.mul_le_mul_right _ ?_)
    exact card_roots_le hA fun x hx => Finset.mem_filter.mp hx
  omega

variable [S : Slots Validator]

/-! ## Decisions read a band -/

/-- **A decision passes between two held sets**, for a slot at round
`ρ + K − 1` or above, and not below `ρ`, when they agree above `ρ` on the
blocks held with their references, on the indirect test and on the fetch
test. -/
theorem nodeDecided_of_agree (hrow : Row Validator p) {H₁ H₂ : Finset BlockId}
    (hH₁ : H₁ ⊆ U.ids) {ρ : ℕ}
    (hheld : ∀ s : Finset BlockId, (∀ b ∈ s, b ∈ U.ids ∧ ρ + 1 ≤ (U.block b).round) →
      heldWithRefs U H₁ s = heldWithRefs U H₂ s)
    (hlink : ∀ A L r, ρ + K ≤ r + 1 → (LinkedIn p U K H₁ A L r ↔ LinkedIn p U K H₂ A L r))
    (hfetch : ∀ A ρ', ρ + K ≤ (U.block A).round → ρ + K ≤ ρ' →
      (FetchedIn U K H₁ A ρ' ↔ FetchedIn U K H₂ A ρ'))
    {i : ℕ} {v : Option BlockId} (h : NodeDecided p U K H₁ i v) :
    ρ ≤ S.slotRound i → ρ + K ≤ S.slotRound i + 1 → NodeDecided p U K H₂ i v := by
  have hw : 2 ≤ p.waveLength := by rcases hrow with ⟨-, h, -⟩ | ⟨-, h, -⟩ <;> omega
  induction h with
  | @directCommit k L hL hc =>
    intro h1 h2
    refine NodeDecided.directCommit hL ?_
    rw [← hheld _ fun b hb => by
      obtain ⟨hbi, hbr⟩ := mem_certsFor hb
      exact ⟨hbi, by omega⟩]
    exact hc
  | @directSkip k hs =>
    intro h1 h2
    refine NodeDecided.directSkip ?_
    rw [← hheld _ fun b hb => by
      obtain ⟨hbi, hbr⟩ := mem_blocksAt.mp (Finset.mem_filter.mp hb).1
      exact ⟨hbi, by omega⟩]
    exact hs
  | @indirectCommit k j A L hkj helig hj hmid hf hL hl hleast ihj ihm =>
    intro h1 h2
    have hkj' := S.mono hkj.le
    have hA := (hj.voted hrow hH₁).1
    have hAr : ρ + K ≤ (U.block A).round := by
      rw [hA.2.1]; have := eligibleAt_iff.mp helig; omega
    exact NodeDecided.indirectCommit hkj helig (ihj (by omega) (by omega))
      (fun m h3 h4 h5 => ihm m h3 h4 h5 (by have := S.mono h3.le; omega)
        (by have := S.mono h3.le; omega)) ((hfetch A _ hAr (by omega)).mp hf) hL
      ((hlink A L _ h2).mp hl) fun L' hL' hlt hl' => hleast L' hL' hlt ((hlink A L' _ h2).mpr hl')
  | @indirectSkip k j A hkj helig hj hmid hf hnone ihj ihm =>
    intro h1 h2
    have hkj' := S.mono hkj.le
    have hA := (hj.voted hrow hH₁).1
    have hAr : ρ + K ≤ (U.block A).round := by
      rw [hA.2.1]; have := eligibleAt_iff.mp helig; omega
    exact NodeDecided.indirectSkip hkj helig (ihj (by omega) (by omega))
      (fun m h3 h4 h5 => ihm m h3 h4 h5 (by have := S.mono h3.le; omega)
        (by have := S.mono h3.le; omega))
      ((hfetch A _ hAr (by omega)).mp hf) fun L hL hl' => hnone L hL ((hlink A L _ h2).mpr hl')

/-- **A decision of a slot at round `ρ + K − 1` or above, and not below `ρ`,
reads only the band from `ρ`.** -/
theorem nodeDecided_band_iff (hrow : Row Validator p) (hH : H ⊆ U.ids) {ρ i : ℕ}
    {v : Option BlockId} (h1 : ρ ≤ S.slotRound i) (h2 : ρ + K ≤ S.slotRound i + 1) :
    NodeDecided p U K (Band U H ρ) i v ↔ NodeDecided p U K H i v := by
  have hw : 2 ≤ p.waveLength := by rcases hrow with ⟨-, h, -⟩ | ⟨-, h, -⟩ <;> omega
  exact ⟨fun h => nodeDecided_of_agree hrow (band_subset.trans hH)
      (fun _ hs => heldWithRefs_band hs) (fun _ _ _ hr => linkedIn_band_iff hH hrow hr)
      (fun _ _ hA hρ => fetchedIn_band_iff hH hA hρ) h h1 h2,
    fun h => nodeDecided_of_agree hrow hH (fun _ hs => (heldWithRefs_band hs).symm)
      (fun _ _ _ hr => (linkedIn_band_iff hH hrow hr).symm)
      (fun _ _ hA hρ => (fetchedIn_band_iff hH hA hρ).symm) h h1 h2⟩

/-- **Progress from a band**: on a responsive run, a node holding the blocks
of `T` over the run with their references, and the available sub-DAG below
every voted leader up to the run's end from round `ρ` up, decides every
slot up to the run's end at round `ρ + K − 1` or above, and not below `ρ`. -/
theorem nodeDecided_of_run_band (hrow : Row Validator p) (hlive : LiveRow Validator p)
    {T : Finset Validator} (hcard : kQuorum Validator ≤ T.card) (hH : H ⊆ U.ids)
    {b c ρ : ℕ} (hc : 0 < c)
    (hspan : ∀ b i, i < b → EligibleAt (S := S) (p.waveLength - 1) i (b + c - 1))
    (hresp : ∀ j, b ≤ j → j ≤ b + c - 1 → Responds U T j)
    (hW : WithRefs U T (S.slotRound b) (S.slotRound (b + c - 1) + 2) ⊆ ↑H)
    (hav : ∀ z ∈ AvailBelow U K (b + c - 1), ρ ≤ (U.block z).round → z ∈ H) :
    ∀ i, i < b + c → ρ ≤ S.slotRound i → ρ + K ≤ S.slotRound i + 1 →
      ∃ v, NodeDecided p U K H i v := by
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
    refine (Finset.filter_union _ _ _).trans (Finset.union_eq_left.mpr fun z hz => ?_)
    obtain ⟨hz, hρ⟩ := Finset.mem_filter.mp hz
    exact mem_band.mpr ⟨hav z (Finset.mem_filter.mp hz).2 hρ, hρ⟩
  intro i hi h1 h2
  obtain ⟨v, hv⟩ := nodeDecided_of_run hrow hlive hcard hH' hc hspan hresp hheld i hi
  have := (nodeDecided_band_iff hrow hH' h1 h2).mpr hv
  rw [heq] at this
  exact ⟨v, (nodeDecided_band_iff hrow hH h1 h2).mp this⟩

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
