import LeanDag.KPartialDag.Model.Node
import LeanDag.KPartialDag.Helpers.Rule
/-!
# What a node reads — helpers

`docs/kpartial.md` §5. A history to depth `K` that a node holds is the same
under every block map agreeing on what it holds
(`historyUptoFrom_eq_of_subset`), so the sub-DAG read on `H`, the indirect
test and the fetch test read only `H` (`linkedIn_congr`, `fetchedIn_congr`).
Read on `H`, the sub-DAG lies in the record's (`availIn_subset`), so a link
read on `H` is the record's (`linkedIn_avail`); once it is fetched it is the
record's whole sub-DAG (`avail_subset_availIn`), so the record's link is read
on `H` too (`avail_linkedIn`). Holding the record's sub-DAG fetches it
(`fetchedIn_of_subset`). So a decision a node takes on what it holds is a
decision on every view holding it (`NodeDecided.decided`).
-/

namespace LeanDag

namespace KPartialDag

variable {Validator : Type*} [Fintype Validator] [DecidableEq Validator] [F : Faults Validator]
variable {BlockId : Type*} [DecidableEq BlockId] {Payload : Type*}
variable {U U' : KRecord Validator BlockId Payload} {K : ℕ} {H : Finset BlockId} {A : BlockId}

omit [Fintype Validator] [DecidableEq Validator] in
/-- **A held history is read alike** under two block maps agreeing on what
is held. -/
theorem historyUptoFrom_eq_of_subset {blk blk' : BlockId → Block Validator BlockId Payload}
    (hb : ∀ i ∈ H, blk i = blk' i) :
    ∀ (n : ℕ) (x : BlockId), historyUptoFrom blk n x ⊆ H →
      historyUptoFrom blk' n x = historyUptoFrom blk n x
  | 0, _, _ => rfl
  | n + 1, x, h => by
    have hx : x ∈ H := h mem_historyUptoFrom_self
    rw [historyUptoFrom_succ, historyUptoFrom_succ, ← hb x hx]
    refine congrArg (insert x) (Finset.biUnion_congr rfl fun j hj =>
      historyUptoFrom_eq_of_subset hb n j fun i hi => h ?_)
    rw [historyUptoFrom_succ]
    exact Finset.mem_insert_of_mem (Finset.mem_biUnion.mpr ⟨j, hj, hi⟩)

/-- A held history of a record is read alike on a record agreeing on what
is held. -/
theorem historyUpto_eq_of_subset (hb : ∀ i ∈ H, U.block i = U'.block i) {y : BlockId}
    (h : historyUpto U K y ⊆ H) : historyUpto U' K y = historyUpto U K y :=
  historyUptoFrom_eq_of_subset hb K y h

/-- A block anchored in `H` has its history to depth `K` held. -/
theorem AnchoredIn.window {y : BlockId} (h : AnchoredIn U K H A y) : historyUpto U K y ⊆ H := by
  cases h with
  | anchor h => exact h
  | referenced _ _ _ _ _ _ hx => exact hx

/-- The sub-DAG read on `H` is held. -/
theorem availIn_subset_held {z : BlockId} (hz : z ∈ AvailIn U K H A) : z ∈ H := by
  obtain ⟨y, hy, hzy⟩ := hz
  exact hy.window hzy

/-- **Anchoring read on `H` reads only `H`.** -/
theorem AnchoredIn.congr (hb : ∀ i ∈ H, U.block i = U'.block i) {x : BlockId}
    (h : AnchoredIn U K H A x) : AnchoredIn U' K H A x := by
  have hwin : ∀ y, historyUpto U K y ⊆ H → historyUpto U' K y = historyUpto U K y :=
    fun y hy => historyUptoFrom_eq_of_subset hb K y hy
  induction h with
  | anchor h => exact AnchoredIn.anchor (by rw [hwin A h]; exact h)
  | @referenced x S y hy hz href hcard hx ih =>
    have hSH : ∀ z ∈ S, z ∈ H := fun z hzS => (hy z hzS).window (hz z hzS)
    refine AnchoredIn.referenced S y ih (fun z hzS => ?_) (fun z hzS => ?_) ?_
      (by rw [hwin x hx]; exact hx)
    · rw [hwin (y z) (hy z hzS).window]; exact hz z hzS
    · rw [← hb z (hSH z hzS)]; exact href z hzS
    · have : creatorsOf U'.block S = creatorsOf U.block S :=
        Finset.image_congr fun z hzS => by rw [hb z (hSH z hzS)]
      rw [this]; exact hcard

/-- **The sub-DAG read on `H` reads only `H`.** -/
theorem availIn_congr (hb : ∀ i ∈ H, U.block i = U'.block i) :
    AvailIn U K H A = AvailIn U' K H A := by
  have hb' : ∀ i ∈ H, U'.block i = U.block i := fun i hi => (hb i hi).symm
  ext z
  constructor
  · rintro ⟨y, hy, hzy⟩
    refine ⟨y, hy.congr hb, ?_⟩
    rw [historyUpto_eq_of_subset hb hy.window]; exact hzy
  · rintro ⟨y, hy, hzy⟩
    refine ⟨y, hy.congr hb', ?_⟩
    rw [historyUpto_eq_of_subset hb' hy.window]; exact hzy

/-- **The indirect test read on `H` reads only `H`.** -/
theorem linkedIn_congr (hb : ∀ i ∈ H, U.block i = U'.block i) {L : BlockId} {r : ℕ} :
    LinkedIn U K H A L r → LinkedIn U' K H A L r := by
  rintro ⟨C, hC, hCr, hrefs, hv⟩
  have hav := availIn_congr (K := K) (A := A) hb
  have hCH := availIn_subset_held hC
  rw [hav] at hC
  refine ⟨C, hC, by rw [← hb C hCH]; exact hCr, fun j hj => ?_, ?_⟩
  · rw [← hb C hCH] at hj; rw [← hav]; exact hrefs j hj
  · unfold CarriesVotes carriedVotes at hv ⊢
    have hset : ((U'.block C).refs.filter fun b => IsVote U' b L) =
        ((U.block C).refs.filter fun b => IsVote U b L) := by
      rw [← hb C hCH]
      refine Finset.filter_congr fun b hbC => ?_
      change L ∈ (U'.block b).refs ↔ L ∈ (U.block b).refs
      rw [hb b (availIn_subset_held (hrefs b hbC))]
    rw [hset]
    have : creatorsOf U'.block ((U.block C).refs.filter fun b => IsVote U b L) =
        creatorsOf U.block ((U.block C).refs.filter fun b => IsVote U b L) :=
      Finset.image_congr fun b hbC => by
        rw [hb b (availIn_subset_held (hrefs b (Finset.mem_filter.mp hbC).1))]
    rw [this]; exact hv

/-- **The fetch test reads only `H`.** -/
theorem fetchedIn_congr (hb : ∀ i ∈ H, U.block i = U'.block i) :
    FetchedIn U K H A → FetchedIn U' K H A := by
  rintro ⟨hA, hall⟩
  have hb' : ∀ i ∈ H, U'.block i = U.block i := fun i hi => (hb i hi).symm
  have hav := availIn_congr (K := K) (A := A) hb
  refine ⟨by rw [historyUpto_eq_of_subset hb hA]; exact hA, fun S x hS href hcard => ?_⟩
  have hSH : ∀ z ∈ S, z ∈ H := fun z hz => availIn_subset_held (hav ▸ hS z hz)
  have hx := hall S x (fun z hz => hav ▸ hS z hz)
    (fun z hz => by rw [hb z (hSH z hz)]; exact href z hz)
    (by
      have : creatorsOf U.block S = creatorsOf U'.block S :=
        Finset.image_congr fun z hz => by rw [hb z (hSH z hz)]
      rw [this]; exact hcard)
  rw [historyUpto_eq_of_subset hb hx]; exact hx

/-- A block anchored in `H` is anchored below `A`. -/
theorem AnchoredIn.toBelow {y : BlockId} (h : AnchoredIn U K H A y) : AnchoredBelow U K A y := by
  induction h with
  | anchor => exact AnchoredBelow.anchor
  | referenced S y hy hz href hcard hx ih => exact AnchoredBelow.referenced S y ih hz href hcard

/-- **The sub-DAG read on `H` lies in the record's.** -/
theorem availIn_subset {z : BlockId} (hz : z ∈ AvailIn U K H A) : z ∈ Avail U K A := by
  obtain ⟨y, hy, hzy⟩ := hz
  exact ⟨y, hy.toBelow, hzy⟩

/-- **A link read on `H` is the record's**, for blocks of the record. -/
theorem linkedIn_avail (hH : H ⊆ U.ids) {L : BlockId} {r : ℕ} (h : LinkedIn U K H A L r) :
    AvailLinked U K A L r := by
  obtain ⟨C, hC, hCr, hrefs, hv⟩ := h
  exact ⟨C, mem_certificatesAt.mpr ⟨hH (availIn_subset_held hC), hCr, hv⟩, availIn_subset hC,
    fun j hj => availIn_subset (hrefs j hj)⟩

/-- **A fetched sub-DAG is the record's whole sub-DAG.** -/
theorem avail_subset_availIn (hf : FetchedIn U K H A) {z : BlockId} (hz : z ∈ Avail U K A) :
    z ∈ AvailIn U K H A := by
  obtain ⟨y, hy, hzy⟩ := hz
  suffices h : AnchoredIn U K H A y from ⟨y, h, hzy⟩
  clear hzy
  induction hy with
  | anchor => exact AnchoredIn.anchor hf.1
  | @referenced x S y hy hz href hcard ih =>
    exact AnchoredIn.referenced S y ih hz href hcard
      (hf.2 S x (fun z hzS => ⟨y z, ih z hzS, hz z hzS⟩) href hcard)

/-- **On a fetched sub-DAG, the record's link is read on `H`.** -/
theorem avail_linkedIn (hf : FetchedIn U K H A) {L : BlockId} {r : ℕ}
    (h : AvailLinked U K A L r) : LinkedIn U K H A L r := by
  obtain ⟨C, hC, hCa, hrefs⟩ := h
  obtain ⟨-, hCr, hv⟩ := mem_certificatesAt.mp hC
  exact ⟨C, avail_subset_availIn hf hCa, hCr, fun j hj => avail_subset_availIn hf (hrefs j hj),
    hv⟩

/-- **Holding the record's sub-DAG fetches it.** -/
theorem fetchedIn_of_subset (hsub : ∀ z ∈ Avail U K A, z ∈ H) : FetchedIn U K H A := by
  classical
  refine ⟨fun z hz => hsub z ⟨A, AnchoredBelow.anchor, hz⟩, fun S x hS href hcard => ?_⟩
  let y : BlockId → BlockId := fun z => if h : z ∈ Avail U K A then h.choose else A
  have hy : ∀ z ∈ S, AnchoredBelow U K A (y z) ∧ z ∈ historyUpto U K (y z) := fun z hz => by
    have h := availIn_subset (hS z hz)
    simp only [y, dif_pos h]
    exact h.choose_spec
  have hx : AnchoredBelow U K A x :=
    AnchoredBelow.referenced S y (fun z hz => (hy z hz).1) (fun z hz => (hy z hz).2) href hcard
  exact fun z hz => hsub z ⟨x, hx, hz⟩

variable [S : Slots Validator]

omit S in
/-- Blocks a node holds with their references are held by a view holding
what the node holds. -/
theorem holdsAtLeast_of_held {V : U.View} (hHV : H ⊆ V.ids) {s : Finset BlockId}
    (h : quorumCard Validator ≤ (creatorsOf U.block (heldWithRefs U H s)).card) :
    HoldsAtLeast U V (quorumCard Validator) s :=
  h.trans (Finset.card_le_card (Finset.image_subset_image fun b hb => by
    obtain ⟨hbs, hbH, -⟩ := Finset.mem_filter.mp hb
    exact Finset.mem_inter.mpr ⟨hbs, hHV hbH⟩))

/-- **A node's decision is a decision on every view holding what it holds**,
for a node holding blocks of the record. -/
theorem NodeDecided.decided (hH : H ⊆ U.ids) {V : U.View} (hHV : H ⊆ V.ids) {k : ℕ}
    {v : Option BlockId} (h : NodeDecided U K H k v) : (kRule K).Decided U V k v := by
  induction h with
  | directCommit hL hc => exact AnchoredRule.Decided.directCommit hL (holdsAtLeast_of_held hHV hc)
  | directSkip hs => exact AnchoredRule.Decided.directSkip (holdsAtLeast_of_held hHV hs)
  | indirectCommit hkj helig _ _ hL hlink ihj ihm =>
    exact AnchoredRule.Decided.indirectCommit_single rfl (fun _ _ h => h) hkj helig ihj ihm hL
      (linkedIn_avail hH hlink)
  | indirectSkip hkj helig _ _ hf hnone ihj ihm =>
    exact AnchoredRule.Decided.indirectSkip_single rfl hkj helig ihj ihm
      (fun L hL hlink => hnone L hL (avail_linkedIn hf hlink))

end KPartialDag

end LeanDag
