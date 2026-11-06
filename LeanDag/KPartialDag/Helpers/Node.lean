import LeanDag.KPartialDag.Model.Node
import LeanDag.KPartialDag.Helpers.Rule
/-!
# What a node reads — helpers

`docs/kpartial.md` §5. A node's tests read only what it holds, holding the
sub-DAG fetches it (`fetchedIn_of_subset`), and a node's decision is one on
every view holding what it holds (`NodeDecided.decided`).
-/

namespace LeanDag

namespace KPartialDag

variable {Validator : Type*} [Fintype Validator] [DecidableEq Validator] [F : Faults Validator]
variable {BlockId : Type*} [LinearOrder BlockId] {Payload : Type*}
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
  induction h with
  | anchor h => exact AnchoredIn.anchor (by rw [historyUpto_eq_of_subset hb h]; exact h)
  | @referenced x S y hy hz href hcard hx ih =>
    have hSH : ∀ z ∈ S, z ∈ H := fun z hzS => (hy z hzS).window (hz z hzS)
    refine AnchoredIn.referenced S y ih (fun z hzS => ?_) (fun z hzS => ?_) ?_
      (by rw [historyUpto_eq_of_subset hb hx]; exact hx)
    · rw [historyUpto_eq_of_subset hb (hy z hzS).window]; exact hz z hzS
    · rw [← hb z (hSH z hzS)]; exact href z hzS
    · have : creatorsOf U'.block S = creatorsOf U.block S :=
        Finset.image_congr fun z hzS => by rw [hb z (hSH z hzS)]
      rw [this]; exact hcard

/-- **The sub-DAG read on `H` reads only `H`.** -/
theorem availIn_congr (hb : ∀ i ∈ H, U.block i = U'.block i) :
    AvailIn U K H A = AvailIn U' K H A := by
  have sub : ∀ {U U' : KRecord Validator BlockId Payload}, (∀ i ∈ H, U.block i = U'.block i) →
      AvailIn U K H A ⊆ AvailIn U' K H A := fun hb z ⟨y, hy, hzy⟩ =>
    ⟨y, hy.congr hb, by rw [historyUpto_eq_of_subset hb hy.window]; exact hzy⟩
  exact (sub hb).antisymm (sub fun i hi => (hb i hi).symm)

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
theorem fetchedIn_congr (hb : ∀ i ∈ H, U.block i = U'.block i) {ρ : ℕ} :
    FetchedIn U K H A ρ → FetchedIn U' K H A ρ := by
  rintro ⟨hA, hall⟩
  have hav := availIn_congr (K := K) (A := A) hb
  refine ⟨by rw [historyUpto_eq_of_subset hb hA]; exact hA, fun S x hS href hcard => ?_⟩
  have hSH : ∀ z ∈ S, z ∈ H := fun z hz => availIn_subset_held (hav ▸ (hS z hz).1)
  have hx := hall S x (fun z hz => ⟨hav ▸ (hS z hz).1, by rw [hb z (hSH z hz)]; exact (hS z hz).2⟩)
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

/-- **A block of the history to depth `n` of a block of the record** lies at
most `n` rounds below it. -/
theorem round_of_mem_historyUpto : ∀ (n : ℕ) {y w : BlockId}, y ∈ U.ids →
    w ∈ historyUpto U n y → (U.block w).round ≤ (U.block y).round ∧
      (U.block y).round ≤ (U.block w).round + n
  | 0, y, w, _, hw => by
    rw [historyUpto_zero, Finset.mem_singleton] at hw
    subst hw; omega
  | n + 1, y, w, hy, hw => by
    rcases mem_historyUpto_succ.mp hw with rfl | ⟨j, hj, hwj⟩
    · omega
    · have hr := (U.valid y hy).predecessor j hj
      have := round_of_mem_historyUpto n (U.complete y hy j hj) hwj
      omega

/-- **A sub-DAG fetched down to round `ρ` is the record's above `ρ`.** -/
theorem avail_subset_availIn (hH : H ⊆ U.ids) {ρ : ℕ} (hf : FetchedIn U K H A ρ) {z : BlockId}
    (hz : z ∈ Avail U K A) (hρ : ρ ≤ (U.block z).round) : z ∈ AvailIn U K H A := by
  have hA : A ∈ U.ids := hH (hf.1 mem_historyUpto_self)
  obtain ⟨y, hy, hzy⟩ := hz
  suffices h : ρ ≤ (U.block y).round → AnchoredIn U K H A y from
    ⟨y, h (le_trans hρ (round_of_mem_historyUpto K (hy.mem hA) hzy).1), hzy⟩
  clear hzy
  induction hy with
  | anchor => exact fun _ => AnchoredIn.anchor hf.1
  | @referenced x S y hy hz href hcard ih =>
    intro hρx
    have hzr : ∀ z ∈ S, ρ < (U.block z).round ∧ ρ ≤ (U.block (y z)).round := fun z hzS => by
      have hzi := historyUpto_subset_ids K ((hy z hzS).mem hA) (hz z hzS)
      have := (U.valid z hzi).predecessor x (href z hzS)
      have := (round_of_mem_historyUpto K ((hy z hzS).mem hA) (hz z hzS)).1
      omega
    have ih' : ∀ z ∈ S, AnchoredIn U K H A (y z) := fun z hzS => ih z hzS (hzr z hzS).2
    exact AnchoredIn.referenced S y ih' hz href hcard
      (hf.2 S x (fun z hzS => ⟨⟨y z, ih' z hzS, hz z hzS⟩, (hzr z hzS).1⟩) href hcard)

/-- **Fetched down to the round above the slot's, the record's link is read on
`H`.** -/
theorem avail_linkedIn (hH : H ⊆ U.ids) {L : BlockId} {r : ℕ} (hf : FetchedIn U K H A (r + 1))
    (h : AvailLinked U K A L r) : LinkedIn U K H A L r := by
  obtain ⟨C, hC, hCa, hrefs⟩ := h
  obtain ⟨hCi, hCr, hv⟩ := mem_certificatesAt.mp hC
  refine ⟨C, avail_subset_availIn hH hf hCa (by omega), hCr, fun j hj => ?_, hv⟩
  have := (U.valid C hCi).predecessor j hj
  exact avail_subset_availIn hH hf (hrefs j hj) (by omega)

/-- **Holding the record's sub-DAG to depth `K` below round `ρ` fetches it down
to `ρ`**, for an anchor of the record at or above `ρ`. -/
theorem fetchedIn_of_subset (hA : A ∈ U.ids) {ρ : ℕ} (hρ : ρ ≤ (U.block A).round)
    (hsub : ∀ z ∈ Avail U K A, ρ ≤ (U.block z).round + K → z ∈ H) : FetchedIn U K H A ρ := by
  refine ⟨fun z hz => hsub z ⟨A, AnchoredBelow.anchor, hz⟩
    (by have := (round_of_mem_historyUpto K hA hz).2; omega), fun S x hS href hcard => ?_⟩
  have hx : AnchoredBelow U K A x :=
    AnchoredBelow.of_avail (fun z hz => availIn_subset (hS z hz).1) href hcard
  obtain ⟨z, hzS⟩ := nonempty_of_creatorsOf_card_pos (by omega : 0 < (creatorsOf U.block S).card)
  have hzi := avail_subset_ids hA (availIn_subset (hS z hzS).1)
  have hxz := (U.valid z hzi).predecessor x (href z hzS)
  have hρz := (hS z hzS).2
  exact fun w hw => hsub w ⟨x, hx, hw⟩
    (by have := (round_of_mem_historyUpto K (hx.mem hA) hw).2; omega)

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
      (fun L hL hlink => hnone L hL (avail_linkedIn hH hf hlink))

/-- **Two nodes decide each slot alike**, at `K ≥ 3`. -/
theorem NodeDecided.agree (hK : 3 ≤ K) {H₁ H₂ : Finset BlockId} (hH₁ : H₁ ⊆ U.ids)
    (hH₂ : H₂ ⊆ U.ids) {k : ℕ} {v₁ v₂ : Option BlockId} (h₁ : NodeDecided U K H₁ k v₁)
    (h₂ : NodeDecided U K H₂ k v₂) : v₁ = v₂ :=
  (kRule K).decided_agree (kRule_laws hK) trivial
    (h₁.decided (V := View.full U) hH₁ hH₁) (h₂.decided (V := View.full U) hH₂ hH₂)

end KPartialDag

end LeanDag
