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
variable [Cr : Crashes Validator]
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

/-- An anchor point read on `H` has the history it brings held. -/
theorem AnchoredIn.window {y : BlockId} {d : ℕ} (h : AnchoredIn U K H A y d) :
    historyUpto U d y ⊆ H := by
  cases h with
  | anchor h => exact h
  | referenced _ _ _ _ _ _ _ hx => exact hx
  | reached _ _ _ _ _ _ _ _ _ _ _ _ _ _ hx => exact hx

/-- The sub-DAG read on `H` is held. -/
theorem availIn_subset_held {z : BlockId} (hz : z ∈ AvailIn U K H A) : z ∈ H := by
  obtain ⟨y, d, hy, hzy⟩ := hz
  exact hy.window hzy

/-- **Anchoring read on `H` reads only `H`.** -/
theorem AnchoredIn.congr (hb : ∀ i ∈ H, U.block i = U'.block i) {x : BlockId} {d : ℕ}
    (h : AnchoredIn U K H A x d) : AnchoredIn U' K H A x d := by
  induction h with
  | anchor h => exact AnchoredIn.anchor (by rw [historyUpto_eq_of_subset hb h]; exact h)
  | @referenced x S y d hy hz href hcard hx ih =>
    have hSH : ∀ z ∈ S, z ∈ H := fun z hzS => (hy z hzS).window (hz z hzS)
    refine AnchoredIn.referenced S y d ih (fun z hzS => ?_) (fun z hzS => ?_) ?_
      (by rw [historyUpto_eq_of_subset hb hx]; exact hx)
    · rw [historyUpto_eq_of_subset hb (hy z hzS).window]; exact hz z hzS
    · rw [← hb z (hSH z hzS)]; exact href z hzS
    · have : creatorsOf U'.block S = creatorsOf U.block S :=
        Finset.image_congr fun z hzS => by rw [hb z (hSH z hzS)]
      rw [this]; exact hcard
  | @reached x S m y d y' d' hy hz hy' hmz hm href hcard hc hx ih ih' =>
    have hSH : ∀ z ∈ S, z ∈ H := fun z hzS => (hy z hzS).window (hz z hzS)
    have hmH : ∀ z ∈ S, m z ∈ H := fun z hzS => (hy' z hzS).window (hmz z hzS)
    refine AnchoredIn.reached S m y d y' d' ih (fun z hzS => ?_) ih' (fun z hzS => ?_)
      (fun z hzS => ?_) (fun z hzS => ?_) ?_ hc (by rw [historyUpto_eq_of_subset hb hx]; exact hx)
    · rw [historyUpto_eq_of_subset hb (hy z hzS).window]; exact hz z hzS
    · rw [historyUpto_eq_of_subset hb (hy' z hzS).window]; exact hmz z hzS
    · rw [← hb z (hSH z hzS)]; exact hm z hzS
    · rw [← hb (m z) (hmH z hzS)]; exact href z hzS
    · have : creatorsOf U'.block S = creatorsOf U.block S :=
        Finset.image_congr fun z hzS => by rw [hb z (hSH z hzS)]
      rw [this]; exact hcard

/-- **The sub-DAG read on `H` reads only `H`.** -/
theorem availIn_congr (hb : ∀ i ∈ H, U.block i = U'.block i) :
    AvailIn U K H A = AvailIn U' K H A := by
  have sub : ∀ {U U' : KRecord Validator BlockId Payload}, (∀ i ∈ H, U.block i = U'.block i) →
      AvailIn U K H A ⊆ AvailIn U' K H A := fun hb z ⟨y, d, hy, hzy⟩ =>
    ⟨y, d, hy.congr hb, by rw [historyUpto_eq_of_subset hb hy.window]; exact hzy⟩
  exact (sub hb).antisymm (sub fun i hi => (hb i hi).symm)

/-- **Certifying reads only `H`**, for a block of `H` whose references, when
votes are certified apart, are in `H`. -/
theorem certifies_congr (hb : ∀ i ∈ H, U.block i = U'.block i) {p : Scheme.Params}
    {C L : BlockId} {r : ℕ} (hC : C ∈ H) (hrefs : p.voteIsCert = false → ∀ j ∈ (U.block C).refs,
      j ∈ H) : Certifies p U C L r → Certifies p U' C L r := by
  rintro ⟨hCr, hcv⟩
  refine ⟨by rw [← hb C hC]; exact hCr, ?_⟩
  cases hv : p.voteIsCert
  · simp only [hv, Bool.false_eq_true, if_false] at hcv ⊢
    unfold CarriesVotes carriedVotes at hcv ⊢
    have hset : ((U'.block C).refs.filter fun b => IsVote U' b L) =
        ((U.block C).refs.filter fun b => IsVote U b L) := by
      rw [← hb C hC]
      refine Finset.filter_congr fun b hbC => ?_
      change L ∈ (U'.block b).refs ↔ L ∈ (U.block b).refs
      rw [hb b (hrefs hv b hbC)]
    rw [hset]
    have : creatorsOf U'.block ((U.block C).refs.filter fun b => IsVote U b L) =
        creatorsOf U.block ((U.block C).refs.filter fun b => IsVote U b L) :=
      Finset.image_congr fun b hbC => by rw [hb b (hrefs hv b (Finset.mem_filter.mp hbC).1)]
    rw [this]; exact hcv
  · simp only [hv, if_true] at hcv ⊢
    change L ∈ (U'.block C).refs
    rw [← hb C hC]; exact hcv

/-- **The indirect test read on `H` reads only `H`.** -/
theorem linkedIn_congr (hb : ∀ i ∈ H, U.block i = U'.block i) {p : Scheme.Params} {L : BlockId}
    {r : ℕ} : LinkedIn p U K H A L r → LinkedIn p U' K H A L r := by
  rintro ⟨X, hX, hXn⟩
  have hav := availIn_congr (K := K) (A := A) hb
  have hXH : ∀ C ∈ X, C ∈ H := fun C hC => availIn_subset_held (hX C hC).1
  refine ⟨X, fun C hC => ?_, ?_⟩
  · obtain ⟨hCa, hCc, hrefs⟩ := hX C hC
    refine ⟨hav ▸ hCa, certifies_congr hb (hXH C hC)
      (fun hv j hj => availIn_subset_held (hrefs hv j hj)) hCc, fun hv j hj => ?_⟩
    rw [← hb C (hXH C hC)] at hj
    exact hav ▸ hrefs hv j hj
  · have : creatorsOf U'.block X = creatorsOf U.block X :=
      Finset.image_congr fun C hC => by rw [hb C (hXH C hC)]
    rw [this]; exact hXn

/-- **The fetch test reads only `H`.** -/
theorem fetchedIn_congr (hb : ∀ i ∈ H, U.block i = U'.block i) {ρ : ℕ} :
    FetchedIn U K H A ρ → FetchedIn U' K H A ρ := by
  rintro ⟨hA, hall, hall₂⟩
  have hav := availIn_congr (K := K) (A := A) hb
  have hcr : ∀ S : Finset BlockId, (∀ z ∈ S, z ∈ H) →
      creatorsOf U.block S = creatorsOf U'.block S := fun S hSH =>
    Finset.image_congr fun z hz => by rw [hb z (hSH z hz)]
  refine ⟨by rw [historyUpto_eq_of_subset hb hA]; exact hA, fun S x hS href hcard => ?_,
    fun S m x hS hm href hcard hc => ?_⟩
  · have hSH : ∀ z ∈ S, z ∈ H := fun z hz => availIn_subset_held (hav ▸ (hS z hz).1)
    have hx := hall S x
      (fun z hz => ⟨hav ▸ (hS z hz).1, by rw [hb z (hSH z hz)]; exact (hS z hz).2⟩)
      (fun z hz => by rw [hb z (hSH z hz)]; exact href z hz) (by rw [hcr S hSH]; exact hcard)
    rw [historyUpto_eq_of_subset hb hx]; exact hx
  · have hSH : ∀ z ∈ S, z ∈ H := fun z hz => availIn_subset_held (hav ▸ (hS z hz).1)
    have hmH : ∀ z ∈ S, m z ∈ H := fun z hz => availIn_subset_held (hav ▸ (hS z hz).2.1)
    have hx := hall₂ S m x
      (fun z hz => ⟨hav ▸ (hS z hz).1, hav ▸ (hS z hz).2.1,
        by rw [hb (m z) (hmH z hz)]; exact (hS z hz).2.2⟩)
      (fun z hz => by rw [hb z (hSH z hz)]; exact hm z hz)
      (fun z hz => by rw [hb (m z) (hmH z hz)]; exact href z hz) (by rw [hcr S hSH]; exact hcard) hc
    rw [historyUpto_eq_of_subset hb hx]; exact hx

/-- An anchor point read on `H` is an anchor point below `A`. -/
theorem AnchoredIn.toBelow {y : BlockId} {d : ℕ} (h : AnchoredIn U K H A y d) :
    AnchoredBelow U K A y d := by
  induction h with
  | anchor => exact AnchoredBelow.anchor
  | referenced S y d hy hz href hcard hx ih => exact AnchoredBelow.referenced S y d ih hz href hcard
  | reached S m y d y' d' hy hz hy' hmz hm href hcard hc hx ih ih' =>
    exact AnchoredBelow.reached S m y d y' d' ih hz ih' hmz hm href hcard hc

/-- **The sub-DAG read on `H` lies in the record's.** -/
theorem availIn_subset {z : BlockId} (hz : z ∈ AvailIn U K H A) : z ∈ Avail U K A := by
  obtain ⟨y, d, hy, hzy⟩ := hz
  exact ⟨y, d, hy.toBelow, hzy⟩

/-- **A link read on `H` is the record's**, for blocks of the record. -/
theorem linkedIn_avail (hH : H ⊆ U.ids) {p : Scheme.Params} {L : BlockId} {r : ℕ}
    (h : LinkedIn p U K H A L r) : AvailLinked p U K A L r := by
  obtain ⟨X, hX, hXn⟩ := h
  exact ⟨X, fun C hC => mem_certsFor_iff.mpr ⟨hH (availIn_subset_held (hX C hC).1), (hX C hC).2.1⟩,
    fun C hC => ⟨availIn_subset (hX C hC).1, fun hv j hj => availIn_subset ((hX C hC).2.2 hv j hj)⟩,
    hXn⟩

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
  obtain ⟨y, d, hy, hzy⟩ := hz
  suffices h : ρ ≤ (U.block y).round → AnchoredIn U K H A y d from
    ⟨y, d, h (le_trans hρ (round_of_mem_historyUpto d (hy.mem hA) hzy).1), hzy⟩
  clear hzy
  induction hy with
  | anchor => exact fun _ => AnchoredIn.anchor hf.1
  | @referenced x S y d hy hz href hcard ih =>
    intro hρx
    have hzr : ∀ z ∈ S, ρ < (U.block z).round ∧ ρ ≤ (U.block (y z)).round := fun z hzS => by
      have hzi := historyUpto_subset_ids _ ((hy z hzS).mem hA) (hz z hzS)
      have := (U.valid z hzi).predecessor x (href z hzS)
      have := (round_of_mem_historyUpto _ ((hy z hzS).mem hA) (hz z hzS)).1
      omega
    have ih' : ∀ z ∈ S, AnchoredIn U K H A (y z) (d z) := fun z hzS => ih z hzS (hzr z hzS).2
    exact AnchoredIn.referenced S y d ih' hz href hcard
      (hf.2.1 S x (fun z hzS => ⟨⟨y z, d z, ih' z hzS, hz z hzS⟩, (hzr z hzS).1⟩) href hcard)
  | @reached x S m y d y' d' hy hz hy' hmz hm href hcard hc ih ih₂ =>
    intro hρx
    have hzr : ∀ z ∈ S, ρ < (U.block (m z)).round ∧ ρ ≤ (U.block (y z)).round ∧
        ρ ≤ (U.block (y' z)).round := fun z hzS => by
      have hmi := historyUpto_subset_ids _ ((hy' z hzS).mem hA) (hmz z hzS)
      have hzi := historyUpto_subset_ids _ ((hy z hzS).mem hA) (hz z hzS)
      have := (U.valid (m z) hmi).predecessor x (href z hzS)
      have := (U.valid z hzi).predecessor (m z) (hm z hzS)
      have := (round_of_mem_historyUpto _ ((hy z hzS).mem hA) (hz z hzS)).1
      have := (round_of_mem_historyUpto _ ((hy' z hzS).mem hA) (hmz z hzS)).1
      omega
    have i₁ : ∀ z ∈ S, AnchoredIn U K H A (y z) (d z) := fun z hzS => ih z hzS (hzr z hzS).2.1
    have i₂ : ∀ z ∈ S, AnchoredIn U K H A (y' z) (d' z) := fun z hzS =>
      ih₂ z hzS (hzr z hzS).2.2
    exact AnchoredIn.reached S m y d y' d' i₁ hz i₂ hmz hm href hcard hc
      (hf.2.2 S m x (fun z hzS => ⟨⟨y z, d z, i₁ z hzS, hz z hzS⟩,
        ⟨y' z, d' z, i₂ z hzS, hmz z hzS⟩, (hzr z hzS).1⟩) hm href hcard hc)

/-- **Fetched down to the round above the slot's, the record's link is read on
`H`**, at a row. -/
theorem avail_linkedIn (hH : H ⊆ U.ids) {p : Scheme.Params} (hrow : Row Validator p) {L : BlockId}
    {r : ℕ} (hf : FetchedIn U K H A (r + 1)) (h : AvailLinked p U K A L r) :
    LinkedIn p U K H A L r := by
  obtain ⟨X, hXs, hX, hXn⟩ := h
  obtain ⟨hw2, hw3⟩ := row_wave hrow
  refine ⟨X, fun C hC => ?_, hXn⟩
  obtain ⟨hCi, hCc⟩ := mem_certsFor_iff.mp (hXs hC)
  have hCr := hCc.1
  have hw : 2 ≤ p.waveLength := by cases hv : p.voteIsCert <;> simp_all
  refine ⟨avail_subset_availIn hH hf (hX C hC).1 (by omega), hCc, fun hv j hj => ?_⟩
  have := (U.valid C hCi).predecessor j hj
  have := hw3 hv
  exact avail_subset_availIn hH hf ((hX C hC).2 hv j hj) (by omega)

/-- **Holding the record's sub-DAG to depth `K` below round `ρ` fetches it down
to `ρ`**, for an anchor of the record at or above `ρ`. -/
theorem fetchedIn_of_subset (hA : A ∈ U.ids) {ρ : ℕ} (hρ : ρ ≤ (U.block A).round)
    (hsub : ∀ z ∈ Avail U K A, ρ ≤ (U.block z).round + K → z ∈ H) : FetchedIn U K H A ρ := by
  refine ⟨fun z hz => hsub z ⟨A, K, AnchoredBelow.anchor, hz⟩
    (by have := (round_of_mem_historyUpto K hA hz).2; omega), fun S x hS href hcard => ?_,
    fun S m x hS hm href hcard hc => ?_⟩
  · have hx : AnchoredBelow U K A x K :=
      AnchoredBelow.of_avail (fun z hz => availIn_subset (hS z hz).1) href hcard
    obtain ⟨z, hzS⟩ := nonempty_of_creatorsOf_card_pos (by omega : 0 < (creatorsOf U.block S).card)
    have hzi := avail_subset_ids hA (availIn_subset (hS z hzS).1)
    have hxz := (U.valid z hzi).predecessor x (href z hzS)
    have hρz := (hS z hzS).2
    exact fun w hw => hsub w ⟨x, K, hx, hw⟩
      (by have := (round_of_mem_historyUpto K (hx.mem hA) hw).2; omega)
  · have hx : AnchoredBelow U K A x (K - 1) :=
      AnchoredBelow.of_avail_two (fun z hz => ⟨availIn_subset (hS z hz).1,
        availIn_subset (hS z hz).2.1⟩) hm href hcard hc
    obtain ⟨z, hzS⟩ := nonempty_of_creatorsOf_card_pos (by omega : 0 < (creatorsOf U.block S).card)
    have hmi := avail_subset_ids hA (availIn_subset (hS z hzS).2.1)
    have hxm := (U.valid (m z) hmi).predecessor x (href z hzS)
    have hρm := (hS z hzS).2.2
    exact fun w hw => hsub w ⟨x, K - 1, hx, hw⟩
      (by have := (round_of_mem_historyUpto (K - 1) (hx.mem hA) hw).2; omega)

variable [S : Slots Validator]

omit S in
/-- Blocks a node holds with their references are held by a view holding
what the node holds. -/
theorem holdsAtLeast_of_held {V : U.View} (hHV : H ⊆ V.ids) {s : Finset BlockId} {t : ℕ}
    (h : t ≤ (creatorsOf U.block (heldWithRefs U H s)).card) : HoldsAtLeast U V t s :=
  h.trans (Finset.card_le_card (Finset.image_subset_image fun b hb => by
    obtain ⟨hbs, hbH, -⟩ := Finset.mem_filter.mp hb
    exact Finset.mem_inter.mpr ⟨hbs, hHV hbH⟩))

/-- **A node's decision is a decision on every view holding what it holds**,
at a row, for a node holding blocks of the record. -/
theorem NodeDecided.decided {p : Scheme.Params} (hrow : Row Validator p) (hH : H ⊆ U.ids)
    {V : U.View} (hHV : H ⊆ V.ids) {k : ℕ} {v : Option BlockId} (h : NodeDecided p U K H k v) :
    (kRule p K).Decided U V k v := by
  induction h with
  | directCommit hL hc => exact AnchoredRule.Decided.directCommit hL (holdsAtLeast_of_held hHV hc)
  | directSkip hs => exact AnchoredRule.Decided.directSkip (holdsAtLeast_of_held hHV hs)
  | indirectCommit hkj helig _ _ hf hL hlink hleast ihj ihm =>
    exact AnchoredRule.Decided.indirectCommit (i := 0) hkj helig ihj ihm Nat.one_pos
      (fun i' hi' => absurd hi' (Nat.not_lt_zero _)) hL (linkedIn_avail hH hlink)
      fun L' hL' hl' hlt => hleast L' hL' hlt (avail_linkedIn hH hrow hf hl')
  | indirectSkip hkj helig _ _ hf hnone ihj ihm =>
    exact AnchoredRule.Decided.indirectSkip_single rfl hkj helig ihj ihm
      (fun L hL hlink => hnone L hL (avail_linkedIn hH hrow hf hlink))

/-- **Two nodes decide each slot alike**, at a row and `K ≥ 3`. -/
theorem NodeDecided.agree {p : Scheme.Params} (hrow : Row Validator p) (hK : 3 ≤ K)
    {H₁ H₂ : Finset BlockId} (hH₁ : H₁ ⊆ U.ids) (hH₂ : H₂ ⊆ U.ids) {k : ℕ}
    {v₁ v₂ : Option BlockId} (h₁ : NodeDecided p U K H₁ k v₁)
    (h₂ : NodeDecided p U K H₂ k v₂) : v₁ = v₂ :=
  (kRule p K).decided_agree (kRule_laws hrow hK) trivial
    (h₁.decided hrow (V := View.full U) hH₁ hH₁) (h₂.decided hrow (V := View.full U) hH₂ hH₂)

end KPartialDag

end LeanDag
