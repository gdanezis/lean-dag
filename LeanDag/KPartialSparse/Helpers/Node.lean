import LeanDag.KPartialSparse.Model.Node
import LeanDag.KPartialSparse.Helpers.Rule
import LeanDag.KPartialDag.Helpers.Node
/-!
# Sparse K-partial DAG — what a node reads, helpers

`docs/kpartial-sparse.md` §5. The node's tests read only what it holds
(`AnchoredIn.congr`, `linkedIn_congr`, `fetchedIn_congr`); the sub-DAG read
on `H` lies in the record's (`availIn_subset`), and fetched down to a round it
is the record's above that round (`avail_subset_availIn`); holding the
sub-DAG fetches it (`fetchedIn_of_subset`); and a node's decisions are the
commit rule's (`NodeDecided.decided`) and agree (`NodeDecided.agree`).
-/

namespace LeanDag

namespace KPartialSparse

open KPartialDag Scheme

variable {Validator : Type*} [Fintype Validator] [DecidableEq Validator] [F : Faults Validator]
variable [Cr : Crashes Validator] [Ld : Leaders Validator]
variable {BlockId : Type*} [LinearOrder BlockId] {Payload : Type*}
variable {U U' : SRecord Validator BlockId Payload} {K : ℕ} {H : Finset BlockId} {A : BlockId}

/-! ## Reading only what is held -/

/-- A held history of a record is read alike on a record agreeing on what is
held. -/
theorem historyUpto_eq_of_subset (hb : ∀ i ∈ H, U.block i = U'.block i) {n : ℕ} {y : BlockId}
    (h : historyUpto U n y ⊆ H) : historyUpto U' n y = historyUpto U n y :=
  historyUptoFrom_eq_of_subset hb n y h

omit [Fintype Validator] [DecidableEq Validator] Ld in
/-- One step beyond a held history is read alike. -/
theorem historyUptoFrom_succ_eq {blk blk' : BlockId → Block Validator BlockId Payload}
    (hb : ∀ i ∈ H, blk i = blk' i) :
    ∀ (n : ℕ) (b : BlockId), historyUptoFrom blk n b ⊆ H →
      historyUptoFrom blk' (n + 1) b = historyUptoFrom blk (n + 1) b
  | 0, b, h => by
    have hbH : b ∈ H := h mem_historyUptoFrom_self
    rw [historyUptoFrom_succ, historyUptoFrom_succ, ← hb b hbH]; rfl
  | n + 1, b, h => by
    have hbH : b ∈ H := h mem_historyUptoFrom_self
    rw [historyUptoFrom_succ (n := n + 1), historyUptoFrom_succ (n := n + 1), ← hb b hbH]
    refine congrArg (insert b) (Finset.biUnion_congr rfl fun j hj =>
      historyUptoFrom_succ_eq hb n j fun i hi => h ?_)
    rw [historyUptoFrom_succ]
    exact Finset.mem_insert_of_mem (Finset.mem_biUnion.mpr ⟨j, hj, hi⟩)

/-- **A block reached through a held path is read alike**: the history to depth
`i` of a block whose history to depth `i − 1` is held. -/
theorem historyUpto_eq_of_path (hb : ∀ i ∈ H, U.block i = U'.block i) {i : ℕ} {b : BlockId}
    (h : 0 < i → historyUpto U (i - 1) b ⊆ H) : historyUpto U' i b = historyUpto U i b := by
  rcases Nat.eq_zero_or_pos i with rfl | hpos
  · rfl
  · obtain ⟨n, rfl⟩ : ∃ n, i = n + 1 := ⟨i - 1, by omega⟩
    exact historyUptoFrom_succ_eq hb n b (h hpos)

/-- An anchor point read on `H` has the history it brings held. -/
theorem AnchoredIn.window {y : BlockId} {d : ℕ} (h : AnchoredIn U K H A y d) :
    historyUpto U d y ⊆ H := by
  cases h with
  | anchor h => exact h
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
  | @reached x i S m y d y' d' hy hz hy' hmz hi hm hcard hx ih ih' =>
    have hzH : ∀ z ∈ S, z ∈ H := fun z hzS => (hy z hzS).window (hz z hzS)
    have hpath : ∀ z ∈ S, 0 < i → historyUpto U (i - 1) (m z) ⊆ H := fun z hzS hpos =>
      (hmz z hzS hpos).trans (hy' z hzS hpos).window
    refine AnchoredIn.reached i S m y d y' d' ih (fun z hzS => ?_) ih' (fun z hzS hpos => ?_) hi
      (fun z hzS => ?_) ?_ ?_
    · rw [historyUpto_eq_of_subset hb ((hy z hzS).window)]; exact hz z hzS
    · rw [historyUpto_eq_of_subset hb ((hy' z hzS hpos).window),
        historyUpto_eq_of_subset hb (hpath z hzS hpos)]
      exact hmz z hzS hpos
    · rw [← hb z (hzH z hzS), historyUpto_eq_of_path hb (hpath z hzS)]; exact hm z hzS
    · have : creatorsOf U'.block S = creatorsOf U.block S :=
        Finset.image_congr fun z hzS => by rw [hb z (hzH z hzS)]
      rw [this]; exact hcard
    · rw [historyUpto_eq_of_subset hb hx]; exact hx

/-- The sub-DAG read on `H` is read alike on a record agreeing on `H`. -/
theorem availIn_congr (hb : ∀ i ∈ H, U.block i = U'.block i) :
    AvailIn U K H A = AvailIn U' K H A := by
  have hb' : ∀ i ∈ H, U'.block i = U.block i := fun i hi => (hb i hi).symm
  ext z
  constructor
  · rintro ⟨y, d, hy, hzy⟩
    exact ⟨y, d, hy.congr hb, by rw [historyUpto_eq_of_subset hb hy.window]; exact hzy⟩
  · rintro ⟨y, d, hy, hzy⟩
    exact ⟨y, d, hy.congr hb', by rw [historyUpto_eq_of_subset hb' hy.window]; exact hzy⟩

/-- **The fetch test reads only `H`.** -/
theorem fetchedIn_congr (hb : ∀ i ∈ H, U.block i = U'.block i) {ρ : ℕ}
    (h : FetchedIn U K H A ρ) : FetchedIn U' K H A ρ := by
  have hb' : ∀ i ∈ H, U'.block i = U.block i := fun i hi => (hb i hi).symm
  refine ⟨by rw [historyUpto_eq_of_subset hb h.1]; exact h.1, fun i S m x hi hS hcard => ?_⟩
  have hav := availIn_congr (K := K) (A := A) hb
  have hzH : ∀ z ∈ S, z ∈ H := fun z hzS => availIn_subset_held (hav ▸ (hS z hzS).1)
  have hcard' : F.f + Cr.c + 1 ≤ (creatorsOf U.block S).card := by
    have : creatorsOf U'.block S = creatorsOf U.block S :=
      Finset.image_congr fun z hzS => by rw [hb z (hzH z hzS)]
    rwa [this] at hcard
  have hx := h.2 i S m x hi (fun z hzS => by
    obtain ⟨h₁, h₂, h₃, h₄, h₅⟩ := hS z hzS
    have hpath : 0 < i → historyUpto U' (i - 1) (m z) ⊆ H := fun hpos => by
      obtain ⟨y, d, hy, hmy⟩ := h₃ hpos
      exact hmy.trans hy.window
    have hpath' : 0 < i → historyUpto U (i - 1) (m z) ⊆ H := fun hpos => by
      rw [historyUpto_eq_of_subset hb' (hpath hpos)]; exact hpath hpos
    refine ⟨hav ▸ h₁, by rw [hb z (hzH z hzS)]; exact h₂, fun hpos => ?_,
      by rw [hb z (hzH z hzS)]; exact h₄, ?_⟩
    · obtain ⟨y, d, hy, hmy⟩ := h₃ hpos
      refine ⟨y, d, hy.congr hb', ?_⟩
      rw [historyUpto_eq_of_subset hb' (hpath hpos), historyUpto_eq_of_subset hb' hy.window]
      exact hmy
    · rw [← historyUpto_eq_of_path hb hpath']; exact h₅) hcard'
  rw [historyUpto_eq_of_subset hb hx]; exact hx

variable [ClaimFormat BlockId Payload]

omit [LinearOrder BlockId] in
/-- Certifying reads only the certificate's block. -/
theorem certifies_congr {p : Params} {C L : BlockId} {r : ℕ} (hC : U.block C = U'.block C)
    (h : Certifies p U C L r) : Certifies p U' C L r := by
  unfold Certifies claimsOf at *
  rwa [← hC]

/-- **The link read on `H` reads only `H`.** -/
theorem linkedIn_congr (hb : ∀ i ∈ H, U.block i = U'.block i) {p : Params} {L : BlockId} {r : ℕ}
    (h : LinkedIn p U K H A L r) : LinkedIn p U' K H A L r := by
  obtain ⟨X, hX, hXn⟩ := h
  have hXH : ∀ C ∈ X, C ∈ H := fun C hC => availIn_subset_held (hX C hC).1
  refine ⟨X, fun C hC => ⟨availIn_congr hb ▸ (hX C hC).1,
    certifies_congr (hb C (hXH C hC)) (hX C hC).2⟩, ?_⟩
  have : creatorsOf U'.block X = creatorsOf U.block X :=
    Finset.image_congr fun C hC => by rw [hb C (hXH C hC)]
  rw [this]; exact hXn

omit [ClaimFormat BlockId Payload]

/-! ## The record's sub-DAG -/

/-- An anchor point read on `H` is an anchor point of the record. -/
theorem AnchoredIn.toAnchored {y : BlockId} {d : ℕ} (h : AnchoredIn U K H A y d) :
    Anchored U K A y d := by
  induction h with
  | anchor _ => exact Anchored.anchor
  | reached i S m y d y' d' _ hz _ hmz hi hm hcard _ ih ih' =>
    exact Anchored.reached i S m y d y' d' ih hz ih' hmz hi hm hcard

/-- The sub-DAG read on `H` lies in the record's. -/
theorem availIn_subset {z : BlockId} (hz : z ∈ AvailIn U K H A) : z ∈ Avail U K A := by
  obtain ⟨y, d, hy, hzy⟩ := hz
  exact ⟨y, d, hy.toAnchored, hzy⟩

/-- A block of a history lies at or below the block. -/
theorem round_le_of_mem_historyUpto : ∀ (n : ℕ) {y w : BlockId}, y ∈ U.ids →
    w ∈ historyUpto U n y → (U.block w).round ≤ (U.block y).round
  | 0, y, w, _, hw => by
    rw [historyUpto_zero, Finset.mem_singleton] at hw
    subst hw; exact le_rfl
  | n + 1, y, w, hy, hw => by
    rcases mem_historyUpto_succ.mp hw with rfl | ⟨j, hj, hwj⟩
    · exact le_rfl
    · have := (U.valid y hy).below j hj
      have := round_le_of_mem_historyUpto n (U.complete y hy j hj) hwj
      omega

/-- **The available sub-DAG lies at or below its anchor.** -/
theorem round_le_of_avail (hA : A ∈ U.ids) {z : BlockId} (hz : z ∈ Avail U K A) :
    (U.block z).round ≤ (U.block A).round := by
  obtain ⟨y, d, hy, hzy⟩ := hz
  suffices h : (U.block y).round ≤ (U.block A).round from
    (round_le_of_mem_historyUpto d (hy.mem hA) hzy).trans h
  clear hzy
  induction hy with
  | anchor => exact le_rfl
  | @reached x i S m y d y' d' hy hz hy' hmz hi hm hcard ih ih' =>
    obtain ⟨z, hzS⟩ : S.Nonempty := by
      rw [← Finset.card_pos]; exact lt_of_lt_of_le (by omega) (hcard.trans Finset.card_image_le)
    have hzi := historyUpto_subset_ids _ ((hy z hzS).mem hA) (hz z hzS)
    have hmi := U.complete z hzi _ (hm z hzS).1
    have := (U.valid z hzi).below _ (hm z hzS).1
    have := round_le_of_mem_historyUpto _ hmi (hm z hzS).2
    have := round_le_of_mem_historyUpto _ ((hy z hzS).mem hA) (hz z hzS)
    have := ih z hzS
    omega

/-- **A sub-DAG fetched down to round `ρ` is the record's at and above `ρ`.** -/
theorem avail_subset_availIn (hH : H ⊆ U.ids) {ρ : ℕ} (hf : FetchedIn U K H A ρ) {z : BlockId}
    (hz : z ∈ Avail U K A) (hρ : ρ ≤ (U.block z).round) : z ∈ AvailIn U K H A := by
  have hA : A ∈ U.ids := hH (hf.1 mem_historyUpto_self)
  obtain ⟨y, d, hy, hzy⟩ := hz
  suffices h : ρ ≤ (U.block y).round → AnchoredIn U K H A y d from
    ⟨y, d, h (le_trans hρ (round_le_of_mem_historyUpto d (hy.mem hA) hzy)), hzy⟩
  clear hzy
  induction hy with
  | anchor => exact fun _ => AnchoredIn.anchor hf.1
  | @reached x i S m y d y' d' hy hz hy' hmz hi hm hcard ih ih' =>
    intro hρx
    have hzr : ∀ z ∈ S, ρ < (U.block z).round ∧ ρ ≤ (U.block (y z)).round ∧
        ρ ≤ (U.block (m z)).round := fun z hzS => by
      have hzi := historyUpto_subset_ids _ ((hy z hzS).mem hA) (hz z hzS)
      have hmi := U.complete z hzi _ (hm z hzS).1
      have := (U.valid z hzi).below _ (hm z hzS).1
      have := round_le_of_mem_historyUpto _ hmi (hm z hzS).2
      have := round_le_of_mem_historyUpto _ ((hy z hzS).mem hA) (hz z hzS)
      omega
    have i₁ : ∀ z ∈ S, AnchoredIn U K H A (y z) (d z) := fun z hzS => ih z hzS (hzr z hzS).2.1
    have i₂ : ∀ z ∈ S, 0 < i → AnchoredIn U K H A (y' z) (d' z) := fun z hzS hpos =>
      ih' z hzS hpos (le_trans (hzr z hzS).2.2
        (round_le_of_mem_historyUpto _ ((hy' z hzS hpos).mem hA)
          (hmz z hzS hpos mem_historyUpto_self)))
    exact AnchoredIn.reached i S m y d y' d' i₁ hz i₂ hmz hi hm hcard
      (hf.2 i S m x hi (fun z hzS => ⟨⟨y z, d z, i₁ z hzS, hz z hzS⟩, (hzr z hzS).1,
        fun hpos => ⟨y' z, d' z, i₂ z hzS hpos, hmz z hzS hpos⟩, hm z hzS⟩) hcard)

/-- **Holding what the record's anchor points bring fetches the sub-DAG**,
down to any round. -/
theorem fetchedIn_of_subset {ρ : ℕ}
    (hsub : ∀ y d, Anchored U K A y d → historyUpto U d y ⊆ H) : FetchedIn U K H A ρ := by
  classical
  refine ⟨hsub A K Anchored.anchor, fun i S m x hi hS hcard => hsub x (K - i) ?_⟩
  have h₁ : ∀ z ∈ S, z ∈ Avail U K A := fun z hzS => availIn_subset (hS z hzS).1
  have h₂ : ∀ z ∈ S, 0 < i → ∃ y d, Anchored U K A y d ∧
      historyUpto U (i - 1) (m z) ⊆ historyUpto U d y := fun z hzS hpos => by
    obtain ⟨y, d, hy, hmy⟩ := (hS z hzS).2.2.1 hpos
    exact ⟨y, d, hy.toAnchored, hmy⟩
  refine Anchored.reached i S m (fun z => if h : z ∈ S then (h₁ z h).choose else A)
    (fun z => if h : z ∈ S then (h₁ z h).choose_spec.choose else K)
    (fun z => if h : z ∈ S ∧ 0 < i then (h₂ z h.1 h.2).choose else A)
    (fun z => if h : z ∈ S ∧ 0 < i then (h₂ z h.1 h.2).choose_spec.choose else K)
    (fun z hz => ?_) (fun z hz => ?_) (fun z hz hpos => ?_) (fun z hz hpos => ?_) hi
    (fun z hz => (hS z hz).2.2.2) hcard
  · simp only [dif_pos hz]; exact (h₁ z hz).choose_spec.choose_spec.1
  · simp only [dif_pos hz]; exact (h₁ z hz).choose_spec.choose_spec.2
  · simp only [dif_pos (And.intro hz hpos)]; exact (h₂ z hz hpos).choose_spec.choose_spec.1
  · simp only [dif_pos (And.intro hz hpos)]; exact (h₂ z hz hpos).choose_spec.choose_spec.2

variable [ClaimFormat BlockId Payload]

omit [LinearOrder BlockId] in
/-- A certificate lies at its certificate round. -/
theorem round_of_certifies {p : Params} {C L : BlockId} {r : ℕ} (h : Certifies p U C L r) :
    (U.block C).round = certRound p r := by
  unfold Certifies at h
  unfold certRound
  split_ifs at h ⊢ <;> exact h.1

/-- A link read on `H` is the record's. -/
theorem linkedIn_certLinked (hH : H ⊆ U.ids) {p : Params} {L : BlockId} {r : ℕ}
    (h : LinkedIn p U K H A L r) : CertLinked p U K A L r := by
  obtain ⟨X, hX, hXn⟩ := h
  exact ⟨X, fun C hC => ⟨hH (availIn_subset_held (hX C hC).1), availIn_subset (hX C hC).1,
    (hX C hC).2⟩, hXn⟩

/-- **Fetched down to the round of the certificates, the record's link is read
on `H`.** -/
theorem certLinked_linkedIn (hH : H ⊆ U.ids) {p : Params} {L : BlockId} {r : ℕ}
    (hf : FetchedIn U K H A (certRound p r)) (h : CertLinked p U K A L r) :
    LinkedIn p U K H A L r := by
  obtain ⟨X, hX, hXn⟩ := h
  exact ⟨X, fun C hC => ⟨avail_subset_availIn hH hf (hX C hC).2.1
    (round_of_certifies (hX C hC).2.2).ge, (hX C hC).2.2⟩, hXn⟩

/-! ## Checks -/

omit [ClaimFormat BlockId Payload] in
/-- Backing reads only what is held. -/
theorem backs_congr (hb : ∀ i ∈ H, U.block i = U'.block i) {t : ℕ} {L : BlockId}
    (h : Backs U t H L) : Backs U' t H L := by
  obtain ⟨hL, hn⟩ := h
  refine ⟨hL, ?_⟩
  have hf : (H.filter fun b => (U'.block b).round = (U'.block L).round + 1 ∧
      L ∈ (U'.block b).refs) = H.filter fun b =>
        (U.block b).round = (U.block L).round + 1 ∧ L ∈ (U.block b).refs :=
    Finset.filter_congr fun b hbH => by rw [hb b hbH, hb L hL]
  have hc : creatorsOf U'.block (H.filter fun b => (U.block b).round = (U.block L).round + 1 ∧
      L ∈ (U.block b).refs) = creatorsOf U.block (H.filter fun b =>
        (U.block b).round = (U.block L).round + 1 ∧ L ∈ (U.block b).refs) :=
    Finset.image_congr fun b hbH => by rw [hb b (Finset.mem_filter.mp hbH).1]
  rw [hf, hc]; exact hn

omit [ClaimFormat BlockId Payload] in
/-- **A backed claim names a certified block**: the votes held are votes of the
record. -/
theorem certified_of_backs (hH : H ⊆ U.ids) {t : ℕ} {L : BlockId} (h : Backs U t H L) :
    Certified U t L := by
  refine h.2.trans (Finset.card_le_card (Finset.image_subset_image fun b hb => ?_))
  obtain ⟨hbH, hbr, hLb⟩ := Finset.mem_filter.mp hb
  exact mem_votesFor.mpr ⟨hH hbH, hbr, hLb⟩

/-- **Checking what they hold, correct authors check and claim truthfully.** -/
theorem checks_of_buildsChecked {t : ℕ} (h : BuildsChecked U K t) :
    Checks U K t ∧ Truthful U t := by
  refine ⟨fun z hz hzc m hm X hX L hL => ?_, fun C hC hCc L hL => ?_⟩
  · obtain ⟨H, hH, -, hrefs⟩ := h z hz hzc
    exact certified_of_backs hH ((hrefs m hm).2 X hX L hL)
  · obtain ⟨H, hH, hcl, -⟩ := h C hC hCc
    exact certified_of_backs hH (hcl L hL)

/-! ## Decisions -/

variable [S : Slots Validator]

omit S [ClaimFormat BlockId Payload] in
/-- Blocks a node holds are held by a view holding what the node holds. -/
theorem holdsAtLeast_of_held {V : U.View} (hHV : H ⊆ V.ids) {s : Finset BlockId} {t : ℕ}
    (h : t ≤ (creatorsOf U.block (s.filter (· ∈ H))).card) : HoldsAtLeast U V t s :=
  h.trans (Finset.card_le_card (Finset.image_subset_image fun b hb => by
    obtain ⟨hbs, hbH⟩ := Finset.mem_filter.mp hb
    exact Finset.mem_inter.mpr ⟨hbs, hHV hbH⟩))

/-- **A node's decision is a decision on every view holding what it holds**,
for a node holding blocks of the record. -/
theorem NodeDecided.decided {p : Params} (hH : H ⊆ U.ids) {V : U.View} (hHV : H ⊆ V.ids) {k : ℕ}
    {v : Option BlockId} (h : NodeDecided p U K H k v) : (sRule p K).Decided U V k v := by
  induction h with
  | directCommit hL hc => exact AnchoredRule.Decided.directCommit hL (holdsAtLeast_of_held hHV hc)
  | directSkip hs => exact AnchoredRule.Decided.directSkip (holdsAtLeast_of_held hHV hs)
  | indirectCommit hkj helig _ _ hf hL hlink hleast ihj ihm =>
    exact AnchoredRule.Decided.indirectCommit (i := 0) hkj helig ihj ihm Nat.one_pos
      (fun i' hi' => absurd hi' (Nat.not_lt_zero _)) hL (linkedIn_certLinked hH hlink)
      fun L' hL' hl' hlt => hleast L' hL' hlt (certLinked_linkedIn hH hf hl')
  | indirectSkip hkj helig _ _ hf hnone ihj ihm =>
    exact AnchoredRule.Decided.indirectSkip_single rfl hkj helig ihj ihm
      (fun L hL hlink => hnone L hL (certLinked_linkedIn hH hf hlink))

/-- **Two nodes decide each slot alike**, at a row and the depth the sub-DAG
needs, on a disciplined schedule and record. -/
theorem NodeDecided.agree {p : Params} (hrow : Row Validator p) (hdeep : Deep Validator K)
    (hI : Disciplined K p.certThreshold S U) {H₁ H₂ : Finset BlockId}
    (hH₁ : H₁ ⊆ U.ids) (hH₂ : H₂ ⊆ U.ids) {k : ℕ} {v₁ v₂ : Option BlockId}
    (h₁ : NodeDecided p U K H₁ k v₁) (h₂ : NodeDecided p U K H₂ k v₂) : v₁ = v₂ :=
  (sRule p K).decided_unique (sRule_laws hrow hdeep) hI
    (h₁.decided (V := View.full U) hH₁ hH₁) _ _ (h₂.decided (V := View.full U) hH₂ hH₂)

end KPartialSparse

end LeanDag
