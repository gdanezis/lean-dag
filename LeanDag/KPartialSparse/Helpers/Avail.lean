import LeanDag.KPartialSparse.Model.Substrate
import LeanDag.KPartialDag.Helpers.Avail
/-!
# Sparse K-partial DAG — the available sub-DAG, helpers

`docs/kpartial-sparse.md` §3. Every block reaches the correct blocks of `q − f`
authors two rounds down in two steps (`card_reach2`), so a quorum of the
sub-DAG anchors a correct block (`exists_reached`); dense blocks of the
sub-DAG recur within four rounds (`DenseAt`, `denseAt_step`), and a quorum's
claim lies under one of them (`linked`). Claims of the sub-DAG were checked
by a correct author (`backed`).
-/

namespace LeanDag

namespace KPartialSparse

open KPartialDag

variable {Validator : Type*} [Fintype Validator] [DecidableEq Validator] [F : Faults Validator]
variable [Cr : Crashes Validator] [Ld : Leaders Validator]
variable {BlockId : Type*} [LinearOrder BlockId] {Payload : Type*}
variable {U : SRecord Validator BlockId Payload}

/-! ## Histories -/

theorem ref_mem_historyUpto {k : ℕ} {y x : BlockId} (hx : x ∈ (U.block y).refs) :
    x ∈ historyUpto U (k + 1) y :=
  mem_historyUpto_succ.mpr (Or.inr ⟨x, hx, mem_historyUpto_self⟩)

/-- Histories compose: depth `a` then depth `b` is depth `a + b`. -/
theorem historyUpto_trans : ∀ {a b : ℕ} {y x z : BlockId}, x ∈ historyUpto U a y →
    z ∈ historyUpto U b x → z ∈ historyUpto U (a + b) y
  | 0, b, y, x, z, hx, hz => by
    rw [historyUpto_zero, Finset.mem_singleton] at hx
    subst hx
    simpa using hz
  | a + 1, b, y, x, z, hx, hz => by
    rcases mem_historyUpto_succ.mp hx with rfl | ⟨j, hj, hxj⟩
    · exact historyUpto_mono (by omega) _ hz
    · rw [show a + 1 + b = (a + b) + 1 by omega]
      exact mem_historyUpto_succ.mpr (Or.inr ⟨j, hj, historyUpto_trans hxj hz⟩)

/-- **An honest chain lies in the history**: a correct author's earlier block
lies in the history of its later block, to the depth of their round gap. -/
theorem mem_historyUpto_of_chain (hch : Chains U) : ∀ (k : ℕ) {x y : BlockId}, y ∈ U.ids →
    x ∈ U.ids → (U.block y).creator ∈ (Correct : Finset Validator) →
    (U.block x).creator = (U.block y).creator → (U.block x).round ≤ (U.block y).round →
    (U.block y).round - (U.block x).round ≤ k → x ∈ historyUpto U k y := by
  intro k
  induction k with
  | zero =>
    intro x y hy hx hyc hxy hle hk
    have : x = y := U.no_equivocation x hx y hy (hxy ▸ hyc) hxy (by omega)
    subst this
    exact mem_historyUpto_self
  | succ k ih =>
    intro x y hy hx hyc hxy hle hk
    rcases Nat.lt_or_ge (U.block x).round (U.block y).round with hlt | hge
    · obtain ⟨s, hs, hsc, hsr⟩ := hch y hy hyc x hx hxy hlt
      have hs' : s ∈ U.ids := U.complete y hy s hs
      have hsy := (U.valid y hy).below s hs
      exact mem_historyUpto_succ.mpr (Or.inr ⟨s, hs,
        ih hs' hx (hsc ▸ hyc) (hxy.trans hsc.symm) hsr (by omega)⟩)
    · have : x = y := U.no_equivocation x hx y hy (hxy ▸ hyc) hxy (by omega)
      subst this
      exact mem_historyUpto_self

/-- A history of a block of the record lies in the record. -/
theorem historyUpto_subset_ids : ∀ (n : ℕ) {b : BlockId}, b ∈ U.ids → historyUpto U n b ⊆ U.ids
  | 0, b, hb, i, hi => by
    rw [historyUpto_zero, Finset.mem_singleton] at hi
    exact hi ▸ hb
  | n + 1, b, hb, i, hi => by
    rcases mem_historyUpto_succ.mp hi with rfl | ⟨j, hj, hij⟩
    · exact hb
    · exact historyUpto_subset_ids n (U.complete b hb j hj) hij

/-! ## Anchor points -/

/-- Anchor points below a block of the record lie in the record. -/
theorem Anchored.mem {K : ℕ} {A : BlockId} (hA : A ∈ U.ids) {x : BlockId} {d : ℕ}
    (h : Anchored U K A x d) : x ∈ U.ids := by
  induction h with
  | anchor => exact hA
  | referenced S y d hy hz href hcard ih =>
    obtain ⟨z, hz'⟩ : S.Nonempty := by
      rw [← Finset.card_pos]; exact lt_of_lt_of_le (by omega) (hcard.trans Finset.card_image_le)
    exact U.complete z (historyUpto_subset_ids _ (ih z hz') (hz z hz')) _ (href z hz')
  | reached S m y d y' d' hy hz hy' hmz hm href hcard ih ih' =>
    obtain ⟨z, hz'⟩ : S.Nonempty := by
      rw [← Finset.card_pos]; exact lt_of_lt_of_le (by omega) (hcard.trans Finset.card_image_le)
    exact U.complete (m z) (historyUpto_subset_ids _ (ih' z hz') (hmz z hz')) _ (href z hz')

/-- An anchor point brings `K − 1` rounds or more. -/
theorem Anchored.pred_le {K : ℕ} {A x : BlockId} {d : ℕ} (h : Anchored U K A x d) : K - 1 ≤ d := by
  cases h <;> omega

/-- **Anchoring in two steps from the sub-DAG**: a block that blocks of the
available sub-DAG from `f + c + 1` distinct authors reach through blocks of it
is an anchor point. -/
theorem Anchored.of_avail_two {K : ℕ} {A x : BlockId} {S : Finset BlockId}
    {m : BlockId → BlockId} (hS : ∀ z ∈ S, z ∈ Avail U K A ∧ m z ∈ Avail U K A)
    (hm : ∀ z ∈ S, m z ∈ (U.block z).refs) (href : ∀ z ∈ S, x ∈ (U.block (m z)).refs)
    (hcard : F.f + Cr.c + 1 ≤ (creatorsOf U.block S).card) :
    Anchored U K A x (K - 1) := by
  classical
  refine Anchored.reached S m (fun z => if h : z ∈ S then (hS z h).1.choose else A)
    (fun z => if h : z ∈ S then (hS z h).1.choose_spec.choose else K)
    (fun z => if h : z ∈ S then (hS z h).2.choose else A)
    (fun z => if h : z ∈ S then (hS z h).2.choose_spec.choose else K)
    (fun z hz => ?_) (fun z hz => ?_) (fun z hz => ?_) (fun z hz => ?_) hm href hcard <;>
    simp only [dif_pos hz]
  exacts [(hS z hz).1.choose_spec.choose_spec.1, (hS z hz).1.choose_spec.choose_spec.2,
    (hS z hz).2.choose_spec.choose_spec.1, (hS z hz).2.choose_spec.choose_spec.2]

/-! ## The double count -/

omit [LinearOrder BlockId] in
/-- A dense block names the correct authors of `q − f` blocks one round
below. -/
theorem card_dense_named {m : BlockId} {ρ : ℕ} (hmr : (U.block m).round = ρ + 1)
    (hd : Dense (kQuorum Validator) U.block (U.block m)) :
    kQuorum Validator - F.byzantine.card ≤ ((Correct : Finset Validator).filter fun w =>
      ∃ x ∈ (U.block m).refs, (U.block x).round = ρ ∧ (U.block x).creator = w).card := by
  have hsplit := card_le_card_inter_correct_add_byzantine (creatorsOf U.block (below1 U.block (U.block m)))
  have hsub : creatorsOf U.block (below1 U.block (U.block m)) ∩ (Correct : Finset Validator) ⊆
      (Correct : Finset Validator).filter fun w =>
        ∃ x ∈ (U.block m).refs, (U.block x).round = ρ ∧ (U.block x).creator = w := by
    intro w hw
    obtain ⟨hw₁, hw₂⟩ := Finset.mem_inter.mp hw
    obtain ⟨x, hx, rfl⟩ := mem_creatorsOf.mp hw₁
    obtain ⟨hxr, hxe⟩ := Finset.mem_filter.mp hx
    exact Finset.mem_filter.mpr ⟨hw₂, x, hxr, by omega, rfl⟩
  have := Finset.card_le_card hsub
  unfold Dense at hd
  omega

/-- **A block reaches `q − f` correct authors two rounds down in two steps**:
through a leader block when it is sparse, and when it is dense, through a
dense correct reference or through the self-references of its sparse correct
references. -/
theorem card_reach2 {z : BlockId} (hz : z ∈ U.ids) {ρ : ℕ} (hzr : (U.block z).round = ρ + 2) :
    kQuorum Validator - F.byzantine.card ≤ ((Correct : Finset Validator).filter fun w =>
      ∃ m ∈ (U.block z).refs, ∃ x ∈ (U.block m).refs,
        (U.block x).round = ρ ∧ (U.block x).creator = w).card := by
  classical
  -- through one dense reference one round below
  have hvia : ∀ m ∈ (U.block z).refs, (U.block m).round = ρ + 1 →
      Dense (kQuorum Validator) U.block (U.block m) →
      kQuorum Validator - F.byzantine.card ≤ ((Correct : Finset Validator).filter fun w =>
        ∃ m ∈ (U.block z).refs, ∃ x ∈ (U.block m).refs,
          (U.block x).round = ρ ∧ (U.block x).creator = w).card := by
    intro m hm hmr hd
    refine (card_dense_named hmr hd).trans (Finset.card_le_card fun w hw => ?_)
    obtain ⟨hwC, x, hx, hxr, hxw⟩ := Finset.mem_filter.mp hw
    exact Finset.mem_filter.mpr ⟨hwC, m, hm, x, hx, hxr, hxw⟩
  rcases (U.valid z hz).shape (by omega) with hdz | ⟨-, -, ℓ, hℓ, hℓr, hℓL⟩
  · by_cases hd : ∃ m ∈ below1 U.block (U.block z),
        (U.block m).creator ∈ (Correct : Finset Validator) ∧
          Dense (kQuorum Validator) U.block (U.block m)
    · obtain ⟨m, hm, -, hdm⟩ := hd
      obtain ⟨hm₁, hmr⟩ := Finset.mem_filter.mp hm
      exact hvia m hm₁ (by omega) hdm
    · push Not at hd
      have hsplit := card_le_card_inter_correct_add_byzantine
        (creatorsOf U.block (below1 U.block (U.block z)))
      refine le_trans ?_ (Finset.card_le_card (s := creatorsOf U.block (below1 U.block (U.block z)) ∩
        (Correct : Finset Validator)) fun w hw => ?_)
      · unfold Dense at hdz
        omega
      obtain ⟨hw₁, hw₂⟩ := Finset.mem_inter.mp hw
      obtain ⟨m, hm, rfl⟩ := mem_creatorsOf.mp hw₁
      obtain ⟨hm₁, hmr⟩ := Finset.mem_filter.mp hm
      have hm' : m ∈ U.ids := U.complete z hz m hm₁
      rcases (U.valid m hm').shape (by omega) with hdm | ⟨⟨s, hs, hsc, hsr⟩, -, -⟩
      · exact absurd hdm (hd m hm hw₂)
      · exact Finset.mem_filter.mpr ⟨hw₂, m, hm₁, s, hs, by omega, hsc⟩
  · have hℓ' : ℓ ∈ U.ids := U.complete z hz ℓ hℓ
    have hℓr' : (U.block ℓ).round = ρ + 1 := by omega
    have hdl := (U.valid ℓ hℓ').leader (by omega) (by rw [hℓr']; rw [hzr] at hℓL; exact hℓL)
    exact hvia ℓ hℓ hℓr' hdl

omit [LinearOrder BlockId] in
/-- **The double count**: when blocks of a quorum of distinct authors each name
`q − f` correct authors, under the spreading condition some correct author is
named by `f + c + 1` of them. -/
theorem exists_correct_named (hsp : Spread Validator) {S : Finset BlockId}
    (R : BlockId → Validator → Prop) [∀ z, DecidablePred (R z)]
    (hq : kQuorum Validator ≤ (creatorsOf U.block S).card)
    (hper : ∀ z ∈ S,
      kQuorum Validator - F.byzantine.card ≤ ((Correct : Finset Validator).filter (R z)).card) :
    ∃ w ∈ (Correct : Finset Validator),
      F.f + Cr.c + 1 ≤ (creatorsOf U.block (S.filter fun z => R z w)).card := by
  classical
  obtain ⟨hcb, hbf, hnv⟩ := faults_arith (Validator := Validator)
  let Rc : Validator → Validator → Prop := fun c w => ∃ z ∈ S, (U.block z).creator = c ∧ R z w
  let g : Validator → ℕ := fun w => ((creatorsOf U.block S).filter fun c => Rc c w).card
  have hper' : ∀ c ∈ creatorsOf U.block S, kQuorum Validator - F.byzantine.card ≤
      ((Correct : Finset Validator).filter fun w => Rc c w).card := by
    intro c hc
    obtain ⟨z, hzS, hzc⟩ := mem_creatorsOf.mp hc
    refine (hper z hzS).trans (Finset.card_le_card fun w hw => ?_)
    obtain ⟨hwC, hR⟩ := Finset.mem_filter.mp hw
    exact Finset.mem_filter.mpr ⟨hwC, z, hzS, hzc, hR⟩
  have hCne : (Correct : Finset Validator).Nonempty := by rw [← Finset.card_pos]; omega
  obtain ⟨w, hwC, hwmax⟩ := (Correct : Finset Validator).exists_max_image g hCne
  have hbig : (creatorsOf U.block S).card * (kQuorum Validator - F.byzantine.card) ≤
      (Correct : Finset Validator).card * g w := by
    have := Finset.card_nsmul_le_card_nsmul (r := fun c w => Rc c w) (s := creatorsOf U.block S)
      (t := (Correct : Finset Validator))
      (m := kQuorum Validator - F.byzantine.card) (n := g w)
      (fun c hc => by
        change _ ≤ ((Correct : Finset Validator).filter fun w => Rc c w).card
        exact hper' c hc)
      (fun v hv => hwmax v hv)
    simpa [smul_eq_mul] using this
  have hgw : F.f + Cr.c + 1 ≤ g w := by
    by_contra hlt
    push Not at hlt
    exact count_arith Cr.card_validators hbf hcb hq hbig (by omega) hsp
  refine ⟨w, hwC, hgw.trans (Finset.card_le_card fun c hc => ?_)⟩
  obtain ⟨-, z, hzS, hzc, hR⟩ := Finset.mem_filter.mp hc
  exact mem_creatorsOf.mpr ⟨z, Finset.mem_filter.mpr ⟨hzS, hR⟩, hzc⟩

/-- **A quorum of the sub-DAG anchors a correct block two rounds down**:
blocks of the available sub-DAG at round `ρ + 2` from a quorum of distinct
authors, whose references lie in the sub-DAG, reach in two steps a correct
author's round-`ρ` block from `f + c + 1` of those authors. -/
theorem exists_reached (hsp : Spread Validator) {K : ℕ} {A : BlockId} {S : Finset BlockId}
    {ρ : ℕ}
    (hS : ∀ z ∈ S, z ∈ U.ids ∧ (U.block z).round = ρ + 2 ∧ z ∈ Avail U K A ∧
      ∀ m ∈ (U.block z).refs, m ∈ Avail U K A)
    (hq : kQuorum Validator ≤ (creatorsOf U.block S).card) :
    ∃ x ∈ U.ids, (U.block x).round = ρ ∧ (U.block x).creator ∈ (Correct : Finset Validator) ∧
      Anchored U K A x (K - 1) := by
  classical
  let R : BlockId → Validator → Prop := fun z w =>
    ∃ m ∈ (U.block z).refs, ∃ x ∈ (U.block m).refs, (U.block x).round = ρ ∧ (U.block x).creator = w
  obtain ⟨w, hwC, hcard⟩ := exists_correct_named hsp R hq
    fun z hz => card_reach2 (hS z hz).1 (hS z hz).2.1
  set S' := S.filter fun z => R z w
  obtain ⟨z₀, hz₀⟩ : S'.Nonempty := by
    rw [← Finset.card_pos]
    exact lt_of_lt_of_le (by omega) (hcard.trans (Finset.card_image_le))
  obtain ⟨hz₀S, m₀, hm₀, x, hx, hxr, hxw⟩ := Finset.mem_filter.mp hz₀
  have hz₀' := (hS z₀ hz₀S).1
  have hm₀' : m₀ ∈ U.ids := U.complete z₀ hz₀' m₀ hm₀
  have hx' : x ∈ U.ids := U.complete m₀ hm₀' x hx
  let m : BlockId → BlockId := fun z => if h : R z w then h.choose else z
  have hmz : ∀ z ∈ S', m z ∈ (U.block z).refs ∧ x ∈ (U.block (m z)).refs := by
    intro z hz
    obtain ⟨hzS, hR⟩ := Finset.mem_filter.mp hz
    have hmdef : m z = hR.choose := dif_pos hR
    obtain ⟨hmref, x', hx'm, hx'r, hx'w⟩ := hR.choose_spec
    rw [hmdef]
    refine ⟨hmref, ?_⟩
    have hmi : hR.choose ∈ U.ids := U.complete z (hS z hzS).1 _ hmref
    have hx'i : x' ∈ U.ids := U.complete _ hmi x' hx'm
    have : x' = x := U.no_equivocation x' hx'i x hx' (hx'w ▸ hwC) (hx'w.trans hxw.symm)
      (hx'r.trans hxr.symm)
    exact this ▸ hx'm
  refine ⟨x, hx', hxr, hxw ▸ hwC, Anchored.of_avail_two (S := S') (m := m)
    (fun z hz => ?_) (fun z hz => (hmz z hz).1) (fun z hz => (hmz z hz).2) hcard⟩
  have hzS := (Finset.mem_filter.mp hz).1
  exact ⟨(hS z hzS).2.2.1, (hS z hzS).2.2.2 _ (hmz z hz).1⟩

/-! ## Descent -/

/-- A dense block at round `t` within one step of an anchor point bringing
`K − 1` rounds or more. -/
def DenseAt (U : SRecord Validator BlockId Payload) (K : ℕ) (A : BlockId) (t : ℕ) : Prop :=
  ∃ y d v, Anchored U K A y d ∧ K - 1 ≤ d ∧ v ∈ historyUpto U 1 y ∧ v ∈ U.ids ∧
    Dense (kQuorum Validator) U.block (U.block v) ∧ (U.block v).round = t

/-- The two-step reach of a dense block's references lies in the sub-DAG. -/
theorem below_mem_avail {K : ℕ} (hK : 4 ≤ K) {A y v : BlockId} {d : ℕ} (hy : Anchored U K A y d)
    (hd : K - 1 ≤ d) (hv : v ∈ historyUpto U 1 y) {z : BlockId}
    (hz : z ∈ (U.block v).refs) :
    z ∈ Avail U K A ∧ ∀ m ∈ (U.block z).refs, m ∈ Avail U K A := by
  have hz2 : z ∈ historyUpto U 2 y := historyUpto_trans hv (ref_mem_historyUpto (k := 0) hz)
  refine ⟨⟨y, d, hy, historyUpto_mono (by omega) _ hz2⟩, fun m hm => ⟨y, d, hy, ?_⟩⟩
  exact historyUpto_mono (by omega) _ (historyUpto_trans hz2 (ref_mem_historyUpto (k := 0) hm))

/-- **Dense blocks of the sub-DAG recur within four rounds**: below a dense
block at round `t ≥ 5` near an anchor point, a correct block three rounds down
is an anchor point, and it or its leader reference is dense. -/
theorem denseAt_step (hsp : Spread Validator) {K : ℕ} (hK : 4 ≤ K) {A : BlockId} {t : ℕ}
    (h : DenseAt U K A t) (ht : 5 ≤ t) : ∃ t', t - 4 ≤ t' ∧ t' < t ∧ DenseAt U K A t' := by
  obtain ⟨y, d, v, hy, hd, hvy, hv, hdv, hvr⟩ := h
  obtain ⟨x, hx, hxr, -, hxa⟩ := exists_reached hsp (K := K) (A := A)
    (S := below1 U.block (U.block v)) (ρ := t - 3)
    (fun z hz => by
      obtain ⟨hz₁, hzr⟩ := Finset.mem_filter.mp hz
      obtain ⟨ha, hb⟩ := below_mem_avail hK hy hd hvy hz₁
      exact ⟨U.complete v hv z hz₁, by omega, ha, hb⟩) hdv
  rcases (U.valid x hx).shape (by omega) with hdx | ⟨-, -, ℓ, hℓ, hℓr, hℓL⟩
  · exact ⟨t - 3, by omega, by omega, x, K - 1, x, hxa, le_refl _, mem_historyUpto_self, hx, hdx, hxr⟩
  · have hℓ' : ℓ ∈ U.ids := U.complete x hx ℓ hℓ
    have hℓr' : (U.block ℓ).round = t - 4 := by omega
    have hdl := (U.valid ℓ hℓ').leader (by omega)
      (by rw [hℓr', show t - 4 = (U.block x).round - 1 by omega]; exact hℓL)
    exact ⟨t - 4, le_refl _, by omega, x, K - 1, ℓ, hxa, le_refl _,
      ref_mem_historyUpto (k := 0) hℓ, hℓ', hdl, hℓr'⟩

/-- **A dense block of the sub-DAG in every four-round window** from `ρ + 3`
up to a dense block of the sub-DAG. -/
theorem denseAt_window (hsp : Spread Validator) {K : ℕ} (hK : 4 ≤ K) {A : BlockId} (ρ : ℕ) :
    ∀ t, DenseAt U K A t → ρ + 3 ≤ t → ∃ t', ρ + 3 ≤ t' ∧ t' ≤ ρ + 6 ∧ DenseAt U K A t' := by
  intro t
  induction t using Nat.strong_induction_on with
  | _ t ih =>
    intro h ht
    by_cases hle : t ≤ ρ + 6
    · exact ⟨t, ht, hle, h⟩
    · obtain ⟨t', ht'₁, ht'₂, h'⟩ := denseAt_step hsp hK h (by omega)
      exact ih t' ht'₂ h' (by omega)

/-! ## Linked and backed -/

variable [ClaimFormat BlockId Payload]

omit Ld in
/-- A quorum and `cm` authors with `n + f < q + cm` share a correct author. -/
theorem exists_correct_inter {X Y : Finset Validator} {cm : ℕ} (hX : kQuorum Validator ≤ X.card)
    (hY : cm ≤ Y.card) (h : Fintype.card Validator + F.f < kQuorum Validator + cm) :
    ∃ a ∈ X ∩ Y, a ∈ (Correct : Finset Validator) := by
  have hu := Finset.card_union_add_card_inter X Y
  have huniv : (X ∪ Y).card ≤ Fintype.card Validator := Finset.card_le_univ _
  have hsplit := card_le_card_inter_correct_add_byzantine (X ∩ Y)
  have hb := F.card_byzantine
  obtain ⟨a, ha⟩ : ((X ∩ Y) ∩ (Correct : Finset Validator)).Nonempty := by
    rw [← Finset.card_pos]; omega
  exact ⟨a, (Finset.mem_inter.mp ha).1, (Finset.mem_inter.mp ha).2⟩

/-- **A quorum's claim lies in the sub-DAG** below a leader block at round
`ρ + 3` or above. -/
theorem linked (hsp : Spread Validator) {K cm ρ : ℕ} (hK : 6 ≤ K) (hch : Chains U) {A L : BlockId}
    (hA : A ∈ U.ids) (hAl : (U.block A).creator ∈ Ld.leaders (U.block A).round)
    (hAr : ρ + 3 ≤ (U.block A).round)
    (hcm : Fintype.card Validator + F.f < kQuorum Validator + cm)
    (hcl : cm ≤ (creatorsOf U.block (claimersOf U L (ρ + 2))).card) :
    ∃ C ∈ Avail U K A, (U.block C).round = ρ + 2 ∧ L ∈ claimsOf U C := by
  have hdA := (U.valid A hA).leader (by omega) hAl
  obtain ⟨t, ht₁, ht₂, y, d, v, hy, hd, hvy, hv, hdv, hvr⟩ :=
    denseAt_window hsp (by omega) ρ _ ⟨A, K, A, Anchored.anchor, by omega, mem_historyUpto_self,
      hA, hdA, rfl⟩ hAr
  obtain ⟨a, ha, haC⟩ := exists_correct_inter hdv hcl hcm
  obtain ⟨ha₁, ha₂⟩ := Finset.mem_inter.mp ha
  obtain ⟨X, hX, hXa⟩ := mem_creatorsOf.mp ha₁
  obtain ⟨C, hC, hCa⟩ := mem_creatorsOf.mp ha₂
  obtain ⟨hX₁, hXr⟩ := Finset.mem_filter.mp hX
  obtain ⟨hCb, hCL⟩ := Finset.mem_filter.mp hC
  obtain ⟨hCi, hCr⟩ := mem_blocksAt.mp hCb
  have hXi : X ∈ U.ids := U.complete v hv X hX₁
  have hCX : C ∈ historyUpto U ((U.block X).round - (U.block C).round) X :=
    mem_historyUpto_of_chain hch _ hXi hCi (hXa ▸ haC) (hCa.trans hXa.symm) (by omega) le_rfl
  have hX2 : X ∈ historyUpto U 2 y := historyUpto_trans hvy (ref_mem_historyUpto (k := 0) hX₁)
  refine ⟨C, ⟨y, d, hy, historyUpto_mono ?_ _ (historyUpto_trans hX2 hCX)⟩, hCr, hCL⟩
  omega

/-- **Claims of the sub-DAG are backed**: each lies in the history to depth `K`
of a block a correct author references, which that author checked. -/
theorem backed {K t : ℕ} (hK : 1 ≤ K) (hck : Checks U K t) {A : BlockId}
    (hA : ∃ z ∈ U.ids, (U.block z).creator ∈ (Correct : Finset Validator) ∧ A ∈ (U.block z).refs)
    {X : BlockId} (hX : X ∈ Avail U K A) {L : BlockId} (hL : L ∈ claimsOf U X) :
    Certified U t L := by
  obtain ⟨y, d, hy, hXy⟩ := hX
  -- a correct author among `f + c + 1`
  have hcorrect : ∀ S : Finset BlockId, F.f + Cr.c + 1 ≤ (creatorsOf U.block S).card →
      ∃ z ∈ S, (U.block z).creator ∈ (Correct : Finset Validator) := by
    intro S hS
    have hsplit := card_le_card_inter_correct_add_byzantine (creatorsOf U.block S)
    have hb := F.card_byzantine
    obtain ⟨w, hw⟩ : (creatorsOf U.block S ∩ (Correct : Finset Validator)).Nonempty := by
      rw [← Finset.card_pos]; omega
    obtain ⟨hw₁, hw₂⟩ := Finset.mem_inter.mp hw
    obtain ⟨z, hz, rfl⟩ := mem_creatorsOf.mp hw₁
    exact ⟨z, hz, hw₂⟩
  obtain ⟨z₀, hz₀, hz₀c, hAz₀⟩ := hA
  have hAi : A ∈ U.ids := U.complete z₀ hz₀ A hAz₀
  cases hy with
  | anchor => exact hck z₀ hz₀ hz₀c A hAz₀ X hXy L hL
  | referenced S y d hy hz href hcard =>
    obtain ⟨z, hzS, hzc⟩ := hcorrect S hcard
    have hzi : z ∈ U.ids := historyUpto_subset_ids _ ((hy z hzS).mem hAi) (hz z hzS)
    exact hck z hzi hzc _ (href z hzS) X hXy L hL
  | reached S m y d y' d' hy hz hy' hmz hm href hcard =>
    obtain ⟨z, hzS, hzc⟩ := hcorrect S hcard
    have hzi : z ∈ U.ids := historyUpto_subset_ids _ ((hy z hzS).mem hAi) (hz z hzS)
    have hXm : X ∈ historyUpto U (1 + (K - 1)) (m z) :=
      historyUpto_trans (ref_mem_historyUpto (k := 0) (href z hzS)) hXy
    rw [show 1 + (K - 1) = K by omega] at hXm
    exact hck z hzi hzc _ (hm z hzS) X hXm L hL

end KPartialSparse

end LeanDag
