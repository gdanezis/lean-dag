import LeanDag.KPartialSparse.Model.Substrate
import LeanDag.KPartialDag.Helpers.Avail
/-!
# Sparse K-partial DAG — the available sub-DAG, helpers

`docs/kpartial-sparse.md` §3. Every block reaches the correct blocks of `q − f`
authors two rounds down in two steps (`card_reach2`), so a quorum of the
sub-DAG anchors a correct block (`exists_reached`); dense blocks of the
sub-DAG recur within four rounds; without the spreading condition, every
block of a quorum reaches one block in four steps (`exists_core_reached`), and
dense blocks recur within six rounds (`Recurs`, `exists_recurs`); a quorum's
claim lies under one of them (`linked`). Every block of the sub-DAG lies in
the window a correct author holds (`exists_holder`), so it is held
(`avail_correctHeld`) and its claims were checked (`backed`).
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

/-! ## Windows -/

section WindowFrom

variable {blk : BlockId → Block Validator BlockId Payload}

omit [Fintype Validator] [DecidableEq Validator] Ld in
theorem mem_windowFrom_succ {n lo : ℕ} {b z : BlockId} :
    z ∈ windowFrom blk (n + 1) lo b ↔
      z = b ∨ ∃ j ∈ (blk b).refs, lo ≤ (blk j).round ∧ z ∈ windowFrom blk n lo j := by
  simp only [windowFrom, Finset.mem_insert, Finset.mem_biUnion, Finset.mem_filter, and_assoc]

omit [Fintype Validator] [DecidableEq Validator] Ld in
theorem mem_windowFrom_self {n lo : ℕ} {b : BlockId} : b ∈ windowFrom blk n lo b := by
  cases n with
  | zero => simp [windowFrom]
  | succ n => exact mem_windowFrom_succ.mpr (Or.inl rfl)

omit [Fintype Validator] [DecidableEq Validator] Ld in
theorem mem_windowFrom_zero {lo : ℕ} {b z : BlockId} (h : z ∈ windowFrom blk 0 lo b) : z = b := by
  simpa [windowFrom] using h

omit [Fintype Validator] [DecidableEq Validator] Ld in
/-- Every block of a window but its top is at round `lo` or above. -/
theorem windowFrom_round : ∀ {n lo : ℕ} {b z : BlockId}, z ∈ windowFrom blk n lo b →
    z = b ∨ lo ≤ (blk z).round
  | 0, _, _, _, h => Or.inl (mem_windowFrom_zero h)
  | n + 1, _, _, _, h => by
    rcases mem_windowFrom_succ.mp h with rfl | ⟨j, -, hj, hz⟩
    · exact Or.inl rfl
    · rcases windowFrom_round hz with rfl | h'
      · exact Or.inr hj
      · exact Or.inr h'

omit [Fintype Validator] [DecidableEq Validator] Ld in
/-- More steps and a lower bound never lose anything. -/
theorem windowFrom_mono : ∀ {m n lo lo' : ℕ}, m ≤ n → lo' ≤ lo → ∀ b : BlockId,
    windowFrom blk m lo b ⊆ windowFrom blk n lo' b
  | 0, _, _, _, _, _, b, z, hz => by rw [mem_windowFrom_zero hz]; exact mem_windowFrom_self
  | m + 1, n, lo, lo', h, hlo, b, z, hz => by
    obtain ⟨n, rfl⟩ : ∃ n', n = n' + 1 := ⟨n - 1, by omega⟩
    rcases mem_windowFrom_succ.mp hz with rfl | ⟨j, hj, hjr, hzj⟩
    · exact mem_windowFrom_self
    · exact mem_windowFrom_succ.mpr (Or.inr ⟨j, hj, by omega,
        windowFrom_mono (by omega) hlo j hzj⟩)

omit [Fintype Validator] [DecidableEq Validator] Ld in
/-- Windows at one bound compose. -/
theorem windowFrom_trans : ∀ {a b lo : ℕ} {y x z : BlockId}, x ∈ windowFrom blk a lo y →
    z ∈ windowFrom blk b lo x → z ∈ windowFrom blk (a + b) lo y
  | 0, b, lo, y, x, z, hx, hz => by
    rw [mem_windowFrom_zero hx] at hz; exact windowFrom_mono (by omega) le_rfl _ hz
  | a + 1, b, lo, y, x, z, hx, hz => by
    rcases mem_windowFrom_succ.mp hx with rfl | ⟨j, hj, hjr, hxj⟩
    · exact windowFrom_mono (by omega) le_rfl _ hz
    · rw [show a + 1 + b = (a + b) + 1 by omega]
      exact mem_windowFrom_succ.mpr (Or.inr ⟨j, hj, hjr, windowFrom_trans hxj hz⟩)

omit [Fintype Validator] [DecidableEq Validator] Ld in
theorem windowFrom_subset_history : ∀ {n lo : ℕ} {b : BlockId},
    windowFrom blk n lo b ⊆ historyUptoFrom blk n b
  | 0, _, _, z, hz => by rw [mem_windowFrom_zero hz]; exact mem_historyUptoFrom_self
  | n + 1, _, _, z, hz => by
    rcases mem_windowFrom_succ.mp hz with rfl | ⟨j, hj, -, hzj⟩
    · exact mem_historyUptoFrom_self
    · exact mem_historyUptoFrom_succ.mpr (Or.inr ⟨j, hj, windowFrom_subset_history hzj⟩)

end WindowFrom

theorem self_mem_window {n : ℕ} {y : BlockId} : y ∈ window U n y := mem_windowFrom_self

/-- A block of the window to depth `n` is at most `n` rounds below its top. -/
theorem round_of_mem_window {n : ℕ} {y z : BlockId} (h : z ∈ window U n y) :
    (U.block y).round ≤ (U.block z).round + n := by
  rcases windowFrom_round h with rfl | h'
  · omega
  · omega

theorem window_subset_historyUpto {n : ℕ} {y : BlockId} : window U n y ⊆ historyUpto U n y :=
  windowFrom_subset_history

theorem window_mono {m n : ℕ} (h : m ≤ n) (y : BlockId) : window U m y ⊆ window U n y :=
  windowFrom_mono h (by omega) y

theorem interior_subset_window {i : ℕ} {b : BlockId} : interior U i b ⊆ window U i b :=
  windowFrom_mono (by omega) le_rfl b

/-- Windows compose: depth `a` then depth `b` is depth `a + b`. -/
theorem window_trans {a b : ℕ} {y x z : BlockId} (hx : x ∈ window U a y)
    (hz : z ∈ window U b x) : z ∈ window U (a + b) y := by
  have hr := round_of_mem_window hx
  exact windowFrom_trans (windowFrom_mono le_rfl (by omega) _ hx)
    (windowFrom_mono le_rfl (by omega) _ hz)

/-- The interior of a window, then a window, lies in a window. -/
theorem interior_trans {i b : ℕ} {y x z : BlockId} (hx : x ∈ window U i y)
    (hz : z ∈ interior U b x) : z ∈ window U (i + b) y :=
  window_trans hx (interior_subset_window hz)

/-- A reference one round below lies in the window to depth one. -/
theorem ref_mem_window {k : ℕ} {y x : BlockId} (hx : x ∈ (U.block y).refs)
    (hr : (U.block x).round + 1 = (U.block y).round) : x ∈ window U (k + 1) y :=
  mem_windowFrom_succ.mpr (Or.inr ⟨x, hx, by omega, mem_windowFrom_self⟩)

theorem mem_window_zero {y z : BlockId} (h : z ∈ window U 0 y) : z = y := mem_windowFrom_zero h

/-- A window of a block of the record lies in the record. -/
theorem window_subset_ids (n : ℕ) {b : BlockId} (hb : b ∈ U.ids) : window U n b ⊆ U.ids :=
  window_subset_historyUpto.trans (historyUpto_subset_ids n hb)

/-- **An honest chain lies in the window**: a correct author's earlier block lies
in the window of its later block, to the depth of their round gap. -/
theorem mem_windowFrom_of_chain (hch : Chains U) : ∀ (k lo : ℕ) {x y : BlockId}, y ∈ U.ids →
    x ∈ U.ids → (U.block y).creator ∈ (Correct : Finset Validator) →
    (U.block x).creator = (U.block y).creator → (U.block x).round ≤ (U.block y).round →
    (U.block y).round - (U.block x).round ≤ k → lo ≤ (U.block x).round →
    x ∈ windowFrom U.block k lo y := by
  intro k lo
  induction k with
  | zero =>
    intro x y hy hx hyc hxy hle hk _
    have : x = y := U.no_equivocation x hx y hy (hxy ▸ hyc) hxy (by omega)
    subst this
    exact mem_windowFrom_self
  | succ k ih =>
    intro x y hy hx hyc hxy hle hk hlo
    rcases Nat.lt_or_ge (U.block x).round (U.block y).round with hlt | hge
    · obtain ⟨s, hs, hsc, hsr⟩ := hch y hy hyc x hx hxy hlt
      have hs' : s ∈ U.ids := U.complete y hy s hs
      have hsy := (U.valid y hy).below s hs
      exact mem_windowFrom_succ.mpr (Or.inr ⟨s, hs, by omega,
        ih hs' hx (hsc ▸ hyc) (hxy.trans hsc.symm) hsr (by omega) hlo⟩)
    · have : x = y := U.no_equivocation x hx y hy (hxy ▸ hyc) hxy (by omega)
      subst this
      exact mem_windowFrom_self

theorem mem_window_of_chain (hch : Chains U) (k : ℕ) {x y : BlockId} (hy : y ∈ U.ids)
    (hx : x ∈ U.ids) (hyc : (U.block y).creator ∈ (Correct : Finset Validator))
    (hxy : (U.block x).creator = (U.block y).creator) (hle : (U.block x).round ≤ (U.block y).round)
    (hk : (U.block y).round - (U.block x).round ≤ k) : x ∈ window U k y :=
  mem_windowFrom_of_chain hch k _ hy hx hyc hxy hle hk (by omega)

/-! ## Anchor points -/

/-- Anchor points below a block of the record lie in the record. -/
theorem Anchored.mem {K : ℕ} {A : BlockId} (hA : A ∈ U.ids) {x : BlockId} {d : ℕ}
    (h : Anchored U K A x d) : x ∈ U.ids := by
  induction h with
  | anchor => exact hA
  | reached i S m y d y' d' hy hz hy' hmz hi hm hcard ih ih' =>
    obtain ⟨z, hz'⟩ : S.Nonempty := by
      rw [← Finset.card_pos]; exact lt_of_lt_of_le (by omega) (hcard.trans Finset.card_image_le)
    have hzi := window_subset_ids _ (ih z hz') (hz z hz')
    exact window_subset_ids _ (U.complete z hzi _ (hm z hz').1) (hm z hz').2.1

/-- **Anchoring from the sub-DAG in two steps**: a block that blocks of the
available sub-DAG from `f + c + 1` distinct authors reach through references
in the sub-DAG is an anchor point bringing `K − 1` rounds. -/
theorem Anchored.of_avail_two {K : ℕ} (hK : 1 ≤ K) {A x : BlockId} {S : Finset BlockId}
    {m : BlockId → BlockId} (hS : ∀ z ∈ S, z ∈ Avail U K A ∧ m z ∈ Avail U K A)
    (hm : ∀ z ∈ S, m z ∈ (U.block z).refs) (href : ∀ z ∈ S, x ∈ (U.block (m z)).refs)
    (hround : ∀ z ∈ S, (U.block x).round + 1 = (U.block (m z)).round)
    (hmround : ∀ z ∈ S, (U.block (m z)).round + 1 = (U.block z).round)
    (hcard : F.f + Cr.c + 1 ≤ (creatorsOf U.block S).card) :
    Anchored U K A x (K - 1) := by
  classical
  refine Anchored.reached 1 S m (fun z => if h : z ∈ S then (hS z h).1.choose else A)
    (fun z => if h : z ∈ S then (hS z h).1.choose_spec.choose else K)
    (fun z => if h : z ∈ S then (hS z h).2.choose else A)
    (fun z => if h : z ∈ S then (hS z h).2.choose_spec.choose else K)
    (fun z hz => ?_) (fun z hz => ?_) (fun z hz _ => ?_) (fun z hz _ => ?_) hK
    (fun z hz => ⟨hm z hz, ref_mem_window (k := 0) (href z hz) (hround z hz), hmround z hz⟩)
    hcard <;>
    simp only [dif_pos hz]
  · exact (hS z hz).1.choose_spec.choose_spec.1
  · exact (hS z hz).1.choose_spec.choose_spec.2
  · exact (hS z hz).2.choose_spec.choose_spec.1
  · intro w hw
    obtain rfl := mem_windowFrom_zero hw
    exact (hS z hz).2.choose_spec.choose_spec.2

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

omit [LinearOrder BlockId] in
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
theorem exists_reached (hsp : Spread Validator) {K : ℕ} (hK : 1 ≤ K) {A : BlockId}
    {S : Finset BlockId} {ρ : ℕ}
    (hS : ∀ z ∈ S, z ∈ U.ids ∧ (U.block z).round = ρ + 2 ∧ z ∈ Avail U K A ∧
      ∀ m ∈ (U.block z).refs, (U.block m).round + 1 = (U.block z).round → m ∈ Avail U K A)
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
  have hm₀' : m₀ ∈ U.ids := U.complete z₀ (hS z₀ hz₀S).1 m₀ hm₀
  have hx' : x ∈ U.ids := U.complete m₀ hm₀' x hx
  let m : BlockId → BlockId := fun z => if h : R z w then h.choose else z
  have hmz : ∀ z ∈ S', m z ∈ (U.block z).refs ∧ x ∈ (U.block (m z)).refs ∧
      (U.block (m z)).round = ρ + 1 := by
    intro z hz
    obtain ⟨hzS, hR⟩ := Finset.mem_filter.mp hz
    have hmdef : m z = hR.choose := dif_pos hR
    obtain ⟨hmref, x', hx'm, hx'r, hx'w⟩ := hR.choose_spec
    rw [hmdef]
    have hmi : hR.choose ∈ U.ids := U.complete z (hS z hzS).1 _ hmref
    have hx'i : x' ∈ U.ids := U.complete _ hmi x' hx'm
    have hxx : x' = x := U.no_equivocation x' hx'i x hx' (hx'w ▸ hwC) (hx'w.trans hxw.symm)
      (hx'r.trans hxr.symm)
    have h1 := (U.valid z (hS z hzS).1).below _ hmref
    have h2 := (U.valid _ hmi).below x' hx'm
    have := (hS z hzS).2.1
    exact ⟨hmref, hxx ▸ hx'm, by omega⟩
  refine ⟨x, hx', hxr, hxw ▸ hwC, Anchored.of_avail_two hK (S := S') (m := m)
    (fun z hz => ?_) (fun z hz => (hmz z hz).1) (fun z hz => (hmz z hz).2.1)
    (fun z hz => by rw [(hmz z hz).2.2, hxr])
    (fun z hz => by rw [(hmz z hz).2.2, (hS z (Finset.mem_filter.mp hz).1).2.1]) hcard⟩
  have hzS := (Finset.mem_filter.mp hz).1
  exact ⟨(hS z hzS).2.2.1, (hS z hzS).2.2.2 _ (hmz z hz).1
    (by rw [(hmz z hz).2.2, (hS z hzS).2.1])⟩

/-! ## The core, without the spreading condition -/

/-- The arithmetic of the core: `m` correct authors each naming `q − b` of
`n − b` correct authors cannot leave every author named by `m − (q − b)` or
fewer of them, at `n ≥ 3f + 2c + 1`. -/
theorem core_arith {n f c b Cc m g : ℕ} (hn : 3 * f + 2 * c + 1 ≤ n) (hb : b ≤ f)
    (hC : Cc + b = n) (hmC : m ≤ Cc) (hbig : m * (n - f - c - b) ≤ Cc * g)
    (hg : g + (n - f - c - b) ≤ m) : False := by
  obtain ⟨Q, hQ⟩ : ∃ Q, n = Q + f + c + b := ⟨n - f - c - b, by omega⟩
  have eQ : n - f - c - b = Q := by omega
  rw [eQ] at hbig hg
  have hCc : Cc = Q + f + c := by omega
  subst hCc
  have hQf : f + c + 1 ≤ Q := by omega
  have k1 : (Q + f + c) * g + (Q + f + c) * Q ≤ (Q + f + c) * m := by
    rw [← Nat.mul_add]; exact Nat.mul_le_mul_left _ hg
  have k2 : (f + c) * m ≤ (f + c) * (Q + f + c) := Nat.mul_le_mul_left _ hmC
  have k3 : (f + c + 1) * (Q + f + c) ≤ Q * (Q + f + c) := Nat.mul_le_mul_right _ hQf
  nlinarith

/-- **The core**: blocks of the sub-DAG at round `ρ + 4` from a quorum of
distinct authors, with their window to depth four in the window an anchor
point brings, all reach in four steps one correct author's round-`ρ` block,
an anchor point bringing `K − 3` rounds; at `n ≥ 3f + 2c + 1`, with no
spreading condition. -/
theorem exists_core_reached {K : ℕ} (hK : 3 ≤ K) {A : BlockId} {S : Finset BlockId} {ρ : ℕ}
    (hS : ∀ z ∈ S, z ∈ U.ids ∧ (U.block z).round = ρ + 4 ∧
      ∃ y d, Anchored U K A y d ∧ window U 4 z ⊆ window U d y)
    (hq : kQuorum Validator ≤ (creatorsOf U.block S).card) :
    ∃ x ∈ U.ids, (U.block x).round = ρ ∧ (U.block x).creator ∈ (Correct : Finset Validator) ∧
      Anchored U K A x (K - 3) := by
  classical
  obtain ⟨hcb, hbf, hnv⟩ := faults_arith (Validator := Validator)
  have hnc := Cr.card_validators
  -- two-step names, from a block at round `ρ + 4` and from one at round `ρ + 2`
  let R : BlockId → Validator → Prop := fun z w => ∃ m ∈ (U.block z).refs, ∃ b ∈ (U.block m).refs,
    (U.block b).round = ρ + 2 ∧ (U.block b).creator = w
  let R' : Validator → Validator → Prop := fun w x => ∃ b ∈ U.ids, (U.block b).round = ρ + 2 ∧
    (U.block b).creator = w ∧ ∃ m ∈ (U.block b).refs, ∃ c ∈ (U.block m).refs,
      (U.block c).round = ρ ∧ (U.block c).creator = x
  set Cs := (Correct : Finset Validator)
  set M := Cs.filter fun w => ∃ z ∈ S, R z w
  have hRz : ∀ z ∈ S, kQuorum Validator - F.byzantine.card ≤ (Cs.filter (R z)).card :=
    fun z hz => card_reach2 (hS z hz).1 (by rw [(hS z hz).2.1])
  have hRzM : ∀ z ∈ S, Cs.filter (R z) ⊆ M := fun z hz w hw => by
    obtain ⟨hwC, hR⟩ := Finset.mem_filter.mp hw
    exact Finset.mem_filter.mpr ⟨hwC, z, hz, hR⟩
  -- each author of `M` names `q − f` correct authors two rounds further down
  have hM : ∀ w ∈ M, kQuorum Validator - F.byzantine.card ≤ (Cs.filter (R' w)).card := by
    intro w hw
    obtain ⟨hwC, z, hz, m, hm, b, hb, hbr, hbw⟩ := Finset.mem_filter.mp hw
    have hmi : m ∈ U.ids := U.complete z (hS z hz).1 m hm
    have hbi : b ∈ U.ids := U.complete m hmi b hb
    refine (card_reach2 hbi hbr).trans (Finset.card_le_card fun x hx => ?_)
    obtain ⟨hxC, m', hm', c, hc, hcr, hcx⟩ := Finset.mem_filter.mp hx
    exact Finset.mem_filter.mpr ⟨hxC, b, hbi, hbr, hbw, m', hm', c, hc, hcr, hcx⟩
  have hCne : Cs.Nonempty := by rw [← Finset.card_pos]; omega
  let g : Validator → ℕ := fun x => (M.filter fun w => R' w x).card
  obtain ⟨x, hxC, hxmax⟩ := Cs.exists_max_image g hCne
  have hbig : M.card * (kQuorum Validator - F.byzantine.card) ≤ Cs.card * g x := by
    have := Finset.card_nsmul_le_card_nsmul (r := fun w x => R' w x) (s := M) (t := Cs)
      (m := kQuorum Validator - F.byzantine.card) (n := g x)
      (fun w hw => hM w hw) (fun v hv => hxmax v hv)
    simpa [smul_eq_mul] using this
  obtain ⟨z₀, hz₀⟩ : S.Nonempty := by
    rw [← Finset.card_pos]; exact lt_of_lt_of_le (by omega) (hq.trans Finset.card_image_le)
  have hmq : kQuorum Validator - F.byzantine.card ≤ M.card :=
    (hRz z₀ hz₀).trans (Finset.card_le_card (hRzM z₀ hz₀))
  have hgx : M.card < (M.filter fun w => R' w x).card + (kQuorum Validator - F.byzantine.card) := by
    by_contra hle
    push Not at hle
    exact core_arith hnc hbf hcb (Finset.card_le_card (Finset.filter_subset _ _)) hbig hle
  -- the round-`ρ` block of `x`
  obtain ⟨w₀, hw₀⟩ : (M.filter fun w => R' w x).Nonempty := by
    rw [← Finset.card_pos]; omega
  obtain ⟨-, b₀, hb₀i, -, -, m₀, hm₀, x₀, hx₀, hx₀r, hx₀x⟩ := Finset.mem_filter.mp hw₀
  have hm₀i : m₀ ∈ U.ids := U.complete b₀ hb₀i m₀ hm₀
  have hx₀i : x₀ ∈ U.ids := U.complete m₀ hm₀i x₀ hx₀
  -- every block of `S` reaches it through an author of `M` that names `x`
  have hreach : ∀ z ∈ S, ∃ m ∈ (U.block z).refs, (U.block m).round + 1 = (U.block z).round ∧
      x₀ ∈ window U 3 m := by
    intro z hz
    have hu := Finset.card_union_add_card_inter (Cs.filter (R z)) (M.filter fun w => R' w x)
    have hsub : Cs.filter (R z) ∪ M.filter (fun w => R' w x) ⊆ M :=
      Finset.union_subset (hRzM z hz) (Finset.filter_subset _ _)
    have := Finset.card_le_card hsub
    have := hRz z hz
    obtain ⟨w, hw⟩ : (Cs.filter (R z) ∩ M.filter fun w => R' w x).Nonempty := by
      rw [← Finset.card_pos]; omega
    obtain ⟨hw₁, hw₂⟩ := Finset.mem_inter.mp hw
    obtain ⟨hwC, m, hm, b, hb, hbr, hbw⟩ := Finset.mem_filter.mp hw₁
    obtain ⟨-, b', hb'i, hb'r, hb'w, m', hm', c, hc, hcr, hcx⟩ := Finset.mem_filter.mp hw₂
    have hmi : m ∈ U.ids := U.complete z (hS z hz).1 m hm
    have hbi : b ∈ U.ids := U.complete m hmi b hb
    have hbb : b' = b := U.no_equivocation b' hb'i b hbi (hb'w ▸ hwC) (hb'w.trans hbw.symm)
      (hb'r.trans hbr.symm)
    subst hbb
    have hm'i : m' ∈ U.ids := U.complete b' hb'i m' hm'
    have hci : c ∈ U.ids := U.complete m' hm'i c hc
    have hcc : c = x₀ := U.no_equivocation c hci x₀ hx₀i (hcx ▸ hxC) (hcx.trans hx₀x.symm)
      (hcr.trans hx₀r.symm)
    subst hcc
    have r1 := (U.valid z (hS z hz).1).below m hm
    have r2 := (U.valid m hmi).below b' hb
    have r3 := (U.valid b' hb'i).below m' hm'
    have r4 := (U.valid m' hm'i).below c hc
    have hzr := (hS z hz).2.1
    refine ⟨m, hm, by omega, ?_⟩
    have h1 : b' ∈ window U 1 m := ref_mem_window (k := 0) hb (by omega)
    have h2 : c ∈ window U 2 b' :=
      window_trans (ref_mem_window (k := 0) hm' (by omega)) (ref_mem_window (k := 0) hc (by omega))
    exact window_trans h1 h2
  let mz : BlockId → BlockId := fun z => if h : z ∈ S then (hreach z h).choose else z
  let yz : BlockId → BlockId := fun z => if h : z ∈ S then (hS z h).2.2.choose else A
  let dz : BlockId → ℕ := fun z => if h : z ∈ S then (hS z h).2.2.choose_spec.choose else K
  have hyz : ∀ z ∈ S, Anchored U K A (yz z) (dz z) ∧ window U 4 z ⊆ window U (dz z) (yz z) :=
    fun z hz => by
      simp only [yz, dz, dif_pos hz]
      exact (hS z hz).2.2.choose_spec.choose_spec
  have hmzs : ∀ z ∈ S, mz z ∈ (U.block z).refs ∧
      (U.block (mz z)).round + 1 = (U.block z).round ∧ x₀ ∈ window U 3 (mz z) := fun z hz => by
    simp only [mz, dif_pos hz]
    exact (hreach z hz).choose_spec
  have hcard : F.f + Cr.c + 1 ≤ (creatorsOf U.block S).card := by omega
  refine ⟨x₀, hx₀i, hx₀r, hx₀x ▸ hxC, Anchored.reached 3 S mz yz dz yz dz
    (fun z hz => (hyz z hz).1) (fun z hz => (hyz z hz).2 self_mem_window)
    (fun z hz _ => (hyz z hz).1) (fun z hz _ => ?_) hK
    (fun z hz => ⟨(hmzs z hz).1, (hmzs z hz).2.2, (hmzs z hz).2.1⟩) hcard⟩
  intro w hw
  exact (hyz z hz).2 (interior_trans (ref_mem_window (k := 0) (hmzs z hz).1 (hmzs z hz).2.1) hw)

/-! ## Descent -/

/-- A dense block at round `t` within one step of an anchor point bringing
`e` rounds or more. -/
def DenseAt (U : SRecord Validator BlockId Payload) (K : ℕ) (A : BlockId) (e t : ℕ) : Prop :=
  ∃ y d v, Anchored U K A y d ∧ e ≤ d ∧ v ∈ window U 1 y ∧ v ∈ U.ids ∧
    Dense (kQuorum Validator) U.block (U.block v) ∧ (U.block v).round = t

/-- Dense blocks near anchor points bringing `e` rounds recur at most `g`
rounds apart. -/
def Recurs (U : SRecord Validator BlockId Payload) (K : ℕ) (A : BlockId) (e g : ℕ) : Prop :=
  ∀ t, DenseAt U K A e t → g + 1 ≤ t → ∃ t', t - g ≤ t' ∧ t' < t ∧ DenseAt U K A e t'

/-- An anchor point, or the leader block it references, is dense. -/
theorem denseAt_of_anchored {K e d : ℕ} {A x : BlockId} (hx : x ∈ U.ids)
    (hxr : 2 ≤ (U.block x).round) (hxa : Anchored U K A x d) (hd : e ≤ d) :
    DenseAt U K A e (U.block x).round ∨ DenseAt U K A e ((U.block x).round - 1) := by
  rcases (U.valid x hx).shape (by omega) with hdx | ⟨-, -, ℓ, hℓ, hℓr, hℓL⟩
  · exact Or.inl ⟨x, d, x, hxa, hd, self_mem_window, hx, hdx, rfl⟩
  · have hℓ' : ℓ ∈ U.ids := U.complete x hx ℓ hℓ
    have hdl := (U.valid ℓ hℓ').leader (by omega)
      (by rw [show (U.block ℓ).round = (U.block x).round - 1 by omega]; exact hℓL)
    exact Or.inr ⟨x, d, ℓ, hxa, hd, ref_mem_window (k := 0) hℓ hℓr, hℓ', hdl, by omega⟩

/-- **Under the spreading condition, dense blocks recur within four rounds**:
below a dense block near an anchor point, a correct block three rounds down
is an anchor point, and it or its leader reference is dense. -/
theorem recurs_spread (hsp : Spread Validator) {K : ℕ} (hK : 4 ≤ K) {A : BlockId} :
    Recurs U K A (K - 1) 4 := by
  intro t h ht
  obtain ⟨y, d, v, hy, hd, hvy, hv, hdv, hvr⟩ := h
  obtain ⟨x, hx, hxr, -, hxa⟩ := exists_reached hsp (by omega) (K := K) (A := A)
    (S := below1 U.block (U.block v)) (ρ := t - 3)
    (fun z hz => by
      obtain ⟨hz₁, hzr⟩ := Finset.mem_filter.mp hz
      have hz2 : z ∈ window U 2 y := window_trans hvy (ref_mem_window (k := 0) hz₁ hzr)
      refine ⟨U.complete v hv z hz₁, by omega, ⟨y, d, hy, window_mono (by omega) _ hz2⟩,
        fun m hm hmr => ⟨y, d, hy, window_mono (by omega) _
          (window_trans hz2 (ref_mem_window (k := 0) hm hmr))⟩⟩) hdv
  rcases denseAt_of_anchored hx (by omega) hxa le_rfl with h' | h'
  · exact ⟨_, by omega, by omega, h'⟩
  · exact ⟨_, by omega, by omega, h'⟩

/-- **At any `n ≥ 3f + 2c + 1`, dense blocks recur within six rounds**: below a
dense block near an anchor point, the core five rounds down is an anchor
point, and it or its leader reference is dense. -/
theorem recurs_core {K : ℕ} (hK : 9 ≤ K) {A : BlockId} : Recurs U K A (K - 3) 6 := by
  intro t h ht
  obtain ⟨y, d, v, hy, hd, hvy, hv, hdv, hvr⟩ := h
  obtain ⟨x, hx, hxr, -, hxa⟩ := exists_core_reached (by omega) (K := K) (A := A)
    (S := below1 U.block (U.block v)) (ρ := t - 5)
    (fun z hz => by
      obtain ⟨hz₁, hzr⟩ := Finset.mem_filter.mp hz
      have hz2 : z ∈ window U 2 y := window_trans hvy (ref_mem_window (k := 0) hz₁ hzr)
      refine ⟨U.complete v hv z hz₁, by omega, y, d, hy, fun w hw => ?_⟩
      exact window_mono (by omega) _ (window_trans hz2 hw)) hdv
  rcases denseAt_of_anchored hx (by omega) hxa le_rfl with h' | h'
  · exact ⟨_, by omega, by omega, h'⟩
  · exact ⟨_, by omega, by omega, h'⟩

/-- **A dense block of the sub-DAG in every window of `g` rounds** from `u + 1`
up to a dense block of the sub-DAG. -/
theorem denseAt_window {K e g : ℕ} {A : BlockId} (hrec : Recurs U K A e g) (u : ℕ) :
    ∀ t, DenseAt U K A e t → u + 1 ≤ t → ∃ t', u + 1 ≤ t' ∧ t' ≤ u + g ∧ DenseAt U K A e t' := by
  intro t
  induction t using Nat.strong_induction_on with
  | _ t ih =>
    intro h ht
    by_cases hle : t ≤ u + g
    · exact ⟨t, ht, hle, h⟩
    · obtain ⟨t', ht'₁, ht'₂, h'⟩ := hrec t h (by omega)
      exact ih t' ht'₂ h' (by omega)

/-- **At the depth the sub-DAG needs, dense blocks recur** close enough for the
window an anchor point brings to reach a whole span of rounds. -/
theorem exists_recurs {K : ℕ} (hdeep : Deep Validator K) {A : BlockId} :
    ∃ e g, Recurs U K A e g ∧ g + 1 ≤ e ∧ e ≤ K := by
  rcases hdeep with ⟨hsp, hK⟩ | hK
  · exact ⟨K - 1, 4, recurs_spread hsp (by omega), by omega, by omega⟩
  · exact ⟨K - 3, 6, recurs_core (by omega), by omega, by omega⟩

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

omit [ClaimFormat BlockId Payload] in
/-- **The sub-DAG holds a quorum's overlap**: below a leader block above round
`u`, of blocks at round `u` from `cm` distinct authors, the sub-DAG holds those
of `q + cm − n − f` authors or more. -/
theorem linked_count {K : ℕ} (hdeep : Deep Validator K) (hch : Chains U)
    {A : BlockId} (hA : A ∈ U.ids) (hAl : (U.block A).creator ∈ Ld.leaders (U.block A).round)
    {u : ℕ} (hAr : u + 1 ≤ (U.block A).round) {Cl : Finset BlockId}
    (hCl : ∀ C ∈ Cl, C ∈ U.ids ∧ (U.block C).round = u) :
    ∃ X ⊆ Cl, (∀ C ∈ X, C ∈ Avail U K A) ∧
      kQuorum Validator + (creatorsOf U.block Cl).card ≤
        Fintype.card Validator + F.f + (creatorsOf U.block X).card := by
  classical
  have hdA := (U.valid A hA).leader (by omega) hAl
  obtain ⟨e, g, hrec, hge, heK⟩ := exists_recurs (U := U) hdeep (A := A)
  obtain ⟨t, ht₁, ht₂, y, d, v, hy, hd, hvy, hv, hdv, hvr⟩ :=
    denseAt_window hrec u _ ⟨A, K, A, Anchored.anchor, heK, self_mem_window,
      hA, hdA, rfl⟩ hAr
  set R := creatorsOf U.block (below1 U.block (U.block v))
  set W := (R ∩ creatorsOf U.block Cl) ∩ (Correct : Finset Validator)
  refine ⟨Cl.filter fun C => (U.block C).creator ∈ W, Finset.filter_subset _ _, fun C hC => ?_, ?_⟩
  · obtain ⟨hCCl, hCW⟩ := Finset.mem_filter.mp hC
    obtain ⟨hRCl, hCc⟩ := Finset.mem_inter.mp hCW
    obtain ⟨X, hX, hXa⟩ := mem_creatorsOf.mp (Finset.mem_inter.mp hRCl).1
    obtain ⟨hX₁, hXr⟩ := Finset.mem_filter.mp hX
    obtain ⟨hCi, hCr⟩ := hCl C hCCl
    have hXi : X ∈ U.ids := U.complete v hv X hX₁
    have hCX : C ∈ window U ((U.block X).round - (U.block C).round) X :=
      mem_window_of_chain hch _ hXi hCi (hXa ▸ hCc) hXa.symm (by omega) le_rfl
    have hX2 : X ∈ window U 2 y := window_trans hvy (ref_mem_window (k := 0) hX₁ hXr)
    exact ⟨y, d, hy, window_mono (by omega) _ (window_trans hX2 hCX)⟩
  · have hu : (R ∪ creatorsOf U.block Cl).card + (R ∩ creatorsOf U.block Cl).card =
        R.card + (creatorsOf U.block Cl).card := Finset.card_union_add_card_inter _ _
    have huniv : (R ∪ creatorsOf U.block Cl).card ≤ Fintype.card Validator := Finset.card_le_univ _
    have hsplit : (R ∩ creatorsOf U.block Cl).card ≤ W.card + F.byzantine.card :=
      card_le_card_inter_correct_add_byzantine _
    have hb := F.card_byzantine
    have hR : kQuorum Validator ≤ R.card := hdv
    have hWX : W ⊆ creatorsOf U.block (Cl.filter fun C => (U.block C).creator ∈ W) := by
      intro a ha
      obtain ⟨C, hC, rfl⟩ := mem_creatorsOf.mp (Finset.mem_inter.mp (Finset.mem_inter.mp ha).1).2
      exact mem_creatorsOf.mpr ⟨C, Finset.mem_filter.mpr ⟨hC, ha⟩, rfl⟩
    have := Finset.card_le_card hWX
    omega

/-- **A quorum's claim lies in the sub-DAG** below a leader block at round
`ρ + 3` or above. -/
theorem linked {K cm ρ : ℕ} (hdeep : Deep Validator K) (hch : Chains U) {A L : BlockId}
    (hA : A ∈ U.ids) (hAl : (U.block A).creator ∈ Ld.leaders (U.block A).round)
    (hAr : ρ + 3 ≤ (U.block A).round)
    (hcm : Fintype.card Validator + F.f < kQuorum Validator + cm)
    (hcl : cm ≤ (creatorsOf U.block (claimersOf U L (ρ + 2))).card) :
    ∃ C ∈ Avail U K A, (U.block C).round = ρ + 2 ∧ L ∈ claimsOf U C := by
  obtain ⟨X, hXs, hXa, hXn⟩ := linked_count hdeep hch hA hAl (u := ρ + 2) hAr
    (Cl := claimersOf U L (ρ + 2)) fun C hC => mem_blocksAt.mp (Finset.mem_filter.mp hC).1
  have hpos : 0 < (creatorsOf U.block X).card := by omega
  obtain ⟨C, hC⟩ : X.Nonempty := by
    rw [← Finset.card_pos]
    exact lt_of_lt_of_le hpos Finset.card_image_le
  obtain ⟨hCb, hCL⟩ := Finset.mem_filter.mp (hXs hC)
  exact ⟨C, hXa C hC, (mem_blocksAt.mp hCb).2, hCL⟩

omit [ClaimFormat BlockId Payload] in
/-- **Every block of the sub-DAG has a correct holder**: it lies in the window
to depth `K` of a block a correct author references. -/
theorem exists_holder {K : ℕ} {A : BlockId}
    (hA : ∃ z ∈ U.ids, (U.block z).creator ∈ (Correct : Finset Validator) ∧ A ∈ (U.block z).refs)
    {X : BlockId} (hX : X ∈ Avail U K A) :
    ∃ z ∈ U.ids, (U.block z).creator ∈ (Correct : Finset Validator) ∧
      ∃ m ∈ (U.block z).refs, X ∈ window U K m := by
  obtain ⟨y, d, hy, hXy⟩ := hX
  obtain ⟨z₀, hz₀, hz₀c, hAz₀⟩ := hA
  have hAi : A ∈ U.ids := U.complete z₀ hz₀ A hAz₀
  cases hy with
  | anchor => exact ⟨z₀, hz₀, hz₀c, A, hAz₀, hXy⟩
  | reached i S m y d y' d' hy hz hy' hmz hi hm hcard =>
    have : F.f < (creatorsOf U.block S).card := by omega
    have hsplit := card_le_card_inter_correct_add_byzantine (creatorsOf U.block S)
    have hb := F.card_byzantine
    obtain ⟨w, hw⟩ : (creatorsOf U.block S ∩ (Correct : Finset Validator)).Nonempty := by
      rw [← Finset.card_pos]; omega
    obtain ⟨hw₁, hw₂⟩ := Finset.mem_inter.mp hw
    obtain ⟨z, hzS, rfl⟩ := mem_creatorsOf.mp hw₁
    have hzi : z ∈ U.ids := window_subset_ids _ ((hy z hzS).mem hAi) (hz z hzS)
    have hXm := window_trans (hm z hzS).2.1 hXy
    rw [show i + (K - i) = K by omega] at hXm
    exact ⟨z, hzi, hw₂, m z, (hm z hzS).1, hXm⟩

omit [ClaimFormat BlockId Payload] in
/-- **The sub-DAG is held by correct nodes**, below a block a correct author
references. -/
theorem avail_correctHeld {K : ℕ} {A : BlockId}
    (hA : ∃ z ∈ U.ids, (U.block z).creator ∈ (Correct : Finset Validator) ∧ A ∈ (U.block z).refs)
    {X : BlockId} (hX : X ∈ Avail U K A) : X ∈ CorrectHeld U K := by
  obtain ⟨z, hz, hzc, m, hm, hXm⟩ := exists_holder hA hX
  exact ⟨z, hz, hzc, Or.inr ⟨m, hm, hXm⟩⟩

/-- **Claims of the sub-DAG are backed**: each lies in the window to depth `K`
of a block a correct author references, which that author checked. -/
theorem backed {K t : ℕ} (hck : Checks U K t) {A : BlockId}
    (hA : ∃ z ∈ U.ids, (U.block z).creator ∈ (Correct : Finset Validator) ∧ A ∈ (U.block z).refs)
    {X : BlockId} (hX : X ∈ Avail U K A) {L : BlockId} (hL : L ∈ claimsOf U X) :
    Certified U t L := by
  obtain ⟨z, hz, hzc, m, hm, hXm⟩ := exists_holder hA hX
  exact hck z hz hzc m hm X hXm L hL

end KPartialSparse

end LeanDag
