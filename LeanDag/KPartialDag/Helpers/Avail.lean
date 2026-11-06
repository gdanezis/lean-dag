import LeanDag.KPartialDag.Model.Rule
import LeanDag.Common.Counting
import Mathlib.Combinatorics.Enumerative.DoubleCounting
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Group.Action.Defs
import Mathlib.Tactic.Linarith
/-!
# The available sub-DAG — helpers

`docs/kpartial.md` §3. Histories to depth `K` and anchor points, and the
properties of the available sub-DAG: held by correct nodes
(`avail_correctHeld`), broad under the spreading condition (`broad`), the
two-step core (`exists_core`) and the anchor points it gives
(`exists_cover`), linked at a row of the scheme (`linked`), and exclusive of
a direct skip (`not_directSkip`).
-/

namespace LeanDag

namespace KPartialDag

variable {Validator : Type*} [Fintype Validator] [DecidableEq Validator] [F : Faults Validator]
variable [Cr : Crashes Validator]
variable {BlockId : Type*} [LinearOrder BlockId] {Payload : Type*}
variable {U : KRecord Validator BlockId Payload}

/-- A block's history to any depth lies in the record. -/
theorem historyUpto_subset_ids (n : ℕ) {b : BlockId} (hb : b ∈ U.ids) :
    historyUpto U n b ⊆ U.ids :=
  fun _ hi => mem_ids_of_reaches hb (reaches_of_mem_historyUpto hi)

/-- A reference lies in the history to depth one or more. -/
theorem ref_mem_historyUpto {K : ℕ} (hK : 1 ≤ K) {y x : BlockId} (hx : x ∈ (U.block y).refs) :
    x ∈ historyUpto U K y := by
  obtain ⟨k, rfl⟩ : ∃ k, K = k + 1 := ⟨K - 1, by omega⟩
  exact mem_historyUpto_succ.mpr (Or.inr ⟨x, hx, mem_historyUpto_self⟩)

/-- A reference of a reference lies in the history to depth two or more. -/
theorem ref_ref_mem_historyUpto {K : ℕ} (hK : 2 ≤ K) {y w x : BlockId}
    (hw : w ∈ (U.block y).refs) (hx : x ∈ (U.block w).refs) : x ∈ historyUpto U K y := by
  obtain ⟨k, rfl⟩ : ∃ k, K = k + 2 := ⟨K - 2, by omega⟩
  exact mem_historyUpto_succ.mpr
    (Or.inr ⟨w, hw, mem_historyUpto_succ.mpr (Or.inr ⟨x, hx, mem_historyUpto_self⟩)⟩)

/-- **An anchor point brings at most `K` rounds.** -/
theorem AnchoredBelow.le {K : ℕ} {A x : BlockId} {d : ℕ} (h : AnchoredBelow U K A x d) : d ≤ K := by
  cases h <;> omega

/-- **An anchor point is a block of the record**, when `A` is. -/
theorem AnchoredBelow.mem {K : ℕ} {A : BlockId} (hA : A ∈ U.ids) {x : BlockId} {d : ℕ}
    (h : AnchoredBelow U K A x d) : x ∈ U.ids := by
  induction h with
  | anchor => exact hA
  | @referenced x S y d hy hz href hcard ih =>
    obtain ⟨z, hzS⟩ := nonempty_of_creatorsOf_card_pos (by omega : 0 < (creatorsOf U.block S).card)
    exact U.complete z (historyUpto_subset_ids _ (ih z hzS) (hz z hzS)) _ (href z hzS)
  | @reached x S m y d y' d' hy hz hy' hmz hm href hcard hc ih ih' =>
    obtain ⟨z, hzS⟩ := nonempty_of_creatorsOf_card_pos (by omega : 0 < (creatorsOf U.block S).card)
    exact U.complete (m z) (historyUpto_subset_ids _ (ih' z hzS) (hmz z hzS)) _ (href z hzS)

/-- **An anchor point is in `A`'s history.** -/
theorem AnchoredBelow.reaches {K : ℕ} {A x : BlockId} {d : ℕ} (h : AnchoredBelow U K A x d) :
    Reaches U A x := by
  induction h with
  | anchor => exact Reaches.refl
  | @referenced x S y d hy hz href hcard ih =>
    obtain ⟨z, hzS⟩ := nonempty_of_creatorsOf_card_pos (by omega : 0 < (creatorsOf U.block S).card)
    exact (ih z hzS).trans
      ((reaches_of_mem_historyUpto (hz z hzS)).trans (Reaches.single (href z hzS)))
  | @reached x S m y d y' d' hy hz hy' hmz hm href hcard hc ih ih' =>
    obtain ⟨z, hzS⟩ := nonempty_of_creatorsOf_card_pos (by omega : 0 < (creatorsOf U.block S).card)
    exact (ih' z hzS).trans
      ((reaches_of_mem_historyUpto (hmz z hzS)).trans (Reaches.single (href z hzS)))

/-- **The available sub-DAG lies in the history of `A`**, a block of the
record. -/
theorem mem_history_of_avail {K : ℕ} {A z : BlockId} (hA : A ∈ U.ids) (hz : z ∈ Avail U K A) :
    z ∈ history U A := by
  obtain ⟨y, d, hy, hzy⟩ := hz
  exact (mem_history_iff hA).mpr (hy.reaches.trans (reaches_of_mem_historyUpto hzy))

/-- **Anchoring from the sub-DAG**: a block that blocks of the available
sub-DAG from `f + c + 1` distinct authors reference is an anchor point. -/
theorem AnchoredBelow.of_avail {K : ℕ} {A x : BlockId} {S : Finset BlockId}
    (hS : ∀ z ∈ S, z ∈ Avail U K A) (href : ∀ z ∈ S, x ∈ (U.block z).refs)
    (hcard : F.f + Cr.c + 1 ≤ (creatorsOf U.block S).card) : AnchoredBelow U K A x K := by
  classical
  refine AnchoredBelow.referenced S (fun z => if h : z ∈ Avail U K A then h.choose else A)
    (fun z => if h : z ∈ Avail U K A then h.choose_spec.choose else K)
    (fun z hz => ?_) (fun z hz => ?_) href hcard <;> simp only [dif_pos (hS z hz)]
  exacts [(hS z hz).choose_spec.choose_spec.1, (hS z hz).choose_spec.choose_spec.2]

/-- **Anchoring in two steps from the sub-DAG**: a block that blocks of the
available sub-DAG from `f + c + 1` distinct authors reach through blocks of it is
an anchor point. -/
theorem AnchoredBelow.of_avail_two {K : ℕ} {A x : BlockId} {S : Finset BlockId}
    {m : BlockId → BlockId} (hS : ∀ z ∈ S, z ∈ Avail U K A ∧ m z ∈ Avail U K A)
    (hm : ∀ z ∈ S, m z ∈ (U.block z).refs) (href : ∀ z ∈ S, x ∈ (U.block (m z)).refs)
    (hcard : F.f + Cr.c + 1 ≤ (creatorsOf U.block S).card) (hc : 1 ≤ Cr.c) :
    AnchoredBelow U K A x (K - 1) := by
  classical
  refine AnchoredBelow.reached S m (fun z => if h : z ∈ S then (hS z h).1.choose else A)
    (fun z => if h : z ∈ S then (hS z h).1.choose_spec.choose else K)
    (fun z => if h : z ∈ S then (hS z h).2.choose else A)
    (fun z => if h : z ∈ S then (hS z h).2.choose_spec.choose else K)
    (fun z hz => ?_) (fun z hz => ?_) (fun z hz => ?_) (fun z hz => ?_) hm href hcard hc <;>
    simp only [dif_pos hz]
  exacts [(hS z hz).1.choose_spec.choose_spec.1, (hS z hz).1.choose_spec.choose_spec.2,
    (hS z hz).2.choose_spec.choose_spec.1, (hS z hz).2.choose_spec.choose_spec.2]

/-- The arithmetic of the double count: `T ≥ n − f − c` authors each naming
`n − f − c − b` correct authors cannot spread over `n − b` correct authors
named `f + c` times each, under the spreading condition. -/
theorem count_arith {n f c b T Cc g : ℕ} (hn : 3 * f + 2 * c + 1 ≤ n) (hb : b ≤ f)
    (hC : Cc + b = n) (hT : n - f - c ≤ T) (hbig : T * (n - f - c - b) ≤ Cc * g)
    (hg : g ≤ f + c) (hspread : (n - f) * (f + c) < (n - f - c) * (n - f - c - f)) : False := by
  obtain ⟨P, hP⟩ : ∃ P, n = P + 2 * f + c := ⟨n - 2 * f - c, by omega⟩
  obtain ⟨e, he⟩ : ∃ e, f = b + e := ⟨f - b, by omega⟩
  have eR : n - f - c - f = P := by omega
  have eQ : n - f - c = P + f := by omega
  have eN : n - f = P + f + c := by omega
  have eB : n - f - c - b = P + e := by omega
  rw [eQ] at hT
  rw [eB] at hbig
  rw [eR, eQ, eN] at hspread
  have hCc : Cc = P + f + c + e := by omega
  subst hCc
  have k1 : (P + f) * (P + e) ≤ T * (P + e) := Nat.mul_le_mul_right _ hT
  have k2 : (P + f + c + e) * g ≤ (P + f + c + e) * (f + c) := Nat.mul_le_mul_left _ hg
  have k3 : e * (f + c) ≤ e * (P + f) := Nat.mul_le_mul_left _ (by omega)
  nlinarith

/-- The spreading condition holds at `n ≥ 5f + 3c + 1`. -/
theorem spread_arith {n f c : ℕ} (h : 5 * f + 3 * c + 1 ≤ n) :
    (n - f) * (f + c) < (n - f - c) * (n - f - c - f) := by
  obtain ⟨e, rfl⟩ : ∃ e, n = 5 * f + 3 * c + 1 + e := ⟨n - (5 * f + 3 * c + 1), by omega⟩
  have e1 : 5 * f + 3 * c + 1 + e - f - c - f = 3 * f + 2 * c + 1 + e := by omega
  have e2 : 5 * f + 3 * c + 1 + e - f - c = 4 * f + 2 * c + 1 + e := by omega
  have e3 : 5 * f + 3 * c + 1 + e - f = 4 * f + 3 * c + 1 + e := by omega
  rw [e1, e2, e3]
  nlinarith [Nat.zero_le (f * c), Nat.zero_le (f * f), Nat.zero_le (c * c), Nat.zero_le (e * f),
    Nat.zero_le (e * c), Nat.zero_le (e * e)]

/-- The spreading condition holds when no validator crashes for good. -/
theorem spread_arith_zero {n f c : ℕ} (hc : c = 0) (h : 3 * f + 1 ≤ n) :
    (n - f) * (f + c) < (n - f - c) * (n - f - c - f) := by
  subst hc
  obtain ⟨e, rfl⟩ : ∃ e, n = 3 * f + 1 + e := ⟨n - (3 * f + 1), by omega⟩
  have e1 : 3 * f + 1 + e - f - 0 - f = f + 1 + e := by omega
  have e2 : 3 * f + 1 + e - f - 0 = 2 * f + 1 + e := by omega
  have e3 : 3 * f + 1 + e - f = 2 * f + 1 + e := by omega
  rw [e1, e2, e3]
  nlinarith [Nat.zero_le (e * f), Nat.zero_le (f * f)]

/-- **A correct block referenced by `f + c + 1` authors of a quorum**, under the
spreading condition. -/
theorem exists_correct_referenced (hsp : Spread Validator) {S : Finset BlockId} {ρ : ℕ}
    (hS : ∀ z ∈ S, z ∈ U.ids ∧ (U.block z).round = ρ + 1)
    (hq : kQuorum Validator ≤ (creatorsOf U.block S).card) :
    ∃ x ∈ U.ids, (U.block x).round = ρ ∧ (U.block x).creator ∈ (Correct : Finset Validator) ∧
      F.f + Cr.c + 1 ≤ (creatorsOf U.block (S.filter fun z => x ∈ (U.block z).refs)).card := by
  classical
  obtain ⟨hcb, hbf, hnv⟩ := faults_arith (Validator := Validator)
  -- `c` names `w`: a block of `c` in `S` references a block of `w`
  let R : Validator → Validator → Prop := fun c w =>
    ∃ z ∈ S, (U.block z).creator = c ∧ w ∈ creatorsOf U.block (U.block z).refs
  let g : Validator → ℕ := fun w => ((creatorsOf U.block S).filter fun c => R c w).card
  have hper : ∀ c ∈ creatorsOf U.block S, kQuorum Validator - F.byzantine.card ≤
      ((Correct : Finset Validator).filter fun w => R c w).card := by
    intro c hc
    obtain ⟨z, hzS, hzc⟩ := mem_creatorsOf.mp hc
    obtain ⟨hz, hzr⟩ := hS z hzS
    have hquo : kQuorum Validator ≤ (creatorsOf U.block (U.block z).refs).card :=
      (U.valid z hz).quorum (by omega)
    have hsplit := card_le_card_inter_correct_add_byzantine (creatorsOf U.block (U.block z).refs)
    have hsub : creatorsOf U.block (U.block z).refs ∩ (Correct : Finset Validator) ⊆
        (Correct : Finset Validator).filter fun w => R c w := by
      intro w hw
      obtain ⟨hw₁, hw₂⟩ := Finset.mem_inter.mp hw
      exact Finset.mem_filter.mpr ⟨hw₂, z, hzS, hzc, hw₁⟩
    have := Finset.card_le_card hsub
    omega
  have hCne : (Correct : Finset Validator).Nonempty := by rw [← Finset.card_pos]; omega
  obtain ⟨w, hwC, hwmax⟩ := (Correct : Finset Validator).exists_max_image g hCne
  have hbig : (creatorsOf U.block S).card * (kQuorum Validator - F.byzantine.card) ≤
      (Correct : Finset Validator).card * g w := by
    have := Finset.card_nsmul_le_card_nsmul (r := fun c w => R c w) (s := creatorsOf U.block S)
      (t := (Correct : Finset Validator))
      (m := kQuorum Validator - F.byzantine.card) (n := g w)
      (fun c hc => by
        change _ ≤ ((Correct : Finset Validator).filter fun w => R c w).card
        exact hper c hc)
      (fun v hv => hwmax v hv)
    simpa [smul_eq_mul] using this
  have hgw : F.f + Cr.c + 1 ≤ g w := by
    by_contra hlt
    push Not at hlt
    exact count_arith Cr.card_validators hbf hcb hq hbig (by omega) hsp
  -- the block of `w` the counted authors reference
  obtain ⟨c₀, hc₀⟩ := Finset.card_pos.mp (show 0 < g w by omega)
  obtain ⟨-, z₀, hz₀S, -, hz₀w⟩ := Finset.mem_filter.mp hc₀
  obtain ⟨x, hxz, hxw⟩ := mem_creatorsOf.mp hz₀w
  obtain ⟨hz₀, hz₀r⟩ := hS z₀ hz₀S
  have hx : x ∈ U.ids := U.complete z₀ hz₀ x hxz
  have hxr : (U.block x).round = ρ := by
    have := (U.valid z₀ hz₀).predecessor x hxz; omega
  refine ⟨x, hx, hxr, hxw ▸ hwC, hgw.trans (Finset.card_le_card fun c hc => ?_)⟩
  obtain ⟨-, z, hzS, hzc, hzw⟩ := Finset.mem_filter.mp hc
  obtain ⟨x', hx'z, hx'w⟩ := mem_creatorsOf.mp hzw
  obtain ⟨hz, hzr⟩ := hS z hzS
  have hx' : x' ∈ U.ids := U.complete z hz x' hx'z
  have hx'r : (U.block x').round = ρ := by
    have := (U.valid z hz).predecessor x' hx'z; omega
  have : x' = x := U.eq_of_creator_eq hx' hx hwC hx'w hxw (by rw [hx'r, hxr])
  exact mem_creatorsOf.mpr ⟨z, Finset.mem_filter.mpr ⟨hzS, this ▸ hx'z⟩, hzc⟩

/-- **An anchored correct block below a quorum of the sub-DAG**: blocks of
the available sub-DAG at round `ρ + 1` from a quorum of distinct authors
anchor a correct author's round-`ρ` block. -/
theorem exists_anchored (hsp : Spread Validator) {K : ℕ} {A : BlockId} {S : Finset BlockId}
    {ρ : ℕ}
    (hS : ∀ z ∈ S, z ∈ U.ids ∧ (U.block z).round = ρ + 1 ∧ z ∈ Avail U K A)
    (hq : kQuorum Validator ≤ (creatorsOf U.block S).card) :
    ∃ x ∈ U.ids, (U.block x).round = ρ ∧ (U.block x).creator ∈ (Correct : Finset Validator) ∧
      AnchoredBelow U K A x K := by
  obtain ⟨x, hx, hxr, hxc, hcard⟩ :=
    exists_correct_referenced hsp (fun z hz => ⟨(hS z hz).1, (hS z hz).2.1⟩) hq
  exact ⟨x, hx, hxr, hxc, AnchoredBelow.of_avail
    (fun z hz => (hS z (Finset.mem_filter.mp hz).1).2.2) (fun z hz => (Finset.mem_filter.mp hz).2)
    hcard⟩

/-- **The available sub-DAG is broad**: below a block `A` of the record, at
`K ≥ 2`, each round `t + 2` or more below `A` holds an anchored block of a
correct author. The quorum it is anchored from is the references of `A`, of
a reference of `A`, or of the anchored block two rounds up. -/
theorem broad (hsp : Spread Validator) {K : ℕ} (hK : 2 ≤ K) {A : BlockId} (hA : A ∈ U.ids) :
    ∀ t, t + 2 ≤ (U.block A).round → ∃ x ∈ U.ids,
      (U.block x).round = (U.block A).round - (t + 2) ∧
        (U.block x).creator ∈ (Correct : Finset Validator) ∧ AnchoredBelow U K A x K := by
  intro t
  induction t using Nat.strong_induction_on with
  | _ t ih =>
    intro ht
    -- a block two rounds above, whose references lie in the sub-DAG
    obtain ⟨v, hv, hvr, hvrefs⟩ : ∃ v ∈ U.ids, (U.block v).round = (U.block A).round - t ∧
        ∀ z ∈ (U.block v).refs, z ∈ Avail U K A := by
      by_cases h₀ : t = 0
      · subst h₀
        exact ⟨A, hA, by omega, fun z hz =>
          ⟨A, _, AnchoredBelow.anchor, ref_mem_historyUpto (by omega) hz⟩⟩
      by_cases h₁ : t = 1
      · subst h₁
        obtain ⟨w, hw⟩ := nonempty_of_creatorsOf_card_pos (blk := U.block) (s := (U.block A).refs)
          (lt_of_lt_of_le (by have := Cr.card_validators; omega) ((U.valid A hA).quorum (by omega)))
        refine ⟨w, U.complete A hA w hw, ?_, fun z hz =>
          ⟨A, _, AnchoredBelow.anchor, ref_ref_mem_historyUpto hK hw hz⟩⟩
        have := (U.valid A hA).predecessor w hw
        omega
      obtain ⟨y, hy, hyr, -, hya⟩ := ih (t - 2) (by omega) (by omega)
      exact ⟨y, hy, by omega, fun z hz => ⟨y, K, hya, ref_mem_historyUpto (by omega) hz⟩⟩
    refine exists_anchored hsp (S := (U.block v).refs) (fun z hz => ⟨U.complete v hv z hz, ?_,
      hvrefs z hz⟩) ((U.valid v hv).quorum (by omega))
    have := (U.valid v hv).predecessor z hz
    omega

/-- A reference of a block of a history to depth `k` lies in the history to
depth `k + 1`. -/
theorem mem_historyUpto_succ_of_ref : ∀ {k : ℕ} {y z w : BlockId}, z ∈ historyUpto U k y →
    w ∈ (U.block z).refs → w ∈ historyUpto U (k + 1) y
  | 0, y, z, w, hz, hw => by
    rw [historyUpto_zero, Finset.mem_singleton] at hz
    subst hz
    exact mem_historyUpto_succ.mpr (Or.inr ⟨w, hw, mem_historyUpto_self⟩)
  | k + 1, y, z, w, hz, hw => by
    rcases mem_historyUpto_succ.mp hz with rfl | ⟨j, hj, hzj⟩
    · exact historyUpto_mono (m := 1) (by omega) z
        (mem_historyUpto_succ.mpr (Or.inr ⟨w, hw, mem_historyUpto_self⟩))
    · exact mem_historyUpto_succ.mpr (Or.inr ⟨j, hj, mem_historyUpto_succ_of_ref hzj hw⟩)

/-- **A block's history reaches every round below it**: a block of the record
has a block of each round below it in its history to the depth between. -/
theorem exists_descendant : ∀ (k : ℕ) {y : BlockId}, y ∈ U.ids → k ≤ (U.block y).round →
    ∃ v ∈ historyUpto U k y, (U.block v).round + k = (U.block y).round
  | 0, y, _, _ => ⟨y, mem_historyUpto_self, rfl⟩
  | k + 1, y, hy, hk => by
    obtain ⟨w, hw⟩ := nonempty_of_creatorsOf_card_pos (blk := U.block) (s := (U.block y).refs)
      (lt_of_lt_of_le (by have := Cr.card_validators; omega) ((U.valid y hy).quorum (by omega)))
    have hwr := (U.valid y hy).predecessor w hw
    obtain ⟨v, hv, hvr⟩ := exists_descendant k (y := w) (U.complete y hy w hw) (by omega)
    exact ⟨v, mem_historyUpto_succ.mpr (Or.inr ⟨w, hw, hv⟩), by omega⟩

/-- **The two-step core**: three rounds below a block of the record, some block
is reached from every reference of it through a block it references. -/
theorem exists_core {z : BlockId} (hz : z ∈ U.ids) (hzr : 3 ≤ (U.block z).round) :
    ∃ x ∈ U.ids, (U.block x).round + 3 = (U.block z).round ∧
      ∀ w ∈ (U.block z).refs, ∃ v ∈ (U.block w).refs, x ∈ (U.block v).refs := by
  classical
  obtain ⟨hcb, hbf, -⟩ := faults_arith (Validator := Validator)
  have hn := Cr.card_validators
  -- each block references `q − b` correct authors
  have hcorr : ∀ b ∈ U.ids, 1 ≤ (U.block b).round → kQuorum Validator - F.byzantine.card ≤
      ((U.block b).refs.filter fun j => (U.block j).creator ∈ (Correct : Finset Validator)).card :=
    fun b hb hbr => by
      have hquo : kQuorum Validator ≤ (creatorsOf U.block (U.block b).refs).card :=
        (U.valid b hb).quorum (by omega)
      have hsplit := card_le_card_inter_correct_add_byzantine (creatorsOf U.block (U.block b).refs)
      have : creatorsOf U.block (U.block b).refs ∩ (Correct : Finset Validator) ⊆ creatorsOf U.block
          ((U.block b).refs.filter fun j => (U.block j).creator ∈ (Correct : Finset Validator)) :=
        fun w hw => by
          obtain ⟨hw₁, hw₂⟩ := Finset.mem_inter.mp hw
          obtain ⟨j, hj, rfl⟩ := mem_creatorsOf.mp hw₁
          exact mem_creatorsOf.mpr ⟨j, Finset.mem_filter.mpr ⟨hj, hw₂⟩, rfl⟩
      have := (Finset.card_le_card this).trans Finset.card_image_le
      omega
  -- correct blocks of one round number at most `|C|`
  have hone : ∀ X : Finset BlockId, (∀ x ∈ X, x ∈ U.ids ∧
      (U.block x).creator ∈ (Correct : Finset Validator)) →
      (∀ x ∈ X, ∀ x' ∈ X, (U.block x).round = (U.block x').round) →
      X.card ≤ (Correct : Finset Validator).card := fun X hX hr =>
    Finset.card_le_card_of_injOn (fun x => (U.block x).creator) (fun x hx => (hX x hx).2)
      fun x hx x' hx' h => U.eq_of_creator_eq (hX x hx).1 (hX x' hx').1 (hX x hx).2 rfl h.symm
        (hr x hx x' hx')
  set Q := kQuorum Validator - F.byzantine.card
  -- the correct middle blocks, and the correct blocks they reference
  set B := ((U.block z).refs.biUnion fun w => (U.block w).refs).filter
    fun v => (U.block v).creator ∈ (Correct : Finset Validator)
  set X := (B.biUnion fun v => (U.block v).refs).filter
    fun x => (U.block x).creator ∈ (Correct : Finset Validator)
  have hB : ∀ v ∈ B, v ∈ U.ids ∧ (U.block v).round + 2 = (U.block z).round ∧
      (U.block v).creator ∈ (Correct : Finset Validator) := fun v hv => by
    obtain ⟨hv, hvc⟩ := Finset.mem_filter.mp hv
    obtain ⟨w, hw, hvw⟩ := Finset.mem_biUnion.mp hv
    have := U.round_of_mem_refs hz hw
    have := U.round_of_mem_refs (U.complete z hz w hw) hvw
    exact ⟨U.complete _ (U.complete z hz w hw) v hvw, by omega, hvc⟩
  have hX : ∀ x ∈ X, x ∈ U.ids ∧ (U.block x).round + 3 = (U.block z).round ∧
      (U.block x).creator ∈ (Correct : Finset Validator) := fun x hx => by
    obtain ⟨hx, hxc⟩ := Finset.mem_filter.mp hx
    obtain ⟨v, hv, hxv⟩ := Finset.mem_biUnion.mp hx
    have := (hB v hv).2.1
    have := U.round_of_mem_refs (hB v hv).1 hxv
    exact ⟨U.complete _ (hB v hv).1 x hxv, by omega, hxc⟩
  have hBc := hone B (fun v hv => ⟨(hB v hv).1, (hB v hv).2.2⟩) fun v hv v' hv' => by
    have := (hB v hv).2.1; have := (hB v' hv').2.1; omega
  have hXc := hone X (fun x hx => ⟨(hX x hx).1, (hX x hx).2.2⟩) fun x hx x' hx' => by
    have := (hX x hx).2.1; have := (hX x' hx').2.1; omega
  -- some `x` has more than `m − Q` correct middle referencers
  have hex : ∃ x ∈ X, B.card - Q < (B.filter fun v => x ∈ (U.block v).refs).card := by
    by_contra hno
    push Not at hno
    have hdc := Finset.card_nsmul_le_card_nsmul (r := fun v x => x ∈ (U.block v).refs)
      (s := B) (t := X) (m := Q) (n := B.card - Q)
      (fun v hv => by
        refine (hcorr v (hB v hv).1 (by have := (hB v hv).2.1; omega)).trans
          (Finset.card_le_card fun j hj => ?_)
        obtain ⟨hj, hjc⟩ := Finset.mem_filter.mp hj
        exact Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_biUnion.mpr ⟨v, hv, hj⟩,
          hjc⟩, hj⟩)
      (fun x hx => hno x hx)
    simp only [smul_eq_mul] at hdc
    have hQ : F.f + Cr.c + 1 ≤ Q := by omega
    have hm : B.card * Q ≤ (Correct : Finset Validator).card * (B.card - Q) :=
      hdc.trans (Nat.mul_le_mul_right _ hXc)
    rcases Nat.lt_or_ge B.card Q with hlt | hge
    · have : B.card - Q = 0 := by omega
      rw [this, Nat.mul_zero] at hm
      have hw : ∃ w, w ∈ (U.block z).refs :=
        nonempty_of_creatorsOf_card_pos (blk := U.block) (s := (U.block z).refs)
          (lt_of_lt_of_le (by omega) ((U.valid z hz).quorum (by omega)))
      obtain ⟨w, hw⟩ := hw
      obtain ⟨v, hv⟩ : ∃ v, v ∈ (U.block w).refs.filter
          fun j => (U.block j).creator ∈ (Correct : Finset Validator) :=
        Finset.card_pos.mp (lt_of_lt_of_le (by omega)
          (hcorr w (U.complete z hz w hw) (by have := U.round_of_mem_refs hz hw; omega)))
      obtain ⟨hvw, hvc⟩ := Finset.mem_filter.mp hv
      have : 0 < B.card := Finset.card_pos.mpr
        ⟨v, Finset.mem_filter.mpr ⟨Finset.mem_biUnion.mpr ⟨w, hw, hvw⟩, hvc⟩⟩
      have := Nat.mul_le_mul_left B.card (show 1 ≤ Q by omega)
      omega
    · obtain ⟨k, hk⟩ : ∃ k, B.card = Q + k := ⟨B.card - Q, by omega⟩
      rw [hk, Nat.add_sub_cancel_left] at hm
      have hcc : (Correct : Finset Validator).card = Q + (F.f + Cr.c) := by omega
      rw [hcc] at hm
      have : (Q + k) * Q ≤ (Q + k) * (F.f + Cr.c) := by nlinarith
      have := Nat.le_of_mul_le_mul_left this (by omega)
      omega
  obtain ⟨x, hx, hxd⟩ := hex
  refine ⟨x, (hX x hx).1, (hX x hx).2.1, fun w hw => ?_⟩
  -- `w` misses at most `m − Q` correct middle blocks
  have hwB : ((U.block w).refs.filter fun j => (U.block j).creator ∈ (Correct : Finset Validator))
      ⊆ B := fun j hj => by
    obtain ⟨hj, hjc⟩ := Finset.mem_filter.mp hj
    exact Finset.mem_filter.mpr ⟨Finset.mem_biUnion.mpr ⟨w, hw, hj⟩, hjc⟩
  have hwQ := hcorr w (U.complete z hz w hw) (by have := U.round_of_mem_refs hz hw; omega)
  obtain ⟨v, hv⟩ : (((U.block w).refs.filter fun j =>
      (U.block j).creator ∈ (Correct : Finset Validator)) ∩
      (B.filter fun v : BlockId => x ∈ (U.block v).refs)).Nonempty := by
    rw [← Finset.card_pos]
    have hu := Finset.card_union_add_card_inter ((U.block w).refs.filter
      fun j => (U.block j).creator ∈ (Correct : Finset Validator)) (B.filter
        fun v : BlockId => x ∈ (U.block v).refs)
    have := Finset.card_le_card (Finset.union_subset hwB
      (Finset.filter_subset (fun v : BlockId => x ∈ (U.block v).refs) B))
    omega
  obtain ⟨hv₁, hv₂⟩ := Finset.mem_inter.mp hv
  exact ⟨v, (Finset.mem_filter.mp hv₁).1, (Finset.mem_filter.mp hv₂).2⟩

/-- **The core is an anchor point**, when validators may crash for good: the
core of a block at depth `e − 2` or less in the history an anchor point
brings is reached in two steps by the block's references. -/
theorem core_anchored (hc : 1 ≤ Cr.c) {K : ℕ} {A y z : BlockId} {e : ℕ} (hA : A ∈ U.ids)
    (hy : AnchoredBelow U K A y e) (hzy : z ∈ historyUpto U (e - 2) y) (he : 2 ≤ e)
    (hzr : 3 ≤ (U.block z).round) :
    ∃ x, AnchoredBelow U K A x (K - 1) ∧ (U.block x).round + 3 = (U.block z).round := by
  classical
  have hz := historyUpto_subset_ids _ (hy.mem hA) hzy
  obtain ⟨x, -, hxr, hreach⟩ := exists_core hz hzr
  choose! mf hmf using hreach
  obtain ⟨k, rfl⟩ : ∃ k, e = k + 2 := ⟨e - 2, by omega⟩
  have hzk : z ∈ historyUpto U k y := by simpa using hzy
  have hw : ∀ w ∈ (U.block z).refs, w ∈ historyUpto U (k + 2) y := fun w hw =>
    historyUpto_mono (m := k + 1) (by omega) y (mem_historyUpto_succ_of_ref hzk hw)
  have hm : ∀ w ∈ (U.block z).refs, mf w ∈ historyUpto U (k + 2) y := fun w hw =>
    mem_historyUpto_succ_of_ref (mem_historyUpto_succ_of_ref hzk hw) (hmf w hw).1
  refine ⟨x, AnchoredBelow.reached (U.block z).refs mf (fun _ => y) (fun _ => k + 2)
    (fun _ => y) (fun _ => k + 2) (fun _ _ => hy) hw (fun _ _ => hy) hm
    (fun w hw => (hmf w hw).1) (fun w hw => (hmf w hw).2) ?_ hc, hxr⟩
  exact le_trans (by have := Cr.card_validators; omega) ((U.valid z hz).quorum (by omega))

/-- **Some anchor point covers each round**, at `K ≥ 4`, when validators may
crash for good: its history reaches two rounds below a block of the round. -/
theorem exists_cover (hc : 1 ≤ Cr.c) {K : ℕ} (hK : 4 ≤ K) {A : BlockId} (hA : A ∈ U.ids)
    {t : ℕ} (ht1 : 1 ≤ t) (ht : t ≤ (U.block A).round) :
    ∃ y e, AnchoredBelow U K A y e ∧ 3 ≤ e ∧ t ≤ (U.block y).round ∧
      (U.block y).round + 2 ≤ t + e := by
  -- from a pair of anchor points one round apart
  have pair : ∀ g y y' e e', AnchoredBelow U K A y e → AnchoredBelow U K A y' e' → 3 ≤ e →
      3 ≤ e' → (U.block y').round + 1 = (U.block y).round → (U.block y).round = t + g →
      ∃ y e, AnchoredBelow U K A y e ∧ 3 ≤ e ∧ t ≤ (U.block y).round ∧
        (U.block y).round + 2 ≤ t + e := by
    intro g
    induction g using Nat.strong_induction_on with
    | _ g ih =>
      intro y y' e e' hy hy' he he' hyy hyr
      by_cases hg : g ≤ 1
      · exact ⟨y, e, hy, he, by omega, by omega⟩
      by_cases hg2 : g = 2
      · exact ⟨y', e', hy', he', by omega, by omega⟩
      obtain ⟨x, hx, hxr⟩ := core_anchored hc hA hy (mem_historyUpto_self) (by omega)
        (by omega)
      obtain ⟨x', hx', hx'r⟩ := core_anchored hc hA hy' (mem_historyUpto_self) (by omega)
        (by omega)
      exact ih (g - 3) (by omega) x x' (K - 1) (K - 1) hx hx' (by omega) (by omega) (by omega)
        (by omega)
  by_cases hnear : (U.block A).round + 2 ≤ t + K
  · exact ⟨A, K, AnchoredBelow.anchor, by omega, ht, hnear⟩
  obtain ⟨w, hw⟩ := nonempty_of_creatorsOf_card_pos (blk := U.block) (s := (U.block A).refs)
    (lt_of_lt_of_le (by have := Cr.card_validators; omega) ((U.valid A hA).quorum (by omega)))
  have hwr := (U.valid A hA).predecessor w hw
  obtain ⟨x, hx, hxr⟩ := core_anchored hc hA (AnchoredBelow.anchor (U := U) (K := K) (A := A))
    (mem_historyUpto_self) (by omega) (by omega)
  obtain ⟨x', hx', hx'r⟩ := core_anchored hc hA (AnchoredBelow.anchor (U := U) (K := K) (A := A))
    (z := w) (historyUpto_mono (by omega) A (ref_mem_historyUpto (K := 1) le_rfl hw)) (by omega)
    (by omega)
  exact pair ((U.block x).round - t) x x' (K - 1) (K - 1) hx hx' (by omega) (by omega) (by omega)
    (by omega)

omit [LinearOrder BlockId] in
/-- A row's wave is two rounds or more. -/
theorem two_le_waveLength {p : Scheme.Params} (hrow : Row Validator p) : 2 ≤ p.waveLength := by
  rcases hrow with ⟨-, h, -⟩ | ⟨-, h, -⟩ <;> omega

omit [LinearOrder BlockId] in
/-- A row's depth is three rounds or more. -/
theorem three_le_of_kDepth {p : Scheme.Params} {K : ℕ} (hK : kDepth Validator p ≤ K) :
    3 ≤ K := by
  unfold kDepth at hK; split at hK <;> omega

omit [LinearOrder BlockId] in
/-- **The wave of a row**: two when a vote is its own certificate, three
otherwise. -/
theorem row_wave {p : Scheme.Params} (hrow : Row Validator p) :
    (p.voteIsCert = true → p.waveLength = 2) ∧ (p.voteIsCert = false → p.waveLength = 3) := by
  rcases hrow with ⟨hv, hw, -⟩ | ⟨hv, hw, -⟩
  · exact ⟨fun _ => hw, fun h => absurd (hv.symm.trans h) (by simp)⟩
  · exact ⟨fun h => absurd (hv.symm.trans h) (by simp), fun _ => hw⟩

/-- **A certificate is a block of the record that certifies.** -/
theorem mem_certsFor_iff {p : Scheme.Params} {L C : BlockId} {r : ℕ} :
    C ∈ certsFor p U L r ↔ C ∈ U.ids ∧ Certifies p U C L r := by
  unfold certsFor Certifies
  cases p.voteIsCert <;> simp [mem_votesFor, mem_certificatesAt]

/-- A certificate lies in the record at the decision round. -/
theorem mem_certsFor {p : Scheme.Params} {L C : BlockId} {r : ℕ} (hC : C ∈ certsFor p U L r) :
    C ∈ U.ids ∧ (U.block C).round = r + (p.waveLength - 1) := by
  unfold certsFor at hC
  split at hC
  · exact ⟨(mem_votesFor.mp hC).1, (mem_votesFor.mp hC).2.1⟩
  · exact ⟨(mem_certificatesAt.mp hC).1, (mem_certificatesAt.mp hC).2.1⟩

/-- **A block meets a set of the round below**: it references the blocks of
`|authors X| + q − n − f` authors of `X` or more, `q` the authors it
references. -/
theorem card_refs_filter_ge {v : BlockId} (hv : v ∈ U.ids) {X : Finset BlockId}
    (hX : ∀ x ∈ X, x ∈ U.ids ∧ (U.block x).round + 1 = (U.block v).round) :
    (creatorsOf U.block X).card + (creatorsOf U.block (U.block v).refs).card ≤
      Fintype.card Validator + F.f +
        (creatorsOf U.block (X.filter fun x => x ∈ (U.block v).refs)).card := by
  set R := creatorsOf U.block (U.block v).refs
  set CX := creatorsOf U.block X
  have hsub : (R ∩ CX) ∩ (Correct : Finset Validator) ⊆
      creatorsOf U.block (X.filter fun x => x ∈ (U.block v).refs) := by
    intro w hw
    obtain ⟨hwRC, hwC⟩ := Finset.mem_inter.mp hw
    obtain ⟨hwR, hwX⟩ := Finset.mem_inter.mp hwRC
    obtain ⟨b, hb, hbc⟩ := mem_creatorsOf.mp hwR
    obtain ⟨x, hx, hxc⟩ := mem_creatorsOf.mp hwX
    have hbr := (U.valid v hv).predecessor b hb
    obtain ⟨hxU, hxr⟩ := hX x hx
    obtain rfl : b = x := U.eq_of_creator_eq (U.complete v hv b hb) hxU hwC hbc hxc (by omega)
    exact mem_creatorsOf.mpr ⟨b, Finset.mem_filter.mpr ⟨hx, hb⟩, hbc⟩
  have h1 := Finset.card_union_add_card_inter R CX
  have h2 := Finset.card_le_univ (R ∪ CX)
  have h3 := Finset.card_inter_add_card_sdiff (R ∩ CX) (Correct : Finset Validator)
  have h4 : ((R ∩ CX) \ (Correct : Finset Validator)).card ≤
      (Correct : Finset Validator)ᶜ.card :=
    Finset.card_le_card fun w hw => Finset.mem_compl.mpr (Finset.mem_sdiff.mp hw).2
  have h5 := Finset.card_le_card hsub
  have h6 := card_compl_correct_le (Validator := Validator)
  omega

/-- **A directly committed block is linked through the sub-DAG**, at a row and
its depth, below an anchor one round or more above the decision round: a
block of the round above the decision round whose references and theirs lie
in the sub-DAG references `linkSize` authors of the certificates. -/
theorem linked {p : Scheme.Params} (hrow : Row Validator p) {K : ℕ}
    (hK : kDepth Validator p ≤ K) {A L : BlockId} {r : ℕ} (hA : A ∈ U.ids)
    (hr : r + p.waveLength ≤ (U.block A).round) (hd : DirectCommit p U L r) :
    AvailLinked p U K A L r := by
  have hw := two_le_waveLength hrow
  have hK3 : 3 ≤ K := three_le_of_kDepth hK
  obtain ⟨v, hv, hvr, hvrefs⟩ : ∃ v ∈ U.ids, (U.block v).round = r + p.waveLength ∧
      ∀ z ∈ (U.block v).refs, z ∈ Avail U K A ∧ ∀ j ∈ (U.block z).refs, j ∈ Avail U K A := by
    by_cases hcase : p.voteIsCert = false ∧ 1 ≤ Cr.c
    · have hK4 : 4 ≤ K := by unfold kDepth at hK; rw [if_pos hcase] at hK; exact hK
      obtain ⟨y, e, hy, he, hty, hye⟩ :=
        exists_cover hcase.2 hK4 hA (t := r + p.waveLength) (by omega) hr
      obtain ⟨v, hvy, hvr⟩ := exists_descendant ((U.block y).round - (r + p.waveLength))
        (hy.mem hA) (by omega)
      have hv2 : v ∈ historyUpto U (e - 2) y := historyUpto_mono (by omega) y hvy
      obtain ⟨k, rfl⟩ : ∃ k, e = k + 2 := ⟨e - 2, by omega⟩
      have hvk : v ∈ historyUpto U k y := by simpa using hv2
      refine ⟨v, historyUpto_subset_ids _ (hy.mem hA) hvy, by omega, fun z hz =>
        ⟨⟨y, k + 2, hy, historyUpto_mono (m := k + 1) (by omega) y
          (mem_historyUpto_succ_of_ref hvk hz)⟩, fun j hj => ⟨y, k + 2, hy,
            mem_historyUpto_succ_of_ref (mem_historyUpto_succ_of_ref hvk hz) hj⟩⟩⟩
    have hsp : Spread Validator := by
      rcases hrow with ⟨-, -, -, h5, -⟩ | ⟨hv, -⟩
      · exact spread_arith h5
      · exact spread_arith_zero (by have := not_and.mp hcase hv; omega) F.card_validators
    by_cases h₃ : (U.block A).round = r + p.waveLength
    · exact ⟨A, hA, h₃, fun z hz =>
        ⟨⟨A, _, AnchoredBelow.anchor, ref_mem_historyUpto (K := K) (by omega) hz⟩,
          fun j hj => ⟨A, _, AnchoredBelow.anchor,
            ref_ref_mem_historyUpto (K := K) (by omega) hz hj⟩⟩⟩
    by_cases h₄ : (U.block A).round = r + p.waveLength + 1
    · obtain ⟨w, hw⟩ := nonempty_of_creatorsOf_card_pos (blk := U.block) (s := (U.block A).refs)
        (lt_of_lt_of_le (by have := Cr.card_validators; omega) ((U.valid A hA).quorum (by omega)))
      obtain ⟨k, rfl⟩ : ∃ k, K = k + 1 := ⟨K - 1, by omega⟩
      refine ⟨w, U.complete A hA w hw, ?_, fun z hz =>
        ⟨⟨A, _, AnchoredBelow.anchor, ref_ref_mem_historyUpto (by omega) hw hz⟩,
          fun j hj => ⟨A, _, AnchoredBelow.anchor, mem_historyUpto_succ.mpr
            (Or.inr ⟨w, hw, ref_ref_mem_historyUpto (by omega) hz hj⟩)⟩⟩⟩
      have := (U.valid A hA).predecessor w hw
      omega
    obtain ⟨y, hy, hyr, -, hya⟩ :=
      broad hsp (K := K) (by omega) hA ((U.block A).round - (r + p.waveLength + 2)) (by omega)
    exact ⟨y, hy, by omega, fun z hz => ⟨⟨y, K, hya, ref_mem_historyUpto (K := K) (by omega) hz⟩,
      fun j hj => ⟨y, K, hya, ref_ref_mem_historyUpto (K := K) (by omega) hz hj⟩⟩⟩
  -- the certificates `v` references
  refine ⟨(certsFor p U L r).filter fun C => C ∈ (U.block v).refs, Finset.filter_subset _ _,
    fun C hC => ?_, ?_⟩
  · have hCv := (Finset.mem_filter.mp hC).2
    exact ⟨(hvrefs C hCv).1, fun _ => (hvrefs C hCv).2⟩
  · have hq : kQuorum Validator ≤ (creatorsOf U.block (U.block v).refs).card :=
      (U.valid v hv).quorum (by omega)
    have hcount := card_refs_filter_ge hv (X := certsFor p U L r)
      fun x hx => ⟨(mem_certsFor hx).1, by have := (mem_certsFor hx).2; omega⟩
    unfold DirectCommit at hd
    rcases hrow with ⟨-, -, -, -, -, -, hc⟩ | ⟨-, -, hl, -, -, hc⟩ <;> omega

/-- **Votes and blames exclude each other**, when votes are certificates at a
wave of two: authors of votes for a block and of blames of it number at most
`n + f`. -/
theorem card_votes_add_blames_le {p : Scheme.Params} (hv : p.voteIsCert = true)
    (hw : p.waveLength = 2) {L : BlockId} {r : ℕ} {X : Finset BlockId}
    (hX : X ⊆ certsFor p U L r) :
    (creatorsOf U.block X).card + (blames U L (r + 1)).card ≤ Fintype.card Validator + F.f := by
  have hsub : creatorsOf U.block X ⊆ supporters U L (r + 1) := by
    unfold certsFor at hX
    rw [if_pos hv, hw] at hX
    exact Finset.image_subset_image hX
  have := Finset.card_le_card hsub
  have := card_supporters_add_card_blames_le U.noEquivOn_honest card_compl_correct_le
    (L := L) (n := r + 1)
  omega

/-- **A certificate and blames exclude each other**, when votes are certified
apart at a wave of three: its voters and the blamers number at most
`n + f`. -/
theorem card_cert_add_blames_le {p : Scheme.Params} (hv : p.voteIsCert = false)
    (hw : p.waveLength = 3) {L C : BlockId} {r : ℕ} (hC : C ∈ certsFor p U L r) :
    p.certThreshold + (blames U L (r + 1)).card ≤ Fintype.card Validator + F.f := by
  unfold certsFor at hC
  rw [if_neg (by simp [hv]), hw] at hC
  obtain ⟨hCi, hCr, hcv⟩ := mem_certificatesAt.mp hC
  unfold CarriesVotes at hcv
  have := Finset.card_le_card (creatorsOf_carriedVotes_subset_supporters (L := L) hCi hCr)
  have := card_supporters_add_card_blames_le U.noEquivOn_honest card_compl_correct_le
    (L := L) (n := r + 1)
  omega

/-- **A link excludes a direct skip**, at a row: the link's certificates, or
the votes of one, and the blames come from two large sets of authors. -/
theorem not_directSkip {p : Scheme.Params} (hrow : Row Validator p) {K : ℕ} {A L : BlockId}
    {r : ℕ} (hl : AvailLinked p U K A L r) : ¬ DirectSkip p U L r := by
  intro hs
  unfold DirectSkip at hs
  obtain ⟨X, hX, -, hXn⟩ := hl
  rcases hrow with ⟨hv, hw, -, -, ha, -, -⟩ | ⟨hv, hw, hl1, -, hb, -⟩
  · have := card_votes_add_blames_le hv hw hX
    omega
  · obtain ⟨C, hC⟩ := nonempty_of_creatorsOf_card_pos (blk := U.block) (s := X) (by omega)
    have := card_cert_add_blames_le hv hw (hX hC)
    omega

/-- **An anchor point is `A`, or referenced by a correct author's block of the
sub-DAG, or reached in two steps by one**, with the depth it brings. -/
theorem AnchoredBelow.eq_or_referenced {K : ℕ} {A y : BlockId} {d : ℕ}
    (h : AnchoredBelow U K A y d) :
    (y = A ∧ d = K) ∨ (∃ w ∈ Avail U K A, (U.block w).creator ∈ (Correct : Finset Validator) ∧
      y ∈ (U.block w).refs ∧ d = K) ∨
    ∃ w ∈ Avail U K A, (U.block w).creator ∈ (Correct : Finset Validator) ∧
      ∃ v ∈ (U.block w).refs, y ∈ (U.block v).refs ∧ d = K - 1 ∧ 1 ≤ Cr.c := by
  cases h with
  | anchor => exact Or.inl ⟨rfl, rfl⟩
  | referenced S yf df hyf hzf href hcard =>
    obtain ⟨c, hc, hcC⟩ := exists_correct_of_card (le_trans (by omega) hcard)
    obtain ⟨w, hw, rfl⟩ := mem_creatorsOf.mp hc
    exact Or.inr (Or.inl ⟨w, ⟨yf w, df w, hyf w hw, hzf w hw⟩, hcC, href w hw, rfl⟩)
  | reached S m yf df yf' df' hyf hzf hyf' hmz hm href hcard hgate =>
    obtain ⟨c, hc, hcC⟩ := exists_correct_of_card (le_trans (by omega) hcard)
    obtain ⟨w, hw, rfl⟩ := mem_creatorsOf.mp hc
    exact Or.inr (Or.inr ⟨w, ⟨yf w, df w, hyf w hw, hzf w hw⟩, hcC, m w, hm w hw, href w hw, rfl,
      hgate⟩)

/-- One round less of a reference's history lies in the history of its
referencer. -/
theorem historyUpto_pred_subset {K : ℕ} (hK : 1 ≤ K) {v y : BlockId}
    (h : y ∈ (U.block v).refs) : historyUpto U (K - 1) y ⊆ historyUpto U K v := by
  obtain ⟨k, rfl⟩ : ∃ k, K = k + 1 := ⟨K - 1, by omega⟩
  intro z hz
  exact mem_historyUpto_succ.mpr (Or.inr ⟨y, h, by simpa using hz⟩)

/-- The available sub-DAG below a block of the record lies in the record. -/
theorem avail_subset_ids {K : ℕ} {A z : BlockId} (hA : A ∈ U.ids) (hz : z ∈ Avail U K A) :
    z ∈ U.ids := by
  obtain ⟨y, d, hy, hzy⟩ := hz
  exact historyUpto_subset_ids d (hy.mem hA) hzy

/-- **The available sub-DAG below a voted block is held by correct nodes**, at
`K ≥ 1`: it lies in the history to depth `K` of a block that a correct voter,
or a correct author's block of the sub-DAG, references. -/
theorem avail_correctHeld {K : ℕ} (hK : 1 ≤ K) {A z : BlockId} (hA : A ∈ U.ids) (hV : Voted U A)
    (hz : z ∈ Avail U K A) : z ∈ CorrectHeld U K := by
  obtain ⟨y, d, hy, hzy⟩ := hz
  rcases hy.eq_or_referenced with ⟨rfl, rfl⟩ | ⟨w, hw, hwc, hyw, rfl⟩ |
      ⟨w, hw, hwc, v, hv, hyv, rfl, -⟩
  · obtain ⟨u, hu, hucorr⟩ := exists_correct_of_card (le_trans (by omega) hV)
    obtain ⟨b, hb, hbc⟩ := mem_creatorsOf.mp hu
    obtain ⟨hbi, -, hbA⟩ := mem_votesFor.mp hb
    exact ⟨b, hbi, by rw [hbc]; exact hucorr, Or.inr ⟨y, hbA, hzy⟩⟩
  · exact ⟨w, avail_subset_ids hA hw, hwc, Or.inr ⟨y, hyw, hzy⟩⟩
  · exact ⟨w, avail_subset_ids hA hw, hwc, Or.inr ⟨v, hv, historyUpto_pred_subset hK hyv hzy⟩⟩

end KPartialDag

end LeanDag
