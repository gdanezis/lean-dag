import LeanDag.KPartialDag.Model.Rule
import LeanDag.Common.Counting
import Mathlib.Combinatorics.Enumerative.DoubleCounting
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Group.Action.Defs
import Mathlib.Tactic.Linarith
/-!
# The available sub-DAG — helpers

`docs/kpartial.md` §3. Histories to depth `K` and anchored blocks, and the
properties of the available sub-DAG: held by correct nodes
(`avail_correctHeld`), broad (`broad`), linked at a row of the scheme
(`linked`), and exclusive of a direct skip (`not_directSkip`).
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
sub-DAG from `f + 1` distinct authors reference is an anchor point. -/
theorem AnchoredBelow.of_avail {K : ℕ} {A x : BlockId} {S : Finset BlockId}
    (hS : ∀ z ∈ S, z ∈ Avail U K A) (href : ∀ z ∈ S, x ∈ (U.block z).refs)
    (hcard : F.f + 1 ≤ (creatorsOf U.block S).card) : AnchoredBelow U K A x K := by
  classical
  refine AnchoredBelow.referenced S (fun z => if h : z ∈ Avail U K A then h.choose else A)
    (fun z => if h : z ∈ Avail U K A then h.choose_spec.choose else K)
    (fun z hz => ?_) (fun z hz => ?_) href hcard <;> simp only [dif_pos (hS z hz)]
  exacts [(hS z hz).choose_spec.choose_spec.1, (hS z hz).choose_spec.choose_spec.2]

/-- **Anchoring in two steps from the sub-DAG**: a block that blocks of the
available sub-DAG from `f + 1` distinct authors reach through blocks of it is
an anchor point. -/
theorem AnchoredBelow.of_avail_two {K : ℕ} {A x : BlockId} {S : Finset BlockId}
    {m : BlockId → BlockId} (hS : ∀ z ∈ S, z ∈ Avail U K A ∧ m z ∈ Avail U K A)
    (hm : ∀ z ∈ S, m z ∈ (U.block z).refs) (href : ∀ z ∈ S, x ∈ (U.block (m z)).refs)
    (hcard : F.f + 1 ≤ (creatorsOf U.block S).card) (hc : 1 ≤ Cr.c) :
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

/-- The arithmetic of the double count: `T` authors at the round above, each
naming `n − f − b` correct authors, cannot spread over the `n − b` correct
authors with each named `f` times or fewer. -/
theorem count_arith {n f b T Cc g : ℕ} (hn : 3 * f + 1 ≤ n) (hb : b ≤ f) (hC : Cc + b = n)
    (hT : n ≤ T + f) (hbig : T * (n - f - b) ≤ Cc * g) (hg : g ≤ f) : False := by
  obtain ⟨m, hm⟩ : ∃ m, m + f + b = n := ⟨n - f - b, by omega⟩
  have hm' : n - f - b = m := by omega
  rw [hm'] at hbig
  have h₁ : (m + b) * m ≤ T * m := Nat.mul_le_mul_right m (by omega)
  have h₂ : Cc * g ≤ (m + f) * f := Nat.mul_le_mul (by omega) hg
  have h₃ : f + 1 ≤ m := by omega
  have h₄ : 2 * f + 1 ≤ m + b := by omega
  have h₅ : m * (2 * f + 1) ≤ m * (m + b) := Nat.mul_le_mul_left m h₄
  nlinarith [Nat.mul_le_mul h₃ h₃]

/-- **A correct block referenced by `f + 1` authors of a quorum.** Blocks of
a quorum of distinct authors at round `ρ + 1` reference some correct
author's round-`ρ` block from `f + 1` of those authors. -/
theorem exists_correct_referenced {S : Finset BlockId} {ρ : ℕ}
    (hS : ∀ z ∈ S, z ∈ U.ids ∧ (U.block z).round = ρ + 1)
    (hq : quorumCard Validator ≤ (creatorsOf U.block S).card) :
    ∃ x ∈ U.ids, (U.block x).round = ρ ∧ (U.block x).creator ∈ (Correct : Finset Validator) ∧
      F.f + 1 ≤ (creatorsOf U.block (S.filter fun z => x ∈ (U.block z).refs)).card := by
  classical
  obtain ⟨hcb, hbf, hnv⟩ := faults_arith (Validator := Validator)
  -- `c` names `w`: a block of `c` in `S` references a block of `w`
  let R : Validator → Validator → Prop := fun c w =>
    ∃ z ∈ S, (U.block z).creator = c ∧ w ∈ creatorsOf U.block (U.block z).refs
  let g : Validator → ℕ := fun w => ((creatorsOf U.block S).filter fun c => R c w).card
  have hper : ∀ c ∈ creatorsOf U.block S, quorumCard Validator - F.byzantine.card ≤
      ((Correct : Finset Validator).filter fun w => R c w).card := by
    intro c hc
    obtain ⟨z, hzS, hzc⟩ := mem_creatorsOf.mp hc
    obtain ⟨hz, hzr⟩ := hS z hzS
    have hquo : quorumCard Validator ≤ (creatorsOf U.block (U.block z).refs).card :=
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
  have hbig : (creatorsOf U.block S).card * (quorumCard Validator - F.byzantine.card) ≤
      (Correct : Finset Validator).card * g w := by
    have := Finset.card_nsmul_le_card_nsmul (r := fun c w => R c w) (s := creatorsOf U.block S)
      (t := (Correct : Finset Validator))
      (m := quorumCard Validator - F.byzantine.card) (n := g w)
      (fun c hc => by
        change _ ≤ ((Correct : Finset Validator).filter fun w => R c w).card
        exact hper c hc)
      (fun v hv => hwmax v hv)
    simpa [smul_eq_mul] using this
  have hgw : F.f + 1 ≤ g w := by
    by_contra hlt
    push Not at hlt
    exact count_arith hnv hbf hcb (by omega) hbig (by omega)
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
theorem exists_anchored {K : ℕ} {A : BlockId} {S : Finset BlockId} {ρ : ℕ}
    (hS : ∀ z ∈ S, z ∈ U.ids ∧ (U.block z).round = ρ + 1 ∧ z ∈ Avail U K A)
    (hq : quorumCard Validator ≤ (creatorsOf U.block S).card) :
    ∃ x ∈ U.ids, (U.block x).round = ρ ∧ (U.block x).creator ∈ (Correct : Finset Validator) ∧
      AnchoredBelow U K A x K := by
  obtain ⟨x, hx, hxr, hxc, hcard⟩ :=
    exists_correct_referenced (fun z hz => ⟨(hS z hz).1, (hS z hz).2.1⟩) hq
  exact ⟨x, hx, hxr, hxc, AnchoredBelow.of_avail
    (fun z hz => (hS z (Finset.mem_filter.mp hz).1).2.2) (fun z hz => (Finset.mem_filter.mp hz).2)
    hcard⟩

/-- **The available sub-DAG is broad**: below a block `A` of the record, at
`K ≥ 2`, each round `t + 2` or more below `A` holds an anchored block of a
correct author. The quorum it is anchored from is the references of `A`, of
a reference of `A`, or of the anchored block two rounds up. -/
theorem broad {K : ℕ} (hK : 2 ≤ K) {A : BlockId} (hA : A ∈ U.ids) :
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
          (lt_of_lt_of_le (by have := F.card_validators; omega) ((U.valid A hA).quorum (by omega)))
        refine ⟨w, U.complete A hA w hw, ?_, fun z hz =>
          ⟨A, _, AnchoredBelow.anchor, ref_ref_mem_historyUpto hK hw hz⟩⟩
        have := (U.valid A hA).predecessor w hw
        omega
      obtain ⟨y, hy, hyr, -, hya⟩ := ih (t - 2) (by omega) (by omega)
      exact ⟨y, hy, by omega, fun z hz => ⟨y, K, hya, ref_mem_historyUpto (by omega) hz⟩⟩
    refine exists_anchored (S := (U.block v).refs) (fun z hz => ⟨U.complete v hv z hz, ?_,
      hvrefs z hz⟩) ((U.valid v hv).quorum (by omega))
    have := (U.valid v hv).predecessor z hz
    omega

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

/-- **A directly committed block is linked through the sub-DAG**: at a row
and `K ≥ 3`, below a block `A` one round or more above the decision round of
a directly committed round-`r` block, the available sub-DAG holds `linkSize`
authors of its certificates, with their references. A block one round above
the decision round whose references and theirs lie in the sub-DAG
references them, since its references and the certificates come from two
large sets of authors. -/
theorem linked {p : Scheme.Params} (hrow : Row Validator p) {K : ℕ} (hK : 3 ≤ K)
    {A L : BlockId} {r : ℕ} (hA : A ∈ U.ids) (hr : r + p.waveLength ≤ (U.block A).round)
    (hd : DirectCommit p U L r) : AvailLinked p U K A L r := by
  have hw : 2 ≤ p.waveLength := by rcases hrow with ⟨-, h, -⟩ | ⟨-, h, -⟩ <;> omega
  obtain ⟨v, hv, hvr, hvrefs⟩ : ∃ v ∈ U.ids, (U.block v).round = r + p.waveLength ∧
      ∀ z ∈ (U.block v).refs, z ∈ Avail U K A ∧ ∀ j ∈ (U.block z).refs, j ∈ Avail U K A := by
    by_cases h₃ : (U.block A).round = r + p.waveLength
    · exact ⟨A, hA, h₃, fun z hz =>
        ⟨⟨A, _, AnchoredBelow.anchor, ref_mem_historyUpto (K := K) (by omega) hz⟩,
          fun j hj => ⟨A, _, AnchoredBelow.anchor,
            ref_ref_mem_historyUpto (K := K) (by omega) hz hj⟩⟩⟩
    by_cases h₄ : (U.block A).round = r + p.waveLength + 1
    · obtain ⟨w, hw⟩ := nonempty_of_creatorsOf_card_pos (blk := U.block) (s := (U.block A).refs)
        (lt_of_lt_of_le (by have := F.card_validators; omega) ((U.valid A hA).quorum (by omega)))
      obtain ⟨k, rfl⟩ : ∃ k, K = k + 1 := ⟨K - 1, by omega⟩
      refine ⟨w, U.complete A hA w hw, ?_, fun z hz =>
        ⟨⟨A, _, AnchoredBelow.anchor, ref_ref_mem_historyUpto (by omega) hw hz⟩,
          fun j hj => ⟨A, _, AnchoredBelow.anchor, mem_historyUpto_succ.mpr
            (Or.inr ⟨w, hw, ref_ref_mem_historyUpto (by omega) hz hj⟩)⟩⟩⟩
      have := (U.valid A hA).predecessor w hw
      omega
    obtain ⟨y, hy, hyr, -, hya⟩ :=
      broad (K := K) (by omega) hA ((U.block A).round - (r + p.waveLength + 2)) (by omega)
    exact ⟨y, hy, by omega, fun z hz => ⟨⟨y, K, hya, ref_mem_historyUpto (K := K) (by omega) hz⟩,
      fun j hj => ⟨y, K, hya, ref_ref_mem_historyUpto (K := K) (by omega) hz hj⟩⟩⟩
  -- the certificates `v` references
  refine ⟨(certsFor p U L r).filter fun C => C ∈ (U.block v).refs, Finset.filter_subset _ _,
    fun C hC => ?_, ?_⟩
  · have hCv := (Finset.mem_filter.mp hC).2
    exact ⟨(hvrefs C hCv).1, fun _ => (hvrefs C hCv).2⟩
  · have hq : quorumCard Validator ≤ (creatorsOf U.block (U.block v).refs).card :=
      (U.valid v hv).quorum (by omega)
    have hcount := card_refs_filter_ge hv (X := certsFor p U L r)
      fun x hx => ⟨(mem_certsFor hx).1, by have := (mem_certsFor hx).2; omega⟩
    unfold DirectCommit at hd
    rcases hrow with ⟨-, -, -, -, -, hc⟩ | ⟨-, -, hl, -, -, hc⟩ <;> omega

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
  rcases hrow with ⟨hv, hw, -, ha, -, -⟩ | ⟨hv, hw, hl1, -, hb, -⟩
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
    obtain ⟨c, hc, hcC⟩ := exists_correct_of_card hcard
    obtain ⟨w, hw, rfl⟩ := mem_creatorsOf.mp hc
    exact Or.inr (Or.inl ⟨w, ⟨yf w, df w, hyf w hw, hzf w hw⟩, hcC, href w hw, rfl⟩)
  | reached S m yf df yf' df' hyf hzf hyf' hmz hm href hcard hgate =>
    obtain ⟨c, hc, hcC⟩ := exists_correct_of_card hcard
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
  · obtain ⟨u, hu, hucorr⟩ := exists_correct_of_card hV
    obtain ⟨b, hb, hbc⟩ := mem_creatorsOf.mp hu
    obtain ⟨hbi, -, hbA⟩ := mem_votesFor.mp hb
    exact ⟨b, hbi, by rw [hbc]; exact hucorr, Or.inr ⟨y, hbA, hzy⟩⟩
  · exact ⟨w, avail_subset_ids hA hw, hwc, Or.inr ⟨y, hyw, hzy⟩⟩
  · exact ⟨w, avail_subset_ids hA hw, hwc, Or.inr ⟨v, hv, historyUpto_pred_subset hK hyv hzy⟩⟩

end KPartialDag

end LeanDag
