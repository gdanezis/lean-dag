import LeanDag.KPartialDag.Model.Rule
import LeanDag.Common.Counting
import Mathlib.Combinatorics.Enumerative.DoubleCounting
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Group.Action.Defs
import Mathlib.Tactic.Linarith
/-!
# The available sub-DAG — helpers

`docs/kpartial.md` §3. Blocks of a quorum of distinct authors at one round
reference, between them, some correct author's block of the round below
from `f + 1` of those authors (`exists_correct_referenced`): a double count,
since each references `n − 2f` or more correct blocks and correct authors
have one block a round. So below a block `A`, every round two or more below
it holds an anchored block of a correct author (`broad`); every block at
round `r + 3` references a certificate of a directly committed round-`r`
block, so the available sub-DAG below `A` holds one with its references, at
`K ≥ 3` (`linked`); and a certificate excludes a direct skip
(`not_directSkip`). Each block of the sub-DAG lies in the history to depth
`K` of `A`, or of an anchored block that a correct author's block of the
sub-DAG references (`held`); a correct voter of a certificate for `A`
references `A`, so below a certified block the sub-DAG is held by correct
nodes (`avail_correctHeld`).
-/

namespace LeanDag

namespace KPartialDag

variable {Validator : Type*} [Fintype Validator] [DecidableEq Validator] [F : Faults Validator]
variable {BlockId : Type*} [DecidableEq BlockId] {Payload : Type*}
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

/-- **An anchored block is a block of the record**, when `A` is. -/
theorem AnchoredBelow.mem {K : ℕ} {A : BlockId} (hA : A ∈ U.ids) {x : BlockId}
    (h : AnchoredBelow U K A x) : x ∈ U.ids := by
  induction h with
  | anchor => exact hA
  | @referenced x S y hy hz href hcard ih =>
    obtain ⟨z, hzS⟩ := nonempty_of_creatorsOf_card_pos (by omega : 0 < (creatorsOf U.block S).card)
    exact U.complete z (historyUpto_subset_ids K (ih z hzS) (hz z hzS)) _ (href z hzS)

/-- **Anchoring from the sub-DAG**: a block that blocks of the available
sub-DAG from `f + 1` distinct authors reference is anchored. -/
theorem AnchoredBelow.of_avail {K : ℕ} {A x : BlockId} {S : Finset BlockId}
    (hS : ∀ z ∈ S, z ∈ Avail U K A) (href : ∀ z ∈ S, x ∈ (U.block z).refs)
    (hcard : F.f + 1 ≤ (creatorsOf U.block S).card) : AnchoredBelow U K A x := by
  classical
  refine AnchoredBelow.referenced S (fun z => if h : z ∈ Avail U K A then h.choose else A)
    (fun z hz => ?_) (fun z hz => ?_) href hcard <;> simp only [dif_pos (hS z hz)]
  exacts [(hS z hz).choose_spec.1, (hS z hz).choose_spec.2]

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
      AnchoredBelow U K A x := by
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
        (U.block x).creator ∈ (Correct : Finset Validator) ∧ AnchoredBelow U K A x := by
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
          ⟨A, AnchoredBelow.anchor, ref_mem_historyUpto (by omega) hz⟩⟩
      by_cases h₁ : t = 1
      · subst h₁
        obtain ⟨w, hw⟩ := nonempty_of_creatorsOf_card_pos (blk := U.block) (s := (U.block A).refs)
          (lt_of_lt_of_le (by have := F.card_validators; omega) ((U.valid A hA).quorum (by omega)))
        refine ⟨w, U.complete A hA w hw, ?_, fun z hz =>
          ⟨A, AnchoredBelow.anchor, ref_ref_mem_historyUpto hK hw hz⟩⟩
        have := (U.valid A hA).predecessor w hw
        omega
      obtain ⟨y, hy, hyr, -, hya⟩ := ih (t - 2) (by omega) (by omega)
      exact ⟨y, hy, by omega, fun z hz => ⟨y, hya, ref_mem_historyUpto (by omega) hz⟩⟩
    refine exists_anchored (S := (U.block v).refs) (fun z hz => ⟨U.complete v hv z hz, ?_,
      hvrefs z hz⟩) ((U.valid v hv).quorum (by omega))
    have := (U.valid v hv).predecessor z hz
    omega

/-- **A directly committed block is linked through the sub-DAG**: below a
block `A` at round `r + 3` or above, at `K ≥ 3`, the available sub-DAG holds
a certificate of a directly committed round-`r` block and its references. A
block of round `r + 3` whose references and theirs lie in the sub-DAG
references a certificate of a correct author, since its references and the
certificates come from two quorums. -/
theorem linked {K : ℕ} (hK : 3 ≤ K) {A L : BlockId} {r : ℕ} (hA : A ∈ U.ids)
    (hr : r + 3 ≤ (U.block A).round) (hd : DirectCommit U L r) : AvailLinked U K A L r := by
  obtain ⟨v, hv, hvr, hvrefs⟩ : ∃ v ∈ U.ids, (U.block v).round = r + 3 ∧
      ∀ z ∈ (U.block v).refs, z ∈ Avail U K A ∧ ∀ j ∈ (U.block z).refs, j ∈ Avail U K A := by
    by_cases h₃ : (U.block A).round = r + 3
    · exact ⟨A, hA, h₃, fun z hz =>
        ⟨⟨A, AnchoredBelow.anchor, ref_mem_historyUpto (K := K) (by omega) hz⟩,
          fun j hj => ⟨A, AnchoredBelow.anchor, ref_ref_mem_historyUpto (K := K) (by omega) hz hj⟩⟩⟩
    by_cases h₄ : (U.block A).round = r + 4
    · obtain ⟨w, hw⟩ := nonempty_of_creatorsOf_card_pos (blk := U.block) (s := (U.block A).refs)
        (lt_of_lt_of_le (by have := F.card_validators; omega) ((U.valid A hA).quorum (by omega)))
      obtain ⟨k, rfl⟩ : ∃ k, K = k + 1 := ⟨K - 1, by omega⟩
      refine ⟨w, U.complete A hA w hw, ?_, fun z hz =>
        ⟨⟨A, AnchoredBelow.anchor, ref_ref_mem_historyUpto (by omega) hw hz⟩,
          fun j hj => ⟨A, AnchoredBelow.anchor, mem_historyUpto_succ.mpr
            (Or.inr ⟨w, hw, ref_ref_mem_historyUpto (by omega) hz hj⟩)⟩⟩⟩
      have := (U.valid A hA).predecessor w hw
      omega
    obtain ⟨y, hy, hyr, -, hya⟩ :=
      broad (K := K) (by omega) hA ((U.block A).round - (r + 5)) (by omega)
    exact ⟨y, hy, by omega, fun z hz => ⟨⟨y, hya, ref_mem_historyUpto (K := K) (by omega) hz⟩,
      fun j hj => ⟨y, hya, ref_ref_mem_historyUpto (K := K) (by omega) hz hj⟩⟩⟩
  -- a reference of `v` and a certificate, from two quorums, share a block
  have hq : quorumCard Validator ≤ (creatorsOf U.block (U.block v).refs).card :=
    (U.valid v hv).quorum (by omega)
  obtain ⟨z, hz, hC⟩ := exists_common_block U.noEquivOn_honest card_compl_correct_le
    (t := certificatesAt U (IsVote U) (quorumCard Validator) L (r + 2))
    (fun z hz => ⟨U.complete v hv z hz, by have := (U.valid v hv).predecessor z hz; omega⟩)
    (fun C hC => (mem_certificatesAt.mp hC).imp_right And.left)
    (by have := F.card_validators; unfold DirectCommit at hd; omega)
  exact ⟨z, hC, hvrefs z hz⟩

/-- **A certificate excludes a direct skip**: its votes and the blames come
from two quorums, so a correct author would have a round-`(r+1)` block that
references the block and one that does not. -/
theorem not_directSkip {L C : BlockId} {r : ℕ}
    (hC : C ∈ certificatesAt U (IsVote U) (quorumCard Validator) L (r + 2)) :
    ¬ DirectSkip U L r := by
  intro hs
  unfold DirectSkip at hs
  obtain ⟨hCi, hCr, hcv⟩ := mem_certificatesAt.mp hC
  unfold CarriesVotes at hcv
  have := Finset.card_le_card (creatorsOf_carriedVotes_subset_supporters (L := L) hCi hCr)
  have := card_supporters_add_card_blames_le U.noEquivOn_honest card_compl_correct_le
    (L := L) (n := r + 1)
  have := F.card_validators
  omega

/-- An anchored block is `A`, or referenced by a correct author's block of the
sub-DAG. -/
theorem AnchoredBelow.eq_or_referenced {K : ℕ} {A y : BlockId} (h : AnchoredBelow U K A y) :
    y = A ∨ ∃ w ∈ Avail U K A, (U.block w).creator ∈ (Correct : Finset Validator) ∧
      y ∈ (U.block w).refs := by
  cases h with
  | anchor => exact Or.inl rfl
  | referenced S yf hyf hzf href hcard =>
    obtain ⟨c, hc, hcC⟩ := exists_correct_of_card hcard
    obtain ⟨w, hw, rfl⟩ := mem_creatorsOf.mp hc
    exact Or.inr ⟨w, ⟨yf w, hyf w hw, hzf w hw⟩, hcC, href w hw⟩

/-- **The sub-DAG is held**: each of its blocks lies in the history to depth
`K` of `A`, or of an anchored block a correct author's block of the sub-DAG
references. -/
theorem held {K : ℕ} {A z : BlockId} (hz : z ∈ Avail U K A) :
    ∃ y, AnchoredBelow U K A y ∧ z ∈ historyUpto U K y ∧
      (y = A ∨ ∃ w ∈ Avail U K A, (U.block w).creator ∈ (Correct : Finset Validator) ∧
        y ∈ (U.block w).refs) := by
  obtain ⟨y, hy, hzy⟩ := hz
  exact ⟨y, hy, hzy, hy.eq_or_referenced⟩

/-- The available sub-DAG below a block of the record lies in the record. -/
theorem avail_subset_ids {K : ℕ} {A z : BlockId} (hA : A ∈ U.ids) (hz : z ∈ Avail U K A) :
    z ∈ U.ids := by
  obtain ⟨y, hy, hzy⟩ := hz
  exact historyUpto_subset_ids K (hy.mem hA) hzy

/-- **The available sub-DAG below a certified block is held by correct
nodes**: it lies in the history to depth `K` of a block that a correct voter
of the certificate, or a correct author's block of the sub-DAG, references. -/
theorem avail_correctHeld {K : ℕ} {A z : BlockId} {r : ℕ} (hA : A ∈ U.ids)
    (hC : (certificatesAt U (IsVote U) (quorumCard Validator) A r).Nonempty)
    (hz : z ∈ Avail U K A) : z ∈ CorrectHeld U K := by
  obtain ⟨C, hC⟩ := hC
  obtain ⟨y, -, hzy, hyA | ⟨w, hw, hwc, hyw⟩⟩ := held hz
  · obtain ⟨hCi, -, hv⟩ := mem_certificatesAt.mp hC
    obtain ⟨u, hu, hucorr⟩ := exists_correct_of_card
      (S := creatorsOf U.block (carriedVotes U (IsVote U) C A))
      (by have := F.card_validators; unfold CarriesVotes at hv; omega)
    obtain ⟨b, hb, hbc⟩ := mem_creatorsOf.mp hu
    obtain ⟨hbC, hbA⟩ := mem_carriedVotes.mp hb
    refine ⟨b, U.complete C hCi b hbC, by rw [hbc]; exact hucorr, Or.inr ⟨y, ?_, hzy⟩⟩
    rw [hyA]
    exact hbA
  · exact ⟨w, avail_subset_ids hA hw, hwc, Or.inr ⟨y, hyw, hzy⟩⟩

end KPartialDag

end LeanDag
