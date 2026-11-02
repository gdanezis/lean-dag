import LeanDag.Common.CommonCore
/-!
# Bypassed blocks

`docs/sync-auth.md` §6 and §8. A block `x` of round `r` is *bypassed* in a
set `V` of blocks when the blocks of `V` at round `r + 1` that do not reference
`x` come from at least `q` authors (`Bypassed`). `V` is *closed up to bypass*
when every reference of a block of `V` is in `V` or bypassed in it
(`BypassClosed`). In §6, `V` is what a node holds; in §8, it is what the
node has ordered, below its decided horizon.

* **An unreferenced block is bypassed** (`bypassed_of_unreferenced`): if `V`
  holds a round-`(r + 1)` block of every honest validator, no honest block
  of that round references `x`, and `q ≤ |honest|`, then `x` is bypassed.
* **Bypass persists** (`Bypassed.mono`): a larger set bypasses `x` still.
* **What is not bypassed is bounded** (`card_not_bypassed_le`): under the
  same holding, the round-`r` blocks not bypassed in `V` number at most
  `|honest| · n`, however many blocks the round holds.
* **A block no witness references is bypassed** (`bypassed_of_unreferenced_in`):
  if the blocks of `V` one round above `x` come from at least `q` authors and
  none references `x`, then `x` is bypassed.
* **One author's blocks not bypassed** (`card_not_bypassed_creator_le`):
  under the holding of the first theorem, at most `|honest|` of one author.
* **The blocks not bypassed, by author** (`card_not_bypassed_le_of_twins`):
  if each author outside `D` that is not honest has at most one block of
  round `r`, at most `|D| · |honest| + (n - |D|)`.
* **Supported blocks are never bypassed** (`not_bypassed_of_support`): a
  block referenced at round `r + 1` by `s` honest validators, with
  `n < q + s`, is bypassed in no set.
-/

namespace LeanDag

variable {Validator : Type*} [DecidableEq Validator]
variable {BlockId : Type*} [DecidableEq BlockId] {Payload : Type*}
variable {P : Validity Validator BlockId Payload} {honest : Finset Validator}
variable {U : BlockRecord Validator BlockId Payload P honest}

/-- The authors of the blocks of `V` at round `n` that do not reference `x`. -/
def bypassers (U : BlockRecord Validator BlockId Payload P honest) (V : Finset BlockId)
    (x : BlockId) (n : ℕ) : Finset Validator :=
  creatorsOf U.block (omissionsOf U x n ∩ V)

/-- **Bypassed**: the blocks of `V` one round above `x` that do not reference
it come from at least `q` authors. -/
def Bypassed (U : BlockRecord Validator BlockId Payload P honest) (V : Finset BlockId)
    (q : ℕ) (x : BlockId) : Prop :=
  q ≤ (bypassers U V x ((U.block x).round + 1)).card

instance decidableBypassed (V : Finset BlockId) (q : ℕ) (x : BlockId) :
    Decidable (Bypassed U V q x) :=
  inferInstanceAs (Decidable (q ≤ _))

/-- **Closed up to bypass**: every reference of a block of `V` is in `V` or
bypassed in it. -/
def BypassClosed (U : BlockRecord Validator BlockId Payload P honest) (V : Finset BlockId)
    (q : ℕ) : Prop :=
  ∀ i ∈ V, ∀ j ∈ (U.block i).refs, j ∈ V ∨ Bypassed U V q j

theorem mem_bypassers {V : Finset BlockId} {x : BlockId} {n : ℕ} {v : Validator} :
    v ∈ bypassers U V x n ↔
      ∃ y ∈ V, y ∈ U.ids ∧ (U.block y).round = n ∧ x ∉ (U.block y).refs ∧
        (U.block y).creator = v := by
  simp only [bypassers, mem_creatorsOf, Finset.mem_inter, mem_omissionsOf]
  constructor
  · rintro ⟨y, ⟨⟨hU, hr, hx⟩, hV⟩, hc⟩; exact ⟨y, hV, hU, hr, hx, hc⟩
  · rintro ⟨y, hV, hU, hr, hx, hc⟩; exact ⟨y, ⟨⟨hU, hr, hx⟩, hV⟩, hc⟩

/-- A reference-closed set is closed up to bypass. -/
theorem BypassClosed.of_complete {V : Finset BlockId} {q : ℕ}
    (h : ∀ i ∈ V, ∀ j ∈ (U.block i).refs, j ∈ V) : BypassClosed U V q :=
  fun i hi j hj => Or.inl (h i hi j hj)

/-- **Bypass persists**: a larger set bypasses `x` still. -/
theorem Bypassed.mono {V V' : Finset BlockId} {q : ℕ} {x : BlockId} (hV : V ⊆ V')
    (h : Bypassed U V q x) : Bypassed U V' q x :=
  le_trans h (Finset.card_le_card
    (Finset.image_subset_image (Finset.inter_subset_inter_left hV)))

/-- **An unreferenced block is bypassed**: `V` holds a block of every honest
validator at the round above `x`, and no honest block of that round
references `x`. -/
theorem bypassed_of_unreferenced {V : Finset BlockId} {q : ℕ} {x : BlockId}
    (hq : q ≤ honest.card)
    (hpop : ∀ v ∈ honest, ∃ y ∈ V, y ∈ U.ids ∧ (U.block y).round = (U.block x).round + 1 ∧
      (U.block y).creator = v)
    (hx : ∀ y ∈ U.ids, (U.block y).round = (U.block x).round + 1 →
      (U.block y).creator ∈ honest → x ∉ (U.block y).refs) :
    Bypassed U V q x := by
  refine le_trans hq (Finset.card_le_card fun v hv => ?_)
  obtain ⟨y, hyV, hyU, hyr, hyc⟩ := hpop v hv
  exact mem_bypassers.mpr ⟨y, hyV, hyU, hyr, hx y hyU hyr (hyc ▸ hv), hyc⟩

/-- A block not bypassed, under the holding of `bypassed_of_unreferenced`, is
referenced by an honest block of the round above. -/
theorem exists_honest_ref_of_not_bypassed {V : Finset BlockId} {q : ℕ} {x : BlockId}
    (hq : q ≤ honest.card)
    (hpop : ∀ v ∈ honest, ∃ y ∈ V, y ∈ U.ids ∧ (U.block y).round = (U.block x).round + 1 ∧
      (U.block y).creator = v)
    (h : ¬ Bypassed U V q x) :
    ∃ y ∈ U.ids, (U.block y).round = (U.block x).round + 1 ∧
      (U.block y).creator ∈ honest ∧ x ∈ (U.block y).refs := by
  by_contra hne
  push Not at hne
  exact h (bypassed_of_unreferenced hq hpop fun y hy hr hc => hne y hy hr hc)

omit [DecidableEq Validator] [DecidableEq BlockId] in
/-- A valid block references at most `n` blocks, one for each author. -/
theorem card_refs_le_univ [Fintype Validator] [P.Distinct] {y : BlockId} (hy : y ∈ U.ids) :
    (U.block y).refs.card ≤ Fintype.card Validator :=
  Finset.card_le_card_of_injOn (fun i => (U.block i).creator)
    (fun _ _ => Finset.mem_coe.mpr (Finset.mem_univ _))
    (fun i hi j hj h => Validity.Distinct.distinct U.block (U.block y) (U.valid y hy) i hi j hj h)

/-- **What is not bypassed is bounded**: if `V` holds a block of every honest
validator at round `r + 1`, the round-`r` blocks not bypassed in `V` number at
most `|honest| · n`. -/
theorem card_not_bypassed_le [Fintype Validator] [P.Distinct] {V : Finset BlockId} {q r : ℕ}
    (hq : q ≤ honest.card)
    (hpop : ∀ v ∈ honest, ∃ y ∈ V, y ∈ U.ids ∧ (U.block y).round = r + 1 ∧
      (U.block y).creator = v) :
    ((blocksAt U r).filter fun x => ¬ Bypassed U V q x).card ≤
      honest.card * Fintype.card Validator := by
  have hsub : (blocksAt U r).filter (fun x => ¬ Bypassed U V q x) ⊆
      (honestBlocksAt U (r + 1)).biUnion fun y => (U.block y).refs := by
    intro x hx
    obtain ⟨hxb, hxn⟩ := Finset.mem_filter.mp hx
    obtain ⟨-, hxr⟩ := mem_blocksAt.mp hxb
    obtain ⟨y, hyU, hyr, hyc, hxy⟩ :=
      exists_honest_ref_of_not_bypassed hq (hxr ▸ hpop) hxn
    exact Finset.mem_biUnion.mpr
      ⟨y, Finset.mem_filter.mpr ⟨mem_blocksAt.mpr ⟨hyU, hxr ▸ hyr⟩, hyc⟩, hxy⟩
  have hL : (honestBlocksAt U (r + 1)).card ≤ honest.card := by
    rw [← card_creatorsOf_honestBlocksAt]
    exact Finset.card_le_card creatorsOf_honestBlocksAt_subset
  calc _ ≤ _ := Finset.card_le_card hsub
    _ ≤ ∑ y ∈ honestBlocksAt U (r + 1), (U.block y).refs.card := Finset.card_biUnion_le
    _ ≤ ∑ _y ∈ honestBlocksAt U (r + 1), Fintype.card Validator :=
        Finset.sum_le_sum fun y hy =>
          card_refs_le_univ (mem_blocksAt.mp (Finset.mem_filter.mp hy).1).1
    _ = (honestBlocksAt U (r + 1)).card * Fintype.card Validator := by
        rw [Finset.sum_const, smul_eq_mul]
    _ ≤ _ := Nat.mul_le_mul_right _ hL

/-- **A block no witness references is bypassed**: if the blocks of `V` one round
above `x` come from at least `q` authors and none of them references `x`, then `x`
is bypassed in `V`. -/
theorem bypassed_of_unreferenced_in {V : Finset BlockId} {q : ℕ} {x : BlockId}
    (hV : V ⊆ U.ids) (hq : q ≤ (authorsIn U V ((U.block x).round + 1)).card)
    (hx : ∀ y ∈ V, (U.block y).round = (U.block x).round + 1 → x ∉ (U.block y).refs) :
    Bypassed U V q x := by
  refine le_trans hq (Finset.card_le_card fun v hv => ?_)
  obtain ⟨y, hyV, hyr, hyc⟩ := mem_authorsIn.mp hv
  exact mem_bypassers.mpr ⟨y, hyV, hV hyV, hyr, hx y hyV hyr, hyc⟩

omit [DecidableEq BlockId] in
/-- A valid block references at most one block of each author. -/
theorem card_refs_creator_le_one [P.Distinct] {y : BlockId} (hy : y ∈ U.ids) (a : Validator) :
    ((U.block y).refs.filter fun x => (U.block x).creator = a).card ≤ 1 := by
  refine Finset.card_le_one.mpr fun i hi j hj => ?_
  obtain ⟨hi, hia⟩ := Finset.mem_filter.mp hi
  obtain ⟨hj, hja⟩ := Finset.mem_filter.mp hj
  exact Validity.Distinct.distinct U.block (U.block y) (U.valid y hy) i hi j hj (hia.trans hja.symm)

/-- **One author's blocks not bypassed**: under the holding of
`bypassed_of_unreferenced`, the round-`r` blocks of an author `a` not bypassed in
`V` number at most `|honest|`, since each is referenced by an honest block of round
`r + 1`, and such a block references at most one block of `a`. -/
theorem card_not_bypassed_creator_le [P.Distinct] {V : Finset BlockId} {q r : ℕ}
    (a : Validator) (hq : q ≤ honest.card)
    (hpop : ∀ v ∈ honest, ∃ y ∈ V, y ∈ U.ids ∧ (U.block y).round = r + 1 ∧
      (U.block y).creator = v) :
    ((blocksAt U r).filter fun x => (U.block x).creator = a ∧ ¬ Bypassed U V q x).card ≤
      honest.card := by
  have hsub : (blocksAt U r).filter (fun x => (U.block x).creator = a ∧ ¬ Bypassed U V q x) ⊆
      (honestBlocksAt U (r + 1)).biUnion fun y =>
        (U.block y).refs.filter fun x => (U.block x).creator = a := by
    intro x hx
    obtain ⟨hxb, hxa, hxn⟩ := Finset.mem_filter.mp hx
    obtain ⟨-, hxr⟩ := mem_blocksAt.mp hxb
    obtain ⟨y, hyU, hyr, hyc, hxy⟩ :=
      exists_honest_ref_of_not_bypassed hq (hxr ▸ hpop) hxn
    exact Finset.mem_biUnion.mpr ⟨y, Finset.mem_filter.mpr
      ⟨mem_blocksAt.mpr ⟨hyU, hxr ▸ hyr⟩, hyc⟩, Finset.mem_filter.mpr ⟨hxy, hxa⟩⟩
  have hL : (honestBlocksAt U (r + 1)).card ≤ honest.card := by
    rw [← card_creatorsOf_honestBlocksAt]
    exact Finset.card_le_card creatorsOf_honestBlocksAt_subset
  calc _ ≤ _ := Finset.card_le_card hsub
    _ ≤ ∑ y ∈ honestBlocksAt U (r + 1),
          ((U.block y).refs.filter fun x => (U.block x).creator = a).card :=
        Finset.card_biUnion_le
    _ ≤ ∑ _y ∈ honestBlocksAt U (r + 1), 1 :=
        Finset.sum_le_sum fun y hy =>
          card_refs_creator_le_one (mem_blocksAt.mp (Finset.mem_filter.mp hy).1).1 a
    _ = (honestBlocksAt U (r + 1)).card := by simp
    _ ≤ _ := hL

/-- **The blocks not bypassed, by author**: under the holding of
`bypassed_of_unreferenced`, if each author outside `D` that is not honest has at
most one block of round `r`, the round-`r` blocks not bypassed in `V` number at
most `|D| · |honest| + (n - |D|)`. -/
theorem card_not_bypassed_le_of_twins [Fintype Validator] [P.Distinct] {V : Finset BlockId}
    {q r : ℕ} {D : Finset Validator} (hq : q ≤ honest.card)
    (hpop : ∀ v ∈ honest, ∃ y ∈ V, y ∈ U.ids ∧ (U.block y).round = r + 1 ∧
      (U.block y).creator = v)
    (hD : ∀ a ∉ D, a ∉ honest → ∀ x ∈ blocksAt U r, ∀ y ∈ blocksAt U r,
      (U.block x).creator = a → (U.block y).creator = a → x = y) :
    ((blocksAt U r).filter fun x => ¬ Bypassed U V q x).card ≤
      D.card * honest.card + (Fintype.card Validator - D.card) := by
  have hsub : (blocksAt U r).filter (fun x => ¬ Bypassed U V q x) ⊆
      Finset.univ.biUnion fun a =>
        (blocksAt U r).filter fun x => (U.block x).creator = a ∧ ¬ Bypassed U V q x := by
    intro x hx
    obtain ⟨hxb, hxn⟩ := Finset.mem_filter.mp hx
    exact Finset.mem_biUnion.mpr ⟨_, Finset.mem_univ _, Finset.mem_filter.mpr ⟨hxb, rfl, hxn⟩⟩
  have hA : ∀ a, ((blocksAt U r).filter fun x =>
      (U.block x).creator = a ∧ ¬ Bypassed U V q x).card ≤
        if a ∈ D then honest.card else 1 := by
    intro a
    split_ifs with ha
    · exact card_not_bypassed_creator_le a hq hpop
    · refine Finset.card_le_one.mpr fun x hx y hy => ?_
      obtain ⟨hxb, hxa, -⟩ := Finset.mem_filter.mp hx
      obtain ⟨hyb, hya, -⟩ := Finset.mem_filter.mp hy
      by_cases hah : a ∈ honest
      · obtain ⟨hxU, hxr⟩ := mem_blocksAt.mp hxb
        obtain ⟨hyU, hyr⟩ := mem_blocksAt.mp hyb
        exact U.eq_of_creator_eq hxU hyU hah hxa hya (hxr.trans hyr.symm)
      · exact hD a ha hah x hxb y hyb hxa hya
  calc _ ≤ _ := Finset.card_le_card hsub
    _ ≤ ∑ a, ((blocksAt U r).filter fun x =>
          (U.block x).creator = a ∧ ¬ Bypassed U V q x).card := Finset.card_biUnion_le
    _ ≤ ∑ a : Validator, (if a ∈ D then honest.card else 1) :=
        Finset.sum_le_sum fun a _ => hA a
    _ = D.card * honest.card + (Fintype.card Validator - D.card) := by
        rw [Finset.sum_ite]
        simp [Finset.filter_not, Finset.card_univ_sdiff]

/-- **Supported blocks are never bypassed**: an honest validator whose block
of the round above references `x` is not among its bypassers, so `s` such
validators with `n < q + s` leave fewer than `q`. -/
theorem not_bypassed_of_support [Fintype Validator] {V : Finset BlockId} {q : ℕ}
    {x : BlockId}
    (hs : Fintype.card Validator <
      q + (supporters U x ((U.block x).round + 1) ∩ honest).card) :
    ¬ Bypassed U V q x := by
  intro hb
  have hdis : Disjoint (bypassers U V x ((U.block x).round + 1))
      (supporters U x ((U.block x).round + 1) ∩ honest) := by
    rw [Finset.disjoint_left]
    intro v hv hv'
    obtain ⟨y, -, hyU, hyr, hxy, hyc⟩ := mem_bypassers.mp hv
    obtain ⟨hsup, hvh⟩ := Finset.mem_inter.mp hv'
    obtain ⟨z, hzU, hzr, hxz, hzc⟩ := mem_supporters.mp hsup
    exact hxy (U.eq_of_creator_eq hyU hzU hvh hyc hzc (hyr.trans hzr.symm) ▸ hxz)
  have := Finset.card_le_univ (bypassers U V x ((U.block x).round + 1) ∪
    (supporters U x ((U.block x).round + 1) ∩ honest))
  rw [Finset.card_union_of_disjoint hdis] at this
  unfold Bypassed at hb
  omega

end LeanDag
