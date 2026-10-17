import LeanDag.Common.Support
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Group.Action.Defs
import Mathlib.Combinatorics.Enumerative.DoubleCounting
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Image
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.Finset.Max
import Mathlib.Tactic.Linarith

/-!
# A common correct ancestor

`spec.md` §4, Phase 1b — T3a and T3c. Persistence (T3) says a block
already backed by a quorum survives forever; this file says something
is **always** backed: across any three consecutive rounds, some correct
validator's round-`r` block lies in the causal history of every
round-`(r+2)` block, by a counting argument in the spirit of the Gather
protocol's common-core lemma. This file produces the correct supporters
that `Support.lean` consumes; `Persistence.lean` gets its own free from
a quorum hypothesis instead.

Thresholds are stated **additively** (`p ≤ k + 2 * F.f`) rather than as
`p - 2f ≤ k`: truncated `ℕ` subtraction would silently collapse the
threshold to `0` whenever `p ≤ 2f`, turning a vacuous case into an
apparently provable one.
-/

namespace LeanDag

/-! ## At a general quorum

On a block record whose blocks reference `q` distinct authors one round
down, with at most `f` validators outside its honest set: at
`2q ≥ n + f + 1`, some honest round-`r` block lies in the history of every
block from round `r + 2` up. -/

section General

variable {Validator : Type*} [Fintype Validator] [DecidableEq Validator]
variable {BlockId : Type*} [DecidableEq BlockId] {Payload : Type*}
variable {P : Validity Validator BlockId Payload} {honest : Finset Validator} [P.Mechanised]
variable {q : ℕ} [P.Quorate q]
variable {U : BlockRecord Validator BlockId Payload P honest}

/-- The common core's arithmetic: with `b ≤ f` validators outside the
honest `c = n − b`, `l ≤ c` honest round-`(r+1)` blocks each naming `q`
authors, some author collecting `k` with `l·q ≤ c·k + l·b`, and `p ≤ l + b`
authors at round `r + 1`, `2q ≥ n + f + 1` gives `k + q > p`. -/
theorem commonCore_arith {n f b c l k p : ℕ}
    (hbf : b ≤ f) (hq : n + f + 1 ≤ 2 * q) (hqn : q ≤ n) (hcb : c + b = n) (hlc : l ≤ c)
    (hA : l * q ≤ c * k + l * b) (hE : p ≤ l + b) :
    p + 1 ≤ k + q := by
  by_contra h
  push Not at h
  have h1 : c * k ≤ c * (l + b - q) := Nat.mul_le_mul_left c (by omega)
  obtain ⟨e, he⟩ : ∃ e, l + b = q + e := ⟨l + b - q, by omega⟩
  rw [show l + b - q = e by omega] at h1
  nlinarith [h1, hA, hlc, hcb, he, hq, hbf]

omit [DecidableEq BlockId] [P.Mechanised] [P.Quorate q] in
/-- A set of validators is its honest part and at most the others. -/
theorem card_le_inter_add_compl (s : Finset Validator) :
    s.card ≤ (s ∩ honest).card + honestᶜ.card := by
  have hsplit := Finset.card_inter_add_card_sdiff s honest
  have : (s \ honest).card ≤ honestᶜ.card :=
    Finset.card_le_card fun x hx => Finset.mem_compl.mpr (Finset.mem_sdiff.mp hx).2
  omega

/-- The honest blocks of round `n`. -/
abbrev honestBlocksAt (U : BlockRecord Validator BlockId Payload P honest) (n : ℕ) :
    Finset BlockId :=
  (blocksAt U n).filter (fun b => (U.block b).creator ∈ honest)

omit [Fintype Validator] [DecidableEq BlockId] [P.Mechanised] [P.Quorate q] in
theorem creator_injOn_honestBlocksAt {n : ℕ} :
    Set.InjOn (fun b => (U.block b).creator) (honestBlocksAt U n) := by
  intro b hb b' hb' h
  obtain ⟨hbs, hbh⟩ := Finset.mem_filter.mp hb
  obtain ⟨hbU, hbr⟩ := mem_blocksAt.mp hbs
  obtain ⟨hb's, -⟩ := Finset.mem_filter.mp hb'
  obtain ⟨hb'U, hb'r⟩ := mem_blocksAt.mp hb's
  exact U.eq_of_creator_eq hbU hb'U hbh rfl h.symm (by rw [hbr, hb'r])

omit [Fintype Validator] [DecidableEq BlockId] [P.Mechanised] [P.Quorate q] in
theorem card_creatorsOf_honestBlocksAt {n : ℕ} :
    (creatorsOf U.block (honestBlocksAt U n)).card = (honestBlocksAt U n).card :=
  Finset.card_image_of_injOn creator_injOn_honestBlocksAt

omit [Fintype Validator] [DecidableEq BlockId] [P.Mechanised] [P.Quorate q] in
theorem creatorsOf_honestBlocksAt_subset {n : ℕ} :
    creatorsOf U.block (honestBlocksAt U n) ⊆ honest := by
  intro v hv
  obtain ⟨b, hb, rfl⟩ := mem_creatorsOf.mp hv
  exact (Finset.mem_filter.mp hb).2

omit [DecidableEq BlockId] [P.Mechanised] [P.Quorate q] in
/-- The authors of a round are its honest authors and at most the others. -/
theorem card_authorsAt_le_honest {n : ℕ} :
    (authorsAt U n).card ≤ (honestBlocksAt U n).card + honestᶜ.card := by
  rw [← card_creatorsOf_honestBlocksAt]
  refine le_trans (Finset.card_le_card ?_) (Finset.card_union_le _ _)
  intro v hv
  obtain ⟨i, hi, hir, rfl⟩ := mem_authorsAt.mp hv
  by_cases hc : (U.block i).creator ∈ honest
  · exact Finset.mem_union_left _ (mem_creatorsOf.mpr
      ⟨i, Finset.mem_filter.mpr ⟨mem_blocksAt.mpr ⟨hi, hir⟩, hc⟩, rfl⟩)
  · exact Finset.mem_union_right _ (Finset.mem_compl.mpr hc)

/-- **The common core's count**: at `2q ≥ n + f + 1`, given a round-`(r+1)`
author pool of at least `q`, some honest round-`r` block has so many honest
supporters at round `r + 1` that with `q` they exceed the pool. -/
theorem exists_honest_common_support {f r : ℕ} (hf : honestᶜ.card ≤ f)
    (hq2 : Fintype.card Validator + f + 1 ≤ 2 * q)
    (hp : q ≤ (authorsAt U (r + 1)).card) :
    ∃ bw ∈ U.ids, (U.block bw).round = r ∧ (U.block bw).creator ∈ honest ∧
      (authorsAt U (r + 1)).card + 1 ≤ (supporters U bw (r + 1) ∩ honest).card + q := by
  classical
  have hE := card_authorsAt_le_honest (U := U) (n := r + 1)
  have hlc : (honestBlocksAt U (r + 1)).card ≤ honest.card := by
    rw [← card_creatorsOf_honestBlocksAt]
    exact Finset.card_le_card creatorsOf_honestBlocksAt_subset
  have hcb : honest.card + honestᶜ.card = Fintype.card Validator := Finset.card_add_card_compl _
  have hqn : q ≤ Fintype.card Validator :=
    le_trans hp (card_authorsAt_le_univ (U := U) (n := r + 1))
  set L := honestBlocksAt U (r + 1) with hLdef
  set g : Validator → ℕ :=
    fun w => (L.filter (fun x => w ∈ creatorsOf U.block (U.block x).refs)).card with hgdef
  have hper : ∀ x ∈ L,
      q ≤ ((creatorsOf U.block (U.block x).refs) ∩ honest).card + honestᶜ.card := by
    intro x hx
    obtain ⟨hxs, -⟩ := Finset.mem_filter.mp hx
    obtain ⟨hxU, hxr⟩ := mem_blocksAt.mp hxs
    exact le_trans (U.creators_quorum hxU (by omega)) (card_le_inter_add_compl _)
  have hC_ne : honest.Nonempty := by rw [← Finset.card_pos]; omega
  obtain ⟨w, hw_mem, hw_max⟩ := honest.exists_max_image g hC_ne
  have hbig : L.card * (q - honestᶜ.card) ≤ honest.card * g w := by
    have := Finset.card_nsmul_le_card_nsmul
      (r := fun (x : BlockId) (v : Validator) => v ∈ creatorsOf U.block (U.block x).refs)
      (s := L) (t := honest) (m := q - honestᶜ.card) (n := g w)
      (fun x hx => by
        have h := hper x hx
        change q - honestᶜ.card ≤
          (honest.filter (fun v => v ∈ creatorsOf U.block (U.block x).refs)).card
        rw [Finset.filter_mem_eq_inter, Finset.inter_comm]
        omega)
      (fun v hv => hw_max v hv)
    simpa [smul_eq_mul] using this
  have hA : L.card * q ≤ honest.card * g w + L.card * honestᶜ.card := by
    have hsplit : L.card * q = L.card * (q - honestᶜ.card) + L.card * honestᶜ.card := by
      rw [← Nat.mul_add, Nat.sub_add_cancel (by omega)]
    omega
  have harith := commonCore_arith (q := q) hf hq2 hqn hcb hlc hA hE
  have hgw_pos : 0 < g w := by omega
  obtain ⟨x₀, hx₀⟩ := Finset.card_pos.mp hgw_pos
  obtain ⟨hx₀L, hx₀w⟩ := Finset.mem_filter.mp hx₀
  obtain ⟨hx₀s, -⟩ := Finset.mem_filter.mp hx₀L
  obtain ⟨hx₀U, hx₀r⟩ := mem_blocksAt.mp hx₀s
  obtain ⟨bw, hbw_mem, hbw_creator⟩ := mem_creatorsOf.mp hx₀w
  have hbwU : bw ∈ U.ids := U.complete _ hx₀U _ hbw_mem
  have hbwr : (U.block bw).round = r := by
    have := U.round_of_mem_refs hx₀U hbw_mem; omega
  refine ⟨bw, hbwU, hbwr, hbw_creator ▸ hw_mem, ?_⟩
  have hsub : Finset.image (fun x => (U.block x).creator)
      (L.filter (fun x => w ∈ creatorsOf U.block (U.block x).refs)) ⊆
        supporters U bw (r + 1) ∩ honest := by
    intro v hv
    simp only [Finset.mem_image, Finset.mem_filter] at hv
    obtain ⟨x, ⟨hxL, hxw⟩, rfl⟩ := hv
    obtain ⟨hxs, hxh⟩ := Finset.mem_filter.mp hxL
    obtain ⟨hxU, hxr⟩ := mem_blocksAt.mp hxs
    obtain ⟨i', hi', hi'c⟩ := mem_creatorsOf.mp hxw
    have hi'U : i' ∈ U.ids := U.complete x hxU i' hi'
    have hi'r : (U.block i').round = r := by
      have := U.round_of_mem_refs hxU hi'; omega
    have hib : i' = bw := U.eq_of_creator_eq hi'U hbwU hw_mem hi'c hbw_creator (by rw [hi'r, hbwr])
    exact Finset.mem_inter.mpr ⟨mem_supporters.mpr ⟨x, hxU, hxr, hib ▸ hi', rfl⟩, hxh⟩
  calc (authorsAt U (r + 1)).card + 1
      ≤ g w + q := harith
    _ = (Finset.image (fun x => (U.block x).creator)
          (L.filter (fun x => w ∈ creatorsOf U.block (U.block x).refs))).card + q := by
        rw [Finset.card_image_of_injOn
          (creator_injOn_honestBlocksAt.mono (Finset.coe_subset.mpr (Finset.filter_subset _ _)))]
    _ ≤ _ := Nat.add_le_add_right (Finset.card_le_card hsub) _

omit [DecidableEq BlockId] in
/-- **The common core**: at `2q ≥ n + f + 1`, if a block exists at round
`r + 2`, some honest round-`r` block lies in the history of every block from
round `r + 2` up. -/
theorem exists_commonCore {f r : ℕ} (hf : honestᶜ.card ≤ f)
    (hq2 : Fintype.card Validator + f + 1 ≤ 2 * q) {c₀ : BlockId}
    (hc₀ : c₀ ∈ U.ids) (hc₀r : (U.block c₀).round = r + 2) :
    ∃ b ∈ U.ids, (U.block b).round = r ∧ (U.block b).creator ∈ honest ∧
      ∀ c ∈ U.ids, r + 2 ≤ (U.block c).round → Reaches U c b := by
  classical
  have hp : q ≤ (authorsAt U (r + 1)).card :=
    le_trans (U.creators_quorum hc₀ (by omega))
      (Finset.card_le_card (creators_refs_subset_authorsAt hc₀ (by omega)))
  obtain ⟨b, hb, hbr, hbh, hsup⟩ := exists_honest_common_support hf hq2 hp
  refine ⟨b, hb, hbr, hbh, fun c hc hcr => ?_⟩
  have hbase : ∀ c ∈ U.ids, (U.block c).round = r + 2 → ∃ b', b' = b ∧ Reaches U c b' :=
    fun c hc hcr => ⟨b, rfl, reaches_of_honest_support (b := b) (r := r)
      (S := supporters U b (r + 1) ∩ honest)
      (fun v hv => mem_supporters.mp (Finset.mem_inter.mp hv).1)
      (fun v hv => (Finset.mem_inter.mp hv).2) hsup hc hcr⟩
  obtain ⟨b', rfl, hreach⟩ := reaches_pred_of_round_le (Q := fun b' => b' = b) hbase hc hcr
  exact hreach

end General

/-! ## The core

At the core's quorum `n − f`, `2q ≥ n + f + 1` is `n ≥ 3f + 1`. -/

section Core

variable {Validator : Type*} [Fintype Validator] [DecidableEq Validator]
variable [F : Faults Validator]
variable {BlockId : Type*} {Payload : Type*}
variable {U : BlockUniverse Validator BlockId Payload}

/-- The round-`n` blocks authored by *correct* validators. -/
def correctBlocksAt (U : BlockUniverse Validator BlockId Payload) (n : ℕ) : Finset BlockId :=
  (blocksAt U n).filter (fun q => (U.block q).creator ∈ (Correct : Finset Validator))

/-- Membership in `correctBlocksAt`, unfolded. -/
theorem mem_correctBlocksAt {i : BlockId} {n : ℕ} :
    i ∈ correctBlocksAt U n ↔
      i ∈ U.ids ∧ (U.block i).round = n ∧ (U.block i).creator ∈ (Correct : Finset Validator) := by
  simp [correctBlocksAt, and_assoc]

/-- The core's quorum meets the general count's condition. -/
theorem card_add_f_lt_two_mul_quorum :
    Fintype.card Validator + F.f + 1 ≤ 2 * (quorumCard Validator) := by
  have := F.card_validators; omega

variable [DecidableEq BlockId]

/-- **T3a (Correct-support counting).** Some correct validator's round-`r`
block is backed by enough correct round-`(r+1)` validators to satisfy the
`p - 2f` coverage threshold: the general count at the core's quorum. -/
theorem exists_correct_common_support {r : ℕ}
    (hp : quorumCard Validator ≤ (authorsAt U (r + 1)).card) :
    ∃ bw ∈ U.ids, (U.block bw).round = r ∧
      (U.block bw).creator ∈ (Correct : Finset Validator) ∧
      (authorsAt U (r + 1)).card + F.f + 1
        ≤ (correctSupporters U bw (r + 1)).card + Fintype.card Validator := by
  obtain ⟨bw, hb, hbr, hbc, h⟩ :=
    exists_honest_common_support card_compl_correct_le card_add_f_lt_two_mul_quorum hp
  have := F.card_validators
  exact ⟨bw, hb, hbr, hbc, by unfold correctSupporters; omega⟩

omit [DecidableEq BlockId] in
/-- **T3c (Common correct ancestor).** If any block exists at round `r+2`,
some correct validator's round-`r` block lies in the causal history of
*every* round-`(r+2)` block: the general common core at the core's
quorum. -/
theorem exists_common_correct_ancestor {r : ℕ} {c₀ : BlockId}
    (hc₀ : c₀ ∈ U.ids) (hc₀r : (U.block c₀).round = r + 2) :
    ∃ bw ∈ U.ids, (U.block bw).round = r ∧
      (U.block bw).creator ∈ (Correct : Finset Validator) ∧
      ∀ c ∈ U.ids, (U.block c).round = r + 2 → Reaches U c bw := by
  classical
  obtain ⟨b, hb, hbr, hbc, h⟩ :=
    exists_commonCore card_compl_correct_le card_add_f_lt_two_mul_quorum hc₀ hc₀r
  exact ⟨b, hb, hbr, hbc, fun c hc hcr => h c hc hcr.ge⟩

end Core

end LeanDag
