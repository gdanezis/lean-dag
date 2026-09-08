import LeanDag.Common.Support
-- Broad import: the counting argument below uses big operators, ordered
-- sums, pigeonhole and `nlinarith`. Narrowing this to specific modules is
-- not worth the churn -- the rest of the library keeps its targeted imports.
import Mathlib

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

variable {Validator : Type*} [Fintype Validator] [DecidableEq Validator]
variable [F : Faults Validator]
variable {BlockId : Type*} {Payload : Type*}
variable {U : BlockUniverse Validator BlockId Payload}

/-- The round-`n` blocks authored by *correct* validators. The counting
argument ranges over these: a correct author has exactly one block per round
(T1), so `creator` is injective here and blocks and authors can be counted
interchangeably. -/
def correctBlocksAt (U : BlockUniverse Validator BlockId Payload) (n : ℕ) : Finset BlockId :=
  (blocksAt U n).filter (fun q => (U.block q).creator ∈ (Correct : Finset Validator))

/-- Membership in `correctBlocksAt`, unfolded. -/
theorem mem_correctBlocksAt {i : BlockId} {n : ℕ} :
    i ∈ correctBlocksAt U n ↔
      i ∈ U.ids ∧ (U.block i).round = n ∧ (U.block i).creator ∈ (Correct : Finset Validator) := by
  simp [correctBlocksAt, and_assoc]

/-- Distinct correct round-`n` blocks have distinct authors — non-equivocation
(T1) in the form the count needs. -/
theorem creator_injOn_correctBlocksAt {n : ℕ} :
    Set.InjOn (fun q => (U.block q).creator) (correctBlocksAt U n) := by
  intro q hq q' hq' h
  obtain ⟨hq_ids, hq_round, hq_corr⟩ := mem_correctBlocksAt.mp hq
  obtain ⟨hq'_ids, hq'_round, _⟩ := mem_correctBlocksAt.mp hq'
  exact U.eq_of_creator_eq hq_ids hq'_ids hq_corr rfl h.symm (by rw [hq_round, hq'_round])

theorem card_creatorsOf_correctBlocksAt {n : ℕ} :
    (creatorsOf U.block (correctBlocksAt U n)).card = (correctBlocksAt U n).card :=
  Finset.card_image_of_injOn creator_injOn_correctBlocksAt

theorem creatorsOf_correctBlocksAt_subset {n : ℕ} :
    creatorsOf U.block (correctBlocksAt U n) ⊆ (Correct : Finset Validator) := by
  intro v hv
  rw [mem_creatorsOf] at hv
  obtain ⟨q, hq, rfl⟩ := hv
  exact (mem_correctBlocksAt.mp hq).2.2

/-- The author pool at round `n` is covered by the correct authors together
with the Byzantine validators, bounding `p` by `l + b`. -/
theorem card_authorsAt_le {n : ℕ} :
    (authorsAt U n).card ≤ (correctBlocksAt U n).card + F.byzantine.card := by
  rw [← card_creatorsOf_correctBlocksAt]
  refine le_trans (Finset.card_le_card ?_) (Finset.card_union_le _ _)
  intro v hv
  rw [mem_authorsAt] at hv
  obtain ⟨i, hi_ids, hi_round, hi_creator⟩ := hv
  by_cases hc : v ∈ (Correct : Finset Validator)
  · refine Finset.mem_union_left _ ?_
    rw [mem_creatorsOf]
    exact ⟨i, mem_correctBlocksAt.mpr ⟨hi_ids, hi_round, hi_creator ▸ hc⟩, hi_creator⟩
  · exact Finset.mem_union_right _ (by simpa using hc)

variable [DecidableEq BlockId]

/-- The arithmetic core of T3a, isolated from the combinatorics.

With `f` the fault bound, `b = |Byzantine|`, `c = |Correct|`, `l` the number
of correct round-`(r+1)` blocks, `k` the largest support degree and `p` the
author-pool size: the double count gives `hA`, and the conclusion is the
`p - 2f` coverage threshold. The contradiction is `c² ≤ f(l+c)`, which `l ≤ c` collapses to
`c ≤ 2f` — impossible, since `b ≤ f` forces `c ≥ 2f+1`. -/
private theorem support_threshold_arith {f b c l k p n : ℕ}
    (hbf : b ≤ f) (hn : 3 * f + 1 ≤ n) (hcb : c + b = n) (hlc : l ≤ c)
    (hA : l * (n - f) ≤ c * k + l * b) (hE : p ≤ l + b) :
    p + f + 1 ≤ k + n := by
  obtain ⟨d, rfl⟩ : ∃ d, n = d + f := ⟨n - f, by omega⟩
  rw [show d + f - f = d from by omega] at hA
  by_contra hcon
  push Not at hcon
  have h1 : k + d ≤ p := by omega
  have h2 : c * (k + d) ≤ c * (l + b) :=
    Nat.mul_le_mul_left c (le_trans h1 hE)
  have hcge : 2 * f + 1 ≤ c := by omega
  have key : c * c ≤ f * (l + c) := by nlinarith [h2, hA]
  nlinarith [key, hlc, hcge]

/-- **T3a (Correct-support counting).** Some correct validator's round-`r`
block is backed by enough correct round-`(r+1)` validators to satisfy the
`p - 2f` coverage threshold.

Double counting: each correct round-`(r+1)` block names at least
`(n-f) - b` correct round-`r` authors, and there are `l` such blocks spread
over `c = n - b` correct validators, so some author `w` collects at least
`l(n-f-b)/c`. The arithmetic obligation reduces to `c² ≤ f(l+c)`, which
`l ≤ c` turns into `c ≤ 2f` — impossible, since `b ≤ f` and `n ≥ 3f+1`
force `c ≥ 2f+1`. The same contradiction as at `n = 3f+1`, verbatim. -/
theorem exists_correct_common_support {r : ℕ}
    (hp : quorumCard Validator ≤ (authorsAt U (r + 1)).card) :
    ∃ bw ∈ U.ids, (U.block bw).round = r ∧
      (U.block bw).creator ∈ (Correct : Finset Validator) ∧
      (authorsAt U (r + 1)).card + F.f + 1
        ≤ (correctSupporters U bw (r + 1)).card + Fintype.card Validator := by
  classical
  -- Derive the ambient cardinality facts *before* abbreviating, so that
  -- `set` rewrites them too; otherwise `omega` sees `Correct.card` and
  -- `C.card` as unrelated atoms.
  obtain ⟨hcb, hbf, hnv⟩ := faults_arith (Validator := Validator)
  have hE := card_authorsAt_le (U := U) (n := r + 1)
  have hlc : (correctBlocksAt U (r + 1)).card ≤ (Correct : Finset Validator).card := by
    rw [← card_creatorsOf_correctBlocksAt]
    exact Finset.card_le_card creatorsOf_correctBlocksAt_subset
  set L := correctBlocksAt U (r + 1) with hLdef
  set C := (Correct : Finset Validator) with hCdef
  set g : Validator → ℕ :=
    fun w => (L.filter (fun q => w ∈ creatorsOf U.block (U.block q).refs)).card with hgdef
  -- Each correct round-(r+1) block names n−f validators, at most b Byzantine.
  have hper : ∀ q ∈ L,
      quorumCard Validator ≤ ((creatorsOf U.block (U.block q).refs) ∩ C).card + F.byzantine.card := by
    intro q hq
    obtain ⟨hq_ids, hq_round, _⟩ := mem_correctBlocksAt.mp hq
    exact le_trans (U.creators_quorum hq_ids (by omega))
      (card_le_card_inter_correct_add_byzantine _)
  -- Pick a correct author of maximum support degree.
  have hC_ne : C.Nonempty := by
    rw [← Finset.card_pos]; omega
  obtain ⟨w, hw_mem, hw_max⟩ := C.exists_max_image g hC_ne
  -- **Double counting** (`Finset.card_nsmul_le_card_nsmul`): each correct
  -- round-(r+1) block contributes at least `2f+1 - b` incidences, and each
  -- correct author absorbs at most `g w`.
  have hbig : L.card * (quorumCard Validator - F.byzantine.card) ≤ C.card * g w := by
    have := Finset.card_nsmul_le_card_nsmul
      (r := fun (q : BlockId) (v : Validator) => v ∈ creatorsOf U.block (U.block q).refs)
      (s := L) (t := C)
      (m := quorumCard Validator - F.byzantine.card) (n := g w)
      (fun q hq => by
        have h := hper q hq
        -- `bipartiteAbove` is by definition the filter, so `change` retypes it.
        change quorumCard Validator - F.byzantine.card
            ≤ (C.filter (fun v => v ∈ creatorsOf U.block (U.block q).refs)).card
        rw [Finset.filter_mem_eq_inter, Finset.inter_comm]
        omega)
      (fun v hv => hw_max v hv)
    simpa [smul_eq_mul] using this
  have hb_le : F.byzantine.card ≤ quorumCard Validator := by omega
  have hA : L.card * (quorumCard Validator) ≤ C.card * g w + L.card * F.byzantine.card := by
    have hsplit : L.card * (quorumCard Validator)
        = L.card * (quorumCard Validator - F.byzantine.card) + L.card * F.byzantine.card := by
      rw [← Nat.mul_add, Nat.sub_add_cancel hb_le]
    omega
  -- The arithmetic core: p ≤ (max degree) + 2f.
  have harith : (authorsAt U (r + 1)).card + F.f + 1 ≤ g w + Fintype.card Validator :=
    support_threshold_arith hbf hnv hcb hlc hA hE
  -- The maximiser has positive degree, so it really does author a round-r block.
  have hgw_pos : 0 < g w := by omega
  obtain ⟨q₀, hq₀⟩ := Finset.card_pos.mp hgw_pos
  rw [Finset.mem_filter] at hq₀
  obtain ⟨hq₀L, hq₀w⟩ := hq₀
  obtain ⟨hq₀_ids, hq₀_round, _⟩ := mem_correctBlocksAt.mp hq₀L
  rw [mem_creatorsOf] at hq₀w
  obtain ⟨bw, hbw_mem, hbw_creator⟩ := hq₀w
  have hbw_ids : bw ∈ U.ids := U.complete _ hq₀_ids _ hbw_mem
  have hbw_round : (U.block bw).round = r := by
    have := U.round_of_mem_refs hq₀_ids hbw_mem; omega
  have hw_correct : w ∈ C := hw_mem
  refine ⟨bw, hbw_ids, hbw_round, hbw_creator ▸ hw_correct, ?_⟩
  -- Every block counted by `g w` references `bw` (T1), and distinct such
  -- blocks have distinct correct authors, so they inject into the support set.
  have hsub : Finset.image (fun q => (U.block q).creator)
      (L.filter (fun q => w ∈ creatorsOf U.block (U.block q).refs))
      ⊆ correctSupporters U bw (r + 1) := by
    intro v hv
    simp only [Finset.mem_image, Finset.mem_filter] at hv
    obtain ⟨q, ⟨hqL, hqw⟩, rfl⟩ := hv
    obtain ⟨hq_ids, hq_round, hq_corr⟩ := mem_correctBlocksAt.mp hqL
    rw [mem_creatorsOf] at hqw
    obtain ⟨i', hi'_mem, hi'_creator⟩ := hqw
    have hi'_ids : i' ∈ U.ids := U.complete q hq_ids i' hi'_mem
    have hi'_round : (U.block i').round = r := by
      have := U.round_of_mem_refs hq_ids hi'_mem; omega
    have hib : i' = bw :=
      U.eq_of_creator_eq hi'_ids hbw_ids hw_correct hi'_creator hbw_creator
        (by rw [hi'_round, hbw_round])
    refine Finset.mem_inter.mpr ⟨?_, hq_corr⟩
    rw [mem_supporters]
    exact ⟨q, hq_ids, hq_round, hib ▸ hi'_mem, rfl⟩
  calc (authorsAt U (r + 1)).card + F.f + 1
      ≤ g w + Fintype.card Validator := harith
    _ = (Finset.image (fun q => (U.block q).creator)
          (L.filter (fun q => w ∈ creatorsOf U.block (U.block q).refs))).card
        + Fintype.card Validator := by
        rw [Finset.card_image_of_injOn
          (creator_injOn_correctBlocksAt.mono (Finset.coe_subset.mpr (Finset.filter_subset _ _)))]
    _ ≤ _ := Nat.add_le_add_right (Finset.card_le_card hsub) _

omit [DecidableEq BlockId] in
/-- **T3c (Common correct ancestor).** If any block exists at round `r+2`,
some correct validator's round-`r` block lies in the causal history of
*every* round-`(r+2)` block.

The only premise is that a round-`(r+2)` block exists — a fact about the DAG
in hand, not an assumption that anyone makes progress. Its own reference
quorum supplies the `2f+1` author bound T3a needs.

Note the statement mentions no `Finset BlockId` operation, so unlike T3a it
does **not** require decidable equality on ids; the proof supplies that
classically. -/
theorem exists_common_correct_ancestor {r : ℕ} {c₀ : BlockId}
    (hc₀ : c₀ ∈ U.ids) (hc₀r : (U.block c₀).round = r + 2) :
    ∃ bw ∈ U.ids, (U.block bw).round = r ∧
      (U.block bw).creator ∈ (Correct : Finset Validator) ∧
      ∀ c ∈ U.ids, (U.block c).round = r + 2 → Reaches U c bw := by
  -- The statement mentions no `Finset BlockId` operation, so decidable
  -- equality on ids is an artefact of the proof only.
  classical
  -- A round-(r+2) block names n−f distinct round-(r+1) authors, so the
  -- author pool is at least that large -- exactly T3a's hypothesis.
  have hp : quorumCard Validator ≤ (authorsAt U (r + 1)).card :=
    le_trans (U.creators_quorum hc₀ (by omega))
      (Finset.card_le_card (creators_refs_subset_authorsAt hc₀ (by omega)))
  obtain ⟨bw, hbw_ids, hbw_round, hbw_correct, hbw_support⟩ :=
    exists_correct_common_support (U := U) (r := r) hp
  refine ⟨bw, hbw_ids, hbw_round, hbw_correct, fun c hc hcr => ?_⟩
  refine reaches_of_honest_support (b := bw) (r := r)
    (S := correctSupporters U bw (r + 1)) ?_ (fun _ hv => correctSupporters_correct hv)
    (by have := F.card_validators; omega) hc hcr
  intro v hv
  exact mem_supporters.mp (correctSupporters_subset hv)

end LeanDag
