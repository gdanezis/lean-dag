import LeanDag.Common.Bypass
/-!
# The mass of a window

`docs/sync-auth.md` §8. A node that keeps no block at or below a horizon
`h`, and fetches above it only the histories of the blocks it takes as
tops, holds a bounded number of blocks in each round above `h` once its
tops lie within `W` rounds of `h`. The bound does not depend on how far
below `h` an attacker dates its blocks.

* **The depth bound** (`card_depthBlocks_le`): the blocks of a block's
  history `k` rounds below it number at most `n ^ k`, since a block
  references at most one block of each author, one round below.
* **The window bound** (`card_window_le`): if every held block above `h`
  lies in the history of a top, every top lies at most `W` rounds above
  `h`, and each round holds at most `B` tops, each round above `h` holds
  at most `B · Σ_{k < W} n ^ k` held blocks.
* **The tops** (`card_tops_le`): at most one top of each author in a
  round, or two for an author in `D`, are at most `n + |D|` tops a round.
* **The bound** (`card_window_le_of_tops`): the two together give at most
  `(n + |D|) · Σ_{k < W} n ^ k` held blocks in each round above `h`.
-/

namespace LeanDag

variable {Validator : Type*} [DecidableEq Validator]
variable {BlockId : Type*} [DecidableEq BlockId] {Payload : Type*}
variable {P : Validity Validator BlockId Payload} {honest : Finset Validator}
variable {U : BlockRecord Validator BlockId Payload P honest}

open scoped Classical in
/-- The blocks of `t`'s history `k` rounds below it. -/
noncomputable def depthBlocks (U : BlockRecord Validator BlockId Payload P honest)
    (t : BlockId) (k : ℕ) : Finset BlockId :=
  U.ids.filter fun x => Reaches U t x ∧ (U.block x).round + k = (U.block t).round

omit [DecidableEq Validator] [DecidableEq BlockId] in
theorem mem_depthBlocks {t x : BlockId} {k : ℕ} :
    x ∈ depthBlocks U t k ↔
      x ∈ U.ids ∧ Reaches U t x ∧ (U.block x).round + k = (U.block t).round := by
  classical
  simp [depthBlocks]

omit [DecidableEq BlockId] in
/-- A block's history at its own round is the block alone. -/
theorem depthBlocks_zero_subset [P.Mechanised] {t : BlockId} (ht : t ∈ U.ids) :
    depthBlocks U t 0 ⊆ {t} := by
  intro x hx
  obtain ⟨-, hr, hround⟩ := mem_depthBlocks.mp hx
  rcases Relation.ReflTransGen.cases_head hr with rfl | ⟨j, hj, hjx⟩
  · exact Finset.mem_singleton_self _
  · have hjU := U.complete t ht j hj
    have hle := round_le_of_reaches hjU hjx
    have hpred := Validity.Mechanised.pred U.block (U.block t) (U.valid t ht) j hj
    omega

omit [DecidableEq Validator] in
/-- The history `k + 1` rounds below `t` is the history `k` rounds below
its references. -/
theorem depthBlocks_succ_subset [P.Mechanised] {t : BlockId} (ht : t ∈ U.ids) (k : ℕ) :
    depthBlocks U t (k + 1) ⊆ (U.block t).refs.biUnion fun j => depthBlocks U j k := by
  classical
  intro x hx
  obtain ⟨hxU, hr, hround⟩ := mem_depthBlocks.mp hx
  rcases Relation.ReflTransGen.cases_head hr with rfl | ⟨j, hj, hjx⟩
  · omega
  · have hpred := Validity.Mechanised.pred U.block (U.block t) (U.valid t ht) j hj
    exact Finset.mem_biUnion.mpr ⟨j, hj, mem_depthBlocks.mpr ⟨hxU, hjx, by omega⟩⟩

/-- **The depth bound**: the blocks of `t`'s history `k` rounds below it
number at most `n ^ k`. -/
theorem card_depthBlocks_le [Fintype Validator] [P.Mechanised] [P.Distinct] (k : ℕ) :
    ∀ {t : BlockId}, t ∈ U.ids → (depthBlocks U t k).card ≤ Fintype.card Validator ^ k := by
  induction k with
  | zero =>
    intro t ht
    simpa using Finset.card_le_card (depthBlocks_zero_subset ht)
  | succ k ih =>
    intro t ht
    calc (depthBlocks U t (k + 1)).card
        ≤ ((U.block t).refs.biUnion fun j => depthBlocks U j k).card :=
          Finset.card_le_card (depthBlocks_succ_subset ht k)
      _ ≤ ∑ j ∈ (U.block t).refs, (depthBlocks U j k).card := Finset.card_biUnion_le
      _ ≤ ∑ _j ∈ (U.block t).refs, Fintype.card Validator ^ k :=
          Finset.sum_le_sum fun j hj => ih (U.complete t ht j hj)
      _ = (U.block t).refs.card * Fintype.card Validator ^ k := by
          rw [Finset.sum_const, smul_eq_mul]
      _ ≤ Fintype.card Validator * Fintype.card Validator ^ k :=
          Nat.mul_le_mul_right _ (card_refs_le_univ ht)
      _ = Fintype.card Validator ^ (k + 1) := by rw [pow_succ, Nat.mul_comm]

/-- **The window bound**: held blocks above `h` lie in the histories of
tops at most `W` rounds above `h`, at most `B` in a round; then each round
above `h` holds at most `B · Σ_{k < W} n ^ k` of them. -/
theorem card_window_le [Fintype Validator] [P.Mechanised] [P.Distinct]
    {S V : Finset BlockId} {h W B ρ : ℕ} (hS : S ⊆ U.ids)
    (hV : ∀ x ∈ V, h < (U.block x).round → ∃ t ∈ S, Reaches U t x)
    (hW : ∀ t ∈ S, (U.block t).round ≤ h + W)
    (hB : ∀ r, (S.filter fun t => (U.block t).round = r).card ≤ B) (hρ : h < ρ) :
    (V.filter fun x => (U.block x).round = ρ).card ≤
      B * ∑ k ∈ Finset.range W, Fintype.card Validator ^ k := by
  classical
  set top : ℕ → Finset BlockId := fun k => S.filter fun t => (U.block t).round = ρ + k
  have hsub : V.filter (fun x => (U.block x).round = ρ) ⊆
      (Finset.range W).biUnion fun k => (top k).biUnion fun t => depthBlocks U t k := by
    intro x hx
    obtain ⟨hxV, hxr⟩ := Finset.mem_filter.mp hx
    obtain ⟨t, htS, htx⟩ := hV x hxV (hxr ▸ hρ)
    have htU := hS htS
    have hxU := mem_ids_of_reaches htU htx
    have hle := round_le_of_reaches htU htx
    have htW := hW t htS
    refine Finset.mem_biUnion.mpr ⟨(U.block t).round - ρ, Finset.mem_range.mpr (by omega), ?_⟩
    exact Finset.mem_biUnion.mpr ⟨t, Finset.mem_filter.mpr ⟨htS, by omega⟩,
      mem_depthBlocks.mpr ⟨hxU, htx, by omega⟩⟩
  calc _ ≤ _ := Finset.card_le_card hsub
    _ ≤ ∑ k ∈ Finset.range W, ((top k).biUnion fun t => depthBlocks U t k).card :=
        Finset.card_biUnion_le
    _ ≤ ∑ k ∈ Finset.range W, B * Fintype.card Validator ^ k := by
        refine Finset.sum_le_sum fun k _ => ?_
        calc _ ≤ ∑ t ∈ top k, (depthBlocks U t k).card := Finset.card_biUnion_le
          _ ≤ ∑ _t ∈ top k, Fintype.card Validator ^ k :=
              Finset.sum_le_sum fun t ht =>
                card_depthBlocks_le k (hS (Finset.mem_filter.mp ht).1)
          _ = (top k).card * Fintype.card Validator ^ k := by
              rw [Finset.sum_const, smul_eq_mul]
          _ ≤ _ := Nat.mul_le_mul_right _ (hB (ρ + k))
    _ = _ := by rw [Finset.mul_sum]

omit [DecidableEq BlockId] in
/-- **The tops**: at most one top of each author in a round, or two for an
author in `D`, are at most `n + |D|` tops a round. -/
theorem card_tops_le [Fintype Validator] {S : Finset BlockId} {D : Finset Validator} {r : ℕ}
    (hS : ∀ a, (S.filter fun t => (U.block t).creator = a ∧ (U.block t).round = r).card ≤
      if a ∈ D then 2 else 1) :
    (S.filter fun t => (U.block t).round = r).card ≤ Fintype.card Validator + D.card := by
  classical
  have hsub : S.filter (fun t => (U.block t).round = r) ⊆
      Finset.univ.biUnion fun a =>
        S.filter fun t => (U.block t).creator = a ∧ (U.block t).round = r := by
    intro t ht
    obtain ⟨htS, htr⟩ := Finset.mem_filter.mp ht
    exact Finset.mem_biUnion.mpr ⟨(U.block t).creator, Finset.mem_univ _,
      Finset.mem_filter.mpr ⟨htS, rfl, htr⟩⟩
  calc _ ≤ _ := Finset.card_le_card hsub
    _ ≤ ∑ a, (S.filter fun t => (U.block t).creator = a ∧ (U.block t).round = r).card :=
        Finset.card_biUnion_le
    _ ≤ ∑ a : Validator, (if a ∈ D then 2 else 1) := Finset.sum_le_sum fun a _ => hS a
    _ = ∑ a : Validator, (1 + if a ∈ D then 1 else 0) :=
        Finset.sum_congr rfl fun a _ => by split_ifs <;> rfl
    _ = Fintype.card Validator + D.card := by
        rw [Finset.sum_add_distrib, Finset.sum_boole]
        simp

/-- **The bound**: under the premises of `card_window_le`, with at most one
top of each author in a round, or two for an author in `D`, each round
above `h` holds at most `(n + |D|) · Σ_{k < W} n ^ k` held blocks. -/
theorem card_window_le_of_tops [Fintype Validator] [P.Mechanised] [P.Distinct]
    {S V : Finset BlockId} {D : Finset Validator} {h W ρ : ℕ} (hS : S ⊆ U.ids)
    (hV : ∀ x ∈ V, h < (U.block x).round → ∃ t ∈ S, Reaches U t x)
    (hW : ∀ t ∈ S, (U.block t).round ≤ h + W)
    (hA : ∀ a r, (S.filter fun t => (U.block t).creator = a ∧ (U.block t).round = r).card ≤
      if a ∈ D then 2 else 1) (hρ : h < ρ) :
    (V.filter fun x => (U.block x).round = ρ).card ≤
      (Fintype.card Validator + D.card) * ∑ k ∈ Finset.range W, Fintype.card Validator ^ k :=
  card_window_le hS hV hW (fun r => card_tops_le (hA · r)) hρ

end LeanDag
