import LeanDag.RedSnapper.Helpers.CausalHistory

/-!
# The chain of a correct validator

Generated: the consequences of `Universe.self_parent`,
`no_equivocation` and `predecessor` for a correct author — its blocks
reach every own block at a lower round, any two of them are comparable,
and reachability between distinct blocks is strict in rounds. What the
docstring of `Model/Universe.lean` promises, proved. Nothing here is
part of the audit surface.
-/

namespace LeanDag

namespace RedSnapper

variable {Validator BlockId Tx Obj : Type*} [Fintype Validator] [DecidableEq Validator]
  [F : Faults Validator] {U : Universe Validator BlockId Tx Obj}

/-- Reachability between distinct blocks descends strictly in rounds. -/
theorem round_lt_of_reaches_ne {b p : BlockId} (hb : b ∈ U.ids)
    (h : Reaches U b p) (hne : p ≠ b) : (U.block p).round < (U.block b).round := by
  rcases h.cases_head with rfl | ⟨j, hstep, hreach⟩
  · exact absurd rfl hne
  · have hj : j ∈ U.ids := U.complete b hb j hstep
    have h1 := round_of_mem_parents hb hstep
    have h2 := round_le_of_reaches hj hreach
    omega

/-- A correct author's block reaches its own block at every round at most
its own. -/
theorem reaches_own_of_round_le {b p : BlockId} (hb : b ∈ U.ids) (hp : p ∈ U.ids)
    (hc : (U.block b).author ∈ (Correct : Finset Validator))
    (ha : (U.block p).author = (U.block b).author)
    (hr : (U.block p).round ≤ (U.block b).round) : Reaches U b p := by
  obtain ⟨n, hn⟩ : ∃ n, (U.block b).round = n := ⟨_, rfl⟩
  induction n using Nat.strong_induction_on generalizing b with
  | _ n ih =>
      subst hn
      by_cases heq : (U.block p).round = (U.block b).round
      · have : p = b := U.no_equivocation p hp b hb (ha ▸ hc) ha heq
        exact this ▸ Reaches.refl
      · have hpos : 0 < (U.block b).round := by omega
        obtain ⟨j, hj, haj⟩ := U.self_parent b hb hc hpos
        have hjid : j ∈ U.ids := U.complete b hb j hj
        have hjr := round_of_mem_parents hb hj
        have : Reaches U j p :=
          ih (U.block j).round (by omega) hjid (haj ▸ hc) (ha.trans haj.symm)
            (by omega) rfl
        exact Reaches.of_mem_parents hj this

/-- A correct author's block has an own reachable block at every round
at most its own — the no-gap consequence of the self-parent chain. -/
theorem exists_own_block_of_le {b : BlockId} {m : ℕ} (hb : b ∈ U.ids)
    (hc : (U.block b).author ∈ (Correct : Finset Validator))
    (hm : m ≤ (U.block b).round) :
    ∃ p, p ∈ U.ids ∧ (U.block p).author = (U.block b).author ∧
      (U.block p).round = m ∧ Reaches U b p := by
  obtain ⟨n, hn⟩ : ∃ n, (U.block b).round = n := ⟨_, rfl⟩
  induction n using Nat.strong_induction_on generalizing b with
  | _ n ih =>
      subst hn
      by_cases heq : (U.block b).round = m
      · exact ⟨b, hb, rfl, heq, Reaches.refl⟩
      · have hpos : 0 < (U.block b).round := by omega
        obtain ⟨j, hj, haj⟩ := U.self_parent b hb hc hpos
        have hjid := U.complete b hb j hj
        have hjr := round_of_mem_parents hb hj
        obtain ⟨p, hp, hap, hrp, hreach⟩ :=
          ih (U.block j).round (by omega) hjid (haj.symm ▸ hc) (by omega) rfl
        exact ⟨p, hp, hap.trans haj, hrp, Reaches.of_mem_parents hj hreach⟩

/-- Two blocks of one correct author are comparable by reachability. -/
theorem own_comparable {b p : BlockId} (hb : b ∈ U.ids) (hp : p ∈ U.ids)
    (hc : (U.block b).author ∈ (Correct : Finset Validator))
    (ha : (U.block p).author = (U.block b).author) :
    Reaches U b p ∨ Reaches U p b := by
  rcases le_total (U.block p).round (U.block b).round with h | h
  · exact Or.inl (reaches_own_of_round_le hb hp hc ha h)
  · exact Or.inr (reaches_own_of_round_le hp hb (ha ▸ hc) ha.symm h)

end RedSnapper

end LeanDag
