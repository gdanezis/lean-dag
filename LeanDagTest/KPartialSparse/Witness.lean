import LeanDag.KPartialSparse.Avail.Proof
/-!
# Sparse K-partial DAG — a witness

Four validators, of which `3` is Byzantine and silent, `f = 1`, no crashes,
rounds `0` to `6`, and validator `r % 3` leading round `r`. Block `4r + v` is
validator `v`'s block of round `r`. A leader's block
references the three blocks one round below; every other block references
its author's block and the leader's block one round below, and is sparse.
From round `2` up a block claims the leader block two rounds below, which
every block one round below references. The record meets every premise of
Theorem 1 at `K = 6`, and `Avail.Linked` applies to the claims at round `4`.
-/

namespace LeanDagTest

namespace KPartialSparse

open LeanDag LeanDag.KPartialDag LeanDag.KPartialSparse

instance wFaults : Faults (Fin 4) where
  f := 1
  byzantine := {3}
  card_validators := by decide
  card_byzantine := by decide

/-- No validator crashes for good. -/
instance wCrashes : Crashes (Fin 4) := ⟨0, by decide⟩

/-- The leader of round `r`. -/
def lead (r : ℕ) : Fin 4 := ⟨r % 3, by omega⟩

instance wLeaders : Leaders (Fin 4) := ⟨fun r => {lead r}⟩

/-- Block `4r + v` is validator `v`'s block of round `r`. -/
abbrev Id := ℕ

/-- The block of validator `v` at round `r`. -/
def bid (r : ℕ) (v : Fin 4) : Id := 4 * r + v.val

instance : ClaimFormat Id (Finset Id) := ⟨id⟩

/-- Block `bid r v`: a leader's block references the correct blocks one round
below; any other block references its own and the leader's block one round
below. From round `2` up it claims the leader block two rounds below. -/
def wBlock (b : Id) : Block (Fin 4) Id (Finset Id) :=
  let r := b / 4
  let v : Fin 4 := ⟨b % 4, Nat.mod_lt _ (by omega)⟩
  ⟨r, v,
    if r = 0 then ∅
    else if v = lead r then ({0, 1, 2} : Finset (Fin 4)).image fun w => bid (r - 1) w
    else {bid (r - 1) v, bid (r - 1) (lead (r - 1))},
    if 2 ≤ r then {bid (r - 2) (lead (r - 2))} else ∅⟩

/-- The blocks of the correct validators at rounds `0` to `6`. -/
def wIds : Finset Id := (Finset.range 28).filter fun b => b % 4 ≠ 3

theorem wComplete : ∀ i ∈ wIds, ∀ j ∈ (wBlock i).refs, j ∈ wIds := by decide

theorem wValid : ∀ i ∈ wIds, SValid (Fin 4) Id (Finset Id) wBlock (wBlock i) := by
  have h₁ : ∀ i ∈ wIds, ∀ j ∈ (wBlock i).refs, (wBlock j).round < (wBlock i).round := by decide
  have h₂ : ∀ i ∈ wIds, ∀ j ∈ (wBlock i).refs, (wBlock j).creator ≠ (wBlock i).creator →
      (wBlock j).round + 1 = (wBlock i).round := by decide
  have h₃ : ∀ i ∈ wIds, ∀ j ∈ (wBlock i).refs, ∀ k ∈ (wBlock i).refs,
      (wBlock j).creator = (wBlock k).creator → j = k := by decide
  have h₄ : ∀ i ∈ wIds, 0 < (wBlock i).round →
      Dense (kQuorum (Fin 4)) wBlock (wBlock i) ∨ Sparse wBlock (wBlock i) := by decide
  have h₅ : ∀ i ∈ wIds, 0 < (wBlock i).round →
      (wBlock i).creator ∈ Leaders.leaders (wBlock i).round →
      Dense (kQuorum (Fin 4)) wBlock (wBlock i) := by decide
  exact fun i hi => ⟨h₁ i hi, h₂ i hi, h₃ i hi, h₄ i hi, h₅ i hi⟩

theorem wNoEquivocation : ∀ i ∈ wIds, ∀ j ∈ wIds,
    (wBlock i).creator ∈ (Correct : Finset (Fin 4)) → (wBlock i).creator = (wBlock j).creator →
    (wBlock i).round = (wBlock j).round → i = j := by decide

/-- The witness record. -/
def wU : SRecord (Fin 4) Id (Finset Id) where
  ids := wIds
  block := wBlock
  complete := wComplete
  valid := wValid
  no_equivocation := wNoEquivocation

theorem wSpread : Spread (Fin 4) := by unfold Spread; decide

theorem wChains : Chains wU := by
  unfold Chains; decide

/-- Every claim of the record names a block certified at threshold `3`. -/
theorem wCertified : ∀ X ∈ wU.ids, ∀ L ∈ claimsOf wU X, Certified wU 3 L := by
  unfold Certified; decide

theorem wChecks : Checks wU 6 3 := by
  intro z hz _ m hm X hX L hL
  have hm' : m ∈ wU.ids := wU.complete z hz m hm
  have hX' : X ∈ wU.ids := KPartialSparse.historyUpto_subset_ids (U := wU) 6 hm' hX
  exact wCertified X hX' L hL

/-- **Theorem 1, linked**: below the leader block of round `5`, the sub-DAG
holds a round-`4` claim for the leader block of round `2`. -/
theorem wLinked : ∃ C ∈ Avail wU 6 (bid 5 2), (wU.block C).round = 2 + 2 ∧
    bid 2 2 ∈ claimsOf wU C :=
  Avail.holds.1 (Fin 4) Id (Finset Id) wU 6 3 2 (bid 5 2) (bid 2 2) wSpread le_rfl wChains
    (by decide) (by decide) (by decide) (by decide) (by decide)

/-- **Theorem 1, backed**: the round-`6` block of validator `0` references the
leader block of round `5`, so every claim below it is certified. -/
theorem wBacked : ∀ X ∈ Avail wU 6 (bid 5 2), ∀ L ∈ claimsOf wU X, Certified wU 3 L :=
  Avail.holds.2 (Fin 4) Id (Finset Id) wU 6 3 (bid 5 2) (by decide) wChecks
    ⟨bid 6 0, by decide, by decide, by decide⟩

end KPartialSparse

end LeanDagTest
