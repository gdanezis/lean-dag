import LeanDag.KPartialSparse.Avail.Proof
import LeanDag.KPartialSparse.Agreement.Proof
import LeanDag.KPartialSparse.Node.Proof
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
With one slot a round, the schedule and record are disciplined, and at
Mysticeti's row the full view commits slot `2` directly; by Theorem 2 every
view that decides slot `2` decides it alike. A node holding only the
round-`4` blocks commits slot `2`, and by Theorem 3 every node agrees.
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
  Avail.holds.2.1 (Fin 4) Id (Finset Id) wU 6 3 (bid 5 2) (by decide) wChecks
    ⟨bid 6 0, by decide, by decide, by decide⟩

/-! ## The commit rule -/

/-- One slot a round, led by the round's leader. -/
instance wSlots : Slots (Fin 4) := Slots.identity lead

theorem wTruthful : Truthful wU 3 := fun C hC _ L hL => wCertified C hC L hL

theorem wDisciplined : Disciplined 6 3 wSlots wU :=
  ⟨fun _ => Finset.mem_singleton.mpr rfl, wChains, wChecks, wTruthful⟩

/-- Mysticeti at `n = 4`, `f = 1`: a row, and the spreading condition holds. -/
theorem wRow : KPartialSparse.Row (Fin 4) (Scheme.Params.mysticeti 4 1) ∧ Spread (Fin 4) :=
  Agreement.rows (Fin 4) |>.1 rfl

/-- **Theorem 2 at work**: the full view commits slot `2` directly, and every
view that decides slot `2` decides it alike. -/
theorem wCommits : (sRule (Scheme.Params.mysticeti 4 1) 6).Decided (S := wSlots) wU (View.full wU)
    2 (some (bid 2 2)) :=
  AnchoredRule.Decided.directCommit ⟨by decide, rfl, rfl⟩ (by decide)

theorem wAgrees (V : wU.View) (v : Option Id)
    (h : (sRule (Scheme.Params.mysticeti 4 1) 6).Decided (S := wSlots) wU V 2 v) :
    v = some (bid 2 2) :=
  (Agreement.agrees (Fin 4) Id (Finset Id) (Scheme.Params.mysticeti 4 1) wU 6 V (View.full wU) 2
    v _ wRow.1 wRow.2 le_rfl wDisciplined h wCommits)

/-! ## What a node reads -/

/-- The three round-`4` blocks. -/
def wHeld : Finset Id := {bid 4 0, bid 4 1, bid 4 2}

/-- **Theorem 3 at work**: a node holding only the three round-`4` blocks
commits slot `2` directly, and every node holding blocks of the record that
decides slot `2` decides it alike. -/
theorem wNodeCommits :
    NodeDecided (S := wSlots) (Scheme.Params.mysticeti 4 1) wU 6 wHeld 2 (some (bid 2 2)) :=
  NodeDecided.directCommit ⟨by decide, rfl, rfl⟩ (by decide)

theorem wNodeAgrees (H : Finset Id) (hH : H ⊆ wU.ids) (v : Option Id)
    (h : NodeDecided (S := wSlots) (Scheme.Params.mysticeti 4 1) wU 6 H 2 v) :
    v = some (bid 2 2) :=
  (Node.agrees (Fin 4) Id (Finset Id) (Scheme.Params.mysticeti 4 1) wU 6 H wHeld 2 v _ wRow.1
    wRow.2 le_rfl wDisciplined hH (by decide) h wNodeCommits)

/-- Every correct node checks claims on what it holds: holding the whole
record backs every claim. -/
theorem wBuildsChecked : BuildsChecked wU 6 3 := by
  have h : ∀ z ∈ wIds, (∀ L ∈ claimsOf wU z, Backs wU 3 wIds L) ∧
      ∀ m ∈ (wU.block z).refs, ∀ X ∈ wIds, ∀ L ∈ claimsOf wU X, Backs wU 3 wIds L := by
    unfold Backs; decide
  intro z hz _
  refine ⟨wIds, subset_rfl, (h z hz).1, fun m hm => ⟨?_, fun X hX => ?_⟩⟩
  · exact KPartialSparse.historyUpto_subset_ids (U := wU) 6 (wU.complete z hz m hm)
  · exact (h z hz).2 m hm X (KPartialSparse.historyUpto_subset_ids (U := wU) 6
      (wU.complete z hz m hm) hX)

end KPartialSparse

end LeanDagTest
