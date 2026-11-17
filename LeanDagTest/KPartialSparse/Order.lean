import LeanDagTest.KPartialSparse.Timed
import LeanDag.KPartialSparse.Order.Proof
/-!
# Sparse K-partial DAG — an order witness

On the record of `Witness.lean`, leader blocks reference every correct block
one round below, so leaders of the correct validators cover them. A node
holding the record decides slots `0` to `4`; by Theorem 6 validator `0`'s
round-`1` block enters its ledger, with outputs `D = 1` round deep.
-/

namespace LeanDagTest

namespace KPartialSparse

open LeanDag LeanDag.KPartialSparse
open scoped LeanDag.KPartialDag

/-- Leaders of the correct validators cover them over rounds `0` to `6`. -/
theorem wCovers : CoversFrom (S := wSlots) wU wT 0 6 := by
  intro k _ hk _ L hL y hy hyT hyr
  have hsr : wSlots.slotRound k = k := rfl
  rw [hsr] at hk hyr
  have hLe : L = bid k (lead k) := isLeaderBlock_unique_of_honest (S := wSlots) (U := wU)
    (lead_mem _ |> wT_correct) hL (isLeader_bid k hk)
  have key : ∀ y : ℕ, y ∈ wIds → (wBlock y).creator ∈ wT → y / 4 + 1 ≤ 6 →
      y ∈ (wBlock (bid (y / 4 + 1) (lead (y / 4 + 1)))).refs := by decide
  change (wBlock y).round + 1 = k at hyr
  rw [round_wBlock] at hyr
  rw [hLe, ← hyr]
  exact key y hy hyT (by omega)

/-- The record is synchronous among the correct validators up to any round to
`6`. -/
theorem wSync_le {N : ℕ} (hN : N ≤ 6) : SyncFrom (S := wSlots) wU wT 0 N :=
  ⟨wSync.1, fun r h1 h2 => wSync.2.1 r h1 (by omega),
    fun k h1 h2 => wSync.2.2.1 k h1 (by omega), fun k h1 h2 => wSync.2.2.2 k h1 (by omega)⟩

/-- A node holding the record, with its verdicts on slots `0` to `4`. -/
noncomputable def wVerdict (k : ℕ) : Option ℕ :=
  if h : k < 5 then (wDecides k h).choose else none

theorem wVerdict_spec (k : ℕ) (hk : k < 5) :
    NodeDecided (S := wSlots) (Scheme.Params.mysticeti 4 1) wU 6 wIds k (wVerdict k) := by
  unfold wVerdict
  rw [dif_pos hk]
  exact (wDecides k hk).choose_spec

/-- **Theorem 6 at work**: validator `0`'s round-`1` block enters the ledger of
a node holding the record after slots `0` to `4`. -/
theorem wIncluded : bid 1 0 ∈ LedgerIn wU 6 wIds 1 wVerdict 5 := by
  have hround : (wU.block (bid 1 0)).round = 1 := by
    change (wBlock (bid 1 0)).round = 1; rw [round_wBlock, bid_div]
  have hsr : ∀ k, wSlots.slotRound k = k := fun _ => rfl
  refine Order.included (Fin 4) ℕ (Finset ℕ) (Scheme.Params.mysticeti 4 1) wU 6 1 wIds wT 0
    wVerdict 5 (bid 1 0) wRow.1 (Or.inl ⟨wRow.2, le_rfl⟩) wDisciplined wLive wT_correct
    (by omega) subset_rfl (fun r => ⟨r + 1, by rw [hsr]; omega, by rw [hsr], lead_mem _⟩)
    wVerdict_spec ?_ (by decide) (by decide) (Nat.zero_le _) ?_ ?_ ?_ (fun z hz => hz.1)
  · intro k L hk hL
    have hLi : L ∈ wU.ids := (hL ▸ wVerdict_spec k hk).isLeaderBlock.1
    exact fetchedIn_of_subset fun y d hy =>
      KPartialSparse.historyUpto_subset_ids _ (hy.mem hLi)
  · intro k hk
    rw [hsr, hround] at hk
    omega
  · rw [hround]
    exact wSync_le (by omega)
  · intro k h1 h2 h3
    rw [hround] at h2
    exact wCovers k h1 (by rw [hsr] at h2 ⊢; omega) h3

end KPartialSparse

end LeanDagTest
