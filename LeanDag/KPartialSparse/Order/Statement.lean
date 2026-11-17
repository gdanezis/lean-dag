import LeanDag.KPartialSparse.Model.Order
/-!
# Sparse K-partial DAG — the order, statement

`docs/kpartial-sparse.md` §8, Theorem 6: the ledger, the outputs of the
committed leaders ordered by slot and within a slot, is read on what a node
holds, agreed, totally ordered, never retracted and settled; and after
synchrony, with leaders of `T` covering `T`, it includes every block of `T`.

Statements only; the proofs are `Proof.lean`.
-/

namespace LeanDag

namespace KPartialSparse

namespace Order

open KPartialDag (Crashes LiveRow)
open scoped KPartialDag
open Scheme

/-- **A node reads a leader's output on what it holds**, and reads all of it
once it has fetched the sub-DAG down to `D` rounds below the leader. -/
def Local : Prop :=
  ∀ (Validator BlockId Payload : Type) [Fintype Validator] [DecidableEq Validator]
    [Faults Validator] [Crashes Validator] [Leaders Validator] [LinearOrder BlockId]
    (U : SRecord Validator BlockId Payload) (K D : ℕ) (H : Finset BlockId) (L : BlockId),
    H ⊆ U.ids → OutIn U K H D L ⊆ Out U K D L ∧
      (FetchedIn U K H L ((U.block L).round - D) → OutIn U K H D L = Out U K D L)

/-- **Ledgers agree and are never retracted**: at a row and the depth the
sub-DAG needs, on a disciplined schedule and record, what a node outputs after
slots `0, …, n-1`, it and every other node output at the same slot and in the
same order after `n' ≥ n` slots, once each has fetched below the leaders it
committed. -/
def Agrees : Prop :=
  ∀ (Validator BlockId Payload : Type) [Fintype Validator] [DecidableEq Validator]
    [LinearOrder Validator] [Faults Validator] [Crashes Validator] [Leaders Validator]
    [LinearOrder BlockId] [ClaimFormat BlockId Payload] [S : Slots Validator] (p : Params)
    (U : SRecord Validator BlockId Payload) (K D : ℕ) (H₁ H₂ : Finset BlockId)
    (g₁ g₂ : ℕ → Option BlockId) (n n' : ℕ), Row Validator p → Deep Validator K →
    Disciplined K p.certThreshold S U → H₁ ⊆ U.ids → H₂ ⊆ U.ids → n ≤ n' →
    (∀ k, k < n → NodeDecided p U K H₁ k (g₁ k)) →
    (∀ k, k < n' → NodeDecided p U K H₂ k (g₂ k)) →
    (∀ k L, k < n → g₁ k = some L → FetchedIn U K H₁ L ((U.block L).round - D)) →
    (∀ k L, k < n' → g₂ k = some L → FetchedIn U K H₂ L ((U.block L).round - D)) →
    LedgerIn U K H₁ D g₁ n ⊆ LedgerIn U K H₂ D g₂ n' ∧
      (∀ b k, k < n → EntersIn U K H₁ D g₁ b k → EntersIn U K H₂ D g₂ b k) ∧
      ∀ b b', PrecedesIn U K H₁ D g₁ n b b' → PrecedesIn U K H₂ D g₂ n' b b'

/-- **The ledger is a strict total order**, causal within a slot. -/
def Total : Prop :=
  ∀ (Validator BlockId Payload : Type) [Fintype Validator] [DecidableEq Validator]
    [LinearOrder Validator] [Faults Validator] [Crashes Validator] [Leaders Validator]
    [LinearOrder BlockId] (U : SRecord Validator BlockId Payload) (K D : ℕ) (H : Finset BlockId)
    (g : ℕ → Option BlockId) (n : ℕ),
    (∀ b, ¬ PrecedesIn U K H D g n b b) ∧
    (∀ b b' b'', PrecedesIn U K H D g n b b' → PrecedesIn U K H D g n b' b'' →
      PrecedesIn U K H D g n b b'') ∧
    (∀ b ∈ LedgerIn U K H D g n, ∀ b' ∈ LedgerIn U K H D g n, b ≠ b' →
      PrecedesIn U K H D g n b b' ∨ PrecedesIn U K H D g n b' b) ∧
    ∀ b b' k, b ∈ U.ids → b' ∈ (U.block b).refs → k < n → EntersIn U K H D g b k →
      EntersIn U K H D g b' k → PrecedesIn U K H D g n b' b

/-- **A block's fate is settled** once every slot at most `D` rounds above it is
decided: if it is not in the ledger then, it never enters. -/
def Settled : Prop :=
  ∀ (Validator BlockId Payload : Type) [Fintype Validator] [DecidableEq Validator]
    [Faults Validator] [Crashes Validator] [Leaders Validator] [LinearOrder BlockId]
    [ClaimFormat BlockId Payload] [S : Slots Validator] (p : Params)
    (U : SRecord Validator BlockId Payload) (K D : ℕ) (H : Finset BlockId)
    (g : ℕ → Option BlockId) (n n' : ℕ) (b : BlockId),
    (∀ k, k < n' → NodeDecided p U K H k (g k)) →
    (∀ k, S.slotRound k ≤ (U.block b).round + D → k < n) →
    b ∈ LedgerIn U K H D g n' → b ∈ LedgerIn U K H D g n

/-- **A block settled out of one ledger is in none**: at a row and the depth the
sub-DAG needs, on a disciplined schedule and record, a block not in a node's
ledger once the node has decided every slot at most `D` rounds above it is in
no node's ledger, once each has fetched below the leaders it committed. -/
def Excluded : Prop :=
  ∀ (Validator BlockId Payload : Type) [Fintype Validator] [DecidableEq Validator]
    [Faults Validator] [Crashes Validator] [Leaders Validator] [LinearOrder BlockId]
    [ClaimFormat BlockId Payload] [S : Slots Validator] (p : Params)
    (U : SRecord Validator BlockId Payload) (K D : ℕ) (H₁ H₂ : Finset BlockId)
    (g₁ g₂ : ℕ → Option BlockId) (n n' : ℕ) (b : BlockId),
    Row Validator p → Deep Validator K → Disciplined K p.certThreshold S U →
    H₁ ⊆ U.ids → H₂ ⊆ U.ids → (∀ k, k < n → NodeDecided p U K H₁ k (g₁ k)) →
    (∀ k, k < n' → NodeDecided p U K H₂ k (g₂ k)) →
    (∀ k L, k < n → g₁ k = some L → FetchedIn U K H₁ L ((U.block L).round - D)) →
    (∀ k L, k < n' → g₂ k = some L → FetchedIn U K H₂ L ((U.block L).round - D)) →
    (∀ k, S.slotRound k ≤ (U.block b).round + D → k < n) →
    b ∉ LedgerIn U K H₁ D g₁ n → b ∉ LedgerIn U K H₂ D g₂ n'

/-- **A leader of `T` covering `T` outputs every block of `T` at most `D ≤ K`
rounds below it**, from round `R` on, with correct chains and `T` populated. -/
def Outputs : Prop :=
  ∀ (Validator BlockId Payload : Type) [Fintype Validator] [DecidableEq Validator]
    [Faults Validator] [Crashes Validator] [Leaders Validator] [LinearOrder BlockId]
    [S : Slots Validator] (U : SRecord Validator BlockId Payload) (K D : ℕ)
    (T : Finset Validator) (R k : ℕ) (L x : BlockId), T ⊆ (Correct : Finset Validator) →
    Chains U → D ≤ K → IsLeaderBlock U k L → S.leader k ∈ T →
    CoversFrom U T R (S.slotRound k) → (∀ r, R ≤ r → r < S.slotRound k → PopulatedOn U T r) →
    x ∈ U.ids → (U.block x).creator ∈ T → R ≤ (U.block x).round →
    (U.block x).round < S.slotRound k → S.slotRound k ≤ (U.block x).round + D →
    x ∈ Out U K D L

/-- **After synchrony with leaders of `T` covering `T`, every block of `T` enters
the ledger** of a node that has decided every slot at most `D ≤ K` rounds above
it, when every `D` rounds hold a slot led by `T`, at a live row and the depth
the sub-DAG needs, on a disciplined schedule and record. -/
def Included : Prop :=
  ∀ (Validator BlockId Payload : Type) [Fintype Validator] [DecidableEq Validator]
    [Faults Validator] [Crashes Validator] [Leaders Validator] [LinearOrder BlockId]
    [ClaimFormat BlockId Payload] [S : Slots Validator] (p : Params)
    (U : SRecord Validator BlockId Payload) (K D : ℕ) (H : Finset BlockId)
    (T : Finset Validator) (R : ℕ) (g : ℕ → Option BlockId) (n : ℕ) (x : BlockId),
    Row Validator p → Deep Validator K → Disciplined K p.certThreshold S U →
    LiveRow Validator p → T ⊆ (Correct : Finset Validator) → D ≤ K → H ⊆ U.ids →
    (∀ r, ∃ k, r < S.slotRound k ∧ S.slotRound k ≤ r + D ∧ S.leader k ∈ T) →
    (∀ k, k < n → NodeDecided p U K H k (g k)) →
    (∀ k L, k < n → g k = some L → FetchedIn U K H L ((U.block L).round - D)) →
    x ∈ U.ids → (U.block x).creator ∈ T → R ≤ (U.block x).round →
    (∀ k, S.slotRound k ≤ (U.block x).round + D → k < n) →
    SyncFrom U T R ((U.block x).round + D + 2) → CoversFrom U T R ((U.block x).round + D) →
    HeldBy U T ((U.block x).round + 2) ((U.block x).round + D + 2) ⊆ ↑H →
    x ∈ LedgerIn U K H D g n

/-- The order. -/
def Statement : Prop := Local ∧ Agrees ∧ Total ∧ Settled ∧ Excluded ∧ Outputs ∧ Included

end Order

end KPartialSparse

end LeanDag
