import LeanDag.KPartialDag.Model.Order
/-!
# The order — statement

`docs/kpartial.md` §7, Theorem 5: the ledger, the outputs of the committed
leaders ordered by slot and within a slot, is agreed, totally ordered and
never retracted, and after synchrony includes every block of `T`.

Statements only; the proofs are `Proof.lean`.
-/

namespace LeanDag

namespace KPartialDag

namespace Order

/-- **A node reads a leader's output on what it holds**, and reads all of it
once it has fetched the sub-DAG down to `D` rounds below the leader. -/
def Local : Prop :=
  ∀ (Validator BlockId Payload : Type) [Fintype Validator] [DecidableEq Validator]
    [Faults Validator] [Crashes Validator]
    [LinearOrder BlockId] (U : KRecord Validator BlockId Payload)
    (K D : ℕ) (H : Finset BlockId) (L : BlockId), H ⊆ U.ids →
    OutIn U K H D L ⊆ Out U K D L ∧
      (FetchedIn U K H L ((U.block L).round - D) → OutIn U K H D L = Out U K D L)

/-- **Ledgers agree and are never retracted**: at `K ≥ 3`, what a node outputs
after slots `0, …, n-1`, it and every other node output at the same slot and
in the same order after `n' ≥ n` slots, once each has fetched below the
leaders it committed. -/
def Agrees : Prop :=
  ∀ (Validator BlockId Payload : Type) [Fintype Validator] [DecidableEq Validator]
    [LinearOrder Validator] [Faults Validator] [Crashes Validator] [LinearOrder BlockId]
    [Slots Validator] (p : Scheme.Params) (U : KRecord Validator BlockId Payload) (K D : ℕ)
    (H₁ H₂ : Finset BlockId) (g₁ g₂ : ℕ → Option BlockId) (n n' : ℕ), Row Validator p → 3 ≤ K →
    H₁ ⊆ U.ids → H₂ ⊆ U.ids → n ≤ n' → (∀ k, k < n → NodeDecided p U K H₁ k (g₁ k)) →
    (∀ k, k < n' → NodeDecided p U K H₂ k (g₂ k)) →
    (∀ k L, k < n → g₁ k = some L → FetchedIn U K H₁ L ((U.block L).round - D)) →
    (∀ k L, k < n' → g₂ k = some L → FetchedIn U K H₂ L ((U.block L).round - D)) →
    LedgerIn U K H₁ D g₁ n ⊆ LedgerIn U K H₂ D g₂ n' ∧
      (∀ b k, k < n → EntersIn U K H₁ D g₁ b k → EntersIn U K H₂ D g₂ b k) ∧
      ∀ b b', PrecedesIn U K H₁ D g₁ n b b' → PrecedesIn U K H₂ D g₂ n' b b'

/-- **The ledger is a strict total order**, causal within a slot. -/
def Total : Prop :=
  ∀ (Validator BlockId Payload : Type) [Fintype Validator] [DecidableEq Validator]
    [LinearOrder Validator] [Faults Validator] [Crashes Validator] [LinearOrder BlockId]
    (U : KRecord Validator BlockId Payload) (K D : ℕ) (H : Finset BlockId)
    (g : ℕ → Option BlockId) (n : ℕ),
    (∀ b, ¬ PrecedesIn U K H D g n b b) ∧
    (∀ b b' b'', PrecedesIn U K H D g n b b' → PrecedesIn U K H D g n b' b'' →
      PrecedesIn U K H D g n b b'') ∧
    (∀ b ∈ LedgerIn U K H D g n, ∀ b' ∈ LedgerIn U K H D g n, b ≠ b' →
      PrecedesIn U K H D g n b b' ∨ PrecedesIn U K H D g n b' b) ∧
    ∀ b b' k, b ∈ U.ids → b' ∈ (U.block b).refs → k < n → EntersIn U K H D g b k →
      EntersIn U K H D g b' k → PrecedesIn U K H D g n b' b

/-- **A block's fate is settled** once every slot at most `D` rounds above it
is decided: if it is not in the ledger then, it never enters. -/
def Settled : Prop :=
  ∀ (Validator BlockId Payload : Type) [Fintype Validator] [DecidableEq Validator]
    [Faults Validator] [Crashes Validator] [LinearOrder BlockId] [S : Slots Validator]
    (p : Scheme.Params) (U : KRecord Validator BlockId Payload) (K D : ℕ) (H : Finset BlockId)
    (g : ℕ → Option BlockId) (n n' : ℕ) (b : BlockId), Row Validator p → H ⊆ U.ids →
    (∀ k, k < n' → NodeDecided p U K H k (g k)) →
    (∀ k, S.slotRound k ≤ (U.block b).round + D → k < n) →
    b ∈ LedgerIn U K H D g n' → b ∈ LedgerIn U K H D g n

/-- **A block settled out of one ledger is in none**: at `K ≥ 3`, a block not
in a node's ledger once the node has decided every slot at most `D` rounds
above it is in no node's ledger after any number of slots, once each has
fetched below the leaders it committed. -/
def Excluded : Prop :=
  ∀ (Validator BlockId Payload : Type) [Fintype Validator] [DecidableEq Validator]
    [Faults Validator] [Crashes Validator] [LinearOrder BlockId] [S : Slots Validator]
    (p : Scheme.Params) (U : KRecord Validator BlockId Payload) (K D : ℕ)
    (H₁ H₂ : Finset BlockId) (g₁ g₂ : ℕ → Option BlockId) (n n' : ℕ) (b : BlockId),
    Row Validator p → 3 ≤ K →
    H₁ ⊆ U.ids → H₂ ⊆ U.ids → (∀ k, k < n → NodeDecided p U K H₁ k (g₁ k)) →
    (∀ k, k < n' → NodeDecided p U K H₂ k (g₂ k)) →
    (∀ k L, k < n → g₁ k = some L → FetchedIn U K H₁ L ((U.block L).round - D)) →
    (∀ k L, k < n' → g₂ k = some L → FetchedIn U K H₂ L ((U.block L).round - D)) →
    (∀ k, S.slotRound k ≤ (U.block b).round + D → k < n) →
    b ∉ LedgerIn U K H₁ D g₁ n → b ∉ LedgerIn U K H₂ D g₂ n'

/-- **After synchrony, a leader of `T` outputs every block of `T` at most `D`
rounds below it**, from round `R` on, at `K ≥ 1`. -/
def Outputs : Prop :=
  ∀ (Validator BlockId Payload : Type) [Fintype Validator] [DecidableEq Validator]
    [Faults Validator] [Crashes Validator]
    [LinearOrder BlockId] (U : KRecord Validator BlockId Payload)
    (K D : ℕ) (T : Finset Validator) (R : ℕ) (L x : BlockId), 1 ≤ K →
    SyncFrom U T R (U.block L).round → L ∈ U.ids → (U.block L).creator ∈ T →
    x ∈ U.ids → (U.block x).creator ∈ T → R ≤ (U.block x).round →
    (U.block x).round < (U.block L).round → (U.block L).round ≤ (U.block x).round + D →
    x ∈ Out U K D L

/-- **After synchrony, every block of `T` enters the ledger** of a node that
has decided every slot at most `D` rounds above it, when every `D` rounds
hold a slot led by `T`, at `K ≥ 3`. -/
def Included : Prop :=
  ∀ (Validator BlockId Payload : Type) [Fintype Validator] [DecidableEq Validator]
    [Faults Validator] [Crashes Validator] [LinearOrder BlockId] [S : Slots Validator]
    (p : Scheme.Params) (U : KRecord Validator BlockId Payload) (K D : ℕ) (H : Finset BlockId)
    (T : Finset Validator) (R : ℕ) (g : ℕ → Option BlockId) (n : ℕ) (x : BlockId),
    Row Validator p → LiveRow Validator p → 3 ≤ K → H ⊆ U.ids →
    (∀ r, ∃ k, r < S.slotRound k ∧ S.slotRound k ≤ r + D ∧ S.leader k ∈ T) →
    (∀ k, k < n → NodeDecided p U K H k (g k)) →
    (∀ k L, k < n → g k = some L → FetchedIn U K H L ((U.block L).round - D)) →
    x ∈ U.ids → (U.block x).creator ∈ T → R ≤ (U.block x).round →
    (∀ k, S.slotRound k ≤ (U.block x).round + D → k < n) →
    SyncFrom U T R ((U.block x).round + D + 2) →
    WithRefs U T ((U.block x).round + 2) ((U.block x).round + D + 2) ⊆ ↑H →
    x ∈ LedgerIn U K H D g n

/-- The order. -/
def Statement : Prop := Local ∧ Agrees ∧ Total ∧ Settled ∧ Excluded ∧ Outputs ∧ Included

end Order

end KPartialDag

end LeanDag
