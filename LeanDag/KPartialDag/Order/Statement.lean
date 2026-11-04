import LeanDag.KPartialDag.Model.Order
/-!
# The order — statement

`docs/kpartial.md` §7. A committed leader outputs the blocks of its available
sub-DAG at most `D` rounds below it:

* **available** (`Available`): what a certified block outputs is held by
  correct nodes;
* **local** (`Local`): a node reads a leader's output on what it holds, and
  reads all of it once it has fetched the sub-DAG down to `D` rounds below
  the leader;
* **agreement** (`Agrees`): at `K ≥ 3`, two nodes that have fetched below the
  leaders they committed have one ledger, and one entry slot per block;
* **inclusion** (`Includes`): after synchrony, a leader of `T` outputs every
  block of `T` at most `D` rounds below it;
* **entry** (`Enters`): after synchrony, a node deciding a slot led by `T`
  has in its ledger every block of `T` at most `D` rounds below the slot.

Statements only; the proofs are `Proof.lean`.
-/

namespace LeanDag

namespace KPartialDag

namespace Order

/-- **What a certified block outputs is held by correct nodes.** -/
def Available : Prop :=
  ∀ (Validator BlockId Payload : Type) [Fintype Validator] [DecidableEq Validator]
    [Faults Validator] [DecidableEq BlockId] (U : KRecord Validator BlockId Payload)
    (K D : ℕ) (L : BlockId) (r : ℕ), L ∈ U.ids →
    (certificatesAt U (IsVote U) (quorumCard Validator) L r).Nonempty →
    Out U K D L ⊆ CorrectHeld U K

/-- **A node reads a leader's output on what it holds**, and reads all of it
once it has fetched the sub-DAG down to `D` rounds below the leader. -/
def Local : Prop :=
  ∀ (Validator BlockId Payload : Type) [Fintype Validator] [DecidableEq Validator]
    [Faults Validator] [DecidableEq BlockId] (U : KRecord Validator BlockId Payload)
    (K D : ℕ) (H : Finset BlockId) (L : BlockId), H ⊆ U.ids →
    OutIn U K H D L ⊆ Out U K D L ∧
      (FetchedIn U K H L ((U.block L).round - D) → OutIn U K H D L = Out U K D L)

/-- **Two nodes have one ledger, and one entry slot per block**, at `K ≥ 3`,
once each has fetched down to `D` rounds below the leaders it committed. -/
def Agrees : Prop :=
  ∀ (Validator BlockId Payload : Type) [Fintype Validator] [DecidableEq Validator]
    [Faults Validator] [DecidableEq BlockId] [Slots Validator]
    (U : KRecord Validator BlockId Payload) (K D : ℕ) (H₁ H₂ : Finset BlockId)
    (g₁ g₂ : ℕ → Option BlockId) (n : ℕ), 3 ≤ K → H₁ ⊆ U.ids → H₂ ⊆ U.ids →
    (∀ k, k < n → NodeDecided U K H₁ k (g₁ k)) → (∀ k, k < n → NodeDecided U K H₂ k (g₂ k)) →
    (∀ k L, k < n → g₁ k = some L → FetchedIn U K H₁ L ((U.block L).round - D)) →
    (∀ k L, k < n → g₂ k = some L → FetchedIn U K H₂ L ((U.block L).round - D)) →
    LedgerIn U K H₁ D g₁ n = LedgerIn U K H₂ D g₂ n ∧
      ∀ b k, k < n → (EntersIn U K H₁ D g₁ b k ↔ EntersIn U K H₂ D g₂ b k)

/-- **After synchrony, a leader of `T` outputs every block of `T` at most `D`
rounds below it**, from round `R` on, at `K ≥ 1`. -/
def Includes : Prop :=
  ∀ (Validator BlockId Payload : Type) [Fintype Validator] [DecidableEq Validator]
    [Faults Validator] [DecidableEq BlockId] (U : KRecord Validator BlockId Payload)
    (K D : ℕ) (T : Finset Validator) (R : ℕ) (L x : BlockId), 1 ≤ K →
    quorumCard Validator ≤ T.card → SynchronisedOn U T R →
    (∀ r, R ≤ r → r < (U.block L).round → PopulatedOn U T r) → L ∈ U.ids →
    (U.block L).creator ∈ T → x ∈ U.ids → (U.block x).creator ∈ T →
    R ≤ (U.block x).round → (U.block x).round < (U.block L).round →
    (U.block L).round ≤ (U.block x).round + D → x ∈ Out U K D L

/-- **After synchrony, a node deciding a slot led by `T` has in its ledger
every block of `T` at most `D` rounds below the slot**, from round `R` on,
at `K ≥ 3`, once it holds the blocks of `T` two rounds above the slot with
their references and has fetched below the slot's leader. -/
def Enters : Prop :=
  ∀ (Validator BlockId Payload : Type) [Fintype Validator] [DecidableEq Validator]
    [Faults Validator] [DecidableEq BlockId] [S : Slots Validator]
    (U : KRecord Validator BlockId Payload) (K D : ℕ) (H : Finset BlockId)
    (T : Finset Validator) (R : ℕ) (g : ℕ → Option BlockId) (k : ℕ) (x : BlockId),
    3 ≤ K → quorumCard Validator ≤ T.card → SynchronisedOn U T R → H ⊆ U.ids →
    S.leader k ∈ T → (∀ r, R ≤ r → r ≤ S.slotRound k + 2 → PopulatedOn U T r) →
    WithRefs U T (S.slotRound k + 2) (S.slotRound k + 2) ⊆ ↑H →
    NodeDecided U K H k (g k) →
    (∀ L, g k = some L → FetchedIn U K H L ((U.block L).round - D)) →
    x ∈ U.ids → (U.block x).creator ∈ T → R ≤ (U.block x).round →
    (U.block x).round < S.slotRound k → S.slotRound k ≤ (U.block x).round + D →
    x ∈ LedgerIn U K H D g (k + 1)

/-- The order. -/
def Statement : Prop := Available ∧ Local ∧ Agrees ∧ Includes ∧ Enters

end Order

end KPartialDag

end LeanDag
