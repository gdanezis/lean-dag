import LeanDag.KPartialDag.Model.Bounds
import Mathlib.Algebra.BigOperators.Group.Finset.Defs
/-!
# Bounds for deciding and restarting — statement

`docs/kpartial.md` §10. With no mechanism beyond the K-partial DAG and its
commit rule:

* **decisions read a band** (`Decides`): a node's decision of a slot at
  round `ρ + K − 1` or above, and not below `ρ`, is the same on its blocks at
  round `ρ` or above;
* **progress from a band** (`Progress`): after synchrony, a node holding the
  blocks of `T` over a run and the available sub-DAG above round `ρ` decides
  every slot up to the run's end at round `ρ + K − 1` or above;
* **building** (`Builds`): a block referencing a quorum of distinct authors of
  the round below is valid, and its obligation is met by the node's blocks
  `K` rounds below the quorum's round or above;
* **resuming the ledger** (`Resumes`): at `K ≥ 3`, two nodes that decided the
  slots `D` rounds below `s` and above, and fetched those slots' leaders down
  to `D` rounds below `s`, give each block the same entry slot from `s` on;
* **counting** (`Counts`, `Window`): without equivocation the record holds at
  most `n` blocks per round; a history to depth `K` lies in `K + 1` rounds
  and holds at most `1 + n + ⋯ + n^K` blocks, with no condition on
  equivocation;
* **the available sub-DAG per round** (`AvailRound`): a round holds at most
  `|C| · n` anchored blocks besides the anchor, and so a bounded number of
  blocks of the available sub-DAG, with no condition on equivocation.

Statements only; the proofs are `Proof.lean`.
-/

namespace LeanDag

namespace KPartialDag

namespace Bounds

/-- **Decisions read a band**: a node's decision of a slot at round
`ρ + K − 1` or above, and not below `ρ`, is the same on its blocks at round
`ρ` or above. -/
def Decides : Prop :=
  ∀ (Validator BlockId Payload : Type) [Fintype Validator] [DecidableEq Validator]
    [Faults Validator] [DecidableEq BlockId] [S : Slots Validator]
    (U : KRecord Validator BlockId Payload) (K : ℕ) (H : Finset BlockId) (ρ i : ℕ)
    (v : Option BlockId), H ⊆ U.ids → ρ ≤ S.slotRound i → ρ + K ≤ S.slotRound i + 1 →
    (NodeDecided U K (Band U H ρ) i v ↔ NodeDecided U K H i v)

/-- **Progress from a band**: for a schedule offering runs of `c` slots led by
`T`, each spanning eligibility, past any slot `k` and round `R` there is a run
from `b` such that, on every record synchronous among `T` from `R` to the
run's end, a node holding the blocks of `T` over the run with their
references, and the available sub-DAG below every certified leader up to the
run's end at round `ρ` or above, decides every slot below `b + c` at round
`ρ + K − 1` or above, and not below `ρ`. -/
def Progress : Prop :=
  ∀ (Validator BlockId Payload : Type) [Fintype Validator] [DecidableEq Validator]
    [Faults Validator] [DecidableEq BlockId] [S : Slots Validator] (K : ℕ)
    (T : Finset Validator) (c : ℕ), 0 < c →
    (∀ b i, i < b → EligibleAt (S := S) 2 i (b + c - 1)) → FairRunOn T c →
    ∀ R k, ∃ b, k ≤ b ∧ R ≤ S.slotRound b ∧
      ∀ (U : KRecord Validator BlockId Payload), SyncFrom U T R (S.slotRound (b + c - 1) + 2) →
        ∀ (H : Finset BlockId) (ρ : ℕ), H ⊆ U.ids →
          WithRefs U T (S.slotRound b) (S.slotRound (b + c - 1) + 2) ⊆ ↑H →
          (∀ z ∈ AvailBelow U K (b + c - 1), ρ ≤ (U.block z).round → z ∈ H) →
          ∀ i, i < b + c → ρ ≤ S.slotRound i → ρ + K ≤ S.slotRound i + 1 →
            ∃ v, NodeDecided U K H i v

/-- **Building**: a block of round `r + 1` referencing a quorum `Q` of distinct
authors of round `r` is valid, and a node holding the histories to depth `K`
of `Q` meets its obligation with its blocks at round `r − K` or above. -/
def Builds : Prop :=
  ∀ (Validator BlockId Payload : Type) [Fintype Validator] [DecidableEq Validator]
    [Faults Validator] [DecidableEq BlockId] (U : KRecord Validator BlockId Payload) (K : ℕ)
    (H Q : Finset BlockId) (r : ℕ) (b : Block Validator BlockId Payload),
    (∀ x ∈ Q, x ∈ U.ids ∧ (U.block x).round = r) →
    (∀ x ∈ Q, ∀ y ∈ Q, (U.block x).creator = (U.block y).creator → x = y) →
    quorumCard Validator ≤ (creatorsOf U.block Q).card →
    (∀ x ∈ Q, historyUpto U K x ⊆ H) → b.round = r + 1 → b.refs = Q →
    KValid Validator BlockId Payload U.block b ∧ Obliged U K (Band U H (r - K)) b

/-- **Resuming the ledger**: at `K ≥ 3`, two nodes that decided every slot `D`
rounds below `s` and above, up to `m`, and fetched those slots' leaders down
to `D` rounds below `s`, give each block the same entry slot from `s` to
`m`. Neither needs a verdict of an earlier slot. -/
def Resumes : Prop :=
  ∀ (Validator BlockId Payload : Type) [Fintype Validator] [DecidableEq Validator]
    [Faults Validator] [DecidableEq BlockId] [S : Slots Validator]
    (U : KRecord Validator BlockId Payload) (K D : ℕ) (H₁ H₂ : Finset BlockId)
    (g₁ g₂ : ℕ → Option BlockId) (s m : ℕ), 3 ≤ K → H₁ ⊆ U.ids → H₂ ⊆ U.ids →
    (∀ j L, g₁ j = some L → IsLeaderBlock U j L) →
    (∀ j L, g₂ j = some L → IsLeaderBlock U j L) →
    (∀ j, j < m → S.slotRound s ≤ S.slotRound j + D →
      NodeDecided U K H₁ j (g₁ j) ∧ NodeDecided U K H₂ j (g₂ j)) →
    (∀ j L, j < m → S.slotRound s ≤ S.slotRound j + D → g₁ j = some L →
      FetchedIn U K H₁ L (S.slotRound s - D)) →
    (∀ j L, j < m → S.slotRound s ≤ S.slotRound j + D → g₂ j = some L →
      FetchedIn U K H₂ L (S.slotRound s - D)) →
    ∀ b k, s ≤ k → k < m → (EntersIn U K H₁ D g₁ b k ↔ EntersIn U K H₂ D g₂ b k)

/-- **At most `n` blocks a round without equivocation.** -/
def Counts : Prop :=
  ∀ (Validator BlockId Payload : Type) [Fintype Validator] [DecidableEq Validator]
    [Faults Validator] [DecidableEq BlockId] (U : KRecord Validator BlockId Payload)
    (lo hi : ℕ), EquivFree U lo hi →
    (Between U lo hi).card ≤ (hi + 1 - lo) * Fintype.card Validator

/-- **A history to depth `K`** lies in `K + 1` rounds and holds at most
`1 + n + ⋯ + n^K` blocks. -/
def Window : Prop :=
  ∀ (Validator BlockId Payload : Type) [Fintype Validator] [DecidableEq Validator]
    [Faults Validator] [DecidableEq BlockId] (U : KRecord Validator BlockId Payload) (K : ℕ)
    (x : BlockId), x ∈ U.ids →
    historyUpto U K x ⊆ Between U ((U.block x).round - K) (U.block x).round ∧
      (historyUpto U K x).card ≤ ∑ d ∈ Finset.range (K + 1), Fintype.card Validator ^ d

/-- **The available sub-DAG per round**, with no condition on equivocation:
below a block of the record, a round holds at most `|C| · n` anchored blocks
besides the anchor, and at most `(K + 1)(|C| · n + 1)(1 + n + ⋯ + n^K)`
blocks of the available sub-DAG. -/
def AvailRound : Prop :=
  ∀ (Validator BlockId Payload : Type) [Fintype Validator] [DecidableEq Validator]
    [Faults Validator] [DecidableEq BlockId] (U : KRecord Validator BlockId Payload) (K : ℕ)
    (A : BlockId) (ρ : ℕ), A ∈ U.ids →
    (∀ X : Finset BlockId, (∀ x ∈ X, AnchoredBelow U K A x ∧ (U.block x).round = ρ ∧ x ≠ A) →
      X.card ≤ (Correct : Finset Validator).card * Fintype.card Validator) ∧
    ∀ Z : Finset BlockId, (∀ z ∈ Z, z ∈ Avail U K A ∧ (U.block z).round = ρ) →
      Z.card ≤ (K + 1) * ((Correct : Finset Validator).card * Fintype.card Validator + 1) *
        ∑ d ∈ Finset.range (K + 1), Fintype.card Validator ^ d

/-- Bounds for deciding and restarting. -/
def Statement : Prop := Decides ∧ Progress ∧ Builds ∧ Resumes ∧ Counts ∧ Window ∧ AvailRound

end Bounds

end KPartialDag

end LeanDag
