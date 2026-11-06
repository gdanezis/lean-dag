import LeanDag.KPartialDag.Model.Bounds
import Mathlib.Algebra.BigOperators.Group.Finset.Defs
/-!
# Bounds for deciding and restarting — statement

`docs/kpartial.md` §10, Theorem 6: deciding, building and resuming the
ledger read a band of rounds of bounded length, and the blocks of a history
and of a round of the available sub-DAG are counted.

Statements only; the proofs are `Proof.lean`.
-/

namespace LeanDag

namespace KPartialDag

namespace Bounds

/-- **Decisions read a band**: at a row, a node's decision of a slot at round
`ρ + K − 1` or above, and not below `ρ`, is the same on its blocks at round
`ρ` or above. -/
def Decides : Prop :=
  ∀ (Validator BlockId Payload : Type) [Fintype Validator] [DecidableEq Validator]
    [Faults Validator] [Crashes Validator]
    [LinearOrder BlockId] [S : Slots Validator] (p : Scheme.Params)
    (U : KRecord Validator BlockId Payload) (K : ℕ) (H : Finset BlockId) (ρ i : ℕ)
    (v : Option BlockId), Row Validator p → H ⊆ U.ids → ρ ≤ S.slotRound i →
    ρ + K ≤ S.slotRound i + 1 →
    (NodeDecided p U K (Band U H ρ) i v ↔ NodeDecided p U K H i v)

/-- **Progress from a band**: for a schedule offering runs of `c` slots led by
`T`, each spanning eligibility, past any slot `k` and round `R` there is a run
from `b` such that, on every record responsive among `T` from `R` to the
run's end, a node holding the blocks of `T` over the run with their
references, and the available sub-DAG below every voted leader up to the
run's end at round `ρ` or above, decides every slot below `b + c` at round
`ρ + K − 1` or above, and not below `ρ`, at a live row. -/
def Progress : Prop :=
  ∀ (Validator BlockId Payload : Type) [Fintype Validator] [DecidableEq Validator]
    [Faults Validator] [Crashes Validator]
    [LinearOrder BlockId] [S : Slots Validator] (p : Scheme.Params) (K : ℕ)
    (T : Finset Validator) (c : ℕ), Row Validator p → LiveRow Validator p → 0 < c →
    (∀ b i, i < b → EligibleAt (S := S) (p.waveLength - 1) i (b + c - 1)) → FairRunOn T c →
    ∀ R k, ∃ b, k ≤ b ∧ R ≤ S.slotRound b ∧
      ∀ (U : KRecord Validator BlockId Payload),
        RespondsFrom U T R (S.slotRound (b + c - 1) + 2) →
        ∀ (H : Finset BlockId) (ρ : ℕ), H ⊆ U.ids →
          WithRefs U T (S.slotRound b) (S.slotRound (b + c - 1) + 2) ⊆ ↑H →
          (∀ z ∈ AvailBelow U K (b + c - 1), ρ ≤ (U.block z).round → z ∈ H) →
          ∀ i, i < b + c → ρ ≤ S.slotRound i → ρ + K ≤ S.slotRound i + 1 →
            ∃ v, NodeDecided p U K H i v

/-- **Building**: a block of round `r + 1` referencing a quorum `Q` of distinct
authors of round `r` is valid, and a node holding the histories to depth `K`
of `Q` meets its obligation with its blocks at round `r − K` or above. -/
def Builds : Prop :=
  ∀ (Validator BlockId Payload : Type) [Fintype Validator] [DecidableEq Validator]
    [Faults Validator] [Crashes Validator]
    [LinearOrder BlockId] (U : KRecord Validator BlockId Payload) (K : ℕ)
    (H Q : Finset BlockId) (r : ℕ) (b : Block Validator BlockId Payload),
    (∀ x ∈ Q, x ∈ U.ids ∧ (U.block x).round = r) →
    (∀ x ∈ Q, ∀ y ∈ Q, (U.block x).creator = (U.block y).creator → x = y) →
    quorumCard Validator ≤ (creatorsOf U.block Q).card →
    (∀ x ∈ Q, historyUpto U K x ⊆ H) → b.round = r + 1 → b.refs = Q →
    KValid Validator BlockId Payload U.block b ∧ Obliged U K (Band U H (r - K)) b

/-- **Resuming the ledger**: at a row and `K ≥ 3`, two nodes that decided every slot `D`
rounds below `s` and above, up to `m`, and fetched those slots' leaders down
to `D` rounds below `s`, give each block the same entry slot from `s` to
`m`. Neither needs a verdict of an earlier slot. -/
def Resumes : Prop :=
  ∀ (Validator BlockId Payload : Type) [Fintype Validator] [DecidableEq Validator]
    [Faults Validator] [Crashes Validator]
    [LinearOrder BlockId] [S : Slots Validator] (p : Scheme.Params)
    (U : KRecord Validator BlockId Payload) (K D : ℕ) (H₁ H₂ : Finset BlockId)
    (g₁ g₂ : ℕ → Option BlockId) (s m : ℕ), Row Validator p → 3 ≤ K → H₁ ⊆ U.ids →
    H₂ ⊆ U.ids →
    (∀ j L, g₁ j = some L → IsLeaderBlock U j L) →
    (∀ j L, g₂ j = some L → IsLeaderBlock U j L) →
    (∀ j, j < m → S.slotRound s ≤ S.slotRound j + D →
      NodeDecided p U K H₁ j (g₁ j) ∧ NodeDecided p U K H₂ j (g₂ j)) →
    (∀ j L, j < m → S.slotRound s ≤ S.slotRound j + D → g₁ j = some L →
      FetchedIn U K H₁ L (S.slotRound s - D)) →
    (∀ j L, j < m → S.slotRound s ≤ S.slotRound j + D → g₂ j = some L →
      FetchedIn U K H₂ L (S.slotRound s - D)) →
    ∀ b k, s ≤ k → k < m → (EntersIn U K H₁ D g₁ b k ↔ EntersIn U K H₂ D g₂ b k)

/-- **At most `n` blocks a round without equivocation.** -/
def Counts : Prop :=
  ∀ (Validator BlockId Payload : Type) [Fintype Validator] [DecidableEq Validator]
    [Faults Validator] [Crashes Validator]
    [LinearOrder BlockId] (U : KRecord Validator BlockId Payload)
    (lo hi : ℕ), EquivFree U lo hi →
    (Between U lo hi).card ≤ (hi + 1 - lo) * Fintype.card Validator

/-- **A history to depth `K`** lies in `K + 1` rounds and holds at most
`N_0 + ⋯ + N_K` blocks, with `N_0 = 1` and `N_{d+1} = |C| + f · N_d`
(`layerBound`), with no condition on equivocation. -/
def Window : Prop :=
  ∀ (Validator BlockId Payload : Type) [Fintype Validator] [DecidableEq Validator]
    [Faults Validator] [Crashes Validator]
    [LinearOrder BlockId] (U : KRecord Validator BlockId Payload) (K : ℕ)
    (x : BlockId), x ∈ U.ids →
    historyUpto U K x ⊆ Between U ((U.block x).round - K) (U.block x).round ∧
      (historyUpto U K x).card ≤
        ∑ d ∈ Finset.range (K + 1),
          layerBound (Correct : Finset Validator).card (Faults.f Validator) d

/-- **The available sub-DAG per round**, with no condition on equivocation:
below a block of the record, a round holds at most `|C| · w · n` anchor
points besides the anchor, and at most `|C| + (|C|(w f + 1) + 1)(1 + f + ⋯ +
f^K)` blocks of the available sub-DAG, `w` the reach width (`1` when no
validator crashes for good, `n + 1` otherwise). -/
def AvailRound : Prop :=
  ∀ (Validator BlockId Payload : Type) [Fintype Validator] [DecidableEq Validator]
    [Faults Validator] [Crashes Validator] [LinearOrder BlockId]
    (U : KRecord Validator BlockId Payload) (K : ℕ) (A : BlockId) (ρ : ℕ), A ∈ U.ids →
    (∀ X : Finset BlockId,
      (∀ x ∈ X, (∃ d, AnchoredBelow U K A x d) ∧ (U.block x).round = ρ ∧ x ≠ A) →
      X.card ≤ (Correct : Finset Validator).card * reachWidth Validator *
        Fintype.card Validator) ∧
    ∀ Z : Finset BlockId, (∀ z ∈ Z, z ∈ Avail U K A ∧ (U.block z).round = ρ) →
      Z.card ≤ (Correct : Finset Validator).card +
        ((Correct : Finset Validator).card * (reachWidth Validator * Faults.f Validator + 1) +
          1) * ∑ s ∈ Finset.range (K + 1), Faults.f Validator ^ s

/-- Bounds for deciding and restarting. -/
def Statement : Prop := Decides ∧ Progress ∧ Builds ∧ Resumes ∧ Counts ∧ Window ∧ AvailRound

end Bounds

end KPartialDag

end LeanDag
