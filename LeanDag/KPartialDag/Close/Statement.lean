import LeanDag.KPartialDag.Model.Close
/-!
# Closing the channel — statement

`docs/kpartial.md` §12, Theorem 8: when the validators of `T` declare the
channel closed, every node of `T` reaches the last commit on a reactive
run, a node holding what such a node holds reaches it alike, and two nodes
reach one last commit with one ledger.

Statements only; the proofs are `Proof.lean`.
-/

namespace LeanDag

namespace KPartialDag

namespace Close

/-- **The channel closes**: at a live row, on a reactive run, at `2δ ≤ γ ≤ τ` and `δ < γ`
and the row's depth, when nodes of `T` fetch the available sub-DAG of the voted
leader blocks they hold within `Δ`, the schedule offers runs of `c` leaders
of `T` spanning eligibility and a slot led by `T` every `D` rounds, and the
validators of `T` declare the channel closed from round `r₀` on, there is a
slot `b` such that, if the run reaches round `σ(b + c − 1) + 2`, every node
of `T` at one time has decided every slot up to its last commit. -/
def Closes : Prop :=
  ∀ (Validator BlockId Payload : Type) [Fintype Validator] [DecidableEq Validator]
    [Faults Validator] [Crashes Validator]
    [LinearOrder BlockId] [S : Slots Validator] (p : Scheme.Params)
    (U : KRecord Validator BlockId Payload) (tl : Timeline Validator BlockId)
    (T : Finset Validator) (G δ τ γ μ R N K D Δ c r₀ : ℕ) (closes : Payload → Prop),
    Row Validator p → LiveRow Validator p →
    ReactiveRun U tl T G δ τ γ μ R N → 2 * δ ≤ γ → δ < γ → γ ≤ τ → kDepth Validator p ≤ K →
    Fetches U tl T K G Δ → 0 < c →
    (∀ b i, i < b → EligibleAt (S := S) (p.waveLength - 1) i (b + c - 1)) →
    FairRunOn T c → (∀ r, ∃ k, r < S.slotRound k ∧ S.slotRound k ≤ r + D ∧ S.leader k ∈ T) →
    DeclaresFrom U T closes r₀ → ∃ b, S.slotRound (b + c - 1) + 2 ≤ N → ∃ t, ∀ v ∈ T,
      ∃ (g : ℕ → Option BlockId) (n : ℕ),
        DecidesBelow p U K (tl.held v t) D g n ∧ ClosesAfter U K (tl.held v t) D closes g n

/-- **Served blocks suffice**: at a row, a node holding, among blocks of the record,
what a node that decided every slot up to its last commit holds decides
those slots alike and reaches the same last commit. -/
def Serves : Prop :=
  ∀ (Validator BlockId Payload : Type) [Fintype Validator] [DecidableEq Validator]
    [Faults Validator] [Crashes Validator]
    [LinearOrder BlockId] [Slots Validator] (p : Scheme.Params)
    (U : KRecord Validator BlockId Payload) (K D : ℕ) (H H' : Finset BlockId)
    (closes : Payload → Prop) (g : ℕ → Option BlockId) (n : ℕ), Row Validator p → H ⊆ H' →
    H' ⊆ U.ids →
    DecidesBelow p U K H D g n → ClosesAfter U K H D closes g n →
    DecidesBelow p U K H' D g n ∧ ClosesAfter U K H' D closes g n

/-- **Nodes agree on the last commit**: at a row and its depth, two nodes that have each
decided every slot up to their last commit, and fetched each leader they
commit down to `D` rounds below it, have the same last commit and the same
ledger after it. -/
def Agrees : Prop :=
  ∀ (Validator BlockId Payload : Type) [Fintype Validator] [DecidableEq Validator]
    [Faults Validator] [Crashes Validator]
    [LinearOrder BlockId] [Slots Validator] (p : Scheme.Params)
    (U : KRecord Validator BlockId Payload) (K D : ℕ) (H₁ H₂ : Finset BlockId)
    (closes : Payload → Prop) (g₁ g₂ : ℕ → Option BlockId) (n₁ n₂ : ℕ), Row Validator p →
    kDepth Validator p ≤ K →
    H₁ ⊆ U.ids → H₂ ⊆ U.ids → DecidesBelow p U K H₁ D g₁ n₁ → ClosesAfter U K H₁ D closes g₁ n₁ →
    DecidesBelow p U K H₂ D g₂ n₂ → ClosesAfter U K H₂ D closes g₂ n₂ →
    n₁ = n₂ ∧ LedgerIn U K H₁ D g₁ n₁ = LedgerIn U K H₂ D g₂ n₂

/-- Closing the channel. -/
def Statement : Prop := Closes ∧ Serves ∧ Agrees

end Close

end KPartialDag

end LeanDag
