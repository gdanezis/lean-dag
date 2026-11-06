import LeanDag.KPartialDag.Model.Close
/-!
# Closing the channel — statement

`docs/kpartial.md` §12, Theorem 8: when the validators of `T` declare the
channel closed, every node of `T` reaches the last commit on a reactive
run, and a node holding what such a node holds reaches it alike.

Statements only; the proofs are `Proof.lean`.
-/

namespace LeanDag

namespace KPartialDag

namespace Close

/-- **The channel closes**: on a reactive run, at `2δ ≤ γ ≤ τ` and `δ < γ`
and `K ≥ 3`, when nodes of `T` fetch the available sub-DAG of the certified
leader blocks they hold within `Δ`, the schedule offers runs of `c` leaders
of `T` spanning eligibility and a slot led by `T` every `D` rounds, and the
validators of `T` declare the channel closed from round `r₀` on, there is a
slot `b` such that, if the run reaches round `σ(b + c − 1) + 2`, every node
of `T` at one time has decided every slot up to its last commit. -/
def Closes : Prop :=
  ∀ (Validator BlockId Payload : Type) [Fintype Validator] [DecidableEq Validator]
    [Faults Validator] [DecidableEq BlockId] [S : Slots Validator]
    (U : KRecord Validator BlockId Payload) (tl : Timeline Validator BlockId)
    (T : Finset Validator) (G δ τ γ μ R N K D Δ c r₀ : ℕ) (closes : Payload → Prop),
    ReactiveRun U tl T G δ τ γ μ R N → 2 * δ ≤ γ → δ < γ → γ ≤ τ → 3 ≤ K →
    Fetches U tl T K G Δ → 0 < c → (∀ b i, i < b → EligibleAt (S := S) 2 i (b + c - 1)) →
    FairRunOn T c → (∀ r, ∃ k, r < S.slotRound k ∧ S.slotRound k ≤ r + D ∧ S.leader k ∈ T) →
    DeclaresFrom U T closes r₀ → ∃ b, S.slotRound (b + c - 1) + 2 ≤ N → ∃ t, ∀ v ∈ T,
      ∃ (g : ℕ → Option BlockId) (n : ℕ),
        DecidesBelow U K (tl.held v t) D g n ∧ ClosesAfter U K (tl.held v t) D closes g n

/-- **Served blocks suffice**: a node holding, among blocks of the record,
what a node that decided every slot up to its last commit holds decides
those slots alike and reaches the same last commit. -/
def Serves : Prop :=
  ∀ (Validator BlockId Payload : Type) [Fintype Validator] [DecidableEq Validator]
    [Faults Validator] [DecidableEq BlockId] [Slots Validator]
    (U : KRecord Validator BlockId Payload) (K D : ℕ) (H H' : Finset BlockId)
    (closes : Payload → Prop) (g : ℕ → Option BlockId) (n : ℕ), H ⊆ H' → H' ⊆ U.ids →
    DecidesBelow U K H D g n → ClosesAfter U K H D closes g n →
    DecidesBelow U K H' D g n ∧ ClosesAfter U K H' D closes g n

/-- Closing the channel. -/
def Statement : Prop := Closes ∧ Serves

end Close

end KPartialDag

end LeanDag
