import LeanDag.KPartialSparse.Model.Close
import LeanDag.KPartialSparse.Model.Reactive
/-!
# Sparse K-partial DAG — closing the channel, statement

`docs/kpartial-sparse.md` §9, Theorem 7: when the validators of `T` declare
the channel closed, every node of `T` reaches the last commit on a timed run,
a node holding what such a node holds reaches it alike, and two nodes reach
one last commit with one ledger.

Statements only; the proofs are `Proof.lean`.
-/

namespace LeanDag

namespace KPartialSparse

namespace Close

open KPartialDag (Crashes Timeline LiveRow)
open scoped KPartialDag
open Scheme

/-- **The channel closes**: at a live row, on a timed run, at `2δ ≤ γ ≤ τ` and
`δ < γ`, the depth the sub-DAG needs and `D ≤ K`, on a disciplined record, when
nodes of `T` fetch, a two-round row links by `f + c + 1` votes or more, each
slot's leader leads its round on the substrate, the schedule offers runs of
`c` leaders of `T` spanning eligibility and a slot led by `T` every `D` rounds,
and the validators of `T` declare the channel closed from round `r₀` on, there
is a slot `b` such that, if the run reaches the round of its last
certificates, every node of `T` at one time has decided every slot up to its
last commit. -/
def Closes : Prop :=
  ∀ (Validator BlockId Payload : Type) [Fintype Validator] [DecidableEq Validator]
    [F : Faults Validator] [Cr : Crashes Validator] [Ld : Leaders Validator] [LinearOrder BlockId]
    [ClaimFormat BlockId Payload] [S : Slots Validator] (p : Params)
    (U : SRecord Validator BlockId Payload) (tl : Timeline Validator BlockId)
    (T : Finset Validator) (G δ τ γ R N K D Δ c r₀ : ℕ) (closes : Payload → Prop),
    Row Validator p → (p.voteIsCert = true → F.f + Cr.c + 1 ≤ p.linkSize) →
    Deep Validator K → Disciplined K p.certThreshold S U → LiveRow Validator p → D ≤ K →
    TimedRun U tl T G δ τ γ R N → 2 * δ ≤ γ → δ < γ → γ ≤ τ → Fetches U tl T K G Δ →
    (∀ k, S.leader k ∈ Ld.leaders (S.slotRound k)) → 0 < c →
    (∀ b i, i < b → EligibleAt (S := S) (p.waveLength - 1) i (b + c - 1)) → FairRunOn T c →
    (∀ r, ∃ k, r < S.slotRound k ∧ S.slotRound k ≤ r + D ∧ S.leader k ∈ T) →
    DeclaresFrom U T closes r₀ → ∃ b, certRound p (S.slotRound (b + c - 1)) ≤ N → ∃ t, ∀ v ∈ T,
      ∃ (g : ℕ → Option BlockId) (n : ℕ),
        DecidesBelow p U K (tl.held v t) D g n ∧ ClosesAfter U K (tl.held v t) D closes g n

/-- **Served blocks suffice**: a node holding, among blocks of the record, what
a node that decided every slot up to its last commit holds decides those slots
alike and reaches the same last commit. -/
def Serves : Prop :=
  ∀ (Validator BlockId Payload : Type) [Fintype Validator] [DecidableEq Validator]
    [Faults Validator] [Crashes Validator] [Leaders Validator] [LinearOrder BlockId]
    [ClaimFormat BlockId Payload] [Slots Validator] (p : Params)
    (U : SRecord Validator BlockId Payload) (K D : ℕ) (H H' : Finset BlockId)
    (closes : Payload → Prop) (g : ℕ → Option BlockId) (n : ℕ), H ⊆ H' → H' ⊆ U.ids →
    DecidesBelow p U K H D g n → ClosesAfter U K H D closes g n →
    DecidesBelow p U K H' D g n ∧ ClosesAfter U K H' D closes g n

/-- **Nodes agree on the last commit**: at a row and the depth the sub-DAG
needs, on a disciplined schedule and record, two nodes that have each decided
every slot up to their last commit, and fetched each leader they commit down to
`D` rounds below it, have the same last commit and the same ledger after it. -/
def Agrees : Prop :=
  ∀ (Validator BlockId Payload : Type) [Fintype Validator] [DecidableEq Validator]
    [Faults Validator] [Crashes Validator] [Leaders Validator] [LinearOrder BlockId]
    [ClaimFormat BlockId Payload] [S : Slots Validator] (p : Params)
    (U : SRecord Validator BlockId Payload) (K D : ℕ) (H₁ H₂ : Finset BlockId)
    (closes : Payload → Prop) (g₁ g₂ : ℕ → Option BlockId) (n₁ n₂ : ℕ), Row Validator p →
    Deep Validator K → Disciplined K p.certThreshold S U → H₁ ⊆ U.ids → H₂ ⊆ U.ids →
    DecidesBelow p U K H₁ D g₁ n₁ → ClosesAfter U K H₁ D closes g₁ n₁ →
    DecidesBelow p U K H₂ D g₂ n₂ → ClosesAfter U K H₂ D closes g₂ n₂ →
    n₁ = n₂ ∧ LedgerIn U K H₁ D g₁ n₁ = LedgerIn U K H₂ D g₂ n₂

/-- Closing the channel. -/
def Statement : Prop := Closes ∧ Serves ∧ Agrees

end Close

end KPartialSparse

end LeanDag
