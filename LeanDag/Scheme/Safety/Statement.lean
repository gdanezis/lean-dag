import LeanDag.Scheme.Model.Rule
import LeanDag.Scheme.Model.VotedBlock
import LeanDag.Odontoceti.Rules
import LeanDag.Properties.Agree
import LeanDag.Common.Anchored.Band
/-!
# The rows with buffer rounds at every vote — statement

`docs/scheme.md` §6. The scheme's own vote, `VotedBlock`, is a
vote-selection rule for every order of the parents; and at every
vote-selection rule two views decide alike at the Mahi-Mahi row for every
wave `w ≥ 3`, at the Cordial Miners Async row, and at the Blue Bottle
Async row.

Statements only; the proofs are `Proof.lean`.
-/

namespace LeanDag

namespace Scheme

namespace Safety

open LeanDag.Properties

/-- **The scheme's vote is a vote-selection rule**, for every order of the
parents. -/
def VotedBlockIsVote : Prop :=
  ∀ (Validator BlockId Payload : Type) [Fintype Validator] [DecidableEq Validator]
    [Faults Validator] [DecidableEq BlockId] (ord : BlockId → Finset BlockId → List BlockId),
    (∀ b s x, x ∈ ord b s ↔ x ∈ s) →
    ∃ σ : VoteSel Validator BlockId Payload ValidWrt Correct, σ.sel = votedBlock ord

/-- **The Mahi-Mahi row agrees at every vote.** -/
def MahiMahiAgree : Prop :=
  ∀ (Validator BlockId Payload : Type) [Fintype Validator] [DecidableEq Validator]
    [F : Faults Validator] [LinearOrder BlockId] (w : ℕ), 3 ≤ w →
    ∀ σ : VoteSel Validator BlockId Payload ValidWrt Correct,
    Agree (schemeAnchored (Params.mahiMahi w (Fintype.card Validator) F.f) σ).toDagRule

/-- **The Cordial Miners Async row agrees at every vote.** -/
def CordialMinersAsyncAgree : Prop :=
  ∀ (Validator BlockId Payload : Type) [Fintype Validator] [DecidableEq Validator]
    [F : Faults Validator] [LinearOrder BlockId]
    (σ : VoteSel Validator BlockId Payload ValidWrt Correct),
    Agree (schemeAnchored (Params.cordialMinersAsync (Fintype.card Validator) F.f) σ).toDagRule

/-- **The Blue Bottle Async row agrees at every vote**, at `n ≥ 5f + 1`. -/
def BlueBottleAsyncAgree : Prop :=
  ∀ (Validator BlockId Payload : Type) [Fintype Validator] [DecidableEq Validator]
    [F : Faults5 Validator] [LinearOrder BlockId]
    (σ : VoteSel Validator BlockId Payload ValidWrt Correct),
    Agree (schemeAnchored (Params.blueBottleAsync (Fintype.card Validator) F.f) σ).toDagRule

/-- The scheme's vote, and the three rows. -/
def Statement : Prop :=
  VotedBlockIsVote ∧ MahiMahiAgree ∧ CordialMinersAsyncAgree ∧ BlueBottleAsyncAgree

end Safety

end Scheme

end LeanDag
