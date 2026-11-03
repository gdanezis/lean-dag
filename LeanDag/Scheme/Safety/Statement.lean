import LeanDag.Scheme.Model.Rule
import LeanDag.Scheme.Model.VotedBlock
/-!
# The scheme's own vote — statement

`docs/scheme.md` §6. The scheme's own vote, `VotedBlock`, is a
vote-selection rule for every order of the parents. Every row agrees at
every vote-selection rule, this one included (`Scheme/Sufficiency/`,
`Scheme.Table.RowsCovered`).

Statements only; the proofs are `Proof.lean`.
-/

namespace LeanDag

namespace Scheme

namespace Safety


/-- **The scheme's vote is a vote-selection rule**, for every order of the
parents. -/
def VotedBlockIsVote : Prop :=
  ∀ (Validator BlockId Payload : Type) [Fintype Validator] [DecidableEq Validator]
    [Faults Validator] [DecidableEq BlockId] (ord : BlockId → Finset BlockId → List BlockId),
    (∀ b s x, x ∈ ord b s ↔ x ∈ s) →
    ∃ σ : VoteSel Validator BlockId Payload ValidWrt Correct, σ.sel = votedBlock ord

/-- The scheme's vote. -/
def Statement : Prop := VotedBlockIsVote

end Safety

end Scheme

end LeanDag
