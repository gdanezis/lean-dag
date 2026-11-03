import LeanDag.Scheme.Safety.Statement
import LeanDag.Scheme.Helpers.VotedBlock
/-!
# The scheme's own vote — proof

The depth-first search is a vote-selection rule (`Helpers/VotedBlock.lean`).
-/

namespace LeanDag

namespace Scheme

namespace Safety

theorem votedBlockIsVote : VotedBlockIsVote := by
  intro Validator BlockId Payload _ _ _ _ ord hord
  exact ⟨votedBlockSel ord hord, rfl⟩

theorem holds : Statement := votedBlockIsVote

end Safety

end Scheme

end LeanDag
