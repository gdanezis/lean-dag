import LeanDag.Scheme.Safety.Statement
import LeanDag.Scheme.Helpers.AnyVoteCert
import LeanDag.Scheme.Helpers.VotedBlock
/-!
# The rows with buffer rounds at every vote — proof

The depth-first search is a vote-selection rule (`Helpers/VotedBlock.lean`);
each row has the anchored laws at every vote (`Helpers/AnyVote.lean`,
`Helpers/AnyVoteCert.lean`), and laws give agreement.
-/

namespace LeanDag

namespace Scheme

namespace Safety

theorem votedBlockIsVote : VotedBlockIsVote := by
  intro Validator BlockId Payload _ _ _ _ ord hord
  exact ⟨votedBlockSel ord hord, rfl⟩

theorem mahiMahiAgree : MahiMahiAgree := by
  intro Validator BlockId Payload _ _ F _ w hw σ
  exact AnchoredRule.agree (quorumRowLaws σ ⟨rfl, hw, rfl, rfl, rfl, le_refl _⟩)

theorem cordialMinersAsyncAgree : CordialMinersAsyncAgree := by
  intro Validator BlockId Payload _ _ F _ σ
  exact AnchoredRule.agree (quorumRowLaws σ ⟨rfl, show 3 ≤ 5 by omega, rfl, rfl, rfl, Nat.sub_le _ _⟩)

theorem blueBottleAsyncAgree : BlueBottleAsyncAgree := by
  intro Validator BlockId Payload _ _ F _ σ
  exact AnchoredRule.agree (blueBottleAsyncLaws σ)

theorem holds : Statement :=
  ⟨votedBlockIsVote, mahiMahiAgree, cordialMinersAsyncAgree, blueBottleAsyncAgree⟩

end Safety

end Scheme

end LeanDag
