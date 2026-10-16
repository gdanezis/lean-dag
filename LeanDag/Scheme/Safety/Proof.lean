import LeanDag.Scheme.Safety.Statement
import LeanDag.Scheme.Helpers.Sufficiency
import LeanDag.Odontoceti.Rules
import LeanDag.Scheme.Helpers.VotedBlock
/-!
# The rows with buffer rounds at every vote — proof

The depth-first search is a vote-selection rule (`Helpers/VotedBlock.lean`).
Each row meets its family's inequalities at `q = n − f`, so it has the
anchored laws at every vote (`Helpers/Sufficiency.lean`) on the core's
universe, where the correct validators never equivocate.
-/

namespace LeanDag

namespace Scheme

namespace Safety

theorem votedBlockIsVote : VotedBlockIsVote := by
  intro Validator BlockId Payload _ _ _ _ ord hord
  exact ⟨votedBlockSel ord hord, rfl⟩

theorem mahiMahiAgree : MahiMahiAgree := by
  intro Validator BlockId Payload _ _ F _ w hw σ
  have := F.card_validators
  have h : (Params.mahiMahi w (Fintype.card Validator) F.f).ThreeRound (Fintype.card Validator)
      F.f (quorumCard Validator) := by
    simp only [Params.ThreeRound, Params.mahiMahi]; omega
  exact AnchoredRule.agree (laws_of_forall (threeRoundLaws σ rfl hw (Hon := Correct)
    card_compl_correct_le (Nat.sub_le _ _) rfl h) fun _ U => U.noEquivOn_honest)

theorem cordialMinersAsyncAgree : CordialMinersAsyncAgree := by
  intro Validator BlockId Payload _ _ F _ σ
  have := F.card_validators
  have h : (Params.cordialMinersAsync (Fintype.card Validator) F.f).ThreeRound
      (Fintype.card Validator) F.f (quorumCard Validator) := by
    simp only [Params.ThreeRound, Params.cordialMinersAsync]; omega
  exact AnchoredRule.agree (laws_of_forall (threeRoundLaws σ rfl (show 3 ≤ 5 by omega)
    (Hon := Correct) card_compl_correct_le (Nat.sub_le _ _) rfl h) fun _ U => U.noEquivOn_honest)

theorem blueBottleAsyncAgree : BlueBottleAsyncAgree := by
  intro Validator BlockId Payload _ _ F _ σ
  have := F.card_validators5
  have h : (Params.blueBottleAsync (Fintype.card Validator) F.f).TwoRound
      (Fintype.card Validator) F.f (quorumCard Validator) := by
    simp only [Params.TwoRound, Params.blueBottleAsync]; omega
  exact AnchoredRule.agree (laws_of_forall (twoRoundLaws σ rfl (Hon := Correct)
    card_compl_correct_le (Nat.sub_le _ _) h) fun _ U => U.noEquivOn_honest)

theorem holds : Statement :=
  ⟨votedBlockIsVote, mahiMahiAgree, cordialMinersAsyncAgree, blueBottleAsyncAgree⟩

end Safety

end Scheme

end LeanDag
