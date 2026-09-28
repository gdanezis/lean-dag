import LeanDag.RedSnapper.Helpers.Freeze
import LeanDag.RedSnapper.Model.Five.HonestVoting

/-!
# The 5f+1 voting rule, computably

Generated proof layer; not part of the audit surface. A computable
sufficient condition for `VotingRuleFive`, for the `decide` witnesses of
`LeanDagTest/RedSnapper/`. It is one-directional: the surrogate asks the
named trigger anchor to be a block of the universe, which the rule does
not, so a witness that *refutes* the rule exhibits the violating block
directly instead.
-/

namespace LeanDag

namespace RedSnapper

variable {Validator BlockId Tx Obj : Type*} [Fintype Validator] [DecidableEq Validator]
  [DecidableEq BlockId] [DecidableEq Tx] [DecidableEq Obj] [F : Faults Validator]
  [T : Transactions Tx Obj]

/-- A computable sufficient condition for `VotingRuleFive`. -/
def VotingRuleFiveDec (U : Universe Validator BlockId Tx Obj) : Prop :=
  (∀ b ∈ U.ids, (U.block b).author ∈ (Correct : Finset Validator) →
    ∀ (o : Obj) (tx : Tx), tx ∈ candidates U b o →
      (∀ tx' ∈ candidates U b o, tx' = tx) →
      ¬ StanceSomeDec U (U.block b).author o b Stance.bot →
      StanceSomeDec U (U.block b).author o b (Stance.ack tx)) ∧
  (∀ b ∈ U.ids, (U.block b).author ∈ (Correct : Finset Validator) →
    ∀ o : Obj, (U.block b).declares o = some Stance.bot →
      1 < (candidates U b o).card ∨ (U.block b).freezes o ≠ none) ∧
  (∀ b ∈ U.ids, (U.block b).author ∈ (Correct : Finset Validator) →
    ∀ o : Obj, (U.block b).freezes o = none ∨
      ∃ aₖ ∈ U.ids, (U.block b).freezes o = some aₖ ∧ TriggersDec U aₖ o)

set_option synthInstance.maxSize 4096 in
instance [Fintype Tx] [Fintype Obj] (U : Universe Validator BlockId Tx Obj) :
    Decidable (VotingRuleFiveDec U) := by
  unfold VotingRuleFiveDec; infer_instance

theorem votingRuleFive_of_dec {U : Universe Validator BlockId Tx Obj}
    (h : VotingRuleFiveDec U) : VotingRuleFive U := by
  obtain ⟨h1, h2, h3⟩ := h
  refine ⟨?_, ?_, ?_⟩
  · intro b hb hc o tx htx hsole hbot
    exact (stanceIs_some_iff hb).mpr (h1 b hb hc o tx
      ((mem_candidates_iff hb).mpr htx)
      (fun tx' htx' => hsole tx' ((mem_candidates_iff hb).mp htx'))
      (fun hs => hbot ((stanceIs_some_iff hb).mpr hs)))
  · intro b hb hc o hd
    exact (h2 b hb hc o hd).imp (conflicted_iff hb).mpr id
  · intro b hb hc o aₖ hf
    rcases h3 b hb hc o with hnone | ⟨a', ha', hf', ht⟩
    · rw [hnone] at hf
      exact absurd hf (by simp)
    · rw [hf'] at hf
      obtain rfl := Option.some.inj hf
      exact (triggers_iff ha').mpr ht

end RedSnapper

end LeanDag
