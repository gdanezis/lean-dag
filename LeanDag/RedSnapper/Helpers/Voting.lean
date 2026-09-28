import LeanDag.RedSnapper.Helpers.Certificates
import LeanDag.RedSnapper.Model.Liveness
import LeanDag.RedSnapper.Model.HonestVoting

/-!
# Computable voting rule

Generated: the decidable surrogate for `VotingRule` of
`Model/HonestVoting.lean`, pinned by an iff — the witness models decide
the computable side and bridge. `PopulatedOn` and `SynchronisedOn` are
bounded quantifiers over decidable atoms and need no surrogate. Nothing
here is part of the audit surface.
-/

namespace LeanDag

namespace RedSnapper

variable {Validator BlockId Tx Obj : Type*} [Fintype Validator] [DecidableEq Validator]
  [DecidableEq BlockId] [DecidableEq Tx] [DecidableEq Obj] [F : Faults Validator]
  [T : Transactions Tx Obj]

/-- The computable form of `VotingRule`. -/
def VotingRuleDec (U : Universe Validator BlockId Tx Obj) : Prop :=
  (∀ b ∈ U.ids, (U.block b).author ∈ (Correct : Finset Validator) →
    ∀ (o : Obj) (tx : Tx), (U.block b).declares o = some (Stance.ack tx) →
      tx ∈ candidates U b o) ∧
  (∀ b ∈ U.ids, (U.block b).author ∈ (Correct : Finset Validator) →
    ∀ o : Obj, (U.block b).declares o = some Stance.bot →
      1 < (candidates U b o).card) ∧
  (∀ b ∈ U.ids, (U.block b).author ∈ (Correct : Finset Validator) →
    ∀ (o : Obj) (tx : Tx), tx ∈ candidates U b o →
      (∀ tx' ∈ candidates U b o, tx' = tx) →
      ¬ StanceSomeDec U (U.block b).author o b Stance.bot →
      StanceSomeDec U (U.block b).author o b (Stance.ack tx)) ∧
  (∀ b ∈ U.ids, (U.block b).author ∈ (Correct : Finset Validator) →
    ∀ o : Obj, 1 < (candidates U b o).card → (U.block b).declares o ≠ none) ∧
  (∀ b ∈ U.ids, (U.block b).author ∈ (Correct : Finset Validator) →
    ∀ (o : Obj) (tx : Tx), 1 < (candidates U b o).card →
      (U.block b).declares o = some (Stance.ack tx) → CertVisibleDec U b tx)

set_option synthInstance.maxSize 4096 in
instance [Fintype Tx] [Fintype Obj] (U : Universe Validator BlockId Tx Obj) :
    Decidable (VotingRuleDec U) := by
  unfold VotingRuleDec; infer_instance

theorem votingRule_iff {U : Universe Validator BlockId Tx Obj} :
    VotingRule U ↔ VotingRuleDec U := by
  constructor
  · intro h
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · intro b hb hc o tx hd
      exact (mem_candidates_iff hb).mpr (h.ack_candidate b hb hc o tx hd)
    · intro b hb hc o hd
      exact (conflicted_iff hb).mp (h.bot_conflicted b hb hc o hd)
    · intro b hb hc o tx htx hsole hbot
      exact (stanceIs_some_iff hb).mp (h.ack_sole b hb hc o tx
        ((mem_candidates_iff hb).mp htx)
        (fun tx' htx' => hsole tx' ((mem_candidates_iff hb).mpr htx'))
        (fun hs => hbot ((stanceIs_some_iff hb).mp hs)))
    · intro b hb hc o hconf
      exact h.conflicted_declares b hb hc o ((conflicted_iff hb).mpr hconf)
    · intro b hb hc o tx hconf hd
      exact (certVisible_iff hb).mp
        (h.keep_certVisible b hb hc o tx ((conflicted_iff hb).mpr hconf) hd)
  · rintro ⟨h1, h2, h3, h4, h5⟩
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · intro b hb hc o tx hd
      exact (mem_candidates_iff hb).mp (h1 b hb hc o tx hd)
    · intro b hb hc o hd
      exact (conflicted_iff hb).mpr (h2 b hb hc o hd)
    · intro b hb hc o tx htx hsole hbot
      exact (stanceIs_some_iff hb).mpr (h3 b hb hc o tx
        ((mem_candidates_iff hb).mpr htx)
        (fun tx' htx' => hsole tx' ((mem_candidates_iff hb).mp htx'))
        (fun hs => hbot ((stanceIs_some_iff hb).mpr hs)))
    · intro b hb hc o hconf
      exact h4 b hb hc o ((conflicted_iff hb).mp hconf)
    · intro b hb hc o tx hconf hd
      exact (certVisible_iff hb).mpr
        (h5 b hb hc o tx ((conflicted_iff hb).mp hconf) hd)

end RedSnapper

end LeanDag
