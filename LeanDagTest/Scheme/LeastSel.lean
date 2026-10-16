import LeanDag.Scheme.Equiv.Proof
import LeanDag.Scheme.Table.Proof
import LeanDag.Scheme.Safety.Proof
import LeanDag.Scheme.Sufficiency.Proof
import LeanDag.Scheme.Loop.Proof
import LeanDag.Scheme.Record
import LeanDag.Scheme.Rows.Proof
/-!
# A vote-selection rule exists

The scheme's rows are stated for every `VoteSel`; `leastSel` is one, so
those statements are not about an empty class. Each row then holds at it.
-/

namespace LeanDagTest

namespace Scheme

open LeanDag LeanDag.Scheme

variable {Validator : Type} [Fintype Validator] [DecidableEq Validator]
variable {BlockId : Type} [LinearOrder BlockId] {Payload : Type}

/-- The Mysticeti row at `leastSel`. -/
example [F : Faults Validator] :
    (schemeAnchored (Params.mysticeti (Fintype.card Validator) F.f)
        (leastSel (Validator := Validator) (BlockId := BlockId) (Payload := Payload)
          (P := ValidWrt) (honest := Correct))).toDagRule =
      MysticetiProperties.mysticetiRule (Validator := Validator) (BlockId := BlockId)
        (Payload := Payload) :=
  Equiv.mysticetiRow Validator BlockId Payload leastSel

/-- The three-round theorem on the core universe, at the Mysticeti row and
any vote: its hypotheses are met. -/
example [F : Faults Validator] (σ : VoteSel Validator BlockId Payload ValidWrt Correct) :
    Properties.Agree ((schemeAnchored (Params.mysticeti (Fintype.card Validator) F.f) σ).toDagRuleOn
      (fun U => U.NoEquivOn Correct)) :=
  Sufficiency.threeRoundAgree Validator BlockId Payload ValidWrt (quorumCard Validator) Correct
    Correct F.f _ σ card_compl_correct_le (Nat.sub_le _ _) rfl (show 3 ≤ 3 by omega) rfl
    (by have := F.card_validators; simp only [Params.ThreeRound, Params.mysticeti]; omega)

/-- The crash theorem on Nemo's universe, at the Async Nemo-Nemo row and any
vote: every validator is honest, and the majority quorum is `c + 1` at
`n = 2c + 1`. -/
example (c : ℕ) (hn : Fintype.card Validator = 2 * c + 1)
    (σ : VoteSel Validator BlockId Payload Nemo.ValidWrt Finset.univ) :
    Properties.Agree ((schemeAnchored (Params.asyncNemoNemo (Fintype.card Validator) c) σ).toDagRuleOn
      (fun U => U.NoEquivOn Finset.univ)) := by
  have hm : Nemo.majority Validator = c + 1 := by unfold Nemo.majority; omega
  haveI : Validity.Quorate (Nemo.ValidWrt (Validator := Validator) (BlockId := BlockId)
      (Payload := Payload)) (c + 1) := hm ▸ Nemo.ValidWrt.quorate
  exact (Sufficiency.nemoRowsAgree Validator BlockId Payload Nemo.ValidWrt c Finset.univ
    Finset.univ σ (by simp) hn).2

end Scheme

end LeanDagTest

#print axioms LeanDag.Scheme.Table.holds
#print axioms LeanDag.Scheme.Equiv.holds
#print axioms LeanDag.Scheme.leastSel
#print axioms LeanDag.Scheme.Safety.holds
#print axioms LeanDag.Scheme.Sufficiency.holds
#print axioms LeanDag.Scheme.Sufficiency.nemoRowsAgree
#print axioms LeanDag.Scheme.Loop.holds
#print axioms LeanDag.Scheme.Rows.holds
#print axioms LeanDag.Scheme.banded
#print axioms LeanDag.Scheme.safety
#print axioms LeanDag.Scheme.lives
#print axioms LeanDag.Scheme.familySupport_ofCoverage
#print axioms LeanDag.Scheme.votedBlockSel_local
