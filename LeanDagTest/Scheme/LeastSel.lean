import LeanDag.Scheme.Equiv.Proof
import LeanDag.Scheme.Table.Proof
import LeanDag.Scheme.Safety.Proof
import LeanDag.Scheme.Sufficiency.Proof
import LeanDag.Scheme.Loop.Proof
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

end Scheme

end LeanDagTest

#print axioms LeanDag.Scheme.Table.holds
#print axioms LeanDag.Scheme.Equiv.holds
#print axioms LeanDag.Scheme.leastSel
#print axioms LeanDag.Scheme.Safety.holds
#print axioms LeanDag.Scheme.Sufficiency.holds
#print axioms LeanDag.Scheme.Loop.holds
