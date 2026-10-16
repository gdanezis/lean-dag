import LeanDag.Scheme.Equiv.Proof
import LeanDag.Scheme.Table.Proof
import LeanDag.Scheme.Safety.Proof
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

end Scheme

end LeanDagTest

#print axioms LeanDag.Scheme.Table.holds
#print axioms LeanDag.Scheme.Equiv.holds
#print axioms LeanDag.Scheme.leastSel
#print axioms LeanDag.Scheme.Safety.holds
