import LeanDag.FinWhale.Model.Anchor
import LeanDag.Common.Anchored
/-!
# FinWhale — the decision relation

FinWhale as the shared anchored relation: the direct commit is the fast
or slow path on the validator's own view, the one rung is the anchored
indirect rule tie-broken by `chooseLeast`, and eligibility is wave two.
The reverse pass computes a derivation of this relation
(`decided_of_wellFormed`), so agreement is the relation's
`decided_agree` at FinWhale's laws.
-/

namespace LeanDag

namespace FinWhale

section Rule

variable (Validator BlockId Payload : Type*) [Fintype Validator] [DecidableEq Validator]
  [F : Faults Validator] [P : Params Validator] [DecidableEq BlockId] [LinearOrder BlockId]

/-- **FinWhale as an anchored rule.** -/
def finWhaleAnchored :
    AnchoredRule Validator BlockId Payload ValidHere (Correct : Finset Validator) where
  waveAt := fun _ => 2
  Commit := fun _ V L _ => DirectCommit V.toRecord L
  decCommit := fun _ _ _ _ => inferInstance
  Skip := fun _ V S k => DirectSkip S V.toRecord k
  rungs := 1
  Link := fun _ U A L S k => IndirectCommit S U A k L
  tie := fun _ L L' => L < L'

end Rule

variable {Validator BlockId Payload : Type*} [Fintype Validator] [DecidableEq Validator]
  [F : Faults Validator] [P : Params Validator] [DecidableEq BlockId] [LinearOrder BlockId]
  [S : Slots Validator]

/-- The verdicts a validator holding view `V` may reach on slot `k`. -/
abbrev Decided (D : Dag Validator BlockId Payload) (V : D.View) : ℕ → Option BlockId → Prop :=
  (finWhaleAnchored Validator BlockId Payload).Decided (S := S) D V

namespace Decided
export AnchoredRule.Decided (directCommit directSkip indirectCommit indirectSkip)
end Decided

end FinWhale

end LeanDag
