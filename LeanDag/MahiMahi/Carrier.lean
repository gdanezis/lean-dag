import LeanDag.MahiMahi.Helpers.Decision
import LeanDag.Properties.Agree
import LeanDag.Properties.Candidate
import LeanDag.Properties.Optional.Direct
import LeanDag.Properties.Optional.Quorate
import LeanDag.Properties.Optional.SelfParent
/-!
# Mahi-Mahi as a carrier, and the properties its rules give

The five properties needing no induction; `Banded` and the two liveness
properties live in `Properties.lean`. Each wave width needs its own
carrier, since `DagRule.Decided` fixes no wave length; conditions such
as `2 ≤ w` are therefore stated at the theorem, not inside the
property, since a rule's carrier already fixes `w`.
-/

namespace LeanDag

namespace MahiMahiProperties

open LeanDag.Properties

variable {Validator : Type} [Fintype Validator] [DecidableEq Validator]
variable [F : Faults Validator]
variable {BlockId : Type} [LinearOrder BlockId] {Payload : Type}

/-- **Mahi-Mahi as a carrier**, one per wave width. -/
def mahiMahiRule (w : ℕ) : DagRule Validator BlockId Payload :=
  (MahiMahi.mahiMahiAnchored Validator BlockId Payload w).toDagRule

/-- **And they are quorate**, at the core's fault model: validity's
counting clause read at the carrier, which is what chain quality reads
(`Properties/Arcs/Quality.lean`). -/
theorem quorate (w : ℕ) : Quorate (mahiMahiRule (Validator := Validator) (BlockId := BlockId)
    (Payload := Payload) w) (coreReliability Validator) :=
  fun U => BlockUniverse.quorateOn U

/-- **P3′ at the carrier.** -/
theorem selfParent (w : ℕ) : SelfParent (mahiMahiRule (Validator := Validator)
    (BlockId := BlockId) (Payload := Payload) w) :=
  fun U b hb hr => (U.valid b hb).self_parent hr

/-- **One block per correct author per round.** -/
theorem noEquiv (w : ℕ) : NoEquiv (mahiMahiRule (Validator := Validator) (BlockId := BlockId)
    (Payload := Payload) w) (coreReliability Validator) :=
  fun U b c hb hc hbc heq hr => U.no_equivocation b hb c hc hbc heq hr

/-- **Two views decide alike.** MM2 under the property's name, at the
widths its safety arc covers. -/
theorem agree {w : ℕ} (hw : 2 ≤ w) :
    Agree (mahiMahiRule (Validator := Validator) (BlockId := BlockId) (Payload := Payload) w) :=
  AnchoredRule.agree (MahiMahi.mahiMahiLaws hw)

/-- **A commit names the slot's candidate.** Both committing
constructors carry `IsLeaderBlock`. -/
theorem commitsCandidate (w : ℕ) :
    CommitsCandidate (mahiMahiRule (Validator := Validator) (BlockId := BlockId)
      (Payload := Payload) w) :=
  AnchoredRule.commitsCandidate

/-- **And a direct commit is a verdict**, at Mahi-Mahi's own direct
predicate. -/
theorem commitsDirect (w : ℕ) :
    CommitsDirect (mahiMahiRule (Validator := Validator) (BlockId := BlockId)
      (Payload := Payload) w)
      (fun {U} V L r => MahiMahi.DirectCommitIn U V w L r) :=
  AnchoredRule.commitsDirect

end MahiMahiProperties

end LeanDag
