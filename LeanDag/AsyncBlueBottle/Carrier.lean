import LeanDag.AsyncBlueBottle.Helpers.Decision
import LeanDag.Properties.Agree
import LeanDag.Properties.Candidate
import LeanDag.Properties.Optional.Direct
import LeanDag.Properties.Optional.Quorate
import LeanDag.Properties.Optional.SelfParent
/-!
# Async BlueBottle as a carrier, and the properties its rules give

The five properties needing no induction; `Banded` and the two liveness
properties live in `Properties.lean`. The carrier is the anchored rule's,
on the core's universes at the `5f + 1` committee.
-/

namespace LeanDag

namespace AsyncBlueBottleProperties

open LeanDag.Properties

variable {Validator : Type} [Fintype Validator] [DecidableEq Validator]
variable [F : Faults5 Validator]
variable {BlockId : Type} [LinearOrder BlockId] {Payload : Type}

/-- **Async BlueBottle as a carrier.** -/
def asyncBlueBottleRule : DagRule Validator BlockId Payload :=
  (AsyncBlueBottle.asyncBlueBottleAnchored Validator BlockId Payload).toDagRule

/-- **The universes are quorate**, at the core's fault model: validity's
counting clause read at the carrier, which is what chain quality reads
(`Properties/Arcs/Quality.lean`). -/
theorem quorate : Quorate (asyncBlueBottleRule (Validator := Validator) (BlockId := BlockId)
    (Payload := Payload)) (coreReliability Validator) :=
  fun U => BlockUniverse.quorateOn U

/-- **P3′ at the carrier.** -/
theorem selfParent {rel : Reliability Validator} {R₀ : ℕ} :
    SelfParent (asyncBlueBottleRule (Validator := Validator)
    (BlockId := BlockId) (Payload := Payload)) rel R₀ :=
  fun U b hb _ hr => (U.valid b hb).self_parent (Nat.lt_of_le_of_lt (Nat.zero_le _) hr)

/-- **One block per correct author per round.** -/
theorem noEquiv : NoEquiv (asyncBlueBottleRule (Validator := Validator) (BlockId := BlockId)
    (Payload := Payload)) (coreReliability Validator) :=
  fun U b c hb hc hbc heq hr => U.no_equivocation b hb c hc hbc heq hr

/-- **Two views decide alike.** ABB5 under the property's name. -/
theorem agree :
    Agree (asyncBlueBottleRule (Validator := Validator) (BlockId := BlockId)
      (Payload := Payload)) :=
  AnchoredRule.agree AsyncBlueBottle.asyncBlueBottleLaws

/-- **A commit names the slot's candidate.** Both committing
constructors carry `IsLeaderBlock`. -/
theorem commitsCandidate :
    CommitsCandidate (asyncBlueBottleRule (Validator := Validator) (BlockId := BlockId)
      (Payload := Payload)) :=
  AnchoredRule.commitsCandidate

/-- **And a direct commit is a verdict**, at the arc's own direct
predicate. -/
theorem commitsDirect :
    CommitsDirect (asyncBlueBottleRule (Validator := Validator) (BlockId := BlockId)
      (Payload := Payload))
      (fun {U} V L r _ => AsyncBlueBottle.DirectCommitIn U V L r) :=
  AnchoredRule.commitsDirect

end AsyncBlueBottleProperties

end LeanDag
