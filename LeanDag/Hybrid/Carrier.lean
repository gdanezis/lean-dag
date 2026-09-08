import LeanDag.Hybrid.Decision
import LeanDag.Properties.Agree
import LeanDag.Properties.Candidate
import LeanDag.Properties.Optional.Direct
import LeanDag.Properties.Optional.Quorate
import LeanDag.Properties.Optional.SelfParent
/-!
# Hybrid as a carrier, and the three properties its own rules give

`docs/porting-plan.md` step 2: the carrier at indirect threshold `k`.
The universe is a subtype `{U // HonestNoEquiv U}` rather than a
hypothesis of the theorems, since `Properties.Agree` is unconditional
and has no graded form; `Admissible Validator k` stays a hypothesis of
the two theorems that need it, since admissibility is a fact about the
committee, not the DAG.
-/

namespace LeanDag

namespace HybridProperties

open LeanDag.Properties

variable {Validator : Type} [Fintype Validator] [DecidableEq Validator]
variable [H : HybridFaults Validator]
variable {BlockId : Type} [LinearOrder BlockId] {Payload : Type}

/-- **Hybrid as a carrier**, one per indirect threshold. -/
def hybridRule (k : ℕ) : DagRule Validator BlockId Payload :=
  (Hybrid.hybridAnchored Validator BlockId Payload k).toDagRuleOn HonestNoEquiv

/-- **Hybrid's universes are quorate**, at the derived fault model:
`f = fb + fc`, so a quorum of `n − fb − fc` distinct authors is what
validity already asks for. -/
theorem quorate (k : ℕ) : Quorate (hybridRule (Validator := Validator) (BlockId := BlockId)
    (Payload := Payload) k) (coreReliability Validator) :=
  fun U => BlockUniverse.quorateOn U.val

/-- **P3′ at the carrier.** -/
theorem selfParent (k : ℕ) : SelfParent (hybridRule (Validator := Validator)
    (BlockId := BlockId) (Payload := Payload) k) :=
  fun U b hb hr => (U.val.valid b hb).self_parent hr

/-- **One block per correct author per round.** -/
theorem noEquiv (k : ℕ) : NoEquiv (hybridRule (Validator := Validator) (BlockId := BlockId)
    (Payload := Payload) k) (coreReliability Validator) :=
  fun U b c hb hc hbc heq hr => U.val.no_equivocation b hb c hc hbc heq hr

/-- **Two views decide alike.** H6 under the property's name, and
unconditional because non-equivocation is now a field of the universe
rather than a premise. -/
theorem agree {k : ℕ} (hk : Hybrid.Admissible Validator k) :
    Agree (hybridRule (Validator := Validator) (BlockId := BlockId) (Payload := Payload) k) :=
  AnchoredRule.agreeOn (Hybrid.hybridLaws hk) (fun _ _ h => h)

/-- **A commit names the slot's candidate.** -/
theorem commitsCandidate (k : ℕ) : CommitsCandidate
    (hybridRule (Validator := Validator) (BlockId := BlockId) (Payload := Payload) k) :=
  AnchoredRule.commitsCandidateOn

/-- **And a direct commit is a verdict**, at Hybrid's own direct
predicate. -/
theorem commitsDirect (k : ℕ) : CommitsDirect
    (hybridRule (Validator := Validator) (BlockId := BlockId) (Payload := Payload) k)
    (fun {U} V L r => Hybrid.DirectCommitIn U.val V L r) :=
  AnchoredRule.commitsDirectOn

end HybridProperties

end LeanDag
