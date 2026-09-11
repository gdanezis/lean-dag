import LeanDag.Adaptive.Score.Proof
import LeanDag.Adaptive.Agreement.Proof
import LeanDag.Adaptive.Ledger.Proof
/-!
# The segmented arc, applied

What AL11 is for: a reputation score is an update rule, and the
segmented arc's results hold of it with no clause left over
(`adaptive-leaders.md` §9, step 4). The rule is generic in the base
rule, so these read at an arbitrary one; the witnesses on data are step
7's.

Everything below is an application of a proved statement, not a
restatement of one.
-/

namespace LeanDagTest

namespace Adaptive

open LeanDag LeanDag.Adaptive LeanDag.Barnacle

variable {Validator : Type} [Fintype Validator] [DecidableEq Validator]
variable {BlockId : Type} [DecidableEq BlockId] {Payload : Type}
variable {R : BaseRule Validator BlockId Payload} {P : Params}

/-- **AL13 at any score.** Two runs over one universe from one genesis
configuration agree on the configuration in force, and `AL11a` is what
discharges agreement's only clause on the rule. -/
example (ha : Properties.Agree R.toDagRule) (score : Score R) (C₀ : Config Validator)
    (U : R.Universe) (V₁ V₂ : R.View U) (K₁ K₂ : ℕ)
    (R₁ : SegRun R P (rule score) C₀ U V₁ K₁) (R₂ : SegRun R P (rule score) C₀ U V₂ K₂)
    (k : ℕ) (hk : k ≤ min K₁ K₂) :
    R₁.cfg k = R₂.cfg k :=
  (Agreement.holds _ _ _ R ha P (rule score) C₀ (Score.rule_anchored score)
    U V₁ V₂ K₁ K₂ R₁ R₂ k hk).2.1

/-- **AL14 at any score.** The output is one list across two views, to
every height both reach. -/
example (ha : Properties.Agree R.toDagRule) (hc : Properties.CommitsCandidate R.toDagRule)
    (score : Score R) (C₀ : Config Validator)
    (U : R.Universe) (V₁ V₂ : R.View U) (K₁ K₂ : ℕ)
    (R₁ : SegRun R P (rule score) C₀ U V₁ K₁) (R₂ : SegRun R P (rule score) C₀ U V₂ K₂)
    (K : ℕ) (hK : K ≤ min K₁ K₂) :
    R₁.ledgerUpto K = R₂.ledgerUpto K :=
  ((Ledger.holds _ _ _ R ha hc P (rule score) C₀ (Score.rule_anchored score)).1
    U V₁ V₂ K₁ K₂ R₁ R₂).2 K hK

/-- **AL11b at any score that keeps the shape.** The rule a run needs to
stay within its parameters. -/
example (score : Score R) (hk : score.Keeps) : UpdBounded P (rule score) :=
  Score.rule_bounded P score hk

/-- **AL11d.** Under the constant score the rule is `constRule`. -/
example : rule (Score.const R) = constRule R := Score.rule_const

end Adaptive

end LeanDagTest
