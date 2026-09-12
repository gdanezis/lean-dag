import LeanDag.Adaptive.Score.Proof
import LeanDag.Adaptive.Agreement.Proof
import LeanDag.Adaptive.Ledger.Proof
import LeanDag.Adaptive.Conservativity.Proof
import LeanDag.Adaptive.Validity.Proof
import LeanDag.Adaptive.Progress.Proof
import LeanDag.Barnacle.Helpers.Heads
import LeanDag.Adaptive.Headline
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

/-- **AL18a on the two facts a designer reaches for**: one configuration
in force, and one anchor closing it. -/
example (ha : Properties.Agree R.toDagRule) (score : Score R) (C₀ : Config Validator)
    (U : R.Universe) (V₁ V₂ : R.View U) (K₁ K₂ : ℕ)
    (R₁ : SegRun R P (rule score) C₀ U V₁ K₁) (R₂ : SegRun R P (rule score) C₀ U V₂ K₂)
    (k : ℕ) (hk : k < min K₁ K₂) :
    R₁.cfg k = R₂.cfg k ∧ R₁.anchor k = R₂.anchor k :=
  let h := score_safe ha score C₀ U V₁ V₂ R₁ R₂ k (le_of_lt hk)
  ⟨h.2.1, (h.2.2.2 hk).1⟩

/-- **AL18b**: the output is one list across two views, to every height
both reach. -/
example (ha : Properties.Agree R.toDagRule) (hc : Properties.CommitsCandidate R.toDagRule)
    (score : Score R) (C₀ : Config Validator)
    (U : R.Universe) (V₁ V₂ : R.View U) (K₁ K₂ : ℕ)
    (R₁ : SegRun R P (rule score) C₀ U V₁ K₁) (R₂ : SegRun R P (rule score) C₀ U V₂ K₂)
    (K : ℕ) (hK : K ≤ min K₁ K₂) :
    R₁.ledgerUpto K = R₂.ledgerUpto K :=
  (score_ledger ha hc score C₀).1 U V₁ V₂ K₁ K₂ R₁ R₂ K hK

/-- **AL11b at any score that keeps the shape.** The rule a run needs to
stay within its parameters. -/
example (score : Score R) (hk : score.Keeps) : UpdBounded P (rule score) :=
  Score.rule_bounded P score hk

/-- **AL11d.** Under the constant score the rule is `constRule`. -/
example : rule (Score.const R) = constRule R := Score.rule_const

/-- **AL15a at the constant rule**, which `Score.rule_const` says is the
constant score: every configuration the run determines is the genesis
one, and the back-off never moves. -/
example (C₀ : Config Validator) (U : R.Universe) (V : R.View U) (K : ℕ)
    (Rn : SegRun R P (constRule R) C₀ U V K) (k : ℕ) (hk : k ≤ K) :
    Rn.cfg k = C₀ ∧ Rn.backoff k = 0 :=
  (Conservativity.holds _ _ _ R P C₀).1 U V K Rn k hk

/-- **AL15b**: and its verdicts are verdicts of the genesis schedule. -/
example (C₀ : Config Validator) (U : R.Universe) (V : R.View U) (K : ℕ)
    (Rn : SegRun R P (constRule R) C₀ U V K) (k : ℕ) (hk : k < K) (κ : ℕ)
    (h1 : Rn.start k < C₀.roundOf κ) (h2 : C₀.roundOf κ ≤ C₀.roundOf (Rn.anchor k)) :
    R.Decided C₀.sched V κ (Rn.vdct k κ) :=
  (Conservativity.holds _ _ _ R P C₀).2 U V K Rn k hk κ h1 h2

/-- **AL15c at any score.** A good author's block two rounds below a
closed configuration's boundary is in the history of the block that
configuration commits — no rotation hypothesis, and the author need
never lead again. -/
example {RL : LiveRule Validator BlockId Payload}
    (hc : Properties.CommitsCandidate RL.toBaseRule.toDagRule) (score : Score RL.toBaseRule)
    (C₀ : Config Validator) (slack : ℕ) :
    Validity.Delivered RL P (rule score) C₀ slack :=
  Validity.holds _ _ _ RL hc P (rule score) C₀ slack

/-! ## AL16 at a permuting score

The liveness clause ranges over the configurations the rule can emit, not
over one fixed schedule. Take the clause to be "the heads are a
permutation of `head`": a score that only permutes keeps it, and every
configuration meeting it is live at `head`'s own gap, because runs of
heads transfer along a permutation. -/

section Liveness

variable {RL : LiveRule Validator BlockId Payload} {slack c₀ : ℕ}

/-- The clause: this configuration's heads are a permutation of `head`. -/
def Permuted (head : ℕ → Validator) (C : Config Validator) : Prop :=
  ∃ σ : Equiv.Perm Validator, C.head = fun ρ => σ (head ρ)

/-- **The liveness hypothesis AL16b asks for, discharged.** Every
configuration whose heads permute `head` is live at `head`'s gap. -/
theorem liveOn_of_permuted (hD : RL.Descent slack) (hw : 0 < RL.waveLength)
    {head : ℕ → Validator}
    (hheads : ∀ T : Finset Validator, Fintype.card Validator ≤ T.card + slack →
      HeadsRun head T RL.waveLength c₀) :
    ∀ C : Config Validator, C.InBounds P → Permuted head C → RL.LiveOn C.sched c₀ := by
  rintro C _ ⟨σ, hσ⟩
  exact liveOn_of_permuted_heads C hD hw hheads σ hσ

/-- **AL18c at a permuting score.** Runs of every height exist under the
horizon, with the liveness clause discharged from runs of heads and the
score's own preservation of the clause. -/
example (ha : Properties.Agree RL.toBaseRule.toDagRule) (hD : RL.Descent slack)
    (hw : 0 < RL.waveLength) {head : ℕ → Validator}
    (hheads : ∀ T : Finset Validator, Fintype.card Validator ≤ T.card + slack →
      HeadsRun head T RL.waveLength c₀)
    (score : Score RL.toBaseRule) (hk : score.Keeps)
    (hperm : ∀ (U : RL.Universe) (V : RL.View U) (v : ℕ → Option BlockId)
      (C : Config Validator), Permuted head C → Permuted head (score U V v C))
    (C₀ : Config Validator) (h₀ : C₀.InBounds P) (hQ₀ : Permuted head C₀)
    (U : RL.Universe) (V : RL.View U) (Rnd N : ℕ) (hgood : RL.Good U Rnd N)
    (hcov : RL.toBaseRule.CoversUpto U V N) (hRnd : Rnd ≤ 1)
    (K : ℕ) (hK : horizon P RL c₀ K ≤ N) :
    Nonempty (SegRun RL.toBaseRule P (rule score) C₀ U V K) :=
  (score_live ha score hk (Permuted head) hperm C₀ c₀).2
    (liveOn_of_permuted hD hw hheads) h₀ hQ₀ U V Rnd N hgood hcov hRnd K hK

end Liveness

end Adaptive

end LeanDagTest
