import LeanDag.Adaptive.Score.Rule
/-!
# AL11 — what a reputation score owes

The three clauses a `Score` has to meet for the segmented arc to run on
it (`adaptive-leaders.md` §9), and they are met by the shape of the rule
rather than by hypothesis wherever that is possible.

* **AL11a, anchored** — the rule does not read the view, so two
  validators holding the anchor take the same step. This is the only
  clause AL13 and AL14 ask of an update rule.
* **AL11b, bounded** — from `Score.Keeps` alone: a score that moves the
  leaders and leaves the widths and the interval where they were keeps a
  configuration within the parameters, `Config.InBounds` mentioning
  nothing else.
* **AL11c, preserving** — whatever clause the score keeps, the rule
  keeps; this is what AL16 will ask, with the clause naming the head
  functions the score can emit.
* **AL11d, conservativity** — the constant score is `constRule`, so the
  segmented arc collapses onto the genesis configuration under it.

The score reads the anchor's causal history **as a view**, the shape
`Barnacle.observed` uses. `BaseRule.Laws.historyView_ids` pins that view
to `historyFrom` and BN2 says any two views holding the anchor restrict
to it identically, so a score's reading is agreed across validators by
construction and owes no clause of its own.

Statements only; the proofs live in `Proof.lean`.
-/

namespace LeanDag

namespace Adaptive

namespace Score

open Barnacle

variable {Validator : Type} [Fintype Validator] [DecidableEq Validator]
  {BlockId : Type} [DecidableEq BlockId] {Payload : Type}

/-- **AL11a, the rule is anchored.** -/
def RuleAnchored (R : BaseRule Validator BlockId Payload) (score : Score R) : Prop :=
  Anchored R (rule score)

/-- **AL11b, the rule keeps a configuration within the parameters**, from
`Score.Keeps` and nothing else. -/
def RuleBounded (R : BaseRule Validator BlockId Payload) (P : Params)
    (score : Score R) : Prop :=
  score.Keeps → UpdBounded P (rule score)

/-- **AL11c, the rule keeps what the score keeps.** -/
def RulePreserves (R : BaseRule Validator BlockId Payload) (score : Score R)
    (Q : Config Validator → Prop) : Prop :=
  (∀ (U : R.Universe) (V : R.View U) (C : Config Validator), Q C → Q (score U V C)) →
    UpdKeeps (rule score) Q

/-- **AL11d, the constant score is the constant rule.** -/
def ConstIsConst (R : BaseRule Validator BlockId Payload) : Prop :=
  rule (Score.const R) = constRule R

/-- What a score owes, for every base rule, parameter set, score and
clause. No law of the rule is consumed. -/
def Statement : Prop :=
  ∀ (Validator BlockId Payload : Type) [Fintype Validator] [DecidableEq Validator]
    [DecidableEq BlockId] (R : BaseRule Validator BlockId Payload) (P : Params)
    (score : Score R) (Q : Config Validator → Prop),
    RuleAnchored R score ∧ RuleBounded R P score ∧ RulePreserves R score Q ∧
      ConstIsConst R

end Score

end Adaptive

end LeanDag
