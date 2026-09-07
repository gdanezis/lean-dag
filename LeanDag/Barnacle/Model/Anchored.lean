import LeanDag.Barnacle.Model.Live
import LeanDag.Common.Anchored.Band
import LeanDag.Common.History
import LeanDag.Timed.Coverage
/-!
# An anchored rule is a Barnacle rule

`ofAnchored R` is the base rule of an anchored rule: the record as
universe, `View.full` and `BlockRecord.historyView` for the two views,
`R.wave + 1` for the wave length — the gap an anchor must clear — and
`R.Commit` for the direct predicate. `ofAnchoredOn R I` is the same over
the records satisfying an invariant `I`. `liveOfAnchored R rel` adds
`Timed.Good` at the fault model `rel` as the notion of a good DAG.
`Good` stays a field of `LiveRule` so that a rule may pin another
notion, as the witnesses of `LeanDagTest/Barnacle/Progress.lean` do.

**Trusted core of the arc: definitions only.**
-/

namespace LeanDag

namespace Barnacle

variable {Validator : Type} [Fintype Validator] [DecidableEq Validator]
variable {BlockId : Type} [DecidableEq BlockId] {Payload : Type}
variable {P : Validity Validator BlockId Payload} {honest : Finset Validator} [P.Mechanised]

/-- **An anchored rule as a base rule.** -/
def ofAnchored (R : AnchoredRule Validator BlockId Payload P honest) :
    BaseRule Validator BlockId Payload where
  toDagRule := R.toDagRule
  full := fun U => View.full U
  historyView := fun U A hA => U.historyView A hA
  waveLength := R.wave + 1
  DirectCommitIn := fun {U} V L r => R.Commit U V L r
  decDirect := fun {U} V L r => R.decCommit U V L r

/-- **An anchored rule under an invariant, as a base rule.** -/
def ofAnchoredOn (R : AnchoredRule Validator BlockId Payload P honest)
    (I : BlockRecord Validator BlockId Payload P honest → Prop) :
    BaseRule Validator BlockId Payload where
  toDagRule := R.toDagRuleOn I
  full := fun U => View.full U.val
  historyView := fun U A hA => U.val.historyView A hA
  waveLength := R.wave + 1
  DirectCommitIn := fun {U} V L r => R.Commit U.val V L r
  decDirect := fun {U} V L r => R.decCommit U.val V L r

/-- **An anchored rule as a live rule**, at a fault model. -/
def liveOfAnchored (R : AnchoredRule Validator BlockId Payload P honest)
    (rel : Reliability Validator) : LiveRule Validator BlockId Payload :=
  { ofAnchored R with Good := Timed.Good R.toDagRule rel }

/-- **An anchored rule under an invariant, as a live rule.** -/
def liveOfAnchoredOn (R : AnchoredRule Validator BlockId Payload P honest)
    (I : BlockRecord Validator BlockId Payload P honest → Prop) (rel : Reliability Validator) :
    LiveRule Validator BlockId Payload :=
  { ofAnchoredOn R I with Good := Timed.Good (R.toDagRuleOn I) rel }

end Barnacle

end LeanDag
