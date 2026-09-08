import LeanDag.Barnacle.Model.Live
import LeanDag.Common.Anchored.Band
import LeanDag.Common.History
import LeanDag.Timed.Coverage
/-!
# An anchored rule is a Barnacle rule

`ofAnchored R` is the base rule of an anchored rule: the record as
universe, `View.full` and `BlockRecord.historyView` for the two views,
`R.wave + 1` for the wave length — the gap an anchor must clear — and
`R.Commit` for the direct predicate. `ofAnchoredVia R f` is the same over
any type projecting to records, and `ofAnchoredOn R I` over the records
satisfying an invariant `I`. `liveOfAnchored R rel` adds
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

/-- **An anchored rule read through a projection, as a base rule**: the
universes are any type projecting to records. -/
def ofAnchoredVia (R : AnchoredRule Validator BlockId Payload P honest) {X : Type}
    (f : X → BlockRecord Validator BlockId Payload P honest) :
    BaseRule Validator BlockId Payload where
  toDagRule := R.toDagRuleVia f
  full := fun U => View.full (f U)
  historyView := fun U A hA => (f U).historyView A hA
  waveLength := R.wave + 1
  DirectCommitIn := fun {U} V L r => R.Commit (f U) V L r
  decDirect := fun {U} V L r => R.decCommit (f U) V L r

/-- **An anchored rule under an invariant, as a base rule.** -/
abbrev ofAnchoredOn (R : AnchoredRule Validator BlockId Payload P honest)
    (I : BlockRecord Validator BlockId Payload P honest → Prop) :
    BaseRule Validator BlockId Payload :=
  ofAnchoredVia R (fun U : {U : BlockRecord Validator BlockId Payload P honest // I U} => U.val)

/-- **An anchored rule as a live rule**, at a fault model. -/
def liveOfAnchored (R : AnchoredRule Validator BlockId Payload P honest)
    (rel : Reliability Validator) : LiveRule Validator BlockId Payload :=
  { ofAnchored R with Good := Timed.Good R.toDagRule rel }

/-- **An anchored rule read through a projection, as a live rule.** -/
def liveOfAnchoredVia (R : AnchoredRule Validator BlockId Payload P honest) {X : Type}
    (f : X → BlockRecord Validator BlockId Payload P honest) (rel : Reliability Validator) :
    LiveRule Validator BlockId Payload :=
  { ofAnchoredVia R f with Good := Timed.Good (R.toDagRuleVia f) rel }

/-- **An anchored rule under an invariant, as a live rule.** -/
abbrev liveOfAnchoredOn (R : AnchoredRule Validator BlockId Payload P honest)
    (I : BlockRecord Validator BlockId Payload P honest → Prop) (rel : Reliability Validator) :
    LiveRule Validator BlockId Payload :=
  liveOfAnchoredVia R (fun U : {U : BlockRecord Validator BlockId Payload P honest // I U} => U.val)
    rel

end Barnacle

end LeanDag
