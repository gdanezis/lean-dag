import LeanDag.Barnacle.Model.Live
import LeanDag.Common.Anchored.Band
import LeanDag.Common.History
import LeanDag.Timed.Coverage
/-!
# An anchored rule is a Barnacle rule

Every commit rule of this development is an `AnchoredRule`
(`Common/Anchored.lean`): a wave, a direct commit and a direct skip,
rungs and a tie. Barnacle's interface asks for less than that and for
one thing more — the full and history views, the wave length, the
direct commit as a decidable predicate — and all of it is read off the
anchored rule, here, once.

`ofAnchored R` is the base rule: the record as universe
(`AnchoredRule.toDagRule`), `View.full` and `BlockRecord.historyView`
for the two views, `R.wave + 1` for the wave length — the gap an anchor
must clear, which is what the indirect law of `LiveRule.Descent` reads —
and `R.Commit` for the direct predicate. `ofAnchoredOn R I` is the same
over the records satisfying an invariant `I`, for the two rules whose
laws hold only under one (Orcaella's `HonestNoEquiv`,
Optimal-Hydrozoan's `LeaderExcludedAll`).

`liveOfAnchored R rel` adds the notion of a good DAG: good from `Rnd` to
`N` when a quorum of the fault model `rel` is synchronised from `Rnd`
and populates every round to `N` — `Timed.Good` at the carrier. Every
live rule of the development is this at its own fault model. `Good`
stays a field of `LiveRule` all the same: a rule with another notion of
a good DAG, such as the test rules of `LeanDagTest/Barnacle/Progress.lean`
that pin one universe, is a live rule too.

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

/-- **An anchored rule under an invariant, as a base rule**: the records
satisfying `I` are the universes. -/
def ofAnchoredOn (R : AnchoredRule Validator BlockId Payload P honest)
    (I : BlockRecord Validator BlockId Payload P honest → Prop) :
    BaseRule Validator BlockId Payload where
  toDagRule := R.toDagRuleOn I
  full := fun U => View.full U.val
  historyView := fun U A hA => U.val.historyView A hA
  waveLength := R.wave + 1
  DirectCommitIn := fun {U} V L r => R.Commit U.val V L r
  decDirect := fun {U} V L r => R.decCommit U.val V L r

/-- **An anchored rule as a live rule**, at a fault model: a DAG is good
when a quorum of the model is synchronised and populates it. -/
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
