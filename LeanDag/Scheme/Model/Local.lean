import LeanDag.Scheme.Model.Rule
import LeanDag.Common.Anchored.Band
import LeanDag.Properties.Support
/-!
# A local vote, and the family's carrier

`docs/scheme.md` §9.1. A vote is **local** when it survives a band: two
records agreeing on a band of rounds from the slot's round up to the
voter give the voter one vote for the slot. `leastSel` and
`votedBlockSel` are local (`Scheme/Helpers/Local.lean`). The band is
`AgreeBand` at any anchored rule's carrier: its fields read the record's
`ids` and `block` only.

`schemeRule p σ` is the decider at `p` and `σ` as a carrier, on block
records, whose honest validators do not equivocate; `familySupport` is
its support: a block certifies a candidate a wave below
it when the decider's `IsCert` holds.

A record whose non-equivocating validators form a larger set than its
honest set, as the hybrid arc's records with their crash-prone validators,
is read at that set by `withHonest`.

Definitions only; the properties are `Scheme/Properties.lean`.
-/

namespace LeanDag

namespace Scheme

variable {Validator : Type} [Fintype Validator] [DecidableEq Validator]
variable {BlockId : Type} [DecidableEq BlockId] {Payload : Type}
variable {P : Validity Validator BlockId Payload} {honest : Finset Validator} [P.Mechanised]

/-- **A local vote**: a voter in a band, reading a slot at or above the
band's floor, votes alike in both records. -/
def VoteSel.Local (σ : VoteSel Validator BlockId Payload P honest) : Prop :=
  ∀ (R : AnchoredRule Validator BlockId Payload P honest)
    {U U' : BlockRecord Validator BlockId Payload P honest} {lo hi g g' : ℕ} {q : BlockId}
    {a : Validator} {r r' : ℕ},
    Properties.AgreeBand R.toDagRule U U' lo hi g g' → q ∈ U.ids →
    lo ≤ (U.block q).round + g → (U.block q).round + g ≤ hi →
    lo ≤ r + g → r + g = r' + g' → σ.sel U' q a r' = σ.sel U q a r

/-- **A record read at a larger honest set**: a record in which the
validators of `H` do not equivocate is a record whose honest set is `H`,
with the same blocks. -/
def withHonest (U : BlockRecord Validator BlockId Payload P honest) {H : Finset Validator}
    (h : U.NoEquivOn H) : BlockRecord Validator BlockId Payload P H where
  ids := U.ids
  block := U.block
  complete := U.complete
  valid := U.valid
  no_equivocation := h

variable [LinearOrder BlockId]

/-- **The family's carrier**: the decider at `p` and `σ`, on block
records. -/
def schemeRule (p : Params) (σ : VoteSel Validator BlockId Payload P honest) :
    Properties.DagRule Validator BlockId Payload :=
  (schemeAnchored p σ).toDagRule

/-- **The family's support.** -/
def familySupport (p : Params) (σ : VoteSel Validator BlockId Payload P honest) :
    Properties.Support (schemeRule p σ) where
  waveAt := fun _ => p.waveLength - 1
  Certifies := fun U c L => IsCert p σ U c L

end Scheme

end LeanDag
