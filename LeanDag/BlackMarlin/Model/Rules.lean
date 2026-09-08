import LeanDag.Common.Support
import LeanDag.Common.History
/-!
# Black Marlin — the commit rule

The rule of `delivery(r)` (Algorithm 2, L14–L17) of *DAG it off: Latency
Prefers No Common Coins* (arXiv:2508.14716v3), `black-marlin.md` §2. One
anchor is elected per round; the anchor of round `r` is committed when
it carries a quorum of support at round `r + 1` and the anchor of round
`r + 1` both references it and carries a quorum of support at round
`r + 2`. Three rounds, no certificate round, no threshold above `n − f`,
so the committee is the core's `n ≥ 3f + 1`.

The DAG layer is consumed unchanged: the paper's validity `V` is
`ValidWrt`, and its `supp` is the core's `supporters`, since
`distinct_creators` already forbids the twin `supp` excludes by hand.
The core's own addition, `self_parent`, restricts the universes below
but is used by none of the results. Only strong references are
modelled: the commit rule reads `strong`, so the arc is stated over the
core's `refs` and the paper's `strong(B)` is `Reaches U B` less its
reflexive step; weak references bear on delivery completeness, not the
rule, and are not modelled.

**Trusted core of the arc: definitions only.** No theorem lives in this
file or in `Decision.lean`.
-/

namespace LeanDag

namespace BlackMarlin

/-- **The anchor rotation.** Black Marlin elects one anchor per round —
the paper's `RR(r)`, round-robin in a deployment. A class of its own
rather than the core's round-indexed `Slots`, since every rule names
round `r + 1` explicitly; the two are reconciled once by
`RotationIsSchedule` (`Safety/Statement.lean`). -/
class Rotation (Validator : Type*) where
  /-- The validator elected to anchor round `r`. -/
  anchor : ℕ → Validator

variable {Validator : Type*} [Fintype Validator] [DecidableEq Validator]
variable [F : Faults Validator] [Rot : Rotation Validator]
variable {BlockId : Type*} [DecidableEq BlockId] {Payload : Type*}
variable {U : BlockUniverse Validator BlockId Payload}

/-- **`L` is an anchor block of round `r`**: a block of the universe, at
that round, by the validator the rotation elected for it. A predicate
rather than a function, since an equivocating elector may have several
anchor blocks at one round; the uniqueness the rule needs is a theorem
about supported anchors, not a property of the rotation. -/
def IsAnchor (U : BlockUniverse Validator BlockId Payload) (r : ℕ) (L : BlockId) : Prop :=
  L ∈ U.ids ∧ (U.block L).round = r ∧ (U.block L).creator = Rot.anchor r

instance (r : ℕ) (L : BlockId) : Decidable (IsAnchor U r L) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _))

/-- **`supp(L) ≥ n − f`** for a block proposed at round `r`: a quorum of
distinct validators reference `L` from round `r + 1`, through the core's
`supporters`, which counts authors so an equivocator contributes one
either way. The paper's cone-based side condition on `supp` coincides
with this, since a reference sits exactly one round below its referrer
(`predecessor`), reducing it to `distinct_creators`. -/
def Supported (U : BlockUniverse Validator BlockId Payload) (L : BlockId) (r : ℕ) : Prop :=
  quorumCard Validator ≤ (supporters U L (r + 1)).card

instance (L : BlockId) (r : ℕ) : Decidable (Supported U L r) :=
  inferInstanceAs (Decidable (_ ≤ _))

/-- **The anchors of round `r + 1` that link `L` to the round above**:
the second clause of L16, as a `Finset` of witnessing blocks — decidable
on a concrete DAG, as the core keeps `certificates` a `Finset` for the
same reason. -/
def linkers (U : BlockUniverse Validator BlockId Payload) (L : BlockId) (r : ℕ) :
    Finset BlockId :=
  (blocksAt U (r + 1)).filter
    (fun L' => (U.block L').creator = Rot.anchor (r + 1) ∧ L ∈ (U.block L').refs ∧
      Supported U L' (r + 1))

/-- **`L` is linked**: some anchor of the round above references it and
is itself supported — reference rather than reachability, the same
thing at a one-round gap since every reference sits immediately
below. -/
def Linked (U : BlockUniverse Validator BlockId Payload) (L : BlockId) (r : ℕ) : Prop :=
  (linkers U L r).Nonempty

instance (L : BlockId) (r : ℕ) : Decidable (Linked U L r) :=
  inferInstanceAs (Decidable (Finset.Nonempty _))

/-- **The commit rule** (L14–L17). The anchor of round `r` is committed
when it is supported and linked — the whole of what safety consumes,
since the descent and sort only order what this rule admits, which is
why the chain and prefix results are stated about `history` rather than
the sort (`black-marlin.md` §4). -/
def Committed (U : BlockUniverse Validator BlockId Payload) (L : BlockId) (r : ℕ) : Prop :=
  IsAnchor U r L ∧ Supported U L r ∧ Linked U L r

instance (L : BlockId) (r : ℕ) : Decidable (Committed U L r) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _))

end BlackMarlin

end LeanDag
