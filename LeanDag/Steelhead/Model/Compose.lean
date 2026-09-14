import LeanDag.Common.Anchored
/-!
# Steelhead — the composite of a family of rules

The paper's Theorem 1 is stated for any two rules of the interface, not
for the Mysticeti and Mahi-Mahi pair alone: whichever rule a round's
slot is decided by, the anchor search reads the slot's own rule. The
composite of a family of anchored rules, one per round, does exactly
that: every datum of a slot, its wave offset, its direct predicates and
its rungs of link, is the datum of the rule of the slot's round, while
the number of rungs and the tie-break, which the relation reads without
a slot, are the family's common ones. `steelheadAnchored w` is this
composite at Mahi-Mahi's rule read at `w r` (`Interface/Statement.lean`,
SH16c).

**Definitions only**, as in the other model files.
-/

namespace LeanDag

namespace Steelhead

variable {Validator : Type*} {BlockId : Type*} {Payload : Type*}
variable {P : Validity Validator BlockId Payload} {honest : Finset Validator}

/-- **The composite of a family of rules**, one per round: the slot proposed at round `r` is
decided by `rules r`, whose wave offset, direct predicates and rungs it takes; the rung count and
the tie-break are read from the rule of round `0`, the family being asked to agree on them. -/
def compose (rules : ℕ → AnchoredRule Validator BlockId Payload P honest) :
    AnchoredRule Validator BlockId Payload P honest where
  waveAt := fun r => (rules r).waveAt r
  Commit := fun U V L r => (rules r).Commit U V L r
  decCommit := fun U V L r => (rules r).decCommit U V L r
  Skip := fun U V S k => (rules (S.slotRound k)).Skip U V S k
  rungs := (rules 0).rungs
  Link := fun i U A L S k => (rules (S.slotRound k)).Link i U A L S k
  tie := (rules 0).tie

end Steelhead

end LeanDag
