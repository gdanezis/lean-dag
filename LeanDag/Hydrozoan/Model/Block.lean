import LeanDag.Common.Block
import LeanDag.Hydrozoan.Model.Faults
/-!
# Blocks and validity

Hydrozoan's block is the shared one, with no payload: a round, a
creator, and the ids it references from the preceding round only — the
model has no weak links.
-/

namespace LeanDag

namespace Hydrozoan

/-- A Hydrozoan block: the shared block with no payload. -/
abbrev Block (Replica BlockId : Type*) := LeanDag.Block Replica BlockId Unit

section Validity

variable {Replica BlockId : Type*} [Fintype Replica] [DecidableEq Replica]
  [F : LeanDag.Hydrozoan.Faults Replica]

/-- Block validity, relative to a lookup function: `q` distinct-creator
references from the preceding round. The predecessor condition is
additive (`+1 =`, never `−1`), so the genesis case (`refs = ∅`) is
derivable rather than assumed. -/
structure ValidWrt (blk : BlockId → Block Replica BlockId)
    (b : Block Replica BlockId) : Prop where
  /-- Every reference sits in the immediately preceding round. -/
  predecessor : ∀ i ∈ b.refs, (blk i).round + 1 = b.round
  /-- A block never references the same creator twice. -/
  distinct_creators : ∀ i ∈ b.refs, ∀ j ∈ b.refs,
    (blk i).creator = (blk j).creator → i = j
  /-- Non-genesis blocks reference a DAG quorum of distinct creators. -/
  quorum : 0 < b.round → q Replica ≤ (creators blk b).card

end Validity

end Hydrozoan

end LeanDag
