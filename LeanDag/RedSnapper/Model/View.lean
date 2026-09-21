import LeanDag.RedSnapper.Model.Universe

/-!
# Views

Trusted core: a **view** is one validator's local DAG — the blocks it
has received, validated, and stored. Views share the universe's lookup
`U.block`, so validators disagree only about *which* blocks they hold,
never about what an id denotes; validity, non-equivocation and the
self-parent chain are inherited from `U` unchanged.

Ref-closure is the local reading of the same DAG-building sentence the
universe's `complete` field encodes: a validator stores a block only
after its entire causal history has been validated, so everything a
stored block references is stored too.

Different correct validators may hold different views — that asymmetry
is what the cross-view agreement theorems are about. Byzantine
withholding is representable as a block present in the universe but
missing from a view. The consensusless routes of the fast path read a
view; the anchor routes read the universe (`docs/red-snapper.md`, D4,
D6).
-/

namespace LeanDag

namespace RedSnapper

/-- A view: one validator's local DAG — a subset of the universe that is
closed under references. -/
structure View {Validator BlockId Tx Obj : Type*} [Fintype Validator]
    [DecidableEq Validator] [F : Faults Validator]
    (U : Universe Validator BlockId Tx Obj) where
  /-- The ids this validator holds. -/
  ids : Finset BlockId
  /-- A view holds only blocks that exist. -/
  subset_ids : ids ⊆ U.ids
  /-- A view is closed downward: it holds everything its blocks
  reference. -/
  complete : ∀ i ∈ ids, ∀ j ∈ (U.block i).parents, j ∈ ids

end RedSnapper

end LeanDag
