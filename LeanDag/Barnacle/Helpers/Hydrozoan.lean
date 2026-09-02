import LeanDag.Barnacle.Model.Rule
import LeanDag.Hydrozoan.Model.Decided

/-!
# Hydrozoan instance helpers

Not part of the audit surface. Three constructions the Hydrozoan
instantiation needs, and nothing else.

**Every Hydrozoan name is written out.** This file is the one place the
two block types meet, and inside `namespace LeanDag` a bare `Block` or
`BlockUniverse` resolves to the core's. Opening `LeanDag.Hydrozoan`
would leave which one is meant to the elaborator, at exactly the point
where the reader needs to see it, so the qualification is deliberate
rather than incidental.

**The block adapter.** `Barnacle.BaseRule.block` returns the core's
`Block`, which carries a payload and spells its fields `creator` and
`refs`; Hydrozoan's carries neither a payload nor those names. `adapt`
renames and supplies `()`. The three field equations are `rfl`, so
every clause the interface states over `refs` reads Hydrozoan's
`parents` with no rewrite.

**The causal structure.** `Causality.lean` is stated over a raw lookup
and id-set through `CausalStructure`, whose two fields are completeness
and the predecessor condition — no quorum, no fault model, no validity
beyond that. A Hydrozoan universe supplies both from its own fields, so
the history layer applies to it with **no side condition**: neither the
self-parent clause of `docs/hydrozoan-integration.md` §3 nor the
committee condition of its §2 is consumed here, which is why this file
imports no bridge.

**The history view.** The interface's `historyView_ids` law demands a
view whose ids are exactly `historyFrom`, so the view is *defined* with
those ids and the law is `rfl`. The closure proof is `historyViewOf`'s,
run over the adapted lookup.
-/

namespace LeanDag

namespace Barnacle

namespace Hydrozoan

variable {Replica : Type} [Fintype Replica] [DecidableEq Replica]
variable [LeanDag.Hydrozoan.Faults Replica]
variable {BlockId : Type}

/-- A Hydrozoan block as a core block: `author` becomes `creator`,
`parents` becomes `refs`, and the payload is `Unit`. -/
def adapt (b : LeanDag.Hydrozoan.Block Replica BlockId) :
    LeanDag.Block Replica BlockId Unit :=
  { round := b.round, creator := b.author, refs := b.parents, payload := () }

/-- The universe's lookup, adapted. -/
def adaptBlk (U : LeanDag.Hydrozoan.BlockUniverse Replica BlockId) :
    BlockId → LeanDag.Block Replica BlockId Unit :=
  fun i => adapt (U.block i)

@[simp] theorem adaptBlk_round (U : LeanDag.Hydrozoan.BlockUniverse Replica BlockId)
    (i : BlockId) : (adaptBlk U i).round = (U.block i).round := rfl

@[simp] theorem adaptBlk_creator (U : LeanDag.Hydrozoan.BlockUniverse Replica BlockId)
    (i : BlockId) : (adaptBlk U i).creator = (U.block i).author := rfl

@[simp] theorem adaptBlk_refs (U : LeanDag.Hydrozoan.BlockUniverse Replica BlockId)
    (i : BlockId) : (adaptBlk U i).refs = (U.block i).parents := rfl

/-- **A Hydrozoan universe is a causal structure.** Completeness is its
own field; the predecessor condition is the first field of its
validity. Nothing else of `BlockUniverse` is read, which is what makes
the history layer available without a bridge. -/
theorem causalStructure (U : LeanDag.Hydrozoan.BlockUniverse Replica BlockId) :
    CausalStructure (adaptBlk U) U.ids :=
  { complete := fun i hi j hj => U.complete i hi j hj
    refs_round := fun i hi j hj => (U.valid i hi).predecessor j hj }

variable [DecidableEq BlockId]

/-- Fast commit in view is a cardinality comparison, so it is decidable;
`Model/DirectRules.lean` leaves the instance to `Helpers/`, and the
interface's `decDirect` field needs it by synthesis rather than through
the `decide` tactic's unfolding. -/
instance decFastCommitInView (U : LeanDag.Hydrozoan.BlockUniverse Replica BlockId)
    (V : LeanDag.Hydrozoan.View U) (L : BlockId) (r : ℕ) :
    Decidable (LeanDag.Hydrozoan.FastCommitInView U V L r) :=
  inferInstanceAs (Decidable (_ ≤ _))

/-- Slow commit in view, likewise. -/
instance decSlowCommitInView (U : LeanDag.Hydrozoan.BlockUniverse Replica BlockId)
    (V : LeanDag.Hydrozoan.View U) (L : BlockId) (r : ℕ) :
    Decidable (LeanDag.Hydrozoan.SlowCommitInView U V L r) :=
  inferInstanceAs (Decidable (_ ≤ _))

/-- The causal history of a block of the universe, as a Hydrozoan view.
The ids are `historyFrom` on the nose, so the interface's
`historyView_ids` law is `rfl`. -/
def historyView (U : LeanDag.Hydrozoan.BlockUniverse Replica BlockId) (A : BlockId)
    (hA : A ∈ U.ids) : LeanDag.Hydrozoan.View U where
  ids := historyFrom (adaptBlk U) A
  subset_ids := (causalStructure U).history_subset_ids hA
  complete := fun _ hi _ hj =>
    ((causalStructure U).mem_history_iff hA).mpr
      ((((causalStructure U).mem_history_iff hA).mp hi).trans (ReachesFrom.single hj))

end Hydrozoan

end Barnacle

end LeanDag
