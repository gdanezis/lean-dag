import LeanDagTest.Hydrozoan.DirectLiveness
import LeanDagTest.Hydrozoan.BlockUniverse
import LeanDag.Integration.Hydrozoan.Universe

/-!
# The universe transport — witnesses

B3 of `docs/hydrozoan-integration.md` §10.3, evaluated before anything
rests on it.

**The side condition restricts, and is met.** `docs/hydrozoan-integration.md`
§11 records that the Hydrozoan arc's witness universes were built
without regard to the self-parent clause, no theorem of that arc
consuming it. Both halves are pinned here: the seven-replica universe
of `LeanDagTest/Hydrozoan/BlockUniverse.lean` fails `SelfParenting` —
its blocks `12` and `13` are authored by replicas `5` and `6` and
reference `{0, 1, 2, 3, 4}`, holding neither one's genesis — while the
low-fault universe `U7` of `LeanDagTest/Hydrozoan/DirectLiveness.lean`
satisfies it, every non-genesis block there referencing all three
blocks of the round below and so its own author's among them.

So the predicate is neither vacuous nor unsatisfiable, which is what
`docs/style.md` §3 asks of a definition before anything is proved from
it.

**The transport computes and round-trips.** `toCore U7` is a core
universe over the same identifiers, its blocks the adapted Hydrozoan
ones, and `ofCore` returns `U7` on the nose — the round trip is `rfl`,
structure eta making the two block functions one term.
-/

namespace LeanDagTest

namespace Integration

open LeanDag LeanDag.Integration.Hydrozoan

/-- The committee condition at the low-fault four-replica model
(`f = 0`, `c = 1`, `k = 1`), which is what makes the transport
available there. -/
instance factFour : Fact (HybridCommittee (Fin 4)) := ⟨by decide⟩

/-! ## The side condition is a real restriction -/

/-- The seven-replica universe does **not** self-parent: replicas `5`
and `6` build on `{0, 1, 2, 3, 4}`, which holds neither one's genesis
block. -/
example : ¬ SelfParenting LeanDagTest.Hydrozoan.U := by decide

/-- The low-fault universe does: each non-genesis block references
every block of the round below, its own author's included. -/
theorem selfParenting_U7 : SelfParenting LeanDagTest.Hydrozoan.U7 := by decide

/-! ## The transport computes -/

example : (toCore LeanDagTest.Hydrozoan.U7 selfParenting_U7).ids
    = LeanDagTest.Hydrozoan.U7.ids := rfl

example : ((toCore LeanDagTest.Hydrozoan.U7 selfParenting_U7).block 4).creator
    = (LeanDagTest.Hydrozoan.U7.block 4).author := rfl

example : ((toCore LeanDagTest.Hydrozoan.U7 selfParenting_U7).block 4).refs
    = (LeanDagTest.Hydrozoan.U7.block 4).parents := rfl

/-! ## The transported universe carries the wider non-equivocation

Hydrozoan's `no_equivocation` is guarded by `NonByzantine`, which the
hybrid arc's `HonestNoEquiv` asks for; the two are one condition, so
this needs no argument of its own. -/

example : HonestNoEquiv (toCore LeanDagTest.Hydrozoan.U7 selfParenting_U7) :=
  honestNoEquiv_toCore _ _

/-! ## The round trip is definitional -/

example : ofCore (toCore LeanDagTest.Hydrozoan.U7 selfParenting_U7)
    (honestNoEquiv_toCore _ _) = LeanDagTest.Hydrozoan.U7 := rfl

end Integration

end LeanDagTest
