import LeanDag.Common.BlockDag
/-!
# Mysticeti — the universe the rule reads

Trusted core of the arc: definitions only, and all of them re-exported
rather than restated, since the names are `Common/`'s and nine arcs
share them.

**The validity is the protocol's, not the model's.** `ValidWrt`
(`Common/Block.lean`) asks four things of a block: its references sit
one round below (P1), it cites no author twice (P2), a non-genesis
block cites `n − f` distinct authors (P3), and a non-genesis block
cites one of its own creator's (P3′). The first three are what a
quorum-based DAG rule needs. The fourth is a choice this protocol
makes and another need not: a block DAG can be run without self
references, and this development shows as much — P3′ is consumed by no
safety or liveness result (report §25), only by the garbage-collection
and denial-of-service arcs, which use it to bound a validator's own
history.

**Why it lives in `Common/`.** Odontoceti, Mahi-Mahi, Safe Skip,
garbage collection, the DoS arc, chain quality, the reactive and
adaptive schedules and the network capstones all run on *this*
universe: they extend the core rather than replace it. Nemo, Hybrid,
Hydrozoan, Optimal-Hydrozoan, FinWhale and Minnow each carry their own
validity and their own universe. So `ValidWrt` is protocol-specific and
widely shared at once, which is why it is filed under the substrate and
named here.
-/

namespace LeanDag

namespace Mysticeti

/-! The core's validity, universe and view, under the names the rest of
the development uses. -/
export LeanDag (ValidWrt BlockUniverse View)

end Mysticeti

end LeanDag
