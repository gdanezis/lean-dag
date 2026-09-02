import LeanDag.Integration.Hydrozoan.Universe
import LeanDag.Integration.Preservation
import LeanDag.SafeSkip.Invariance

/-!
# B4 — the transformer bridge

`docs/hydrozoan-integration.md` §10.4. One definition, after which
every core universe transformer restricts to Hydrozoan universes.

**The side condition is needed only on the way in.** The record
predicted a `SelfParenting` preservation lemma per transformer. There
is one lemma for all of them: `SelfParenting` is the core's
`self_parent` clause stated on a Hydrozoan universe, and *every* core
universe carries that clause as a field of its own validity, so
anything arriving through `ofCore` self-parents by construction
(`selfParenting_ofCore`). `toCore` consumes the condition; `ofCore`
re-supplies it. A transformer added later therefore costs no
`SelfParenting` obligation at all, only its `HonestNoEquiv` one — and
for the two that exist, that half is `integration.md` I1 and is already
proved.

So the two transformers land as three lines each, and the modularity
claim of §10.4 holds in a stronger form than it was stated.
-/

namespace LeanDag

namespace Integration

namespace Hydrozoan

variable {Replica : Type} [Fintype Replica] [DecidableEq Replica]
variable {BlockId : Type} [DecidableEq BlockId]
variable [F : LeanDag.Hydrozoan.Faults Replica]
  [Fact (LeanDag.Hydrozoan.Faults.c Replica ≤ LeanDag.Hydrozoan.Faults.k Replica)]

omit [DecidableEq BlockId] in
/-- **Every core universe self-parents**, so the condition `toCore`
consumes is re-supplied by `ofCore` without an argument: it is the
fourth field of the core's `ValidWrt`, read back. -/
theorem selfParenting_ofCore {Payload : Type}
    (U : LeanDag.BlockUniverse Replica BlockId Payload) (hne : HonestNoEquiv U) :
    SelfParenting (ofCore U hne) :=
  fun i hi h => (U.valid i hi).self_parent h

/-- **The transformer bridge.** `F` closes over its own arguments, so
one definition serves every core universe transformer; the only
obligation is that `F` preserves non-equivocation at the honest class. -/
def transport (U : LeanDag.Hydrozoan.BlockUniverse Replica BlockId)
    (hsp : SelfParenting U)
    (F : LeanDag.BlockUniverse Replica BlockId Unit →
         LeanDag.BlockUniverse Replica BlockId Unit)
    (hF : HonestNoEquiv (F (toCore U hsp))) :
    LeanDag.Hydrozoan.BlockUniverse Replica BlockId :=
  ofCore (F (toCore U hsp)) hF

omit [DecidableEq BlockId] in
/-- Transport preserves the side condition, for **every** `F`. -/
theorem selfParenting_transport (U : LeanDag.Hydrozoan.BlockUniverse Replica BlockId)
    (hsp : SelfParenting U) (F : LeanDag.BlockUniverse Replica BlockId Unit →
      LeanDag.BlockUniverse Replica BlockId Unit)
    (hF : HonestNoEquiv (F (toCore U hsp))) :
    SelfParenting (transport U hsp F hF) :=
  selfParenting_ofCore _ _

omit [DecidableEq BlockId] in
@[simp] theorem transport_ids (U : LeanDag.Hydrozoan.BlockUniverse Replica BlockId)
    (hsp : SelfParenting U) (F : LeanDag.BlockUniverse Replica BlockId Unit →
      LeanDag.BlockUniverse Replica BlockId Unit)
    (hF : HonestNoEquiv (F (toCore U hsp))) :
    (transport U hsp F hF).ids = (F (toCore U hsp)).ids := rfl

/-! ## The two transformers the integration arc has -/

/-- **Truncation at a horizon**, restricted to Hydrozoan universes. The
`HonestNoEquiv` obligation is `integration.md` I1. -/
def chopHZ (U : LeanDag.Hydrozoan.BlockUniverse Replica BlockId)
    (hsp : SelfParenting U) (G : ℕ) :
    LeanDag.Hydrozoan.BlockUniverse Replica BlockId :=
  transport U hsp (fun U' => chop U' G) (honestNoEquiv_chop (honestNoEquiv_toCore U hsp))

theorem selfParenting_chopHZ (U : LeanDag.Hydrozoan.BlockUniverse Replica BlockId)
    (hsp : SelfParenting U) (G : ℕ) : SelfParenting (chopHZ U hsp G) :=
  selfParenting_transport _ _ _ _

@[simp] theorem chopHZ_ids (U : LeanDag.Hydrozoan.BlockUniverse Replica BlockId)
    (hsp : SelfParenting U) (G : ℕ) :
    (chopHZ U hsp G).ids = U.ids.filter fun i => G ≤ (U.block i).round := rfl

/-- **Crash recovery by one message**, restricted to Hydrozoan
universes. The `HonestNoEquiv` obligation is again `integration.md`
I1. -/
def skipFillHZ (U : LeanDag.Hydrozoan.BlockUniverse Replica BlockId)
    (hsp : SelfParenting U) (sk : SkipMsg (toCore U hsp)) :
    LeanDag.Hydrozoan.BlockUniverse Replica BlockId :=
  transport U hsp (fun _ => sk.skipFill)
    (honestNoEquiv_skipFill sk (honestNoEquiv_toCore U hsp))

theorem selfParenting_skipFillHZ (U : LeanDag.Hydrozoan.BlockUniverse Replica BlockId)
    (hsp : SelfParenting U) (sk : SkipMsg (toCore U hsp)) :
    SelfParenting (skipFillHZ U hsp sk) :=
  selfParenting_transport _ _ _ _

/-- The view a replica holds, lifted across the fill — `SafeSkip`'s
`liftView`, reached from a Hydrozoan view through the view transport of
`Universe.lean`. -/
def liftViewHZ (U : LeanDag.Hydrozoan.BlockUniverse Replica BlockId)
    (hsp : SelfParenting U) (sk : SkipMsg (toCore U hsp))
    (V : LeanDag.Hydrozoan.View U) :
    LeanDag.Hydrozoan.View (skipFillHZ U hsp sk) :=
  LeanDag.Integration.Hydrozoan.View.ofCore
    (sk.liftView (LeanDag.Integration.Hydrozoan.View.toCore V hsp))
    (honestNoEquiv_skipFill sk (honestNoEquiv_toCore U hsp))

@[simp] theorem liftViewHZ_ids (U : LeanDag.Hydrozoan.BlockUniverse Replica BlockId)
    (hsp : SelfParenting U) (sk : SkipMsg (toCore U hsp))
    (V : LeanDag.Hydrozoan.View U) :
    (liftViewHZ U hsp sk V).ids = (sk.liftView (LeanDag.Integration.Hydrozoan.View.toCore V hsp)).ids := rfl

end Hydrozoan

end Integration

end LeanDag
