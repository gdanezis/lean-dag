import LeanDag.Integration.Hydrozoan.FillDecided

/-!
# P9 — the composition capstones

`docs/hydrozoan-integration.md` §10.7. A replica that recovered from a
crash by one message and then pruned below a horizon is running two
universe transformers at once, over Hydrozoan's dual-path rule, under
the hybrid fault model, on a schedule the adaptive leader count may
vary. This file says the four hold together.

**Nothing here is a new argument**, which is the point. The stack is a
Hydrozoan universe because `ofCore` re-supplies the self-parent clause
(P6); its verdicts are the original's because the fill preserves them
(P8) and the cut re-indexes them (P7); and safety across it is HZ3
applied, that theorem being quantified over **every** universe. That is
what `integration.md` I7 found for the core, reached here by the same
route.

**The order is the deployment order.** Fill first, then truncate:
`chopHZ (skipFillHZ U …) …` is well formed at every horizon, because
the fill has already happened when the cut is made. The reverse needs
the anchor retained — a `SkipMsg` for the truncation requires its
anchor among the truncation's identifiers — which is `integration.md`
I6's condition appearing as an asymmetry between orders rather than as
an obstacle. §5.2 records what the fill and the cut each do to the
liveness package.
-/

namespace LeanDag

namespace Integration

namespace Hydrozoan

variable {Replica : Type} [Fintype Replica] [DecidableEq Replica]
variable {BlockId : Type} [DecidableEq BlockId]
variable [F : LeanDag.Hydrozoan.Faults Replica]
  [Fact (HybridCommittee Replica)]
variable {U : LeanDag.Hydrozoan.BlockUniverse Replica BlockId}
  {hsp : SelfParenting U} {sk : SkipMsg (toCore U hsp)} {G : ℕ}
  {V : LeanDag.Hydrozoan.View U}

/-- **The stack**: recovered by Safe Skip, then truncated at a horizon.
Well formed at every horizon, the fill having happened before the cut. -/
abbrev stackHZ (U : LeanDag.Hydrozoan.BlockUniverse Replica BlockId)
    (hsp : SelfParenting U) (sk : SkipMsg (toCore U hsp)) (G : ℕ) :
    LeanDag.Hydrozoan.BlockUniverse Replica BlockId :=
  chopHZ (skipFillHZ U hsp sk) (selfParenting_skipFillHZ U hsp sk) G

/-- A replica's view, carried through both transformers. -/
abbrev stackView (U : LeanDag.Hydrozoan.BlockUniverse Replica BlockId)
    (hsp : SelfParenting U) (sk : SkipMsg (toCore U hsp)) (G : ℕ)
    (V : LeanDag.Hydrozoan.View U) :
    LeanDag.Hydrozoan.View (stackHZ U hsp sk G) :=
  View.chopHZ (liftViewHZ U hsp sk V) (selfParenting_skipFillHZ U hsp sk) G

/-- **The stack is still transportable.** Its side condition holds by
`selfParenting_ofCore` at each step, so a third transformer could be
applied to it without a new obligation. -/
theorem selfParenting_stackHZ : SelfParenting (stackHZ U hsp sk G) :=
  selfParenting_chopHZ _ _ _

section Verdicts

variable [LinearOrder BlockId] [S : LeanDag.Hydrozoan.Slots Replica] {d : ℕ}

/-- **Verdicts survive the stack.** A verdict reached before the
recovery, at a slot at or above the base slot, re-derives on the
recovered-and-pruned universe at the re-indexed slot. The composition
of P8 and P7, in that order. -/
theorem decided_stackHZ (hd : G ≤ S.slotRound d) {k : ℕ} {v : Option BlockId}
    (h : LeanDag.Hydrozoan.Decided U V (d + k) v) :
    LeanDag.Hydrozoan.Decided (S := slotsChopHZ hd) (stackHZ U hsp sk G)
      (stackView U hsp sk G V) k v :=
  (decided_chopHZ (V := liftViewHZ U hsp sk V) hd).mpr (decided_fillHZ h)

/-- **The capstone: a recovered and pruned replica cannot disagree.**
Its view `W` is an arbitrary view of the stack — not a transported
full-history view — and its verdict at the re-indexed slot is the
verdict anyone else reached at the original slot. The proof is HZ3
applied to a different universe, with `decided_stackHZ` moving the
other verdict into it. -/
theorem agree_stackHZ (hd : G ≤ S.slotRound d) {k : ℕ} {v w : Option BlockId}
    {W : LeanDag.Hydrozoan.View (stackHZ U hsp sk G)}
    (hV : LeanDag.Hydrozoan.Decided U V (d + k) v)
    (hW : LeanDag.Hydrozoan.Decided (S := slotsChopHZ hd) (stackHZ U hsp sk G) W k w) :
    v = w :=
  @LeanDag.Hydrozoan.SlotAgreement.holds Replica BlockId _ _ _ _ _ (slotsChopHZ hd)
    (stackHZ U hsp sk G) (stackView U hsp sk G V) W k v w (decided_stackHZ hd hV) hW

/-- **Safety across the stack**, in HZ3's own words: no two views of the
recovered-and-pruned universe decide a slot differently, whatever the
routes. Nothing about the fill or the cut is re-proved. -/
theorem decidedUnique_stackHZ (hd : G ≤ S.slotRound d) :
    @LeanDag.Hydrozoan.SlotAgreement.DecidedUnique Replica BlockId _ _ _ _ _
      (slotsChopHZ hd) (stackHZ U hsp sk G) :=
  @LeanDag.Hydrozoan.SlotAgreement.holds Replica BlockId _ _ _ _ _ (slotsChopHZ hd)
    (stackHZ U hsp sk G)

end Verdicts

end Hydrozoan

end Integration

end LeanDag
