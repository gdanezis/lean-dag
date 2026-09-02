import LeanDag.Integration.Hydrozoan.Liveness

/-!
# What a deployment gets

The reader-facing layer. Everything else in `Integration/Hydrozoan/` is
machinery; this file names the object a deployment is and states what
holds of it, so that the claims can be read without following the
transport.

A **deployment** is one replica's situation: the DAG the network built,
a recovery it performed by one message, and a horizon below which it
retains nothing. What it actually holds — `held` — is that DAG with the
recovery applied and then the horizon taken, in that order, which is
the order a deployment does them in and the only one that is
unconditional (`integration.md` I6).

Four claims hold of it, and none is proved here: each is an application
of what the transport establishes.

* **`safe`** — no two views of what the replica holds decide a slot
  differently.
* **`agrees`** — and it agrees with the rest of the network, which
  never recovered or pruned.
* **`preserves`** — every verdict the network reached is a verdict the
  replica reaches, at its own slot numbering.
* **`commits`**, with `covered` and `populated` — Hydrozoan's liveness
  theorems apply to what the replica holds, their hypotheses surviving
  both the recovery and the horizon.

The conditions a deployment must meet are the fields of the structure
and the two instance arguments: a committee of at least `3(f + c) + 1`
(`HybridCommittee`, §2), blocks that carry their author's previous
block (`SelfParenting`, §3), and a horizon at or below the base slot.
Nothing else is assumed.
-/

namespace LeanDag

namespace Integration

namespace Hydrozoan

variable {Replica : Type} [Fintype Replica] [DecidableEq Replica]
variable {BlockId : Type} [DecidableEq BlockId] [LinearOrder BlockId]
variable [LeanDag.Hydrozoan.Faults Replica] [Fact (HybridCommittee Replica)]
variable [S : LeanDag.Hydrozoan.Slots Replica]

/-- **One replica's situation**: what the network built, what it
recovered, and what it has thrown away. -/
structure Deployment (Replica BlockId : Type) [Fintype Replica] [DecidableEq Replica]
    [DecidableEq BlockId] [LinearOrder BlockId]
    [LeanDag.Hydrozoan.Faults Replica] [Fact (HybridCommittee Replica)]
    [S : LeanDag.Hydrozoan.Slots Replica] where
  /-- The DAG as the network built it, before this replica recovered or
  pruned. -/
  network : LeanDag.Hydrozoan.BlockUniverse Replica BlockId
  /-- Every block carries its author's previous block. The deployed
  protocol has this; the Hydrozoan model does not record it, since no
  theorem of that arc consumes it. -/
  selfParents : SelfParenting network
  /-- The one-message recovery this replica performed. -/
  recovery : SkipMsg (toCore network selfParents)
  /-- The horizon below which it retains nothing. -/
  horizon : ℕ
  /-- The slot its numbering restarts at. -/
  base : ℕ
  /-- The horizon does not reach past that slot. -/
  retains : horizon ≤ S.slotRound base

namespace Deployment

variable (D : Deployment Replica BlockId)

/-- **What the replica holds**: recovered, then pruned. -/
abbrev held : LeanDag.Hydrozoan.BlockUniverse Replica BlockId :=
  stackHZ D.network D.selfParents D.recovery D.horizon

/-- **The slot numbering it uses**, rebased at the horizon. Its slot `k`
is the network's slot `base + k`. -/
abbrev numbering : LeanDag.Hydrozoan.Slots Replica := slotsChopHZ D.retains

/-- A view of the network's DAG, carried to what the replica holds. -/
abbrev carry (V : LeanDag.Hydrozoan.View D.network) :
    LeanDag.Hydrozoan.View D.held :=
  stackView D.network D.selfParents D.recovery D.horizon V

/-! ## Safety -/

/-- **Safety.** No two views of what the replica holds decide a slot
differently, whatever the routes. -/
theorem safe :
    @LeanDag.Hydrozoan.SlotAgreement.DecidedUnique Replica BlockId _ _ _ _ _
      D.numbering D.held :=
  decidedUnique_stackHZ D.retains

/-- **Every verdict the network reached, the replica reaches** — at its
own slot numbering, its slot `k` being the network's `base + k`. -/
theorem preserves {V : LeanDag.Hydrozoan.View D.network} {k : ℕ} {v : Option BlockId}
    (h : LeanDag.Hydrozoan.Decided D.network V (D.base + k) v) :
    LeanDag.Hydrozoan.Decided (S := D.numbering) D.held (D.carry V) k v :=
  decided_stackHZ D.retains h

/-- **And it agrees with the network.** Whatever any replica decided at
a slot from the base on, this one decides the same at the corresponding
slot — on an arbitrary view of what it holds, not a carried one. -/
theorem agrees {V : LeanDag.Hydrozoan.View D.network}
    {W : LeanDag.Hydrozoan.View D.held} {k : ℕ} {v w : Option BlockId}
    (hnet : LeanDag.Hydrozoan.Decided D.network V (D.base + k) v)
    (hloc : LeanDag.Hydrozoan.Decided (S := D.numbering) D.held W k w) :
    v = w :=
  agree_stackHZ D.retains hnet hloc

/-! ## Liveness -/

/-- **Coverage carries**, from a round above the recovery, rebased by
the horizon. -/
theorem covered {T : Finset Replica} {R R' R'' : ℕ}
    (hs : LeanDag.Hydrozoan.SynchronisedOn D.network T R)
    (hR : R ≤ R') (hfill : D.recovery.r < R') (hcut : R' ≤ D.horizon + R'') :
    LeanDag.Hydrozoan.SynchronisedOn D.held T R'' :=
  synchronisedOn_stackHZ hs hR hfill hcut

/-- **Production carries across the gap**, with the recovered replica
counted, at the rebased round. This is what the recovery exists to
supply. -/
theorem populated {T : Finset Replica} {k : ℕ}
    (hp : LeanDag.Hydrozoan.PopulatedOn D.network T k)
    (hk1 : D.recovery.r0 < k) (hk2 : k ≤ D.recovery.r) (hG : D.horizon ≤ k) :
    LeanDag.Hydrozoan.PopulatedOn D.held (insert D.recovery.v1 T) (k - D.horizon) :=
  populatedOn_stackHZ hp hk1 hk2 hG

/-- **Liveness.** Hydrozoan's direct-commit theorem holds of what the
replica retains: a quorum of correct replicas, synchronised and
producing through a wave whose leader is among them, commits — on the
replica's own view, once it is caught up to the decision round. -/
theorem commits : LeanDag.Hydrozoan.DirectLiveness.CommitLiveness D.held :=
  commitLiveness_stackHZ

/-- **And the descent applies**, so a committed run on what the replica
holds decides every slot below it. -/
theorem decidesBelow :
    LeanDag.Hydrozoan.IndirectLiveness.AnchoredTotality D.held :=
  anchoredTotality_stackHZ

/-! ## The schedule it runs

Fairness and the runway are properties of the schedule alone, so they
survive the rebasing with no fault model and no DAG (§1). -/

/-- A fair schedule stays fair under the replica's numbering. -/
theorem fair {T : Finset Replica} {c : ℕ}
    (h : LeanDag.Hydrozoan.EventualDecision.FairRunOn Replica T c) :
    @LeanDag.Hydrozoan.EventualDecision.FairRunOn Replica D.numbering T c :=
  fairRunOn_slotsChopHZ D.retains h

/-- And a spanning runway stays spanning. -/
theorem spans {c : ℕ}
    (h : LeanDag.Hydrozoan.IndirectLiveness.SpansEligible Replica c) :
    @LeanDag.Hydrozoan.IndirectLiveness.SpansEligible Replica D.numbering c :=
  spansEligible_slotsChopHZ D.retains h

end Deployment

end Hydrozoan

end Integration

end LeanDag
