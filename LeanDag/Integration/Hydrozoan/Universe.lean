import LeanDag.Integration.Hydrozoan.Faults
import LeanDag.Integration.Hydrozoan.Schedule
import LeanDag.Barnacle.Helpers.Hydrozoan
import LeanDag.Hybrid.Faults
import LeanDag.BlockDag

/-!
# B3 — the universe transport

`docs/hydrozoan-integration.md` §3 and §10.3. The two block universes
differ in exactly two fields, and **each direction supplies the one the
other structure lacks**:

* the core's `ValidWrt` carries `self_parent`, which Hydrozoan's does
  not, so `toCore` takes `SelfParenting` as a side condition;
* Hydrozoan's `no_equivocation` is guarded by `NonByzantine`, wider
  than the core's `Correct`, so `ofCore` takes `HonestNoEquiv` — which
  is the hybrid arc's U5, and whose preservation under both universe
  transformers is `integration.md` I1, already proved.

The second direction is therefore nearly definitional in the forward
sense: `HonestNoEquiv (toCore U hsp)` **is** `U.no_equivocation`, since
`creator ∉ byzantine` and `author ∈ NonByzantine` are one condition.

**What this file consumes that P1 did not.** The core's `BlockUniverse`
is indexed by a `Faults` instance, so `toCore` is available only where
B1 is — under `c ≤ k`. That is the division `docs/hydrozoan-integration.md`
§10.3 records: the causal-history layer needs no bridge and P1 needs
none, while everything reading the whole structure needs this one.

The quorum fields differ in spelling and not in content: the core
counts `creators` against `quorumCard` where Hydrozoan counts `authors`
against `q`, and `adaptBlk` makes the two author-sets one term, leaving
`quorumCard_eq_q` to reconcile the thresholds.
-/

namespace LeanDag

namespace Integration

namespace Hydrozoan

open LeanDag.Barnacle.Hydrozoan (adapt adaptBlk)

variable {Replica : Type} [Fintype Replica] [DecidableEq Replica]
variable {BlockId : Type}

/-! ## The side condition the core's validity adds -/

/-- **The self-parent clause**, P3′ of the core's `ValidWrt`, stated on
a Hydrozoan universe. The Hydrozoan model omits it because no theorem
of that arc consumes it (`docs/hydrozoan-integration.md` §3); the
deployed protocol has it, a Mysticeti block carrying its author's
previous block. -/
def SelfParenting [LeanDag.Hydrozoan.Faults Replica]
    (U : LeanDag.Hydrozoan.BlockUniverse Replica BlockId) : Prop :=
  ∀ i ∈ U.ids, 0 < (U.block i).round →
    ∃ j ∈ (U.block i).parents, (U.block j).author = (U.block i).author

/-- Bounded over two `Finset`s, so a witness model settles it by
`decide`. -/
instance [LeanDag.Hydrozoan.Faults Replica]
    (U : LeanDag.Hydrozoan.BlockUniverse Replica BlockId) :
    Decidable (SelfParenting U) :=
  inferInstanceAs (Decidable (∀ i ∈ U.ids, 0 < (U.block i).round →
    ∃ j ∈ (U.block i).parents, (U.block j).author = (U.block i).author))

section Transport

variable [F : LeanDag.Hydrozoan.Faults Replica]
  [Fact (LeanDag.Hydrozoan.Faults.c Replica ≤ LeanDag.Hydrozoan.Faults.k Replica)]

omit [Fact (LeanDag.Hydrozoan.Faults.c Replica ≤ LeanDag.Hydrozoan.Faults.k Replica)] in
/-- Hydrozoan's `Correct` is inside its `NonByzantine`: a crashed
replica does not equivocate. What lets the core's narrower
non-equivocation guard discharge Hydrozoan's wider one. -/
theorem correct_subset_nonByzantine :
    (LeanDag.Hydrozoan.Correct : Finset Replica)
      ⊆ (LeanDag.Hydrozoan.NonByzantine : Finset Replica) := by
  intro v hv
  simp only [LeanDag.Hydrozoan.Correct, LeanDag.Hydrozoan.NonByzantine,
    Finset.mem_compl, Finset.mem_union] at hv ⊢
  exact fun h => hv (Or.inl h)

/-- **A Hydrozoan universe is a core universe**, given the self-parent
clause. Every field is Hydrozoan's own, modulo the adapter and the
threshold agreement. -/
def toCore (U : LeanDag.Hydrozoan.BlockUniverse Replica BlockId)
    (hsp : SelfParenting U) : LeanDag.BlockUniverse Replica BlockId Unit where
  ids := U.ids
  block := adaptBlk U
  complete := fun i hi j hj => U.complete i hi j hj
  valid := fun i hi =>
    { predecessor := fun j hj => (U.valid i hi).predecessor j hj
      distinct_creators := fun j hj k hk h => (U.valid i hi).distinct_authors j hj k hk h
      quorum := fun h => by
        have hq := (U.valid i hi).quorum h
        rw [quorumCard_eq_q]
        exact hq
      self_parent := fun h => hsp i hi h }
  no_equivocation := fun i hi j hj hc heq hr =>
    U.no_equivocation i hi j hj (correct_subset_nonByzantine hc) heq hr

/-- **The transported universe carries the wider non-equivocation**,
which is Hydrozoan's own field: the hybrid arc's `creator ∉ byzantine`
and Hydrozoan's `author ∈ NonByzantine` are one condition. -/
theorem honestNoEquiv_toCore (U : LeanDag.Hydrozoan.BlockUniverse Replica BlockId)
    (hsp : SelfParenting U) : HonestNoEquiv (toCore U hsp) :=
  fun i hi j hj hnb heq hr =>
    U.no_equivocation i hi j hj (Finset.mem_compl.mpr hnb) heq hr

/-- **A core universe is a Hydrozoan universe**, given non-equivocation
at the wider honest class. The self-parent field is dropped and the
payload forgotten. -/
def ofCore {Payload : Type} (U : LeanDag.BlockUniverse Replica BlockId Payload)
    (hne : HonestNoEquiv U) : LeanDag.Hydrozoan.BlockUniverse Replica BlockId where
  ids := U.ids
  block := fun i =>
    { round := (U.block i).round
      author := (U.block i).creator
      parents := (U.block i).refs }
  complete := fun i hi j hj => U.complete i hi j hj
  valid := fun i hi =>
    { predecessor := fun j hj => (U.valid i hi).predecessor j hj
      distinct_authors := fun j hj k hk h => (U.valid i hi).distinct_creators j hj k hk h
      quorum := fun h => by
        have hq := (U.valid i hi).quorum h
        rw [quorumCard_eq_q] at hq
        exact hq }
  no_equivocation := fun i hi j hj hnb heq hr =>
    hne i hi j hj (Finset.mem_compl.mp hnb) heq hr

/-! ## The round trip

Stated observationally, as `integration.md` I11 states its convergence:
identifier sets equal, and blocks equal at those identifiers. Here both
hold on the nose, structure eta making the block functions one term. -/

@[simp] theorem ofCore_toCore (U : LeanDag.Hydrozoan.BlockUniverse Replica BlockId)
    (hsp : SelfParenting U) :
    ofCore (toCore U hsp) (honestNoEquiv_toCore U hsp) = U := rfl

@[simp] theorem toCore_ids (U : LeanDag.Hydrozoan.BlockUniverse Replica BlockId)
    (hsp : SelfParenting U) : (toCore U hsp).ids = U.ids := rfl

@[simp] theorem toCore_block (U : LeanDag.Hydrozoan.BlockUniverse Replica BlockId)
    (hsp : SelfParenting U) (i : BlockId) :
    (toCore U hsp).block i = adapt (U.block i) := rfl

@[simp] theorem ofCore_ids {Payload : Type}
    (U : LeanDag.BlockUniverse Replica BlockId Payload) (hne : HonestNoEquiv U) :
    (ofCore U hne).ids = U.ids := rfl

/-! ## Views transport too

A view is a downward-closed subset of identifiers, and neither
structure constrains it further, so both directions are the identity on
ids. `View.toCore` is what lets `SafeSkip`'s `liftView` be reached from
a Hydrozoan view (P8). -/

/-- A Hydrozoan view of `U` is a core view of `toCore U hsp`. -/
def View.toCore {U : LeanDag.Hydrozoan.BlockUniverse Replica BlockId}
    (V : LeanDag.Hydrozoan.View U) (hsp : SelfParenting U) :
    LeanDag.View Replica BlockId Unit (Hydrozoan.toCore U hsp) where
  ids := V.ids
  subset_ids := V.subset_ids
  complete := fun i hi j hj => V.complete i hi j hj

/-- And a core view of any universe is a Hydrozoan view of its reading. -/
def View.ofCore {Payload : Type} {U' : LeanDag.BlockUniverse Replica BlockId Payload}
    (W : LeanDag.View Replica BlockId Payload U') (hne : HonestNoEquiv U') :
    LeanDag.Hydrozoan.View (Hydrozoan.ofCore U' hne) where
  ids := W.ids
  subset_ids := W.subset_ids
  complete := fun i hi j hj => W.complete i hi j hj

@[simp] theorem View.toCore_ids {U : LeanDag.Hydrozoan.BlockUniverse Replica BlockId}
    (V : LeanDag.Hydrozoan.View U) (hsp : SelfParenting U) :
    (View.toCore V hsp).ids = V.ids := rfl

@[simp] theorem View.ofCore_ids {Payload : Type}
    {U' : LeanDag.BlockUniverse Replica BlockId Payload}
    (W : LeanDag.View Replica BlockId Payload U') (hne : HonestNoEquiv U') :
    (View.ofCore W hne).ids = W.ids := rfl

end Transport

end Hydrozoan

end Integration

end LeanDag
