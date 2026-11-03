import LeanDag.Scheme.Model.Rule
import LeanDag.Hydrozoan.Model.Decided
/-!
# The Hybrid Mysticeti row against Hydrozoan

`docs/scheme.md` §10. Hydrozoan (`LeanDag/Hydrozoan/`) is the
development's rule under the hybrid fault model, `n ≥ 3f + 2c + k + 1`.
Its slow path is the Hybrid Mysticeti row's direct commit; its fast
path, the weak rung that finds a fast commit through an anchor, and the
skip threshold `q_fast` that excludes a fast commit are what it has
beyond the row.

* `hydrozoanSlowAnchored`: Hydrozoan without the fast path, on
  Hydrozoan's universe: the slow commit, a skip on `⌊(n + f + 1)/2⌋`
  blames, and the certificate rung alone.
* `HybridValid`: Hydrozoan's validity with every block referencing its
  author's previous block, the record on which the row's carrier shows
  inclusion as well as progress.

Definitions only; the claims are `Scheme/Hydrozoan/Statement.lean`.
-/

namespace LeanDag

namespace Scheme

section Slow

variable (Replica BlockId : Type) [Fintype Replica] [DecidableEq Replica] [DecidableEq BlockId]
variable [F : Hydrozoan.Faults Replica]

/-- **Hydrozoan without its fast path**: wave two; the slow commit in view;
a skip on `⌊(n + f + 1)/2⌋` blames in view; one rung, the anchor-linked
certificate, with no tie-break. -/
def hydrozoanSlowAnchored :
    AnchoredRule Replica BlockId Unit Hydrozoan.ValidWrt (Hydrozoan.NonByzantine : Finset Replica) where
  waveAt := fun _ => 2
  Commit := fun U V L r _ => Hydrozoan.SlowCommitInView U V L r
  decCommit := fun _ _ _ _ _ => inferInstance
  Skip := fun U V S k => blameSkip (S := S) ((Fintype.card Replica + F.f + 1) / 2) U V k
  rungs := 1
  Link := fun _ U A L S k => Hydrozoan.CertifiedIn U A L (S.slotRound k)
  tie := fun _ _ _ => False

end Slow

section Hybrid

variable {Replica BlockId : Type} [Fintype Replica] [DecidableEq Replica]
variable [F : Hydrozoan.Faults Replica]

/-- **The hybrid validity with self-reference**: Hydrozoan's `q = n − f − c`
distinct-author references, and a block of every author referencing its
author's previous block. -/
abbrev HybridValid : Validity Replica BlockId Unit :=
  ValidAt (Hydrozoan.q Replica) (Clause.distinct.and Clause.selfParent)

/-- With distinct authors among references. -/
instance HybridValid.distinct : Validity.Distinct (HybridValid (Replica := Replica) (BlockId := BlockId)) :=
  Validity.Distinct.of_validAt (C := Clause.distinct.and Clause.selfParent) (fun _ _ => Iff.rfl)
    fun _ _ h => h.1

/-- And quorate at `q`. -/
instance HybridValid.quorate :
    Validity.Quorate (HybridValid (Replica := Replica) (BlockId := BlockId)) (Hydrozoan.q Replica) :=
  Validity.Quorate.of_validAt (C := Clause.distinct.and Clause.selfParent)
    (by have := F.card_replicas; unfold Hydrozoan.q; omega) fun _ _ => Iff.rfl

end Hybrid

end Scheme

end LeanDag
