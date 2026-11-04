import LeanDag.Common.History
/-!
# K-partial DAG — the substrate

`docs/kpartial.md` §1. A block references blocks of the round below from a
quorum of distinct authors, at most one of each, committing to each by its
hash; it need not reference its author's own previous block. A correct
author that references a block has downloaded that block's history to depth
`K` only. Hashes fix the whole history of every block, so the record of a
run is an ordinary block record (`KRecord`); what a correct node holds of it
is not. A block is held by a correct node when it is a correct author's
block, or lies in the history to depth `K` of a block that a correct
author's block references (`CorrectHeld`).

Below a block `A`, a block referenced by blocks of `f + 1` distinct authors
that lie in the history to depth `K` of anchored blocks is anchored
(`AnchoredBelow`). The union of the histories to depth `K` of the anchored
blocks is the available sub-DAG below `A` (`Avail`).

Definitions only.
-/

namespace LeanDag

namespace KPartialDag

variable {Validator : Type*} [Fintype Validator] [DecidableEq Validator] [F : Faults Validator]
variable {BlockId : Type*} [DecidableEq BlockId] {Payload : Type*}

variable (Validator BlockId Payload) in
/-- **The substrate's validity**: references one round below, from a quorum
of distinct authors, at most one of each author, and no reference to the
author's own block required. -/
abbrev KValid : Validity Validator BlockId Payload :=
  ValidAt (quorumCard Validator) Clause.distinct

variable (Validator BlockId Payload) in
/-- **A K-partial DAG**: a record at the substrate's validity, whose honest
authors are the correct validators. -/
abbrev KRecord := BlockRecord Validator BlockId Payload (KValid Validator BlockId Payload) Correct

/-- **Held by a correct node**: a block of a correct author, or a block in the
history to depth `K` of a block that a correct author's block references. -/
def CorrectHeld (U : KRecord Validator BlockId Payload) (K : ℕ) : Set BlockId :=
  {z | ∃ w ∈ U.ids, (U.block w).creator ∈ (Correct : Finset Validator) ∧
    (z = w ∨ ∃ y ∈ (U.block w).refs, z ∈ historyUpto U K y)}

/-- **The anchored blocks below `A`**: `A` itself, and every block that
blocks of `f + 1` distinct authors reference, each `z` in the history to
depth `K` of an anchored block `y z`. The least such set. -/
inductive AnchoredBelow (U : KRecord Validator BlockId Payload) (K : ℕ) (A : BlockId) :
    BlockId → Prop
  | anchor : AnchoredBelow U K A A
  | referenced {x : BlockId} (S : Finset BlockId) (y : BlockId → BlockId)
      (hy : ∀ z ∈ S, AnchoredBelow U K A (y z)) (hz : ∀ z ∈ S, z ∈ historyUpto U K (y z))
      (href : ∀ z ∈ S, x ∈ (U.block z).refs)
      (hcard : F.f + 1 ≤ (creatorsOf U.block S).card) : AnchoredBelow U K A x

/-- **The available sub-DAG below `A`**: the history to depth `K` of each
anchored block. -/
def Avail (U : KRecord Validator BlockId Payload) (K : ℕ) (A : BlockId) : Set BlockId :=
  {z | ∃ y, AnchoredBelow U K A y ∧ z ∈ historyUpto U K y}

end KPartialDag

end LeanDag
