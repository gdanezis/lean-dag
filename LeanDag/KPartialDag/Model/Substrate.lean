import LeanDag.Common.History
/-!
# K-partial DAG — the substrate

`docs/kpartial.md` §1. The substrate's validity and record (`KValid`,
`KRecord`), what correct nodes hold of it (`CorrectHeld`), and the available
sub-DAG below a block (`AnchoredBelow`, `Avail`).
-/

namespace LeanDag

namespace KPartialDag

variable {Validator : Type*} [Fintype Validator] [DecidableEq Validator] [F : Faults Validator]
variable {BlockId : Type*} [LinearOrder BlockId] {Payload : Type*}

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
