import LeanDag.Common.History
/-!
# K-partial DAG — the substrate

`docs/kpartial.md` §1. The substrate's validity and record (`KValid`,
`KRecord`), what correct nodes hold of it (`CorrectHeld`), and the available
sub-DAG below a block, reached from anchor points by reference or in two
steps (`AnchoredBelow`, `Avail`).
-/

namespace LeanDag

namespace KPartialDag

variable {Validator : Type*} [Fintype Validator] [DecidableEq Validator] [F : Faults Validator]
variable {BlockId : Type*} [LinearOrder BlockId] {Payload : Type*}

variable (Validator) in
/-- **The crash bound**: at most `c` correct validators crash for good, with
`n ≥ 3f + 2c + 1`. A validator that crashes is correct: it never
equivocates. -/
class Crashes where
  /-- The crash bound. -/
  c : ℕ
  /-- At least `3f + 2c + 1` validators. -/
  card_validators : 3 * F.f + 2 * c + 1 ≤ Fintype.card Validator

variable [Cr : Crashes Validator]

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

/-- **The anchor points below `A`, each with the depth of the history it
brings**: `A` itself, to depth `K`; a block that blocks of `f + 1` distinct
authors reference, to depth `K`; and, when validators may crash for good, a
block that blocks of `f + 1` distinct authors reach in two steps, to depth
`K − 1`. Each referencing block `z`,
and the block `m z` it reaches through, lies in the history brought by an
anchor point `y z`. The least such relation. -/
inductive AnchoredBelow (U : KRecord Validator BlockId Payload) (K : ℕ) (A : BlockId) :
    BlockId → ℕ → Prop
  | anchor : AnchoredBelow U K A A K
  | referenced {x : BlockId} (S : Finset BlockId) (y : BlockId → BlockId) (d : BlockId → ℕ)
      (hy : ∀ z ∈ S, AnchoredBelow U K A (y z) (d z))
      (hz : ∀ z ∈ S, z ∈ historyUpto U (d z) (y z))
      (href : ∀ z ∈ S, x ∈ (U.block z).refs)
      (hcard : F.f + 1 ≤ (creatorsOf U.block S).card) : AnchoredBelow U K A x K
  | reached {x : BlockId} (S : Finset BlockId) (m : BlockId → BlockId)
      (y : BlockId → BlockId) (d : BlockId → ℕ) (y' : BlockId → BlockId) (d' : BlockId → ℕ)
      (hy : ∀ z ∈ S, AnchoredBelow U K A (y z) (d z)) (hz : ∀ z ∈ S, z ∈ historyUpto U (d z) (y z))
      (hy' : ∀ z ∈ S, AnchoredBelow U K A (y' z) (d' z))
      (hmz : ∀ z ∈ S, m z ∈ historyUpto U (d' z) (y' z))
      (hm : ∀ z ∈ S, m z ∈ (U.block z).refs) (href : ∀ z ∈ S, x ∈ (U.block (m z)).refs)
      (hcard : F.f + 1 ≤ (creatorsOf U.block S).card) (hc : 1 ≤ Cr.c) :
      AnchoredBelow U K A x (K - 1)

/-- **The available sub-DAG below `A`**: the history each anchor point
brings. -/
def Avail (U : KRecord Validator BlockId Payload) (K : ℕ) (A : BlockId) : Set BlockId :=
  {z | ∃ y d, AnchoredBelow U K A y d ∧ z ∈ historyUpto U d y}

end KPartialDag

end LeanDag
