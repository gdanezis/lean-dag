import LeanDag.KPartialDag.Model.Rule
/-!
# The available sub-DAG — statement

`docs/kpartial.md` §3, Theorem 1: the available sub-DAG below a voted block
is held by correct nodes and broad, every block has a two-step core three
rounds down, and at a row of the scheme a direct commit below it is linked
through it, and a link excludes a direct skip.

Statements only; the proofs are `Proof.lean`.
-/

namespace LeanDag

namespace KPartialDag

namespace Avail

/-- **The sub-DAG is held by correct nodes**: at `K ≥ 1`, below a block of the
record with votes from `f + c + 1` distinct authors, every block of the available
sub-DAG is held by a correct node. -/
def Held : Prop :=
  ∀ (Validator BlockId Payload : Type) [Fintype Validator] [DecidableEq Validator]
    [Faults Validator] [Crashes Validator]
    [LinearOrder BlockId] (U : KRecord Validator BlockId Payload) (K : ℕ)
    (A : BlockId), 1 ≤ K → A ∈ U.ids → Voted U A → Avail U K A ⊆ CorrectHeld U K

/-- **The sub-DAG is broad**: under the spreading condition, at `K ≥ 2`, every
round two or more below `A`
holds an anchor point of a correct author, bringing `K` rounds. -/
def Broad : Prop :=
  ∀ (Validator BlockId Payload : Type) [Fintype Validator] [DecidableEq Validator]
    [Faults Validator] [Crashes Validator]
    [LinearOrder BlockId] (U : KRecord Validator BlockId Payload) (K : ℕ)
    (A : BlockId) (ρ : ℕ), Spread Validator → 2 ≤ K → A ∈ U.ids → ρ + 2 ≤ (U.block A).round →
    ∃ x ∈ U.ids, (U.block x).round = ρ ∧ (U.block x).creator ∈ (Correct : Finset Validator) ∧
      AnchoredBelow U K A x K

/-- **The two-step core**: three rounds below a block of the record, some block
is reached from every reference of the block through a block it references,
at `n ≥ 3f + 2c + 1`. -/
def Core : Prop :=
  ∀ (Validator BlockId Payload : Type) [Fintype Validator] [DecidableEq Validator]
    [Faults Validator] [Crashes Validator] [LinearOrder BlockId]
    (U : KRecord Validator BlockId Payload) (z : BlockId), z ∈ U.ids → 3 ≤ (U.block z).round →
    ∃ x ∈ U.ids, (U.block x).round + 3 = (U.block z).round ∧
      ∀ w ∈ (U.block z).refs, ∃ v ∈ (U.block w).refs, x ∈ (U.block v).refs

/-- **A direct commit is linked through the sub-DAG**: at a row of the scheme
and its depth, below a block one round or more above the decision round of a
directly committed round-`r` block, the sub-DAG holds certificates for it
from `linkSize` distinct authors, with their references. -/
def Linked : Prop :=
  ∀ (Validator BlockId Payload : Type) [Fintype Validator] [DecidableEq Validator]
    [Faults Validator] [Crashes Validator] [LinearOrder BlockId] (p : Scheme.Params)
    (U : KRecord Validator BlockId Payload) (K : ℕ) (A L : BlockId) (r : ℕ), Row Validator p →
   
    kDepth Validator p ≤ K → A ∈ U.ids → r + p.waveLength ≤ (U.block A).round →
    DirectCommit p U L r →
    AvailLinked p U K A L r

/-- **A link excludes a direct skip**: at a row of the scheme, a block linked
through the sub-DAG is not directly skipped. -/
def Exclusive : Prop :=
  ∀ (Validator BlockId Payload : Type) [Fintype Validator] [DecidableEq Validator]
    [Faults Validator] [Crashes Validator] [LinearOrder BlockId] (p : Scheme.Params)
    (U : KRecord Validator BlockId Payload) (K : ℕ) (A L : BlockId) (r : ℕ), Row Validator p →
    AvailLinked p U K A L r → ¬ DirectSkip p U L r

/-- The available sub-DAG. -/
def Statement : Prop := Held ∧ Broad ∧ Core ∧ Linked ∧ Exclusive

end Avail

end KPartialDag

end LeanDag
