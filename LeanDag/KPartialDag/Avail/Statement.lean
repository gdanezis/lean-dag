import LeanDag.KPartialDag.Model.Rule
/-!
# The available sub-DAG — statement

`docs/kpartial.md` §3. On a K-partial DAG, for a block `A` and the available
sub-DAG below it (`Avail`):

* **held** (`Held`): below a block with a certificate, every block of the
  sub-DAG is held by a correct node;
* **broad** (`Broad`): at `K ≥ 2`, every round two or more below `A` holds an
  anchored block of a correct author;
* **linked** (`Linked`): at `K ≥ 3`, if a round-`r` block is directly
  committed and `A` lies at round `r + 3` or above, the sub-DAG holds a
  certificate for it, with its references;
* **exclusive** (`Exclusive`): if the sub-DAG holds a certificate for a
  block, that block is not directly skipped.

Statements only; the proofs are `Proof.lean`.
-/

namespace LeanDag

namespace KPartialDag

namespace Avail

/-- **The sub-DAG is held by correct nodes**: below a block of the record with
a certificate, every block of the available sub-DAG is held by a correct
node. -/
def Held : Prop :=
  ∀ (Validator BlockId Payload : Type) [Fintype Validator] [DecidableEq Validator]
    [Faults Validator] [DecidableEq BlockId] (U : KRecord Validator BlockId Payload) (K : ℕ)
    (A : BlockId) (r : ℕ), A ∈ U.ids →
    (certificatesAt U (IsVote U) (quorumCard Validator) A r).Nonempty →
    Avail U K A ⊆ CorrectHeld U K

/-- **The sub-DAG is broad**: at `K ≥ 2`, every round two or more below `A`
holds an anchored block of a correct author. -/
def Broad : Prop :=
  ∀ (Validator BlockId Payload : Type) [Fintype Validator] [DecidableEq Validator]
    [Faults Validator] [DecidableEq BlockId] (U : KRecord Validator BlockId Payload) (K : ℕ)
    (A : BlockId) (ρ : ℕ), 2 ≤ K → A ∈ U.ids → ρ + 2 ≤ (U.block A).round →
    ∃ x ∈ U.ids, (U.block x).round = ρ ∧ (U.block x).creator ∈ (Correct : Finset Validator) ∧
      AnchoredBelow U K A x

/-- **A direct commit is linked through the sub-DAG**: at `K ≥ 3`, below a
block at round `r + 3` or above, the sub-DAG holds a certificate for a
directly committed round-`r` block, with its references. -/
def Linked : Prop :=
  ∀ (Validator BlockId Payload : Type) [Fintype Validator] [DecidableEq Validator]
    [Faults Validator] [DecidableEq BlockId] (U : KRecord Validator BlockId Payload) (K : ℕ)
    (A L : BlockId) (r : ℕ), 3 ≤ K → A ∈ U.ids → r + 3 ≤ (U.block A).round →
    DirectCommit U L r → AvailLinked U K A L r

/-- **A link excludes a direct skip**: a block for which the sub-DAG holds a
certificate is not directly skipped. -/
def Exclusive : Prop :=
  ∀ (Validator BlockId Payload : Type) [Fintype Validator] [DecidableEq Validator]
    [Faults Validator] [DecidableEq BlockId] (U : KRecord Validator BlockId Payload) (K : ℕ)
    (A L : BlockId) (r : ℕ), AvailLinked U K A L r → ¬ DirectSkip U L r

/-- The available sub-DAG. -/
def Statement : Prop := Held ∧ Broad ∧ Linked ∧ Exclusive

end Avail

end KPartialDag

end LeanDag
