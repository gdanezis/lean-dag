import LeanDag.KPartialDag.Model.Substrate
import LeanDag.Common.Anchored
import LeanDag.Common.Rules
/-!
# K-partial DAG — the commit rule's tests

`docs/kpartial.md` §2. The direct tests (`DirectCommit`, `DirectSkip`), the
indirect test read on the available sub-DAG (`AvailLinked`), and the commit
rule (`kRule`).
-/

namespace LeanDag

namespace KPartialDag

variable {Validator : Type*} [Fintype Validator] [DecidableEq Validator] [F : Faults Validator]
variable {BlockId : Type*} [LinearOrder BlockId] {Payload : Type*}

/-- **`L` is directly committed**: certificates for it from a quorum of
distinct authors. -/
def DirectCommit (U : KRecord Validator BlockId Payload) (L : BlockId) (r : ℕ) : Prop :=
  quorumCard Validator ≤
    (creatorsOf U.block (certificatesAt U (IsVote U) (quorumCard Validator) L (r + 2))).card

/-- **`L` is directly skipped**: a quorum of distinct authors with a block at
the round above that does not reference it. -/
def DirectSkip (U : KRecord Validator BlockId Payload) (L : BlockId) (r : ℕ) : Prop :=
  quorumCard Validator ≤ (blames U L (r + 1)).card

/-- **The indirect test**: the available sub-DAG below the anchor `A` holds a
certificate for `L` and the certificate's references, which carry its
votes. -/
def AvailLinked (U : KRecord Validator BlockId Payload) (K : ℕ) (A L : BlockId) (r : ℕ) :
    Prop :=
  ∃ C ∈ certificatesAt U (IsVote U) (quorumCard Validator) L (r + 2), C ∈ Avail U K A ∧
    ∀ j ∈ (U.block C).refs, j ∈ Avail U K A

/-- **The commit rule on a K-partial DAG**: Mysticeti's direct commit and
slot skip read on a view, at wave two, with one rung, linked through the
available sub-DAG below the anchor. -/
def kRule (K : ℕ) :
    AnchoredRule Validator BlockId Payload (KValid Validator BlockId Payload) Correct where
  waveAt := fun _ => 2
  Commit := fun U V L r _ =>
    certCommit IsVote (quorumCard Validator) (quorumCard Validator) 2 U V L r
  decCommit := fun _ _ _ _ _ => inferInstance
  Skip := fun U V S k => blameSkip (S := S) (quorumCard Validator) U V k
  rungs := 1
  Link := fun _ U A L S k => AvailLinked U K A L (S.slotRound k)
  tie := fun _ _ _ => False

end KPartialDag

end LeanDag
