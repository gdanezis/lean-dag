import LeanDag.KPartialDag.Model.Substrate
/-!
# K-partial DAG — the commit rule's tests

`docs/kpartial.md` §2. Mysticeti's tests read on a K-partial DAG. A vote for
a round-`r` block `L` is a round-`(r+1)` block referencing it, and a
certificate a round-`(r+2)` block carrying votes for `L` from a quorum
(`certificatesAt`). The direct tests read rounds `r` to `r + 2`. The
indirect test reads the available sub-DAG below the anchor instead of the
anchor's whole history (`AvailLinked`).

Definitions only.
-/

namespace LeanDag

namespace KPartialDag

variable {Validator : Type*} [Fintype Validator] [DecidableEq Validator] [F : Faults Validator]
variable {BlockId : Type*} [DecidableEq BlockId] {Payload : Type*}

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
certificate for `L`. -/
def AvailLinked (U : KRecord Validator BlockId Payload) (K : ℕ) (A L : BlockId) (r : ℕ) :
    Prop :=
  ∃ C ∈ certificatesAt U (IsVote U) (quorumCard Validator) L (r + 2), C ∈ Avail U K A

end KPartialDag

end LeanDag
