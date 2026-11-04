import LeanDag.KPartialDag.Model.Node
import LeanDag.Common.Participation
/-!
# K-partial DAG — what a node needs to decide

`docs/kpartial.md` §6. Partial synchrony is read on the record as in the rest
of the tree: from round `R` on, every block of an author in a quorum `T`
references every block of an author in `T` of the round below, and `T` has
a block at every round up to `N` (`SyncFrom`).

A node decides the slots up to `n` once it holds two sets of blocks. The
first is the blocks of authors in `T` at rounds `lo` to `hi`, with their
references (`WithRefs`). The second is the available sub-DAG below every
leader block of a slot up to `n` that has a certificate (`AvailBelow`).

Definitions only.
-/

namespace LeanDag

namespace KPartialDag

variable {Validator : Type*} [Fintype Validator] [DecidableEq Validator] [F : Faults Validator]
variable {BlockId : Type*} [DecidableEq BlockId] {Payload : Type*}

/-- **Partial synchrony among `T` from round `R` to round `N`**: `T` is a
quorum, from round `R` on every block of `T` references every block of `T`
of the round below, and `T` has a block at every round from `R` to `N`. -/
def SyncFrom (U : KRecord Validator BlockId Payload) (T : Finset Validator) (R N : ℕ) : Prop :=
  quorumCard Validator ≤ T.card ∧ SynchronisedOn U T R ∧ ∀ r, R ≤ r → r ≤ N → PopulatedOn U T r

/-- The blocks of authors in `T` at rounds `lo` to `hi`, with their
references. -/
def WithRefs (U : KRecord Validator BlockId Payload) (T : Finset Validator) (lo hi : ℕ) :
    Set BlockId :=
  {z | ∃ c ∈ U.ids, (U.block c).creator ∈ T ∧ lo ≤ (U.block c).round ∧
    (U.block c).round ≤ hi ∧ (z = c ∨ z ∈ (U.block c).refs)}

/-- The available sub-DAG below every leader block of a slot up to `n` that
has a certificate. -/
def AvailBelow [S : Slots Validator] (U : KRecord Validator BlockId Payload) (K n : ℕ) :
    Set BlockId :=
  {z | ∃ j A, j ≤ n ∧ IsLeaderBlock U j A ∧
    (certificatesAt U (IsVote U) (quorumCard Validator) A (S.slotRound j + 2)).Nonempty ∧
    z ∈ Avail U K A}

end KPartialDag

end LeanDag
