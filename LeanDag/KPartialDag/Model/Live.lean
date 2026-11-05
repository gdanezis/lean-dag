import LeanDag.KPartialDag.Model.Node
import LeanDag.Common.Participation
/-!
# K-partial DAG — what a node needs to decide

`docs/kpartial.md` §6. Synchrony and responsiveness among a set `T`
(`SyncFrom`, `RespondsFrom`), and what a node holds to decide a run
(`WithRefs`, `AvailBelow`).
-/

namespace LeanDag

namespace KPartialDag

variable {Validator : Type*} [Fintype Validator] [DecidableEq Validator] [F : Faults Validator]
variable {BlockId : Type*} [DecidableEq BlockId] {Payload : Type*}

/-- **References among `T` from round `R` to round `N`**: every block of `T`
at a round from `R + 1` to `N` references every block of `T` of the round
below. -/
def SynchronisedTo (U : KRecord Validator BlockId Payload) (T : Finset Validator) (R N : ℕ) :
    Prop :=
  ∀ n, R ≤ n → n < N → ∀ b ∈ U.ids, (U.block b).round = n + 1 → (U.block b).creator ∈ T →
    ∀ a ∈ U.ids, (U.block a).round = n → (U.block a).creator ∈ T → a ∈ (U.block b).refs

/-- **Partial synchrony among `T` from round `R` to round `N`**: `T` is a
quorum, from round `R` to round `N` every block of `T` references every
block of `T` of the round below, and `T` has a block at every round from `R`
to `N`. -/
def SyncFrom (U : KRecord Validator BlockId Payload) (T : Finset Validator) (R N : ℕ) : Prop :=
  quorumCard Validator ≤ T.card ∧ SynchronisedTo U T R N ∧
    ∀ r, R ≤ r → r ≤ N → PopulatedOn U T r

variable [S : Slots Validator]

/-- **Slot `k` responds among `T`**: `T` has a block two rounds above the
slot, and each block of `T` there carries votes from a quorum for one leader
block of the slot. -/
def Responds (U : KRecord Validator BlockId Payload) (T : Finset Validator) (k : ℕ) : Prop :=
  PopulatedOn U T (S.slotRound k + 2) ∧ ∃ L, IsLeaderBlock U k L ∧
    ∀ C ∈ U.ids, (U.block C).creator ∈ T → (U.block C).round = S.slotRound k + 2 →
      CarriesVotes U (IsVote U) (quorumCard Validator) C L

/-- **Responsiveness among `T` from round `R` to round `N`**: `T` is a quorum,
and every slot led by `T` from round `R` to round `N − 2` responds. -/
def RespondsFrom (U : KRecord Validator BlockId Payload) (T : Finset Validator) (R N : ℕ) :
    Prop :=
  quorumCard Validator ≤ T.card ∧ ∀ k, R ≤ S.slotRound k → S.slotRound k + 2 ≤ N →
    S.leader k ∈ T → Responds U T k

/-- The blocks of authors in `T` at rounds `lo` to `hi`, with their
references. -/
def WithRefs (U : KRecord Validator BlockId Payload) (T : Finset Validator) (lo hi : ℕ) :
    Set BlockId :=
  {z | ∃ c ∈ U.ids, (U.block c).creator ∈ T ∧ lo ≤ (U.block c).round ∧
    (U.block c).round ≤ hi ∧ (z = c ∨ z ∈ (U.block c).refs)}

/-- The available sub-DAG below every leader block of a slot up to `n` that
has a certificate. -/
def AvailBelow (U : KRecord Validator BlockId Payload) (K n : ℕ) :
    Set BlockId :=
  {z | ∃ j A, j ≤ n ∧ IsLeaderBlock U j A ∧
    (certificatesAt U (IsVote U) (quorumCard Validator) A (S.slotRound j + 2)).Nonempty ∧
    z ∈ Avail U K A}

end KPartialDag

end LeanDag
