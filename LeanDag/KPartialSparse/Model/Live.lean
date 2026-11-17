import LeanDag.KPartialSparse.Model.Node
import LeanDag.Common.Participation
import LeanDag.KPartialDag.Model.Rule
/-!
# Sparse K-partial DAG — what a node needs to decide

`docs/kpartial-sparse.md` §6. Synchrony and responsiveness among a set `T` in
sparse terms (`SyncFrom`, `Responds`, `RespondsFrom`), and what a node holds
to decide a run (`HeldBy`, `AvailBelow`).
-/

namespace LeanDag

namespace KPartialSparse

open KPartialDag Scheme

variable {Validator : Type*} [Fintype Validator] [DecidableEq Validator] [F : Faults Validator]
variable [Cr : Crashes Validator] [Ld : Leaders Validator]
variable {BlockId : Type*} [LinearOrder BlockId] {Payload : Type*} [ClaimFormat BlockId Payload]
variable [S : Slots Validator]

/-- **Partial synchrony among `T` from round `R` to round `N`**, in sparse
terms: `T` is a quorum with a block at every round from `R` to `N`; one round
above a slot led by `T`, every block of `T` references every leader block of
the slot; and two rounds above a block that every block of `T` one round up
references, every block of `T` claims it. -/
def SyncFrom (U : SRecord Validator BlockId Payload) (T : Finset Validator) (R N : ℕ) : Prop :=
  kQuorum Validator ≤ T.card ∧ (∀ r, R ≤ r → r ≤ N → PopulatedOn U T r) ∧
    (∀ k, R ≤ S.slotRound k → S.slotRound k + 1 ≤ N → S.leader k ∈ T → ∀ L, IsLeaderBlock U k L →
      ∀ C ∈ U.ids, (U.block C).creator ∈ T → (U.block C).round = S.slotRound k + 1 →
        L ∈ (U.block C).refs) ∧
    ∀ L ∈ U.ids, R ≤ (U.block L).round → (U.block L).round + 2 ≤ N →
      (∀ C ∈ U.ids, (U.block C).creator ∈ T → (U.block C).round = (U.block L).round + 1 →
        L ∈ (U.block C).refs) →
      ∀ D ∈ U.ids, (U.block D).creator ∈ T → (U.block D).round = (U.block L).round + 2 →
        L ∈ claimsOf U D

/-- **Slot `k` responds among `T`** at a row: `T` has blocks at the round of the
slot's certificates, and each of them certifies one leader block of the
slot. -/
def Responds (p : Params) (U : SRecord Validator BlockId Payload) (T : Finset Validator) (k : ℕ) :
    Prop :=
  PopulatedOn U T (certRound p (S.slotRound k)) ∧ ∃ L, IsLeaderBlock U k L ∧
    ∀ C ∈ U.ids, (U.block C).creator ∈ T → (U.block C).round = certRound p (S.slotRound k) →
      Certifies p U C L (S.slotRound k)

/-- **Responsiveness among `T` from round `R` to round `N`**: `T` is a quorum,
and every slot led by `T` from round `R` whose certificates lie at round `N`
or below responds. -/
def RespondsFrom (p : Params) (U : SRecord Validator BlockId Payload) (T : Finset Validator)
    (R N : ℕ) : Prop :=
  kQuorum Validator ≤ T.card ∧ ∀ k, R ≤ S.slotRound k → certRound p (S.slotRound k) ≤ N →
    S.leader k ∈ T → Responds p U T k

omit [ClaimFormat BlockId Payload] S in
/-- The blocks of authors in `T` at rounds `lo` to `hi`. -/
def HeldBy (U : SRecord Validator BlockId Payload) (T : Finset Validator) (lo hi : ℕ) :
    Set BlockId :=
  {c | c ∈ U.ids ∧ (U.block c).creator ∈ T ∧ lo ≤ (U.block c).round ∧ (U.block c).round ≤ hi}

omit [ClaimFormat BlockId Payload] in
/-- The available sub-DAG below every leader block of a slot up to `n`. -/
def AvailBelow (U : SRecord Validator BlockId Payload) (K n : ℕ) : Set BlockId :=
  {z | ∃ j A, j ≤ n ∧ IsLeaderBlock U j A ∧ z ∈ Avail U K A}

end KPartialSparse

end LeanDag
