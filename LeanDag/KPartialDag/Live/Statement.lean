import LeanDag.KPartialDag.Model.Live
/-!
# Liveness — statement

`docs/kpartial.md` §6. Partial synchrony from round `R` on, among a quorum
`T`, read on the record (`SynchronisedOn`, `PopulatedOn`):

* **a leader in `T` commits** (`Commits`): a node holding the blocks of `T`
  two rounds above the slot, with their references, commits the slot
  directly;
* **a committed run decides below it** (`Descends`): a node holding the
  available sub-DAG below every certified leader block up to slot `n`, which
  has committed every slot from `b` to `n`, decides every slot below `b`
  when `n` may anchor each of them;
* **what a node needs, a correct node holds** (`Delivered`), so after
  synchrony a node fetches it;
* **every slot is decided** (`Progress`): past any slot and any round, the
  schedule names a run of `c` slots led by `T`, and a node holding what the
  run needs decides every slot up to the run's end.

No bound on `K` is needed. Statements only; the proofs are `Proof.lean`.
-/

namespace LeanDag

namespace KPartialDag

namespace Live

/-- **A leader in `T` commits**: after synchrony, a node holding the blocks of
`T` two rounds above the slot, with their references, commits the slot
directly. -/
def Commits : Prop :=
  ∀ (Validator BlockId Payload : Type) [Fintype Validator] [DecidableEq Validator]
    [Faults Validator] [DecidableEq BlockId] [S : Slots Validator] (K : ℕ)
    (U : KRecord Validator BlockId Payload) (H : Finset BlockId) (T : Finset Validator)
    (R k : ℕ), quorumCard Validator ≤ T.card → SynchronisedOn U T R → R ≤ S.slotRound k →
    S.leader k ∈ T → (∀ r, S.slotRound k ≤ r → r ≤ S.slotRound k + 2 → PopulatedOn U T r) →
    WithRefs U T (S.slotRound k + 2) (S.slotRound k + 2) ⊆ ↑H →
    ∃ L, IsLeaderBlock U k L ∧ NodeDecided U K H k (some L)

/-- **A committed run decides below it**: a node holding the available
sub-DAG below every certified leader block up to slot `n`, which has
committed every slot from `b` to `n`, decides every slot below `b` that `n`
may anchor. -/
def Descends : Prop :=
  ∀ (Validator BlockId Payload : Type) [Fintype Validator] [DecidableEq Validator]
    [Faults Validator] [DecidableEq BlockId] [S : Slots Validator] (K : ℕ)
    (U : KRecord Validator BlockId Payload) (H : Finset BlockId) (b n : ℕ), H ⊆ U.ids →
    b ≤ n → (∀ i, i < b → EligibleAt (S := S) 2 i n) → AvailBelow U K n ⊆ ↑H →
    (∀ j, b ≤ j → j ≤ n → ∃ A, NodeDecided U K H j (some A)) →
    ∀ i, i < b → ∃ v, NodeDecided U K H i v

/-- **What a node needs, a correct node holds**, for `T` of correct
authors. -/
def Delivered : Prop :=
  ∀ (Validator BlockId Payload : Type) [Fintype Validator] [DecidableEq Validator]
    [Faults Validator] [DecidableEq BlockId] [Slots Validator] (K : ℕ)
    (U : KRecord Validator BlockId Payload) (T : Finset Validator) (lo hi n : ℕ),
    T ⊆ Correct → WithRefs U T lo hi ∪ AvailBelow U K n ⊆ CorrectHeld U K

/-- **Every slot is decided**: for a schedule offering runs of `c` slots led
by `T`, each run spanning eligibility, past any slot `k` and round `R` there
is a run from `b` such that, on every record synchronised on `T` from `R` and
populated over the run, a node holding what the run needs decides every slot
below `b + c`. -/
def Progress : Prop :=
  ∀ (Validator BlockId Payload : Type) [Fintype Validator] [DecidableEq Validator]
    [Faults Validator] [DecidableEq BlockId] [S : Slots Validator] (K : ℕ)
    (T : Finset Validator) (c : ℕ), quorumCard Validator ≤ T.card → 0 < c →
    (∀ b i, i < b → EligibleAt (S := S) 2 i (b + c - 1)) → FairRunOn T c →
    ∀ R k, ∃ b, k ≤ b ∧ R ≤ S.slotRound b ∧
      ∀ (U : KRecord Validator BlockId Payload), SynchronisedOn U T R →
        (∀ r, S.slotRound b ≤ r → r ≤ S.slotRound (b + c - 1) + 2 → PopulatedOn U T r) →
        ∀ H : Finset BlockId, H ⊆ U.ids →
          WithRefs U T (S.slotRound b) (S.slotRound (b + c - 1) + 2) ∪
            AvailBelow U K (b + c - 1) ⊆ ↑H →
          ∀ i, i < b + c → ∃ v, NodeDecided U K H i v

/-- Liveness. -/
def Statement : Prop := Commits ∧ Descends ∧ Delivered ∧ Progress

end Live

end KPartialDag

end LeanDag
