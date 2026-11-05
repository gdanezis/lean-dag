import LeanDag.KPartialDag.Model.Live
/-!
# Liveness — statement

`docs/kpartial.md` §6. Responsiveness among a quorum `T` from round `R`
(`RespondsFrom`): every slot led by `T` has blocks of `T` two rounds above it,
each carrying votes from a quorum for its leader block. A node that waits for
a certificate of the leader before building two rounds above produces it.

* **synchrony implies responsiveness** (`Weaker`): partial synchrony among
  `T` (`SyncFrom`) gives responsiveness among `T`;
* **a responsive slot commits** (`Commits`): a node holding the blocks of `T`
  two rounds above the slot, with their references, commits the slot
  directly;
* **a committed run decides below it** (`Descends`): a node holding the
  available sub-DAG below every certified leader block up to slot `n`, which
  has committed every slot from `b` to `n`, decides every slot below `b`
  when `n` may anchor each of them;
* **every slot is decided** (`Progress`): past any slot and any round, the
  schedule names a run of `c` slots led by `T`, and on every record
  responsive among `T` a node holding what the run needs decides every slot
  up to the run's end.

What the node needs is held by correct nodes: the blocks of `T` and their
references by their authors, and the sub-DAG by `Avail.Held`. No bound on
`K` is needed.
Statements only; the proofs are `Proof.lean`.
-/

namespace LeanDag

namespace KPartialDag

namespace Live

/-- **Synchrony implies responsiveness**: partial synchrony among `T` from
round `R` to round `N` gives responsiveness among `T` over the same
rounds. -/
def Weaker : Prop :=
  ∀ (Validator BlockId Payload : Type) [Fintype Validator] [DecidableEq Validator]
    [Faults Validator] [DecidableEq BlockId] [Slots Validator]
    (U : KRecord Validator BlockId Payload) (T : Finset Validator) (R N : ℕ),
    SyncFrom U T R N → RespondsFrom U T R N

/-- **A responsive slot commits**: a node holding the blocks of `T` two rounds
above a slot led by `T`, with their references, commits the slot directly
on a record responsive among `T`. -/
def Commits : Prop :=
  ∀ (Validator BlockId Payload : Type) [Fintype Validator] [DecidableEq Validator]
    [Faults Validator] [DecidableEq BlockId] [S : Slots Validator]
    (U : KRecord Validator BlockId Payload) (K : ℕ) (H : Finset BlockId)
    (T : Finset Validator) (R k : ℕ), RespondsFrom U T R (S.slotRound k + 2) →
    R ≤ S.slotRound k → S.leader k ∈ T →
    WithRefs U T (S.slotRound k + 2) (S.slotRound k + 2) ⊆ ↑H →
    ∃ L, IsLeaderBlock U k L ∧ NodeDecided U K H k (some L)

/-- **A committed run decides below it**: a node holding the available
sub-DAG below every certified leader block up to slot `n`, which has
committed every slot from `b` to `n`, decides every slot below `b` that `n`
may anchor. -/
def Descends : Prop :=
  ∀ (Validator BlockId Payload : Type) [Fintype Validator] [DecidableEq Validator]
    [Faults Validator] [DecidableEq BlockId] [S : Slots Validator]
    (U : KRecord Validator BlockId Payload) (K : ℕ) (H : Finset BlockId) (b n : ℕ),
    H ⊆ U.ids → b ≤ n → (∀ i, i < b → EligibleAt (S := S) 2 i n) →
    AvailBelow U K n ⊆ ↑H → (∀ j, b ≤ j → j ≤ n → ∃ A, NodeDecided U K H j (some A)) →
    ∀ i, i < b → ∃ v, NodeDecided U K H i v

/-- **Every slot is decided**: for a schedule offering runs of `c` slots led
by `T`, each run spanning eligibility, past any slot `k` and round `R` there
is a run from `b` such that, on every record responsive among `T` from `R`
to the run's end, a node holding what the run needs decides every slot below
`b + c`. -/
def Progress : Prop :=
  ∀ (Validator BlockId Payload : Type) [Fintype Validator] [DecidableEq Validator]
    [Faults Validator] [DecidableEq BlockId] [S : Slots Validator] (K : ℕ)
    (T : Finset Validator) (c : ℕ), 0 < c →
    (∀ b i, i < b → EligibleAt (S := S) 2 i (b + c - 1)) → FairRunOn T c →
    ∀ R k, ∃ b, k ≤ b ∧ R ≤ S.slotRound b ∧
      ∀ (U : KRecord Validator BlockId Payload),
        RespondsFrom U T R (S.slotRound (b + c - 1) + 2) →
        ∀ H : Finset BlockId, H ⊆ U.ids →
          WithRefs U T (S.slotRound b) (S.slotRound (b + c - 1) + 2) ∪
            AvailBelow U K (b + c - 1) ⊆ ↑H →
          ∀ i, i < b + c → ∃ v, NodeDecided U K H i v

/-- Liveness. -/
def Statement : Prop := Weaker ∧ Commits ∧ Descends ∧ Progress

end Live

end KPartialDag

end LeanDag
