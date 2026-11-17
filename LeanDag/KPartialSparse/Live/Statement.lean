import LeanDag.KPartialSparse.Model.Live
/-!
# Sparse K-partial DAG — liveness, statement

`docs/kpartial-sparse.md` §6, Theorem 4: synchrony among `T` gives
responsiveness and the votes behind each claim of `T`; a responsive slot
commits; a committed run decides below it; and past any slot a run led by `T`
decides every slot up to its end.

Statements only; the proofs are `Proof.lean`.
-/

namespace LeanDag

namespace KPartialSparse

namespace Live

open KPartialDag Scheme

/-- **Synchrony implies responsiveness**, at every row. -/
def Weaker : Prop :=
  ∀ (Validator BlockId Payload : Type) [Fintype Validator] [DecidableEq Validator]
    [Faults Validator] [Crashes Validator] [Leaders Validator] [LinearOrder BlockId]
    [ClaimFormat BlockId Payload] [Slots Validator] (p : Params)
    (U : SRecord Validator BlockId Payload) (T : Finset Validator) (R N : ℕ),
    SyncFrom U T R N → RespondsFrom p U T R N

/-- **Under synchrony the votes behind a claim are there to hold**: a node
holding a leader block of a slot led by `T` and the blocks of `T` one round
above it backs a claim for it, at any threshold within the quorum. -/
def Backable : Prop :=
  ∀ (Validator BlockId Payload : Type) [Fintype Validator] [DecidableEq Validator]
    [Faults Validator] [Crashes Validator] [Leaders Validator] [LinearOrder BlockId]
    [ClaimFormat BlockId Payload] [S : Slots Validator] (U : SRecord Validator BlockId Payload)
    (T : Finset Validator) (H : Finset BlockId) (R N k t : ℕ) (L : BlockId),
    SyncFrom U T R N → R ≤ S.slotRound k → S.slotRound k + 1 ≤ N → S.leader k ∈ T →
    IsLeaderBlock U k L → t ≤ kQuorum Validator → L ∈ H →
    HeldBy U T (S.slotRound k + 1) (S.slotRound k + 1) ⊆ ↑H → Backs U t H L

/-- **A responsive slot commits**: at a live row, a node holding the blocks of
`T` at the round of a slot's certificates commits the slot directly, when the
slot is led by `T` on a record responsive among `T`. -/
def Commits : Prop :=
  ∀ (Validator BlockId Payload : Type) [Fintype Validator] [DecidableEq Validator]
    [Faults Validator] [Crashes Validator] [Leaders Validator] [LinearOrder BlockId]
    [ClaimFormat BlockId Payload] [S : Slots Validator] (p : Params)
    (U : SRecord Validator BlockId Payload) (K : ℕ) (H : Finset BlockId) (T : Finset Validator)
    (R k : ℕ), LiveRow Validator p → RespondsFrom p U T R (certRound p (S.slotRound k)) →
    R ≤ S.slotRound k → S.leader k ∈ T →
    HeldBy U T (certRound p (S.slotRound k)) (certRound p (S.slotRound k)) ⊆ ↑H →
    ∃ L, IsLeaderBlock U k L ∧ NodeDecided p U K H k (some L)

/-- **A committed run decides below it**: a node holding the available sub-DAG
below every leader block up to slot `n`, which has committed every slot from
`b` to `n`, decides every slot below `b` that `n` may anchor. -/
def Descends : Prop :=
  ∀ (Validator BlockId Payload : Type) [Fintype Validator] [DecidableEq Validator]
    [Faults Validator] [Crashes Validator] [Leaders Validator] [LinearOrder BlockId]
    [ClaimFormat BlockId Payload] [S : Slots Validator] (p : Params)
    (U : SRecord Validator BlockId Payload) (K : ℕ) (H : Finset BlockId) (b n : ℕ), b ≤ n →
    (∀ i, i < b → EligibleAt (S := S) (p.waveLength - 1) i n) → AvailBelow U K n ⊆ ↑H →
    (∀ j, b ≤ j → j ≤ n → ∃ A, NodeDecided p U K H j (some A)) →
    ∀ i, i < b → ∃ v, NodeDecided p U K H i v

/-- **Every slot is decided**: for a schedule offering runs of `c` slots led by
`T`, each run spanning eligibility, past any slot `k` and round `R` there is a
run from `b` such that, on every record responsive among `T` from `R` to the
run's end, a node holding the blocks of `T` over the run and the available
sub-DAG below its leader blocks decides every slot below `b + c`, at a live
row. -/
def Progress : Prop :=
  ∀ (Validator BlockId Payload : Type) [Fintype Validator] [DecidableEq Validator]
    [Faults Validator] [Crashes Validator] [Leaders Validator] [LinearOrder BlockId]
    [ClaimFormat BlockId Payload] [S : Slots Validator] (p : Params) (K : ℕ)
    (T : Finset Validator) (c : ℕ), LiveRow Validator p → 0 < c →
    (∀ b i, i < b → EligibleAt (S := S) (p.waveLength - 1) i (b + c - 1)) → FairRunOn T c →
    ∀ R k, ∃ b, k ≤ b ∧ R ≤ S.slotRound b ∧
      ∀ (U : SRecord Validator BlockId Payload),
        RespondsFrom p U T R (certRound p (S.slotRound (b + c - 1))) →
        ∀ H : Finset BlockId,
          HeldBy U T (S.slotRound b) (certRound p (S.slotRound (b + c - 1))) ∪
            AvailBelow U K (b + c - 1) ⊆ ↑H →
          ∀ i, i < b + c → ∃ v, NodeDecided p U K H i v

/-- Liveness. -/
def Statement : Prop := Weaker ∧ Backable ∧ Commits ∧ Descends ∧ Progress

end Live

end KPartialSparse

end LeanDag
