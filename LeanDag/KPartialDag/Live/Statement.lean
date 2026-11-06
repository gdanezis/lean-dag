import LeanDag.KPartialDag.Model.Live
/-!
# Liveness — statement

`docs/kpartial.md` §6, Theorem 4: synchrony implies responsiveness, and on a
record responsive among a quorum `T`, a node holding what a run of slots led
by `T` needs decides every slot below the run's end.

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
    [Faults Validator] [Crashes Validator] [LinearOrder BlockId] [Slots Validator]
    (U : KRecord Validator BlockId Payload) (T : Finset Validator) (R N : ℕ),
    SyncFrom U T R N → RespondsFrom U T R N

/-- **A responsive slot commits**: at a live row, a node holding the blocks of
`T` one and two rounds above a slot led by `T`, with their references,
commits the slot directly on a record responsive among `T`. -/
def Commits : Prop :=
  ∀ (Validator BlockId Payload : Type) [Fintype Validator] [DecidableEq Validator]
    [Faults Validator] [Crashes Validator]
    [LinearOrder BlockId] [S : Slots Validator] (p : Scheme.Params)
    (U : KRecord Validator BlockId Payload) (K : ℕ) (H : Finset BlockId)
    (T : Finset Validator) (R k : ℕ), Row Validator p → LiveRow Validator p →
    RespondsFrom U T R (S.slotRound k + 2) → R ≤ S.slotRound k → S.leader k ∈ T →
    WithRefs U T (S.slotRound k + 1) (S.slotRound k + 2) ⊆ ↑H →
    ∃ L, IsLeaderBlock U k L ∧ NodeDecided p U K H k (some L)

/-- **A committed run decides below it**: at a row, a node holding the
available sub-DAG below every voted leader block up to slot `n`, which has
committed every slot from `b` to `n`, decides every slot below `b` that `n`
may anchor. -/
def Descends : Prop :=
  ∀ (Validator BlockId Payload : Type) [Fintype Validator] [DecidableEq Validator]
    [Faults Validator] [Crashes Validator]
    [LinearOrder BlockId] [S : Slots Validator] (p : Scheme.Params)
    (U : KRecord Validator BlockId Payload) (K : ℕ) (H : Finset BlockId) (b n : ℕ),
    Row Validator p → H ⊆ U.ids → b ≤ n →
    (∀ i, i < b → EligibleAt (S := S) (p.waveLength - 1) i n) →
    AvailBelow U K n ⊆ ↑H → (∀ j, b ≤ j → j ≤ n → ∃ A, NodeDecided p U K H j (some A)) →
    ∀ i, i < b → ∃ v, NodeDecided p U K H i v

/-- **Every slot is decided**: for a schedule offering runs of `c` slots led
by `T`, each run spanning eligibility, past any slot `k` and round `R` there
is a run from `b` such that, on every record responsive among `T` from `R`
to the run's end, a node holding what the run needs decides every slot below
`b + c`, at a live row. -/
def Progress : Prop :=
  ∀ (Validator BlockId Payload : Type) [Fintype Validator] [DecidableEq Validator]
    [Faults Validator] [Crashes Validator]
    [LinearOrder BlockId] [S : Slots Validator] (p : Scheme.Params) (K : ℕ)
    (T : Finset Validator) (c : ℕ), Row Validator p → LiveRow Validator p → 0 < c →
    (∀ b i, i < b → EligibleAt (S := S) (p.waveLength - 1) i (b + c - 1)) → FairRunOn T c →
    ∀ R k, ∃ b, k ≤ b ∧ R ≤ S.slotRound b ∧
      ∀ (U : KRecord Validator BlockId Payload),
        RespondsFrom U T R (S.slotRound (b + c - 1) + 2) →
        ∀ H : Finset BlockId, H ⊆ U.ids →
          WithRefs U T (S.slotRound b) (S.slotRound (b + c - 1) + 2) ∪
            AvailBelow U K (b + c - 1) ⊆ ↑H →
          ∀ i, i < b + c → ∃ v, NodeDecided p U K H i v

/-- Liveness. -/
def Statement : Prop := Weaker ∧ Commits ∧ Descends ∧ Progress

end Live

end KPartialDag

end LeanDag
