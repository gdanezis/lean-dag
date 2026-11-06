import LeanDag.KPartialDag.Model.Reactive
/-!
# Reactive nodes in time — statement

`docs/kpartial.md` §11, Theorem 7: nodes that wait for a quorum, the leaders
and a certificate, with a timeout `τ`, a grace period `γ` and a minimum wait
`μ`, under message delay `δ` from time `G` and any crashes and restarts,
build at most one block a round, resume after crashes, and from some round
on produce a responsive and synchronous run in which the ledger grows.

Statements only; the proofs are `Proof.lean`.
-/

namespace LeanDag

namespace KPartialDag

namespace Reactive

/-- **Persisting the last round built avoids equivocation**: a correct
validator that persists the last round it built builds at most one block a
round. -/
def Persisted : Prop :=
  ∀ (Validator BlockId Payload : Type) [Fintype Validator] [DecidableEq Validator]
    [Faults Validator] [Crashes Validator] [LinearOrder BlockId] [Slots Validator]
    (ids : Finset BlockId) (block : BlockId → Block Validator BlockId Payload)
    (order : BlockId → ℕ) (next : Validator → ℕ → ℕ),
    Persists ids block order next → ∀ i ∈ ids, ∀ j ∈ ids,
      (block i).creator ∈ (Correct : Finset Validator) → (block i).creator = (block j).creator →
      (block i).round = (block j).round → i = j

/-- **Building above the disk persists the last round built**: a correct
validator that keeps its highest block on disk, builds at most one block at
a time, and builds only above the blocks of its own on its disk persists the
last round it built, numbering its builds by time. -/
def OnDisk : Prop :=
  ∀ (Validator BlockId Payload : Type) [Fintype Validator] [DecidableEq Validator]
    [Faults Validator] [Crashes Validator] [LinearOrder BlockId] [Slots Validator]
    (ids : Finset BlockId) (block : BlockId → Block Validator BlockId Payload)
    (tl : Timeline Validator BlockId),
    BuildsAboveDisk ids block tl → ∃ next, Persists ids block tl.built next

/-- **Operations resume**: under the rules for nodes from round `R` to round
`N`, with any crashes and restarts before `G`, once a validator of `T` has
built above round `R` by `G`, there is a round `R' > R` such that, if
`R' ≤ N`, the timeline is a reactive run from `R'` to `N`, and every validator
of `T` has reached `R'` by `G + 3δ + 3 max τ μ`. -/
def Resumes : Prop :=
  ∀ (Validator BlockId Payload : Type) [Fintype Validator] [DecidableEq Validator]
    [Faults Validator] [Crashes Validator] [LinearOrder BlockId] [Slots Validator]
    (U : KRecord Validator BlockId Payload) (tl : Timeline Validator BlockId)
    (T : Finset Validator) (G δ τ γ μ R N : ℕ),
    NodeRules U tl T G δ τ γ μ R N → ∀ b ∈ U.ids,
      (U.block b).creator ∈ T → tl.built b ≤ G →
      R < (U.block b).round → ∃ R', R < R' ∧
        (R' ≤ N → ReactiveRun U tl T G δ τ γ μ R' N ∧
          ReachedBy U tl T R' (G + 3 * δ + 3 * max τ μ))

/-- **Every round is reached**: under the reactive rules from round `R` to
round `N`, every validator of `T` has a block at every round from `R` to
`N`, or above it. -/
def Built : Prop :=
  ∀ (Validator BlockId Payload : Type) [Fintype Validator] [DecidableEq Validator]
    [Faults Validator] [Crashes Validator] [LinearOrder BlockId] [Slots Validator]
    (U : KRecord Validator BlockId Payload) (tl : Timeline Validator BlockId)
    (T : Finset Validator) (G δ τ γ μ R N : ℕ),
    ReactiveRules U tl T G δ τ γ μ R N → ∀ s, R ≤ s → s ≤ N → ∃ t, ReachedBy U tl T s t

/-- **Nodes behind catch up within `δ`**: under the rules for nodes from round
`R` to round `N`, once a set `A` of `f + 1` validators of `T` have built at
round `s + 1`, from `R + 1` to `N`, by a time `t ≥ G`, every validator of `T`
has reached round `s + 1` by `t + δ`. -/
def CatchesUp : Prop :=
  ∀ (Validator BlockId Payload : Type) [Fintype Validator] [DecidableEq Validator]
    [F : Faults Validator] [Crashes Validator] [LinearOrder BlockId] [Slots Validator]
    (U : KRecord Validator BlockId Payload) (tl : Timeline Validator BlockId)
    (T : Finset Validator) (G δ τ γ μ R N : ℕ),
    NodeRules U tl T G δ τ γ μ R N → ∀ s t (A : Finset Validator), R ≤ s → s < N → G ≤ t →
      A ⊆ T → F.f + 1 ≤ A.card →
      (∀ v ∈ A, ∃ b ∈ U.ids, (U.block b).creator = v ∧ (U.block b).round = s + 1 ∧
        tl.built b ≤ t) →
      ReachedBy U tl T (s + 1) (t + δ)

/-- **A reactive run starts**: under the reactive rules from round `R` to
round `N`, there is a round `R' ≥ R`, either `R` or one above a round that a
block of `T` reached before `G + τ`, such that, if `R' ≤ N`, the timeline
is a reactive run from `R'` to `N`, and every validator of `T` has reached
`R'` within `2δ + 2 max τ μ` of `G + τ` and of the time all reached `R`. -/
def Starts : Prop :=
  ∀ (Validator BlockId Payload : Type) [Fintype Validator] [DecidableEq Validator]
    [Faults Validator] [Crashes Validator] [LinearOrder BlockId] [Slots Validator]
    (U : KRecord Validator BlockId Payload) (tl : Timeline Validator BlockId)
    (T : Finset Validator) (G δ τ γ μ R N : ℕ),
    ReactiveRules U tl T G δ τ γ μ R N → ∃ R', R ≤ R' ∧
      (R' = R ∨ ∃ x ∈ U.ids, (U.block x).creator ∈ T ∧
        (U.block x).round + 1 = R' ∧ tl.built x < G + τ) ∧
      (R' ≤ N → ReactiveRun U tl T G δ τ γ μ R' N ∧
        ∀ t₀, ReachedBy U tl T R t₀ → ReachedBy U tl T R' (max t₀ (G + τ) + 2 * δ + 2 * max τ μ))

/-- **Each round within `δ + max τ μ`**: at `δ < γ ≤ τ`, once every validator
of `T` has reached round `s`, from `R` to below `N`, by `t`, every validator
of `T` has built at round `s + 1` by `t + δ + max τ μ`. -/
def Slow : Prop :=
  ∀ (Validator BlockId Payload : Type) [Fintype Validator] [DecidableEq Validator]
    [Faults Validator] [Crashes Validator] [LinearOrder BlockId] [Slots Validator]
    (U : KRecord Validator BlockId Payload) (tl : Timeline Validator BlockId)
    (T : Finset Validator) (G δ τ γ μ R N : ℕ),
    ReactiveRun U tl T G δ τ γ μ R N → δ < γ → γ ≤ τ → ∀ s t, R ≤ s → s < N →
      ReachedBy U tl T s t → BuiltBy U tl T (s + 1) (t + δ + max τ μ)

/-- **Rounds led by `T` within `δ + max γ μ`**: at `τ ≥ 2δ`
and `δ < γ ≤ τ`, when the slots at round `s`, from `R + 2` to below `N`, and
one round below have leaders of `T`, once every validator of `T` has built
at round `s` by `t`, every validator of `T` has built at round `s + 1` by
`t + δ + max γ μ`. -/
def Fast : Prop :=
  ∀ (Validator BlockId Payload : Type) [Fintype Validator] [DecidableEq Validator]
    [Faults Validator] [Crashes Validator] [LinearOrder BlockId] [S : Slots Validator]
    (U : KRecord Validator BlockId Payload) (tl : Timeline Validator BlockId)
    (T : Finset Validator) (G δ τ γ μ R N : ℕ),
    ReactiveRun U tl T G δ τ γ μ R N → 2 * δ ≤ τ → δ < γ → γ ≤ τ → ∀ s t, R + 2 ≤ s → s < N →
      (∀ k, S.slotRound k = s ∨ S.slotRound k + 1 = s → S.leader k ∈ T) →
      BuiltBy U tl T s t → BuiltBy U tl T (s + 1) (t + δ + max γ μ)

/-- **The run is responsive**: at `τ ≥ 2δ` and `δ < γ ≤ τ`, a reactive run
from round `R` to round `N` is responsive among `T` from
round `R + 1` to `N`. -/
def Responsive : Prop :=
  ∀ (Validator BlockId Payload : Type) [Fintype Validator] [DecidableEq Validator]
    [Faults Validator] [Crashes Validator] [LinearOrder BlockId] [Slots Validator]
    (U : KRecord Validator BlockId Payload) (tl : Timeline Validator BlockId)
    (T : Finset Validator) (G δ τ γ μ R N : ℕ),
    ReactiveRun U tl T G δ τ γ μ R N → 2 * δ ≤ τ → δ < γ → γ ≤ τ →
      RespondsFrom U T (R + 1) N

/-- **A slot led by `T` commits within `3δ + 2 max γ μ`**: at a live row,
`τ ≥ 2δ` and `δ < γ ≤ τ`, when every slot from one round below a slot at
round `r`, from `R + 2` to `N − 2`, to one round above it has a leader in
`T`, and every validator of `T` has built at round `r` by `t`, every
node of `T` commits the slot directly on what it holds at
`t + 3δ + 2 max γ μ`. -/
def Commits : Prop :=
  ∀ (Validator BlockId Payload : Type) [Fintype Validator] [DecidableEq Validator]
    [Faults Validator] [Crashes Validator]
    [LinearOrder BlockId] [S : Slots Validator] (p : Scheme.Params)
    (U : KRecord Validator BlockId Payload) (tl : Timeline Validator BlockId)
    (T : Finset Validator) (G δ τ γ μ R K N : ℕ), Row Validator p → LiveRow Validator p →
    ReactiveRun U tl T G δ τ γ μ R N → 2 * δ ≤ τ → δ < γ → γ ≤ τ → ∀ k t,
      R + 2 ≤ S.slotRound k → S.slotRound k + 2 ≤ N →
      (∀ j, S.slotRound k ≤ S.slotRound j + 1 → S.slotRound j ≤ S.slotRound k + 1 →
        S.leader j ∈ T) →
      BuiltBy U tl T (S.slotRound k) t → ∀ v ∈ T,
        ∃ L, IsLeaderBlock U k L ∧
          NodeDecided p U K (tl.held v (t + 3 * δ + 2 * max γ μ)) k (some L)

/-- **The run is synchronous**: at `2δ ≤ γ ≤ τ` and `δ < γ`, a reactive run
from round `R` to round `N` is synchronous among `T` from
round `R + 1` to `N`. -/
def Synchronised : Prop :=
  ∀ (Validator BlockId Payload : Type) [Fintype Validator] [DecidableEq Validator]
    [Faults Validator] [Crashes Validator] [LinearOrder BlockId] [Slots Validator]
    (U : KRecord Validator BlockId Payload) (tl : Timeline Validator BlockId)
    (T : Finset Validator) (G δ τ γ μ R N : ℕ),
    ReactiveRun U tl T G δ τ γ μ R N → 2 * δ ≤ γ → δ < γ → γ ≤ τ →
      SyncFrom U T (R + 1) N

/-- **Nothing a leader outputs is lost**: when correct nodes keep on disk the
histories to depth `K` of their blocks' references, every block of the
available sub-DAG of a voted block is on the disk of a node of any quorum
`T` of correct nodes from some time on, through any crash. -/
def Durable : Prop :=
  ∀ (Validator BlockId Payload : Type) [Fintype Validator] [DecidableEq Validator]
    [Faults Validator] [Crashes Validator] [LinearOrder BlockId] [Slots Validator]
    (U : KRecord Validator BlockId Payload) (tl : Timeline Validator BlockId)
    (T : Finset Validator) (K : ℕ), T ⊆ (Correct : Finset Validator) →
    quorumCard Validator ≤ T.card → 1 ≤ K → KeepsHistory U tl K → ∀ A ∈ U.ids, Voted U A →
      ∀ z ∈ Avail U K A, ∃ w ∈ T, ∃ t₀, ∀ t, t₀ ≤ t → z ∈ tl.disk w t

/-- **The ledger grows**: at a live row, on a reactive run from round `R` to
round `N`, at `τ ≥ 2δ` and `δ < γ ≤ τ`, when nodes of `T` fetch the available
sub-DAG of the voted leader blocks they hold within `Δ`, and the schedule offers
runs of `c` leaders of `T` spanning eligibility, past any slot `k` there is
a slot `b` such that, if the run reaches round `σ(b + c − 1) + 2`, every
node of `T`, at one time, decides every slot below `b + c` and has fetched
each leader it commits down to `D` rounds below it. -/
def Ledger : Prop :=
  ∀ (Validator BlockId Payload : Type) [Fintype Validator] [DecidableEq Validator]
    [Faults Validator] [Crashes Validator]
    [LinearOrder BlockId] [S : Slots Validator] (p : Scheme.Params)
    (U : KRecord Validator BlockId Payload) (tl : Timeline Validator BlockId)
    (T : Finset Validator) (G δ τ γ μ R N K D Δ c : ℕ),
    Row Validator p → LiveRow Validator p → ReactiveRun U tl T G δ τ γ μ R N → 2 * δ ≤ τ →
    δ < γ → γ ≤ τ → Fetches U tl T K G Δ →
    0 < c → (∀ b i, i < b → EligibleAt (S := S) (p.waveLength - 1) i (b + c - 1)) →
    FairRunOn T c → ∀ k, ∃ b, k ≤ b ∧
      (S.slotRound (b + c - 1) + 2 ≤ N → ∃ t, ∀ v ∈ T,
        ∃ g : ℕ → Option BlockId, ∀ i, i < b + c → NodeDecided p U K (tl.held v t) i (g i) ∧
          ∀ L, g i = some L → FetchedIn U K (tl.held v t) L ((U.block L).round - D))

/-- Reactive nodes in time. -/
def Statement : Prop :=
  Persisted ∧ OnDisk ∧ Resumes ∧ Built ∧ CatchesUp ∧ Starts ∧ Slow ∧ Fast ∧ Responsive ∧ Commits ∧
    Synchronised ∧ Durable ∧ Ledger

end Reactive

end KPartialDag

end LeanDag
