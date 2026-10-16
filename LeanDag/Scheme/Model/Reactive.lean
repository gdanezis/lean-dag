import LeanDag.Scheme.Model.Local
import LeanDag.Scheme.Model.NoFaults
import LeanDag.Reactive.Basic
/-!
# The family, run reactively

`docs/scheme.md` §13. A responsive validator does not wait a timeout every
round: it builds as soon as what the rule counts has arrived, with the
timeout only as a fallback. The reactive timing is the development's
(`ReactiveCore`, `Reactive/Basic.lean`), read at `noFaults`; the
pacemaker's progress rule is `advancesAt q`, at the committee's quorum `q`
rather than the core's `n − f`, so that the hybrid committees, which the
core's fault class excludes, run reactively too. `SchemeReactive` adds the
family's wait clauses, one per round of the wave:

* **reach or wait**, at each round from the one above the proposal to the
  vote round: a reliable block either already reaches the slot's leader
  block, or its builder waited the timeout and references the leader's
  block of the round below if it holds it;
* **certify or wait**, at the decision round of a row whose votes are
  certified a round later: a reliable block either already certifies the
  leader block, or its builder waited the timeout and references every
  reliable vote for it that it holds.

At the Mysticeti row these are Reactive Mysticeti's `vote_or_wait` and
`cert_or_wait`.

The commit rule is unchanged. `reactiveLive` is the precondition, at a
reliability `rel` (the core's, Hydrozoan's, Nemo's): a quorum of `rel`
running such an execution at `q = n − rel.slack` past GST, the timeout
clearing `2Δ + proc`, the view caught up to the horizon.

Definitions only; the claims are `Scheme/Reactive/Statement.lean`.
-/

namespace LeanDag

namespace Scheme

variable {Validator : Type} [Fintype Validator] [DecidableEq Validator] [Nonempty Validator]
variable {BlockId : Type} [LinearOrder BlockId] {Payload : Type}
variable {P : Validity Validator BlockId Payload} {honest : Finset Validator} [P.Mechanised]

attribute [local instance] noFaults

/-- **The family, run reactively**, at quorum `q`: the reactive timing,
the pacemaker's progress rule at `q`, and the wait clauses of a wave. -/
structure SchemeReactive [S : Slots Validator] (q : ℕ) (p : Params)
    (σ : VoteSel Validator BlockId Payload P honest)
    (U : BlockRecord Validator BlockId Payload P honest) (T : Finset Validator) (N : ℕ)
    extends ReactiveCore U T N where
  /-- **The progress rule at `q`.** A reliable validator holding `q`
  distinct round-`n` authors gets past round `n`. -/
  advancesAt : ∀ v ∈ T, ∀ n < N, ∀ t, q ≤ (authorsIn U (holds v t) n).card → n < top v
  /-- **Reach or wait.** At each round from the one above the proposal to
  the vote round, a reliable block reaches the leader block, or its builder
  waited the timeout and references the leader's block of the round below
  if it holds it. -/
  reach_or_wait : ∀ v ∈ T, ∀ k : ℕ, S.slotRound k + p.voteOffset ≤ N → S.leader k ∈ T →
    ∀ L, IsLeaderBlock U k L → ∀ m, m < p.voteOffset →
    ∀ c ∈ U.ids, (U.block c).creator = v → (U.block c).round = S.slotRound k + m + 1 →
    Reaches U c L ∨
      (built v (S.slotRound k + m) + timeout (S.slotRound k + m)
          ≤ built v (S.slotRound k + m + 1) ∧
        ∀ b ∈ U.ids, (U.block b).creator = S.leader k → (U.block b).round = S.slotRound k + m →
          b ∈ holds v (built v (S.slotRound k + m + 1)) → b ∈ (U.block c).refs)
  /-- **Certify or wait.** Where votes are certified a round later, a
  reliable decision-round block certifies the leader block, or its builder
  waited the timeout and references every reliable vote for it that it
  holds. -/
  cert_or_wait : p.voteIsCert = false → ∀ v ∈ T, ∀ k : ℕ,
    S.slotRound k + p.voteOffset + 1 ≤ N → S.leader k ∈ T →
    ∀ L, IsLeaderBlock U k L →
    ∀ c ∈ U.ids, (U.block c).creator = v → (U.block c).round = S.slotRound k + p.voteOffset + 1 →
    IsCert p σ U c L ∨
      (built v (S.slotRound k + p.voteOffset) + timeout (S.slotRound k + p.voteOffset)
          ≤ built v (S.slotRound k + p.voteOffset + 1) ∧
        ∀ b ∈ U.ids, (U.block b).creator ∈ T →
          (U.block b).round = S.slotRound k + p.voteOffset →
          b ∈ holds v (built v (S.slotRound k + p.voteOffset + 1)) → σ.Votes U b L →
          b ∈ (U.block c).refs)

/-- **The reactive liveness precondition**, at reliability `rel`, over a
slot window: a quorum `T` of `rel` of non-equivocating validators running a
reactive execution at `n − rel.slack` past GST, with the timeout clearing
`2Δ + proc`, the view caught up to the horizon, and every slot of the
window a wave under it. -/
def reactiveLive (p : Params) (σ : VoteSel Validator BlockId Payload P honest)
    (Hon : Finset Validator) (rel : Reliability Validator) (S : Slots Validator)
    {U : (schemeRule p σ Hon).Universe} (V : (schemeRule p σ Hon).View U) (T : Finset Validator)
    (lo K : ℕ) : Prop :=
  rel.IsQuorum T ∧ T ⊆ honest ∧
    ∃ (N R₀ : ℕ) (rs : SchemeReactive (S := S) (Fintype.card Validator - rel.slack) p σ U.val T N),
      rs.gst ≤ R₀ ∧ (∀ n, R₀ ≤ n → 2 * rs.delay + rs.proc ≤ rs.timeout n) ∧
      R₀ ≤ S.slotRound lo ∧ Properties.CoversUpto (schemeRule p σ Hon) V N ∧
      ∀ k, k < K → S.slotRound k + (p.waveLength - 1) ≤ N

end Scheme

end LeanDag
