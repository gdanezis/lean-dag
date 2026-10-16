import LeanDag.Scheme.Model.Local
import LeanDag.Reactive.Basic
/-!
# The family, run reactively

`docs/scheme.md` §13. A responsive validator does not wait a timeout every
round: it builds as soon as what the rule counts has arrived, with the
timeout only as a fallback. The reactive timing is the development's
(`ReactiveCore`, `Reactive/Basic.lean`); `SchemeReactive` adds the
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

The commit rule is unchanged. `reactiveLive` is the precondition: a
reliable quorum running such an execution past GST, the timeout clearing
`2Δ + proc`, the view caught up to the horizon.

Definitions only; the claims are `Scheme/Reactive/Statement.lean`.
-/

namespace LeanDag

namespace Scheme

variable {Validator : Type} [Fintype Validator] [DecidableEq Validator] [F : Faults Validator]
variable {BlockId : Type} [LinearOrder BlockId] {Payload : Type}
variable {P : Validity Validator BlockId Payload} {honest : Finset Validator} [P.Mechanised]

/-- **The family, run reactively**: the reactive timing with the wait
clauses of a wave. -/
structure SchemeReactive [S : Slots Validator] (p : Params)
    (σ : VoteSel Validator BlockId Payload P honest)
    (U : BlockRecord Validator BlockId Payload P honest) (T : Finset Validator) (N : ℕ)
    extends ReactiveCore U T N where
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

/-- **The reactive liveness precondition**, over a slot window: a reliable
quorum `T` of non-equivocating validators running a reactive execution
past GST, with the timeout clearing `2Δ + proc`, the view caught up to the
horizon, and every slot of the window a wave under it. -/
def reactiveLive (p : Params) (σ : VoteSel Validator BlockId Payload P honest)
    (Hon : Finset Validator) (S : Slots Validator) {U : (schemeRule p σ Hon).Universe}
    (V : (schemeRule p σ Hon).View U) (T : Finset Validator) (lo K : ℕ) : Prop :=
  T ⊆ (Correct : Finset Validator) ∧ T ⊆ honest ∧ quorumCard Validator ≤ T.card ∧
    ∃ (N R₀ : ℕ) (rs : SchemeReactive (S := S) p σ U.val T N),
      rs.gst ≤ R₀ ∧ (∀ n, R₀ ≤ n → 2 * rs.delay + rs.proc ≤ rs.timeout n) ∧
      R₀ ≤ S.slotRound lo ∧ Properties.CoversUpto (schemeRule p σ Hon) V N ∧
      ∀ k, k < K → S.slotRound k + (p.waveLength - 1) ≤ N

end Scheme

end LeanDag
