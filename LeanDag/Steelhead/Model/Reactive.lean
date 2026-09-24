import LeanDag.Steelhead.Model.Decision
import LeanDag.Reactive.Basic
/-!
# Steelhead — the reactive discipline

The execution discipline `SynchronisedOn` stands for in SH6a and SH6b, in its reactive form
(`steelhead.md` §6). The core's `ReactivePace` asks its leader wait at every reliably led slot;
Steelhead's leader is hidden at an asynchronous slot and nobody waits for it, so the wait is
asked only at the rounds that carry it, the synchronous slots and the canary rounds, named by
`waits`. The rest is the core's: time advances with rounds, a validator never waits past its
timeout (`deadline`, a ceiling where the timed model puts a floor), and at the round above a
reliable leader of a waiting round a block either votes or its builder waited the timeout out and
votes for any leader block it holds (`vote_or_wait`).

Steelhead adds one clause, and only where the wave leaves no room for the vote to travel. At a
wave of four rounds or more the vote round sits two rounds or more above the candidate, so a
quorum of votes reaches the certifiers through the DAG and nothing further is asked of the
schedule. At the wave of three the certify round is the vote round's successor, and a certifier
must reference the votes themselves: `cert_or_wait` is that wait, stated only at wave three and at
the rounds that carry the leader wait. The paper's pacing states both waits, the certificate
wait as Mysticeti's vote wait, which is what the wave of three needs of an execution.

**Definitions only**, as in the other model files.
-/

namespace LeanDag

namespace Steelhead

variable {Validator : Type} [Fintype Validator] [DecidableEq Validator]
variable [F : Faults Validator]
variable {BlockId : Type} [LinearOrder BlockId] {Payload : Type}
variable [S : Slots Validator]

/-- **Steelhead's reactive schedule** at the wavelength function `w`, the leader wait at the
rounds `waits` names: the core's pace, the reactive ceiling, the leader wait at the round above a
reliable leader of a waiting round, and the certificate wait at the wave of three. At two rounds
above such a leader, any `T`-authored block either already certifies, or its builder waited the
full timeout and references every reliable vote it holds. Above wave three the certificate clause
says nothing: reachability carries the votes, so the discipline is the core's own. -/
structure ReactiveS (U : BlockUniverse Validator BlockId Payload) (T : Finset Validator) (N : ℕ)
    (w : ℕ → ℕ) (waits : ℕ → Prop) extends PaceCore U T N where
  /-- Time advances with rounds, over the rounds `v` reached. -/
  built_lt : ∀ v ∈ T, ∀ n < top v, built v n < built v (n + 1)
  /-- **The reactive ceiling.** A validator never waits past the timeout; it may build any time
  before it. -/
  deadline : ∀ v ∈ T, ∀ n < top v, built v (n + 1) ≤ built v n + timeout n
  /-- **The leader wait, at the rounds that carry it.** At the round above a reliable leader of
  a waiting round, any `T`-authored block either votes (the reactive exit), or its builder waited
  the full timeout and votes for any leader block it holds (the fallback). -/
  vote_or_wait : ∀ v ∈ T, ∀ k : ℕ, waits (S.slotRound k) → S.slotRound k + 1 ≤ N →
    S.leader k ∈ T → ∀ L, IsLeaderBlock U k L →
    ∀ c ∈ U.ids, (U.block c).creator = v → (U.block c).round = S.slotRound k + 1 →
    L ∈ (U.block c).refs ∨
      (built v (S.slotRound k) + timeout (S.slotRound k) ≤ built v (S.slotRound k + 1) ∧
        (L ∈ holds v (built v (S.slotRound k + 1)) → L ∈ (U.block c).refs))
  /-- **The certificate wait, at the wave of three and the rounds that carry the leader wait.** -/
  cert_or_wait : ∀ v ∈ T, ∀ k : ℕ, waits (S.slotRound k) → w (S.kind k) = 3 →
    S.slotRound k + 2 ≤ N → S.leader k ∈ T → ∀ L, IsLeaderBlock U k L →
    ∀ c ∈ U.ids, (U.block c).creator = v → (U.block c).round = S.slotRound k + 2 →
    MahiMahi.Certifies U c L ∨
      (built v (S.slotRound k + 1) + timeout (S.slotRound k + 1)
          ≤ built v (S.slotRound k + 2) ∧
        ∀ b ∈ U.ids, (U.block b).creator ∈ T →
          (U.block b).round = S.slotRound k + 1 →
          b ∈ holds v (built v (S.slotRound k + 2)) →
          L ∈ (U.block b).refs → b ∈ (U.block c).refs)

end Steelhead

end LeanDag
