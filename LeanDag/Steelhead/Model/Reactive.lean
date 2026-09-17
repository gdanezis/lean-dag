import LeanDag.Steelhead.Model.Decision
import LeanDag.Reactive.Basic
/-!
# Steelhead — the reactive discipline

The execution discipline `SynchronisedOn` stands for in SH6a and SH6b, in its reactive form
(`steelhead.md` §6). `ReactivePace` is the core's: time advances with rounds, a validator never
waits past its timeout (`deadline`, a ceiling where the timed model puts a floor), and at the
round above a reliable leader a block either votes or its builder waited the timeout out and
votes for any leader block it holds (`vote_or_wait`).

Steelhead adds one clause, and only where the wave leaves no room for the vote to travel. At a
wave of four rounds or more the vote round sits two rounds or more above the candidate, so a
quorum of votes reaches the certifiers through the DAG and nothing further is asked of the
schedule. At the wave of three the certify round is the vote round's successor, and a certifier
must reference the votes themselves: `cert_or_wait` is that wait, stated only at wave three.

**Definitions only**, as in the other model files.
-/

namespace LeanDag

namespace Steelhead

variable {Validator : Type} [Fintype Validator] [DecidableEq Validator]
variable [F : Faults Validator]
variable {BlockId : Type} [LinearOrder BlockId] {Payload : Type}
variable [S : Slots Validator]

/-- **Steelhead's reactive schedule** at the wavelength function `w`: the core's reactive pace,
plus the certificate wait at the wave of three. At two rounds above a reliable leader, any
`T`-authored block either already certifies, or its builder waited the full timeout and
references every reliable vote it holds. Above wave three the clause says nothing: reachability
carries the votes, so the discipline is the core's own. -/
structure ReactiveS (U : BlockUniverse Validator BlockId Payload) (T : Finset Validator) (N : ℕ)
    (w : ℕ → ℕ) extends ReactivePace U T N where
  /-- **The certificate wait, at the wave of three.** -/
  cert_or_wait : ∀ v ∈ T, ∀ k : ℕ, w (S.slotRound k) = 3 → S.slotRound k + 2 ≤ N →
    S.leader k ∈ T → ∀ L, IsLeaderBlock U k L →
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
