import LeanDag.MahiMahi.Model.Unpredictable
import LeanDag.Mysticeti.Quantitative
/-!
# Partial synchrony, recovered — statement

Two claims keeping the arc usable under partial synchrony
(`mahi-mahi.md` §7): MM5a derives a committed candidate from
`SynchronisedOn` at one round only, where the core's L4 needs two; MM5b
derives the unpredictable-leader clause itself from the core's
`FairWithin` under synchrony and population through the horizon.

Statements only; the proofs live in `Proof.lean`.
-/

namespace LeanDag

namespace MahiMahi

namespace Synchrony

variable {Validator : Type} [Fintype Validator] [DecidableEq Validator]
  [F : Faults Validator] {BlockId : Type} [LinearOrder BlockId] {Payload : Type}
  [S : Slots Validator]

/-- **MM5a, a reliable leader is good under coverage at one round.** -/
def GoodOfSynchrony (U : BlockUniverse Validator BlockId Payload) (w : ℕ) : Prop :=
  ∀ (T : Finset Validator) (R k : ℕ),
    -- four rounds: the voting round is at or above r + 2, where every block
    -- reaches a candidate referenced by every reliable round-(r+1) block
    4 ≤ w →
    -- T is a reliable set: correct, and a quorum
    T ⊆ (Correct : Finset Validator) → quorumCard Validator ≤ T.card →
    -- the core's coverage hypothesis, in force at the slot's round
    SynchronisedOn U T R → R ≤ S.slotRound k →
    -- T populates the proposal round, the round above it, and the decision round
    PopulatedOn U T (S.slotRound k) → PopulatedOn U T (S.slotRound k + 1) →
    PopulatedOn U T ((mahiMahiAnchored Validator BlockId Payload w).decisionRound k) →
    -- the slot's leader is reliable
    S.leader k ∈ T →
    -- then the leader is a committed candidate of its round
    S.leader k ∈ good U w k

/-- **MM5b, the clause is derived under synchrony.** -/
def ClauseOfSynchrony (U : BlockUniverse Validator BlockId Payload) (w : ℕ) : Prop :=
  ∀ (T : Finset Validator) (c N : ℕ),
    4 ≤ w →
    T ⊆ (Correct : Finset Validator) → quorumCard Validator ≤ T.card →
    -- coverage from round 0 and population through the horizon
    SynchronisedOn U T 0 → (∀ n, n ≤ N → PopulatedOn U T n) →
    -- the core's rated fairness: a T-leader in every window of c slots
    FairWithin T c →
    -- then the single-hit clause holds with the same window
    UnpredictableWithin U w c N

/-- Partial synchrony recovered, over every fault configuration, schedule,
block universe and wave length the model admits. -/
def Statement : Prop :=
  ∀ (Validator BlockId Payload : Type) [Fintype Validator] [DecidableEq Validator]
    [Faults Validator] [LinearOrder BlockId] [Slots Validator]
    (U : BlockUniverse Validator BlockId Payload) (w : ℕ),
    GoodOfSynchrony U w ∧ ClauseOfSynchrony U w

end Synchrony

end MahiMahi

end LeanDag
