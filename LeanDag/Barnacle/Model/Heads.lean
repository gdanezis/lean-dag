import LeanDag.Barnacle.Model.Live
/-!
# Barnacle: the descent laws and runs of heads

What a base protocol owes for liveness under multiple leaders per round
(`barnacle.md` §8). The development's own run-of-consecutive-slots route
has no instance under the paper's rotation at several leaders and few
validators, so the argument instead runs on *heads*, first slots of
consecutive rounds. `LiveRule.Descent` packages the two facts this
needs — A4's direct-commit clause and A3's indirect rule — and
`HeadsRun` is the schedule clause a run of heads satisfies; round-robin
meets it by pigeonhole (`Heads/Statement.lean`).

**Trusted core of the arc: definitions only.**
-/

namespace LeanDag

namespace Barnacle

variable {Validator : Type} [Fintype Validator] [DecidableEq Validator]
variable {BlockId : Type} [DecidableEq BlockId] {Payload : Type}

/-- **The descent laws** of a live rule, with `slack` the number of
validators the good set may miss. -/
structure LiveRule.Descent (R : LiveRule Validator BlockId Payload) (slack : ℕ) : Prop where
  /-- **A4, direct commits.** On a DAG good from `Rnd` to `N`, some
  `slack`-missing set of validators commits every slot it leads from
  `Rnd` whose wave fits under `N`, on any view caught up to `N`. -/
  goodLeaders : ∀ (U : R.Universe) (Rnd N : ℕ), R.Good U Rnd N →
    ∃ T : Finset Validator, Fintype.card Validator ≤ T.card + slack ∧
      ∀ (S : Slots Validator) (V : R.View U) (κ : ℕ), R.toBaseRule.CoversUpto U V N →
        Rnd ≤ S.slotRound κ → S.slotRound κ + R.waveLength ≤ N →
        S.leader κ ∈ T → ∃ L, R.Decided S V κ (some L)
  /-- **A3, the indirect rule.** A committed slot a full wave above `i`,
  with every full-wave-eligible slot between them skipped, decides `i`. -/
  indirect : ∀ (S : Slots Validator) {U : R.Universe} (V : R.View U) (i j : ℕ) (A : BlockId),
    S.slotRound i + R.waveLength ≤ S.slotRound j → R.Decided S V j (some A) →
    (∀ i', i < i' → i' < j → S.slotRound i + R.waveLength ≤ S.slotRound i' →
      R.Decided S V i' none) →
    ∃ v, R.Decided S V i v

/-- **A run of heads**: from every round `r`, within `c₀` rounds, `g`
consecutive rounds whose heads — first slots, led by `getLeader` of the
round — are led by members of `T`. -/
def HeadsRun (getLeader : ℕ → Validator) (T : Finset Validator) (g c₀ : ℕ) : Prop :=
  ∀ r, ∃ ρ, r ≤ ρ ∧ ρ + g ≤ r + c₀ ∧ ∀ i, i < g → getLeader (ρ + i) ∈ T

end Barnacle

end LeanDag
