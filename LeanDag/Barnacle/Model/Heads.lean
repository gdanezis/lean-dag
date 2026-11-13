import LeanDag.Properties.Commit
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

/-- **The descent laws** of a live rule, at its own gap: `Properties.Descent`
with goodness read under the schedule it is about, `slack` the number of
validators the good set may miss. -/
structure LiveRule.Descent (R : LiveRule Validator BlockId Payload) (slack : ℕ) : Prop where
  /-- **A4, direct commits.** On a DAG good under `S`, some `slack`-missing
  set of validators commits every slot of `S` it leads whose wave fits under
  `N`, on any view caught up to `N`. -/
  goodLeaders : ∀ (S : Slots Validator) (U : R.Universe) (Rnd N : ℕ), R.Good S U Rnd N →
    ∃ T : Finset Validator, Fintype.card Validator ≤ T.card + slack ∧
      ∀ (V : R.View U) (κ : ℕ), R.toBaseRule.CoversUpto U V N →
        Rnd ≤ S.slotRound κ → S.slotRound κ + R.waveLength ≤ N →
        S.leader κ ∈ T → ∃ L, R.Decided S V κ (some L)
  /-- **A3, the indirect rule**, at the rule's wave. -/
  indirect : ∀ (S : Slots Validator) {U : R.Universe} (V : R.View U) (i j : ℕ) (A : BlockId),
    S.slotRound i + R.waveLength ≤ S.slotRound j → R.Decided S V j (some A) →
    (∀ i', i < i' → i' < j → S.slotRound i + R.waveLength ≤ S.slotRound i' →
      R.Decided S V i' none) →
    ∃ v, R.Decided S V i v

/-- **A run of heads**: from every round `r`, within `c₀` rounds, `g`
consecutive rounds whose heads — first slots, led by `head` of the
round — are led by members of `T`. A configuration's own head function
is `Config.head`. -/
def HeadsRun (head : ℕ → Validator) (T : Finset Validator) (g c₀ : ℕ) : Prop :=
  ∀ r, ∃ ρ, r ≤ ρ ∧ ρ + g ≤ r + c₀ ∧ ∀ i, i < g → head (ρ + i) ∈ T

/-- **Slots led by a decisive set are decided**: on a good DAG, a set `T`
missing at most `slack` validators commits the slots it leads, and a set
`D ⊇ T` missing at most `fb` decides the slots it leads, on any view caught
up to the horizon. -/
def LiveRule.Decisive (R : LiveRule Validator BlockId Payload) (slack fb : ℕ) : Prop :=
  ∀ (S : Slots Validator) (U : R.Universe) (Rnd N : ℕ), R.Good S U Rnd N →
    ∃ T D : Finset Validator, T ⊆ D ∧ Fintype.card Validator ≤ T.card + slack ∧
      Fintype.card Validator ≤ D.card + fb ∧
      (∀ (V : R.View U) (κ : ℕ), R.toBaseRule.CoversUpto U V N →
        Rnd ≤ S.slotRound κ → S.slotRound κ + R.waveLength ≤ N → S.leader κ ∈ T →
        ∃ L, R.Decided S V κ (some L)) ∧
      (∀ (V : R.View U) (κ : ℕ), R.toBaseRule.CoversUpto U V N →
        Rnd ≤ S.slotRound κ → S.slotRound κ + R.waveLength ≤ N → S.leader κ ∈ D →
        ∃ v, R.Decided S V κ v)

/-- **A run of decided rounds ending at a committing head**: from every
round `r`, within `c₀` rounds, `g` consecutive rounds from `ρ` whose first
`g − 1` rounds hold only `D`-led slots and whose last round's head is
`T`-led. -/
def SkipRun (C : Config Validator) (T D : Finset Validator) (g c₀ : ℕ) : Prop :=
  ∀ r, ∃ ρ, r ≤ ρ ∧ ρ + g ≤ r + c₀ ∧
    (∀ κ, ρ ≤ C.sched.slotRound κ → C.sched.slotRound κ + 1 < ρ + g → C.sched.leader κ ∈ D) ∧
    C.head (ρ + g - 1) ∈ T

end Barnacle

end LeanDag
