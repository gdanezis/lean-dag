import LeanDag.BlackMarlin.Model.Decision
import LeanDag.Mysticeti.Liveness
/-!
# Black Marlin — liveness, stated

What the commit rule admits once the DAG is populated and coverage has
taken hold (`black-marlin.md` §8). BML1 says a run of two consecutive
reliable anchors, over three populated rounds, is committed; BML2 says
the full view commits exactly that verdict; BML3 is the paper's Lemma
8, inclusion for reliable authors; BML4 turns a recurring run of two
into recurring commits; BML5 is round-robin supplying that run, at
every committee and fault configuration — a theorem, not an assumption.

None of a timeout, a message delay, a stabilisation time, or a
probability is a hypothesis: this development states liveness above the
structural condition instead (`archive/liveness.md`), replacing the paper's
timing argument rather than transcribing it, and BML5 makes the
recurring run deterministic where the paper's Lemma 11 only bounds an
expectation.

**Why two rounds.** The rule reads support for the anchor at `r + 1`
and support above it at `r + 2`, so BML1 asks population at `r`,
`r + 1`, `r + 2`; coverage already makes every reliable round-`(r+1)`
block reference the round-`r` anchor, so the whole premise is that the
rotation names reliable validators at two consecutive rounds
(`FairRun T 2`).

**Why BML5 is a theorem here and an assumption in the core.** The
core's rotation needs runs of three and states the pigeonhole as prose;
Black Marlin's runs of two are short enough to prove outright — two
cyclically adjacent unreliable anchors would inject the reliable set
into the Byzantine one, giving `2f + 1 ≤ f`.

Statements only; the proofs live in `Proof.lean`.
-/

namespace LeanDag

namespace BlackMarlin

namespace Liveness

variable {Validator : Type*} [Fintype Validator] [DecidableEq Validator]
  [F : Faults Validator] [Rot : Rotation Validator]
  {BlockId : Type*} [DecidableEq BlockId] {Payload : Type*}

/-- **The fairness clause**: the rotation puts `c` consecutive
`T`-anchored rounds arbitrarily far out. The round-indexed counterpart
of the core's `FairRunOn`; unlike there, BML5 discharges this one as a
theorem rather than assuming it. -/
def FairRun (T : Finset Validator) (c : ℕ) : Prop :=
  ∀ r, ∃ r', r ≤ r' ∧ ∀ i, i < c → Rot.anchor (r' + i) ∈ T

/-- **BML1, the commit step.** Two consecutive reliable anchors over
three populated rounds — support for the anchor at the round above it,
and for its linking anchor at the round above that — are committed. -/
def CommitStep (U : BlockUniverse Validator BlockId Payload) : Prop :=
  ∀ (T : Finset Validator) (R r : ℕ),
    -- a quorum of reliable validators
    quorumCard Validator ≤ T.card →
    -- coverage among them from round `R` on, and the anchor is at or above it
    SynchronisedOn U T R → R ≤ r →
    -- the three rounds the rule reads are populated by them
    PopulatedOn U T r → PopulatedOn U T (r + 1) → PopulatedOn U T (r + 2) →
    -- and the rotation names reliable validators at two consecutive rounds
    Rot.anchor r ∈ T → Rot.anchor (r + 1) ∈ T →
    -- then round `r` has a committed anchor
    ∃ L, IsAnchor U r L ∧ Committed U L r

/-- **BML2, the full view commits what the rule commits.** The converse
of BM4 at the view that holds everything, so a universe-level `Committed`
is a verdict some validator can actually reach. -/
def FullViewSound (U : BlockUniverse Validator BlockId Payload) : Prop :=
  ∀ (L : BlockId) (r : ℕ), CommittedIn U (View.full U) L r ↔ Committed U L r

/-- **BML3, inclusion** (the paper's Lemma 8): a reliable validator's
block lies in the causal history of every block two rounds above it,
from coverage and BM2 alone — no clause of the commit rule is
consumed, so this holds whichever anchors the rule admits above. -/
def Inclusion (U : BlockUniverse Validator BlockId Payload) : Prop :=
  ∀ (T : Finset Validator) (R ρ : ℕ) (b c : BlockId),
    -- a quorum of reliable validators, covering from `R` on
    quorumCard Validator ≤ T.card → SynchronisedOn U T R → R ≤ ρ →
    -- the round above `b` is populated by them
    PopulatedOn U T (ρ + 1) →
    -- `b` is a reliable validator's block at round `ρ`
    b ∈ U.ids → (U.block b).round = ρ → (U.block b).creator ∈ T →
    -- and `c` is any block two rounds above it or higher
    c ∈ U.ids → ρ + 2 ≤ (U.block c).round →
    -- then `b` is in what committing `c` delivers
    b ∈ history U c

/-- **What it means for a round to commit in every grown covered DAG.**
The universe is quantified inside, as the core's `CommitsAt` is: fixing
one first would cap how far the rotation may reach. -/
def CommitsAtRound (BlockId : Type*) [DecidableEq BlockId] (Payload : Type*)
    (T : Finset Validator) (R r : ℕ) : Prop :=
  ∀ (U : BlockUniverse Validator BlockId Payload) (N : ℕ),
    (∀ n, R ≤ n → n ≤ N → PopulatedOn U T n) → SynchronisedOn U T R →
    r + 2 ≤ N →
    ∃ L, IsAnchor U r L ∧ Committed U L r

variable (Validator BlockId Payload) in
/-- **BML4, recurrence.** Under a recurring run of two, no round is the
last one a DAG can be grown far enough to commit above. -/
def Recurrence : Prop :=
  ∀ (T : Finset Validator) (R r : ℕ),
    quorumCard Validator ≤ T.card → FairRun T 2 →
    ∃ r', r ≤ r' ∧ R ≤ r' ∧ CommitsAtRound BlockId Payload T R r'

/-- **Round-robin rotation** on `Fin n`: round `r` anchored by `r % n`.
The rotation Black Marlin deploys, written as an instance of the arc's
one-field class. -/
@[reducible]
def roundRobin (n : ℕ) (hn : 0 < n) : Rotation (Fin n) where
  anchor r := ⟨r % n, Nat.mod_lt _ hn⟩

/-- **BML5, the fairness clause is a theorem.** Round-robin puts two
consecutive reliable anchors arbitrarily far out, at every committee and
whichever validators are Byzantine — where the core's counterpart needs
runs of three and stays an assumption, two is short enough to prove. -/
def RotationFair : Prop :=
  ∀ (n : ℕ) (hn : 0 < n) [Faults (Fin n)],
    FairRun (Rot := roundRobin n hn) (Correct : Finset (Fin n)) 2

/-- Liveness of the Black Marlin commit rule, over every fault
configuration, anchor rotation and block universe the model admits, plus
the satisfiability of the one clause it assumes. -/
def Statement : Prop :=
  (∀ (Validator BlockId Payload : Type) [Fintype Validator] [DecidableEq Validator]
    [Faults Validator] [DecidableEq BlockId] [Rotation Validator]
    (U : BlockUniverse Validator BlockId Payload),
    CommitStep U ∧ FullViewSound U ∧ Inclusion U ∧
      Recurrence Validator BlockId Payload) ∧
  RotationFair

end Liveness

end BlackMarlin

end LeanDag
