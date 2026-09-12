import LeanDag.Adaptive.Model.Segment
import LeanDag.Barnacle.Model.Live
/-!
# The reputation score, as an update rule

Hammerhead installs a configuration chosen from the committed anchor's
causal history (`adaptive-leaders.md` §9): validators that voted for
recent leaders gain slots, validators that did not lose them, and the
shape of the schedule — how many slots each round has, how long until
the next reconfiguration — is left alone.

A `Score` reads the anchor's history **as a view**, which is the shape
`Barnacle.observed` uses and the reason no separate clause is needed to
say the score reads nothing else: `BaseRule.historyView` is pinned to
`historyFrom` by `BaseRule.Laws.historyView_ids`, and BN2 says any two
views holding the anchor hold its history whole and restrict to it
identically. So a score's reading is agreed across validators by
construction rather than by hypothesis.

What a score does owe is `Score.Keeps`: it moves the leaders and leaves
the widths and the interval where they were. That one clause carries
`UpdBounded`, since `Config.InBounds` mentions only those two.

This file is not under `Model/`, for the reason `Barnacle/Aimd/Rule.lean`
is not: the rule is a definition, and the facts about it are theorems.
-/

namespace LeanDag

namespace Adaptive

open Barnacle

variable {Validator : Type} [Fintype Validator] [DecidableEq Validator]
variable {BlockId : Type} [DecidableEq BlockId] {Payload : Type}

/-- **A reputation score**: from the anchor's causal history read as a
view, the verdicts of the span just closed, and the configuration in
force, the configuration to install.

The verdict argument is what makes this HammerHead's rule rather than a
weaker one. `UPDATESCHEDULE` scores the validators whose blocks voted for
the leaders the epoch just *committed*, so the score must see the
committed sequence and not only the DAG. It may, and costs no hypothesis:
a run hands over `Barnacle.spanVdct`, and AL13's induction shows the two
validators' copies are one function before either applies the rule. What
a score may never do is derive verdicts from its own view, which would be
subjective and would break `Anchored`. -/
def Score (R : BaseRule Validator BlockId Payload) : Type :=
  (U : R.Universe) → R.View U → (ℕ → Option BlockId) → Config Validator → Config Validator

variable {R : BaseRule Validator BlockId Payload}

/-- **What a score owes.** It changes who leads and leaves the shape
alone: the same slots in every round, and the same interval to the next
reconfiguration. Hammerhead's rule qualifies — it swaps validators
between schedule positions — and an Aimd-style rule, which moves the
widths, does not. -/
def Score.Keeps (score : Score R) : Prop :=
  ∀ (U : R.Universe) (V : R.View U) (v : ℕ → Option BlockId) (C : Config Validator),
    (score U V v C).slotsAt = C.slotsAt ∧ (score U V v C).interval = C.interval

/-- **The score as an update rule.** At an anchor the universe holds, the
next configuration is the score's on the anchor's history view;
elsewhere the configuration stands. The view a validator happens to have
is not read, which is `Anchored`, and the anchor is in the universe at
every step a run takes, by `anchor_commits` and `CommitsCandidate`. -/
def rule (score : Score R) : UpdateRule R :=
  fun C b U _V v A =>
    if hA : A ∈ R.ids U then (score U (R.historyView U A hA) v C, b) else (C, b)

/-- **A permuting score**: relabel who leads by `σ`, leaving the widths
and the interval where they were. The simplest reassignment there is,
and the case D22 takes first — `Barnacle.headsRun_perm` says a permuted
schedule keeps runs of heads at the same gap, so liveness follows for
the whole family at once. A score that reads the anchor's history and
chooses which permutation to apply is adaptive and still of this
family. -/
def Score.permute (σ : Equiv.Perm Validator) : Score R :=
  fun _ _ _ C =>
    { slotsAt := C.slotsAt
      slotsAt_pos := C.slotsAt_pos
      lead := fun r i => σ (C.lead r i)
      keyed := fun r i j hi hj h => C.keyed r i j hi hj (σ.injective h)
      interval := C.interval }

@[simp] theorem Score.permute_slotsAt (σ : Equiv.Perm Validator) (U : R.Universe)
    (V : R.View U) (v : ℕ → Option BlockId) (C : Config Validator) :
    (Score.permute (R := R) σ U V v C).slotsAt = C.slotsAt := rfl

@[simp] theorem Score.permute_interval (σ : Equiv.Perm Validator) (U : R.Universe)
    (V : R.View U) (v : ℕ → Option BlockId) (C : Config Validator) :
    (Score.permute (R := R) σ U V v C).interval = C.interval := rfl

/-- The heads of a permuted configuration are the permuted heads. -/
@[simp] theorem Score.permute_head (σ : Equiv.Perm Validator) (U : R.Universe)
    (V : R.View U) (v : ℕ → Option BlockId) (C : Config Validator) :
    (Score.permute (R := R) σ U V v C).head = fun ρ => σ (C.head ρ) := rfl

/-! ## The conservativity anchor -/

/-- The constant score: install the configuration in force. -/
def Score.const (R : BaseRule Validator BlockId Payload) : Score R := fun _ _ _ C => C

end Adaptive

end LeanDag
