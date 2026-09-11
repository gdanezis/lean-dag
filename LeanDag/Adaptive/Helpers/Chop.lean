import LeanDag.Barnacle.Chop
import LeanDag.Properties.Compose
/-!
# The joiner, at a configuration

I5 for the segmented arc (`adaptive-leaders.md` §9). A validator that
joins from a universe pruned below round `G` renumbers its slots from
`C.cum G`, and runs the same score on what it holds. Two halves, as
before:

* **the verdicts** — across the cut, the joiner's derivation and the
  network's agree on every shared slot. Nothing about adaptivity enters:
  `Config.rebases_chop` makes the cut a truncation at the configuration's
  own schedule, and cross-cut agreement holds at any schedule.
* **the schedule** — `HorizonStable` is what a score owes: from views
  agreeing above the cut it returns the same configuration the network
  installs, chopped. A score reading a bounded window of rounds below its
  anchor has it whenever the cut lies below that window.

The fixpoint arc stated the schedule half over a `pick` reading the whole
verdict function, and re-indexed that function. Here the object being
re-indexed is the configuration, and `Config.chop` is the re-indexing.
-/

namespace LeanDag

namespace Adaptive

open Barnacle Properties

variable {Validator : Type} [Fintype Validator] [DecidableEq Validator]
variable {BlockId : Type} [DecidableEq BlockId] {Payload : Type}

/-! ## The verdict half -/

section Verdicts

variable {R : DagRule Validator BlockId Payload}

/-- **Across the cut the verdicts agree.** The joiner, deriving at the
chopped configuration's schedule on any view of the truncation, and the
network, deriving at the configuration's own, give one verdict to every
shared slot. -/
theorem joiner_decided_agree (ha : Agree R) (hb : Banded R)
    {U U' : R.Universe} {G : ℕ} {C : Config Validator}
    (ht : Truncates R U U' C.sched (C.chop G).sched G (C.cum G))
    {V : R.View U} {V' : R.View U'} (hv : ViewAgreeAbove R V V' G)
    {W : R.View U'} {k : ℕ} {w v : Option BlockId}
    (hW : R.Decided (C.chop G).sched W k w)
    (hV : R.Decided C.sched V (C.cum G + k) v) : w = v :=
  decided_agree_rebased ha hb (Rebased.of_truncates ht) hv
    (by have := ht.slotRound k; omega) hW hV

end Verdicts

/-! ## The schedule half

`HorizonStable` is stated on the bare score-shaped function over a
`DagRule` rather than on `Score R` for a `BaseRule`, for the reason the
fixpoint arc stated it on a bare `pick`: the cut re-indexes, and a
statement tied to the interface a score is installed through would have
to be transported across the re-indexing. An `Adaptive.Score R` for a
`BaseRule R` has exactly this shape at `R.toDagRule`. -/

section Schedule

variable {R : DagRule Validator BlockId Payload}

/-- **Horizon-stability.** A score is horizon-stable at `G` when, from
two views agreeing above `G`, it installs the same configuration on the
cut that it installs on the whole — re-indexed by `Config.chop`. This is
the condition that rules out scores incompatible with pruning, and a
score reading a bounded window of rounds below its anchor meets it once
the cut lies below that window. -/
def HorizonStable
    (score : (U : R.Universe) → R.View U → Config Validator → Config Validator)
    (G : ℕ) : Prop :=
  ∀ (U U' : R.Universe) (V : R.View U) (V' : R.View U'), ViewAgreeAbove R V V' G →
    ∀ C : Config Validator, score U' V' (C.chop G) = (score U V C).chop G

/-- **The joiner installs the network's configuration.** Under a
horizon-stable score, what a joiner computes from its own truncated view
is exactly what the network installed, with the pruned rounds dropped —
so the two run the same leaders on every round both have. -/
theorem joiner_config_agree
    {score : (U : R.Universe) → R.View U → Config Validator → Config Validator}
    {G : ℕ} (hs : HorizonStable score G)
    {U U' : R.Universe} {V : R.View U} {V' : R.View U'}
    (hv : ViewAgreeAbove R V V' G) (C : Config Validator) :
    score U' V' (C.chop G) = (score U V C).chop G :=
  hs U U' V V' hv C

/-- And so the joiner's schedule is the network's, seen from the cut's
own origin. -/
theorem joiner_leader_agree
    {score : (U : R.Universe) → R.View U → Config Validator → Config Validator}
    {G : ℕ} (hs : HorizonStable score G)
    {U U' : R.Universe} {V : R.View U} {V' : R.View U'}
    (hv : ViewAgreeAbove R V V' G) (C : Config Validator) (k : ℕ) :
    (score U' V' (C.chop G)).sched.leader k
      = (score U V C).sched.leader ((score U V C).cum G + k) := by
  rw [joiner_config_agree hs hv C]
  exact ((score U V C).rebases_chop G).leader k

/-- The score that installs what it was given is horizon-stable at every
cut: what it was given was already chopped. `Adaptive.Score.const` is
this one, and AL15's conservativity is its consequence. -/
theorem horizonStable_const (G : ℕ) :
    HorizonStable (R := R) (fun _ _ C => C) G := fun _ _ _ _ _ _ => rfl

end Schedule

end Adaptive

end LeanDag
