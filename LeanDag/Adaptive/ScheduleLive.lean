import LeanDag.Adaptive.ScheduleRun
/-!
# Liveness of the adaptive schedule

A slot led by a reliable validator commits, and every epoch a run has
closed carries a stretch of them. Neither result reads the widths: the
verdict is taken at the run's own schedule whatever the widths do, so a
width may change anywhere inside an epoch, and the epoch's own length is
the policy's too.

`PlacesRunsIn` is `Adaptive.PlacesRuns` at an epoch the policy sized:
the stretch of `c` reliable slots must fall inside the epoch the same
policy chose the length of.

**Trusted core: `PlacesRunsIn` is a definition.**
-/

namespace LeanDag
namespace Adaptive

open Properties

variable {Validator : Type} [Fintype Validator] [DecidableEq Validator]
variable {BlockId : Type} [DecidableEq BlockId] {Payload : Type}
variable {R : DagRule Validator BlockId Payload}
variable {P : Schedule R} {U : R.Universe} {V : R.View U} {H : ℕ}

namespace ScheduleRun

/-- The schedule a run runs on: its own frame at its own assignment. -/
noncomputable def sched (Rn : ScheduleRun P U V H) : Slots Validator :=
  (P.frameOf Rn.vdct).toSlots (P.asgOf Rn.vdct U V) (P.asgOf_keyed Rn.vdct U V)

/-- **The leader of a slot is the policy's at that slot.** `asgOf` says
it of a round and a position; this says it of a slot. -/
theorem sched_leader (Rn : ScheduleRun P U V H) (g : ℕ) :
    Rn.sched.leader g = P.pick U V Rn.vdct g := by
  show P.asgOf Rn.vdct U V ((P.frameOf Rn.vdct).roundOf g)
      (g - (P.frameOf Rn.vdct).cum ((P.frameOf Rn.vdct).roundOf g)) = _
  rw [Schedule.asgOf, (P.frameOf Rn.vdct).index_roundOf_self g]

/-- **A run's schedule decides its own verdicts**, at every slot of an
epoch it has closed. -/
theorem decided_at (Rn : ScheduleRun P U V H) (g : ℕ)
    (hg : (P.epochFrame Rn.vdct).roundOf g < H) :
    R.Decided Rn.sched V g (Rn.vdct g) :=
  Rn.toFrameRun.decided_self g hg

/-- **A reliable leader's slot commits.** The rule supplies the commit
and `Agree` identifies it with the run's own verdict, which the run has
because the slot lies in an epoch it has closed. -/
theorem commits {Live : Slots Validator → ∀ {U : R.Universe}, R.View U →
      Finset Validator → ℕ → ℕ → Prop}
    (hlc : LeaderCommits R Live) (hag : Agree R)
    (Rn : ScheduleRun P U V H) {T : Finset Validator} {lo B g : ℕ}
    (hlive : Live Rn.sched V T lo B) (hlo : lo ≤ g) (hB : g < B)
    (hg : (P.epochFrame Rn.vdct).roundOf g < H) (hlead : Rn.sched.leader g ∈ T) :
    ∃ L, Rn.vdct g = some L := by
  obtain ⟨L, hL⟩ := hlc Rn.sched V T lo B hlive g hlo hB hlead
  exact ⟨L, hag _ V V g _ _ (Rn.decided_at g hg) hL.toDecided⟩

end ScheduleRun

/-- **The fairness clause, at an epoch the policy sized.** Every epoch
past the first holds `c` consecutive slots led by `T`. It is
`Adaptive.PlacesRuns` with the epoch's extent read from the schedule
rather than from a constant. -/
def PlacesRunsIn (P : Schedule R) (U : R.Universe) (V : R.View U)
    (T : Finset Validator) (c : ℕ) : Prop :=
  ∀ (v : ℕ → Option BlockId) (e : ℕ),
    ∃ b, (P.epochFrame v).cum (e + 1) ≤ b ∧ b + c ≤ (P.epochFrame v).cum (e + 2) ∧
      ∀ i, i < c → P.pick U V v (b + i) ∈ T

namespace ScheduleRun

/-- **Every epoch a run has closed carries `c` consecutive commits.**
Nothing about the widths enters: a configuration of the schedule may
change a width anywhere inside the epoch, since the verdict is read at
the run's own schedule whatever the widths do. -/
theorem commits_in_epoch {Live : Slots Validator → ∀ {U : R.Universe}, R.View U →
      Finset Validator → ℕ → ℕ → Prop}
    (hlc : LeaderCommits R Live) (hag : Agree R)
    (Rn : ScheduleRun P U V H) {T : Finset Validator} {c : ℕ}
    (hruns : PlacesRunsIn P U V T c) (e : ℕ) (heH : e + 2 ≤ H)
    (hlive : Live Rn.sched V T ((P.epochFrame Rn.vdct).cum 1)
      ((P.epochFrame Rn.vdct).cum (e + 2))) :
    ∃ b, (P.epochFrame Rn.vdct).cum (e + 1) ≤ b ∧
      b + c ≤ (P.epochFrame Rn.vdct).cum (e + 2) ∧
      ∀ i, i < c → ∃ L, Rn.vdct (b + i) = some L := by
  obtain ⟨b, hb1, hb2, hbT⟩ := hruns Rn.vdct e
  refine ⟨b, hb1, hb2, fun i hi => ?_⟩
  have hlt : b + i < (P.epochFrame Rn.vdct).cum (e + 2) := by omega
  have hmono : (P.epochFrame Rn.vdct).cum 1 ≤ (P.epochFrame Rn.vdct).cum (e + 1) :=
    (P.epochFrame Rn.vdct).cum_mono (by omega)
  have hlo : (P.epochFrame Rn.vdct).cum 1 ≤ b + i := by omega
  refine Rn.commits hlc hag hlive hlo hlt ?_ ?_
  · exact lt_of_lt_of_le (roundOf_lt_iff.mpr hlt) (by omega)
  · rw [Rn.sched_leader]; exact hbT i hi

/-- **The descent applies at a schedule's own frame.** The spanning
clause asks the widths to be bounded, which `widthOf_le` is, and not to
be equal. -/
theorem descends (Rn : ScheduleRun P U V H) {wave c : ℕ}
    (hind : Properties.Indirect R (fun sr i j => sr i + wave + 1 ≤ sr j))
    (hc : 0 < c) (hspan : P.maxWidth * (wave + 1) ≤ c)
    (a : ℕ → Validator)
    (h : ∀ k₁ k₂, Rn.sched.slotRound k₁ = Rn.sched.slotRound k₂ → a k₁ = a k₂ → k₁ = k₂) :
    Properties.Descends R (slotsOfKeyed (S := Rn.sched) a h) c :=
  descends_frame hind hc (P.widthOf_le Rn.vdct) hspan a h

end ScheduleRun

end Adaptive

end LeanDag
