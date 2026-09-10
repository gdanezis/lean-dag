import LeanDag.Adaptive.Frame
import LeanDag.Adaptive.ScheduleLive
import LeanDag.Barnacle.Model.Heads
/-!
# Barnacle's fairness, read as the adaptive arc's

The run over a varying frame is `Adaptive/Frame.lean`, which names no
second mechanism. What is left here is the one place the two arcs meet:
the rotation Barnacle schedules has the stretch of reliable leaders the
adaptive arc asks of every epoch.
-/

namespace LeanDag
namespace Integration

open Properties Adaptive

variable {Validator : Type} [Fintype Validator] [DecidableEq Validator]
variable {BlockId : Type} [DecidableEq BlockId] {Payload : Type}
variable {R : DagRule Validator BlockId Payload}
variable [S : Slots Validator]


/-- **Barnacle's fairness gives the adaptive arc's, at the rotation.**
`HeadsRun` says the rotation has a stretch of `c` reliable leaders within
`c₀` of every round; `PlacesRuns` asks for a stretch of `c` reliable
slots inside every epoch. At one leader per round the two are the same
stretch, and the epoch has room for it as soon as `c₀ ≤ W`.

This is what makes the composition no less live than the schedule it
starts from: the clause the adaptive arc prices is one Barnacle already
pays. -/
theorem placesRuns_const_of_headsRun {W : ℕ} (hW : 0 < W)
    (hinj : Function.Injective S.slotRound)
    {getLeader : ℕ → Validator} (hleader : ∀ κ, S.leader κ = getLeader κ)
    {T : Finset Validator} {c c₀ : ℕ} (hc₀ : c₀ ≤ W)
    (hhr : Barnacle.HeadsRun getLeader T c c₀) :
    PlacesRuns (Policy.const (R := R) W hW hinj) T c := by
  intro U V v e
  obtain ⟨ρ, h1, h2, h3⟩ := hhr (W * (e + 1))
  refine ⟨ρ, ?_, ?_, fun i hi => ?_⟩
  · show W * (e + 1) ≤ ρ
    exact h1
  · show ρ + c ≤ W * (e + 2)
    have he : W * (e + 2) = W * (e + 1) + W := by
      have hee : e + 2 = (e + 1) + 1 := by omega
      rw [hee, Nat.mul_succ]
    omega
  · rw [Policy.const_pick, hleader]
    exact h3 i hi

/-- **Barnacle's fairness gives the adaptive schedule's, at the
rotation.** `HeadsRun` places a stretch of `c` reliable heads within `c₀`
of every round; a schedule at one leader a round has the head of round
`r` at slot `r`, so the stretch is a stretch of slots, and it falls
inside epoch `e + 1` as soon as that epoch is `c₀` slots long.

This is the degenerate case of an emitted schedule: where the score has
nothing to read the policy returns the rotation, and the rotation's own
fairness is what liveness then reads. -/
theorem placesRunsIn_ofFixed_of_headsRun {E : Frame} {M : ℕ}
    (hM : ∀ r, (constFrame 1 Nat.one_pos).width r ≤ M)
    {getLeader : ℕ → Validator}
    (hk : ∀ r i j, i < (constFrame 1 Nat.one_pos).width r →
      j < (constFrame 1 Nat.one_pos).width r →
      getLeader (r + i) = getLeader (r + j) → i = j)
    {U : R.Universe} {V : R.View U} {T : Finset Validator} {c c₀ : ℕ}
    (hc₀ : ∀ e, c₀ ≤ E.width e) (hhr : Barnacle.HeadsRun getLeader T c c₀) :
    Adaptive.PlacesRunsIn
      (Adaptive.Schedule.ofFixed (R := R) E (constFrame 1 Nat.one_pos) M hM
        (fun r i => getLeader (r + i)) hk) U V T c := by
  intro v e
  obtain ⟨ρ, h1, h2, h3⟩ := hhr (E.cum (e + 1))
  refine ⟨ρ, h1, ?_, fun i hi => ?_⟩
  · show ρ + c ≤ E.cum (e + 2)
    have he : E.cum (e + 2) = E.cum (e + 1) + E.width (e + 1) := by
      have : e + 2 = (e + 1) + 1 := by omega
      rw [this, Frame.cum_succ]
    have := hc₀ (e + 1)
    omega
  · show getLeader ((constFrame 1 Nat.one_pos).roundOf (ρ + i)
        + ((ρ + i) - (constFrame 1 Nat.one_pos).cum
            ((constFrame 1 Nat.one_pos).roundOf (ρ + i)))) ∈ T
    rw [constFrame_roundOf, constFrame_cum]
    simpa using h3 i hi

end Integration

end LeanDag
