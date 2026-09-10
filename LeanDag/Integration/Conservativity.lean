import LeanDag.Integration.CompRun
import LeanDag.Barnacle.Helpers.Frame
/-!
# Conservativity of the composition

`Barnacle/Conservativity` says the mechanism costs nothing where it does
nothing: under the update rule that returns the count it was given, the
count never moves and every verdict is a verdict of the base one-leader
schedule.

The composition adds a second way to do nothing — the assignment may be
the base leader function rather than a reassignment — and the two
together say the composed run *is* the base protocol's. `Sched_eq_frame`
is what makes that an identity rather than a comparison: Barnacle's
schedule at one leader a round is a one-slot frame's own schedule.

**Trusted core: nothing. Every declaration is a theorem.**
-/

namespace LeanDag
namespace Integration

open Barnacle Properties

variable {Validator : Type} [Fintype Validator] [DecidableEq Validator]
variable {BlockId : Type} [DecidableEq BlockId] {Payload : Type}
variable {R : Properties.DagRule Validator BlockId Payload} {P : Params}
variable {W : ℕ} {upd : ℕ → ℕ → (U : R.Universe) → R.View U → BlockId → ℕ × ℕ}
variable {pick : (U : R.Universe) → R.View U → (ℕ → Option BlockId) → ℕ → Validator}
variable {U : R.Universe} {V : R.View U} {K H : ℕ}

namespace CompRun

/-- **BN6a at a composed run: the count never moves.** Under the rule
that returns the count and back-off it was given, every configuration the
run determines is the initial one. -/
theorem const_count
    (hconst : ∀ (m b : ℕ) (U' : R.Universe) (V' : R.View U') (A : BlockId),
      upd m b U' V' A = (m, b))
    (Rn : CompRun (R := R) W P upd U V K) :
    ∀ k, k ≤ K → Rn.count k = 1 ∧ Rn.backoff k = 0 := by
  intro k
  induction k with
  | zero => intro _; exact ⟨Rn.init.2.1, Rn.init.2.2⟩
  | succ j ih =>
      intro hj
      obtain ⟨hc, hb⟩ := ih (by omega)
      obtain ⟨⟨A, hA⟩, -⟩ := Rn.anchor_commits j (by omega)
      have h := Rn.update j (by omega) A hA
      rw [hconst, Prod.mk.injEq] at h
      exact ⟨by rw [h.1, hc], by rw [h.2, hb]⟩

/-- **And so every round the run reaches is one leader wide.** -/
theorem const_width
    (hconst : ∀ (m b : ℕ) (U' : R.Universe) (V' : R.View U') (A : BlockId),
      upd m b U' V' A = (m, b))
    (Rn : CompRun (R := R) W P upd U V K) {r : ℕ} (hr : r ≤ Rn.start K) (hK : 0 < K) :
    Rn.F.width r = 1 := by
  rcases Nat.eq_zero_or_pos r with rfl | h0
  · exact Rn.cnt_zero
  · obtain ⟨j, hj, hlo, hhi⟩ := Rn.exists_cfg (k := K - 1) (by omega) h0
      (by rw [show K - 1 + 1 = K by omega]; exact hr)
    rw [Rn.cnt_eq j (by omega) r hlo hhi, (const_count hconst Rn j (by omega)).1]

end CompRun

namespace Composed

/-- **BN6b at a composed run: the verdicts are the base protocol's.**
Where the count never moves and the assignment is the base leader
function, the composed run's schedule below the round it has reached is
`Sched getLeader 1` — the one-leader schedule the base development runs
on — and `closed` decides the slot against it.

`DecidedFrameBelow` is what carries it: the verdict is settled by every
frame and assignment agreeing below the window's end, and the one-slot
frame at the base leaders is one of them. -/
theorem const_decided
    (hconst : ∀ (m b : ℕ) (U' : R.Universe) (V' : R.View U') (A : BlockId),
      upd m b U' V' A = (m, b))
    (Rn : Composed (R := R) W P pick upd U V K H) (hK : 0 < K)
    {getLeader : ℕ → Validator} {w : ℕ} (hkey : Keyed getLeader w) (hmax : 1 ≤ w)
    (hasg : ∀ r i, i < Rn.F.width r → Rn.asg r i = getLeader (r + i))
    {r i : ℕ} (hi : i < Rn.F.width r) (hep : epochOf W (Rn.F.index r i) < H)
    (hB : Rn.F.roundOf (W * (epochOf W (Rn.F.index r i) + 2)) ≤ Rn.start K) :
    R.Decided (Sched getLeader hkey 1 Nat.one_pos hmax) V
      (Rn.F.index r i) (Rn.vdct (Rn.F.index r i)) := by
  rw [Sched_eq_frame getLeader hkey 1 Nat.one_pos hmax]
  exact Rn.closed r i hi hep (constFrame 1 Nat.one_pos) (fun r' i' => getLeader (r' + i'))
    (keyed_frame hkey Nat.one_pos hmax)
    (fun r' hr' => (CompRun.const_width hconst Rn.toCompRun (by omega) hK).symm)
    (fun r' i' hr' hi' => (hasg r' i' hi').symm)

end Composed

end Integration

end LeanDag
