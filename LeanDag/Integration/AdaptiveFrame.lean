import LeanDag.Properties.Derived.Frame
import LeanDag.Adaptive.Basic
/-!
# The adaptive policy over a frame whose widths vary

`Adaptive/Run.lean` states a run over a fixed `Slots`, where a mechanism
may reassign the leaders but not the rounds. This file states one over a
`Frame`, where the widths vary too, and asks what that costs.

The answer is `frameRun_agree`'s hypothesis `hwd`, and it is the shape of
`Policy.adapted` read of the widths rather than the leaders: the width of
a round is a function of the verdicts of epochs two behind the epoch its
slots begin in. Under that clause the safety induction closes with no
restriction on the widths themselves — no alignment between a width
change and an epoch boundary, no divisibility, and no change to the
numbering the policy reads, since a frame has one numbering and nothing
is renumbered when a width changes.

`Frame` asks a leader of every round, so it does not present a schedule
that skips rounds — `Slots.uniform p m` at period `p > 1` does, and the
witnesses use it. This is therefore the run of a mechanism that varies
the widths, not a second run of the arc: `Adaptive/Run.lean` keeps the
general one over a fixed `Slots`, and neither subsumes the other.

**Trusted core: `FrameRun` is a definition.** What it asks of a rule is
`Properties.Agree` and nothing else.
-/

namespace LeanDag
namespace Integration
open Properties

variable {Validator : Type} [Fintype Validator] [DecidableEq Validator]
variable {BlockId : Type} [DecidableEq BlockId] {Payload : Type}
variable {R : DagRule Validator BlockId Payload}

/-- **A run over a global frame.** One numbering: slots are enumerated in
round order over the widths the run itself carries, so nothing is
renumbered at a change of width. -/
structure FrameRun (W : ℕ)
    (pick : (U : R.Universe) → R.View U → (ℕ → Option BlockId) → ℕ → Validator)
    (U : R.Universe) (V : R.View U) (H : ℕ) where
  /-- The widths: how many leaders each round has. -/
  F : Frame
  /-- The leaders, by round and position. -/
  asg : ℕ → ℕ → Validator
  keyed : ∀ r i j, i < F.width r → j < F.width r → asg r i = asg r j → i = j
  /-- The verdicts, by global slot index. -/
  vdct : ℕ → Option BlockId
  /-- The assignment is the policy's. -/
  coherent : ∀ r i, i < F.width r → epochOf W (F.index r i) < H + 1 →
    asg r i = pick U V vdct (F.index r i)
  /-- Every slot of a closed epoch is decided by the schedule below the
  round at which its window ends. -/
  closed : ∀ r i, i < F.width r → epochOf W (F.index r i) < H →
    DecidedFrameBelow R F asg
      (F.roundOf (W * (epochOf W (F.index r i) + 2))) V (F.index r i)
      (vdct (F.index r i))

variable {W : ℕ}
variable {pick : (U : R.Universe) → R.View U → (ℕ → Option BlockId) → ℕ → Validator}
variable {U : R.Universe} {V : R.View U} {H : ℕ}

/-- Every round below the round that holds slot `n` holds only slots
below `n`. -/
theorem index_lt_of_round_lt {F : Frame} {n r i : ℕ} (hr : r < F.roundOf n)
    (hi : i < F.width r) : F.index r i < n := by
  have h1 : F.cum (r + 1) ≤ F.cum (F.roundOf n) := F.cum_mono (by omega)
  have h2 : F.cum (F.roundOf n) ≤ n := F.cum_roundOf_le n
  have h3 : F.cum (r + 1) = F.cum r + F.width r := F.cum_succ r
  simp only [Frame.index]
  omega

namespace FrameRun

variable (Rn : FrameRun (R := R) W pick U V H)

/-- `closed`, read at a global slot rather than at a round and a
position. -/
theorem closed_at (g : ℕ) (hg : epochOf W g < H) :
    DecidedFrameBelow R Rn.F Rn.asg
      (Rn.F.roundOf (W * (epochOf W g + 2))) V g (Rn.vdct g) := by
  have h := Rn.closed (Rn.F.roundOf g) (g - Rn.F.cum (Rn.F.roundOf g))
    (Rn.F.pos_lt_width g) (by rw [Rn.F.index_roundOf_self g]; exact hg)
  rwa [Rn.F.index_roundOf_self g] at h

/-- A run's own schedule decides its own verdicts. -/
theorem decided_self (g : ℕ) (hg : epochOf W g < H) :
    R.Decided (Rn.F.toSlots Rn.asg Rn.keyed) V g (Rn.vdct g) :=
  Rn.closed_at g hg Rn.F Rn.asg Rn.keyed (fun _ _ => rfl) (fun _ _ _ _ => rfl)

end FrameRun

/-- **Safety over a varying frame.** Two runs over one universe and view
have the same verdicts, given that the widths obey the lag the leaders
already do.

`hwd` is the whole of what the varying widths cost: the width of round
`r` is a function of the verdicts of epochs at least two behind the epoch
`r`'s slots begin in. It is `Policy.adapted` read of the widths, and the
induction needs it for the same reason — deciding an epoch reads the
schedule two epochs ahead, and what it reads there must already be
settled. -/
theorem frameRun_agree (hR : Agree R) (hW : 0 < W)
    (hadapted : ∀ (U : R.Universe) (V₁ V₂ : R.View U) v w k,
      (∀ j, epochOf W j + 2 ≤ epochOf W k → v j = w j) →
      pick U V₁ v k = pick U V₂ w k)
    (Rn Rn' : FrameRun (R := R) W pick U V H)
    (hwd : ∀ r, r < Rn.F.roundOf (W * (H + 1)) →
      (∀ j, epochOf W j + 2 ≤ epochOf W (Rn.F.cum r) → Rn.vdct j = Rn'.vdct j) →
      Rn'.F.width r = Rn.F.width r) :
    ∀ g, epochOf W g < H → Rn.vdct g = Rn'.vdct g := by
  suffices main : ∀ e g, epochOf W g = e → epochOf W g < H → Rn.vdct g = Rn'.vdct g by
    intro g hg; exact main _ g rfl hg
  intro e
  induction e using Nat.strong_induction_on with
  | _ e ih =>
    intro g hge hgH
    set B := Rn.F.roundOf (W * (epochOf W g + 2)) with hB
    have hBle : B ≤ Rn.F.roundOf (W * (H + 1)) :=
      Rn.F.roundOf_mono (Nat.mul_le_mul_left W (by omega))
    have hw : ∀ r', r' < B → Rn'.F.width r' = Rn.F.width r' := by
      intro r' hr'
      refine hwd r' (by omega) (fun j hj => ?_)
      have h1 : Rn.F.cum r' < Rn.F.cum B := Rn.F.cum_strictMono hr'
      have h2 : Rn.F.cum B ≤ W * (epochOf W g + 2) := Rn.F.cum_roundOf_le _
      have h3 : epochOf W (Rn.F.cum r') < epochOf W g + 2 :=
        (epochOf_lt_iff hW).mpr (by omega)
      exact ih (epochOf W j) (by omega) j rfl (by omega)
    have hcum : ∀ r', r' ≤ B → Rn'.F.cum r' = Rn.F.cum r' :=
      fun r' hr' => Frame.cum_congr hw hr'
    have ha : ∀ r' i', r' < B → i' < Rn.F.width r' → Rn'.asg r' i' = Rn.asg r' i' := by
      intro r' i' hr' hi'
      have hlt : Rn.F.index r' i' < W * (epochOf W g + 2) :=
        index_lt_of_round_lt hr' hi'
      have hep : epochOf W (Rn.F.index r' i') < epochOf W g + 2 :=
        (epochOf_lt_iff hW).mpr hlt
      have heq : Rn'.F.index r' i' = Rn.F.index r' i' := by
        simp only [Frame.index, hcum r' (by omega)]
      have hi'' : i' < Rn'.F.width r' := by rw [hw r' hr']; exact hi'
      rw [Rn'.coherent r' i' hi'' (by rw [heq]; omega),
        Rn.coherent r' i' hi' (by omega), heq]
      refine hadapted U V V Rn'.vdct Rn.vdct _ (fun j hj => ?_)
      exact (ih (epochOf W j) (by omega) j rfl (by omega)).symm
    have d₁ := Rn.closed_at g hgH Rn'.F Rn'.asg Rn'.keyed hw ha
    have d₂ := Rn'.decided_self g hgH
    exact hR _ V V g _ _ d₁ d₂

end Integration
end LeanDag
