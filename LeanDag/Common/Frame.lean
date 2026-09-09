import LeanDag.Common.Slots
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

namespace LeanDag

variable {Validator : Type*}

/-- **A round structure given by its widths.** Round `r` holds
`width r` slots. Barnacle varies the widths and leaves the leaders
alone; Hammerhead varies the leaders and leaves the widths alone, so
this is the half of a schedule one mechanism owns. -/
structure Frame where
  /-- The number of slots round `r` holds. -/
  width : ℕ → ℕ
  width_pos : ∀ r, 0 < width r

namespace Frame

variable (F : Frame)

/-- The slots at rounds below `r`. -/
def cum (r : ℕ) : ℕ := ∑ r' ∈ Finset.range r, F.width r'

@[simp] theorem cum_zero : F.cum 0 = 0 := by simp [cum]

theorem cum_succ (r : ℕ) : F.cum (r + 1) = F.cum r + F.width r := by
  simp [cum, Finset.sum_range_succ]

theorem cum_lt_succ (r : ℕ) : F.cum r < F.cum (r + 1) := by
  rw [cum_succ]; exact Nat.lt_add_of_pos_right (F.width_pos r)

theorem cum_strictMono : StrictMono F.cum :=
  strictMono_nat_of_lt_succ F.cum_lt_succ

theorem cum_mono : Monotone F.cum := F.cum_strictMono.monotone

/-- A round's index is at most the number of slots below it, since every
round holds one. -/
theorem le_cum (r : ℕ) : r ≤ F.cum r := by
  induction r with
  | zero => simp
  | succ j ih => have := F.width_pos j; rw [cum_succ]; omega

/-- **The round a global slot index falls in.** -/
noncomputable def roundOf (g : ℕ) : ℕ :=
  Nat.findGreatest (fun r => F.cum r ≤ g) g

theorem cum_roundOf_le (g : ℕ) : F.cum (F.roundOf g) ≤ g := by
  classical
  have h0 : F.cum 0 ≤ g := by rw [cum_zero]; exact Nat.zero_le g
  exact Nat.findGreatest_spec (P := fun r => F.cum r ≤ g) (m := 0) (Nat.zero_le g) h0

theorem lt_cum_roundOf_succ (g : ℕ) : g < F.cum (F.roundOf g + 1) := by
  classical
  by_contra hc
  push_neg at hc
  have hle : F.roundOf g + 1 ≤ g := le_trans (F.le_cum _) hc
  have hge := Nat.le_findGreatest (P := fun r => F.cum r ≤ g) hle hc
  simp only [roundOf] at hge
  omega

theorem roundOf_eq {g r : ℕ} (h₁ : F.cum r ≤ g) (h₂ : g < F.cum (r + 1)) :
    F.roundOf g = r := by
  by_contra hne
  rcases Nat.lt_or_ge (F.roundOf g) r with h | h
  · have hm : F.cum (F.roundOf g + 1) ≤ F.cum r := F.cum_mono (Nat.succ_le_of_lt h)
    have hg : g < F.cum (F.roundOf g + 1) := F.lt_cum_roundOf_succ g
    omega
  · have hr : r + 1 ≤ F.roundOf g := by omega
    have hm : F.cum (r + 1) ≤ F.cum (F.roundOf g) := F.cum_mono hr
    have hg : F.cum (F.roundOf g) ≤ g := F.cum_roundOf_le g
    omega

/-- The global index of position `i` of round `r`. -/
def index (r i : ℕ) : ℕ := F.cum r + i

@[simp] theorem roundOf_index {r i : ℕ} (hi : i < F.width r) :
    F.roundOf (F.index r i) = r :=
  F.roundOf_eq (by simp [index]) (by rw [index, cum_succ]; omega)

theorem roundOf_mono : Monotone F.roundOf := by
  intro a b hab
  by_contra hc
  push_neg at hc
  have h1 : F.cum (F.roundOf a) ≤ a := F.cum_roundOf_le a
  have h2 : b < F.cum (F.roundOf b + 1) := F.lt_cum_roundOf_succ b
  have h3 : F.cum (F.roundOf b + 1) ≤ F.cum (F.roundOf a) :=
    F.cum_mono (Nat.succ_le_of_lt hc)
  omega


theorem cum_le_of_roundOf (g : ℕ) : F.cum (F.roundOf g) ≤ g := F.cum_roundOf_le g

theorem pos_lt_width (g : ℕ) : g - F.cum (F.roundOf g) < F.width (F.roundOf g) := by
  have h1 := F.cum_roundOf_le g
  have h2 := F.lt_cum_roundOf_succ g
  rw [cum_succ] at h2
  omega

@[simp] theorem roundOf_cum (r : ℕ) : F.roundOf (F.cum r) = r :=
  F.roundOf_eq le_rfl (F.cum_lt_succ r)

/-- **The schedule a frame and an assignment make.** Slots are
enumerated in round order; the leader of a slot is the assignment at its
round and its position in that round. -/
noncomputable def toSlots (asg : ℕ → ℕ → Validator)
    (hkey : ∀ r i j, i < F.width r → j < F.width r → asg r i = asg r j → i = j) :
    Slots Validator where
  slotRound := F.roundOf
  leader := fun g => asg (F.roundOf g) (g - F.cum (F.roundOf g))
  mono := F.roundOf_mono
  unbounded := fun n => ⟨F.cum n, by rw [F.roundOf_cum]⟩
  keyed := by
    intro g₁ g₂ h
    simp only [Prod.mk.injEq] at h
    obtain ⟨hr, hl⟩ := h
    have e : g₁ - F.cum (F.roundOf g₁) = g₂ - F.cum (F.roundOf g₂) := by
      refine hkey (F.roundOf g₁) _ _ (F.pos_lt_width g₁) ?_ ?_
      · rw [hr]; exact F.pos_lt_width g₂
      · rw [hl, hr]
    have h1 : F.cum (F.roundOf g₁) ≤ g₁ := F.cum_roundOf_le g₁
    have h2 : F.cum (F.roundOf g₂) ≤ g₂ := F.cum_roundOf_le g₂
    rw [hr] at h1 e
    omega

@[simp] theorem toSlots_slotRound {asg : ℕ → ℕ → Validator} {hkey} (g : ℕ) :
    (F.toSlots asg hkey).slotRound g = F.roundOf g := rfl

@[simp] theorem toSlots_leader {asg : ℕ → ℕ → Validator} {hkey} (g : ℕ) :
    (F.toSlots asg hkey).leader g = asg (F.roundOf g) (g - F.cum (F.roundOf g)) := rfl

theorem toSlots_leader_index {asg : ℕ → ℕ → Validator} {hkey} {r i : ℕ}
    (hi : i < F.width r) : (F.toSlots asg hkey).leader (F.index r i) = asg r i := by
  rw [toSlots_leader, F.roundOf_index hi, index]
  simp

end Frame

/-- **The constant frame**: every round holds `m` slots, which is
Barnacle's schedule at a fixed count. -/
def constFrame (m : ℕ) (hm : 0 < m) : Frame where
  width := fun _ => m
  width_pos := fun _ => hm

@[simp] theorem constFrame_cum (m : ℕ) (hm : 0 < m) (r : ℕ) :
    (constFrame m hm).cum r = r * m := by
  simp [Frame.cum, constFrame]

@[simp] theorem constFrame_roundOf (m : ℕ) (hm : 0 < m) (g : ℕ) :
    (constFrame m hm).roundOf g = g / m := by
  refine Frame.roundOf_eq _ ?_ ?_
  · rw [constFrame_cum]; exact Nat.div_mul_le_self g m
  · rw [constFrame_cum]
    have d := Nat.div_add_mod g m
    have e : g % m < m := Nat.mod_lt _ hm
    have c : (g / m + 1) * m = m * (g / m) + m := by
      rw [Nat.succ_mul, Nat.mul_comm]
    omega

end LeanDag
