import LeanDag.Common.Slots
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
/-!
# A configuration: the schedule a reconfiguration installs

Barnacle's update rule returns a leader count, and a configuration's
schedule is the fixed rotation at that count — every round of the
configuration the same width. A `Config` is what it returns instead:
how many slots each round holds, **round by round**, who leads each
place, and how long the configuration runs before the next
reconfiguration is due.

`slotsAt` is the primitive and `sched` derives from it. The reason the
width is in the interface rather than a `Slots` alone is that two places
need the first slot of a round — the ledger's range and the window's
measurement — and a `Slots` gives that only by inverting `slotRound`.

**Trusted core: `Config` and `sched` are definitions.** What they ask of
a rule is stated in `Model/Run.lean`, as `count_pos` and `count_le` were.
-/

namespace LeanDag
namespace Barnacle

variable {Validator : Type}

/-- **A configuration.** The schedule its rounds run on, given by the
slots each round holds and the leader of each place, and the rounds it
runs before the next reconfiguration is due. -/
structure Config (Validator : Type) where
  /-- How many slots round `r` holds. A function of the round, so a
  configuration's rounds need not agree. -/
  slotsAt : ℕ → ℕ
  slotsAt_pos : ∀ r, 0 < slotsAt r
  /-- Who leads position `i` of round `r`. -/
  lead : ℕ → ℕ → Validator
  /-- Distinct positions of a round have distinct leaders, which is what
  `Slots.keyed` asks of the schedule this gives. -/
  keyed : ∀ r i j, i < slotsAt r → j < slotsAt r → lead r i = lead r j → i = j
  /-- Rounds from the configuration's start before the next
  reconfiguration is due. -/
  interval : ℕ

namespace Config

variable (C : Config Validator)

/-- The slots at rounds below `r`, so `cum r` is the first slot of round
`r`. -/
def cum (r : ℕ) : ℕ := ∑ r' ∈ Finset.range r, C.slotsAt r'

@[simp] theorem cum_zero : C.cum 0 = 0 := by simp [cum]

theorem cum_succ (r : ℕ) : C.cum (r + 1) = C.cum r + C.slotsAt r := by
  simp [cum, Finset.sum_range_succ]

theorem cum_lt_succ (r : ℕ) : C.cum r < C.cum (r + 1) := by
  rw [cum_succ]; exact Nat.lt_add_of_pos_right (C.slotsAt_pos r)

theorem cum_strictMono : StrictMono C.cum :=
  strictMono_nat_of_lt_succ C.cum_lt_succ

theorem cum_mono : Monotone C.cum := C.cum_strictMono.monotone

/-- A round is at most the number of slots below it, every round holding
one. -/
theorem le_cum (r : ℕ) : r ≤ C.cum r := by
  induction r with
  | zero => simp
  | succ j ih => have := C.slotsAt_pos j; rw [cum_succ]; omega

/-- The round slot `g` is proposed at. -/
def roundOf (g : ℕ) : ℕ :=
  Nat.findGreatest (fun r => C.cum r ≤ g) g

theorem cum_roundOf_le (g : ℕ) : C.cum (C.roundOf g) ≤ g := by
  classical
  have h0 : C.cum 0 ≤ g := by rw [cum_zero]; exact Nat.zero_le g
  exact Nat.findGreatest_spec (P := fun r => C.cum r ≤ g) (m := 0) (Nat.zero_le g) h0

theorem lt_cum_roundOf_succ (g : ℕ) : g < C.cum (C.roundOf g + 1) := by
  classical
  by_contra hc
  push_neg at hc
  have hle : C.roundOf g + 1 ≤ g := le_trans (C.le_cum _) hc
  exact absurd hc (Nat.findGreatest_is_greatest
    (P := fun r => C.cum r ≤ g) (Nat.lt_succ_self _) hle)

theorem roundOf_eq {g r : ℕ} (h₁ : C.cum r ≤ g) (h₂ : g < C.cum (r + 1)) :
    C.roundOf g = r := by
  have hlo := C.cum_roundOf_le g
  have hhi := C.lt_cum_roundOf_succ g
  by_contra hne
  rcases Nat.lt_or_ge (C.roundOf g) r with h | h
  · have := C.cum_mono (show C.roundOf g + 1 ≤ r by omega)
    omega
  · have := C.cum_mono (show r + 1 ≤ C.roundOf g by omega)
    omega

@[simp] theorem roundOf_cum (r : ℕ) : C.roundOf (C.cum r) = r :=
  C.roundOf_eq (le_refl _) (C.cum_lt_succ r)

/-- Slot `g` is at or past its round's first slot, and short of the
next's. -/
theorem pos_lt_slotsAt (g : ℕ) : g - C.cum (C.roundOf g) < C.slotsAt (C.roundOf g) := by
  have h1 := C.cum_roundOf_le g
  have h2 := C.lt_cum_roundOf_succ g
  rw [cum_succ] at h2
  omega

/-- **A round is at or past `R` exactly when its first slot is.** -/
theorem cum_le_iff_le_roundOf {r g : ℕ} : C.cum r ≤ g ↔ r ≤ C.roundOf g := by
  constructor
  · intro h
    by_contra hc
    have := C.cum_mono (show C.roundOf g + 1 ≤ r by omega)
    have := C.lt_cum_roundOf_succ g
    omega
  · intro h
    exact le_trans (C.cum_mono h) (C.cum_roundOf_le g)

theorem roundOf_mono : Monotone C.roundOf := fun a b hab =>
  C.cum_le_iff_le_roundOf.mp (le_trans (C.cum_roundOf_le a) hab)

/-- The slot at position `i` of round `r`. -/
def index (r i : ℕ) : ℕ := C.cum r + i

@[simp] theorem roundOf_index {r i : ℕ} (hi : i < C.slotsAt r) :
    C.roundOf (C.index r i) = r :=
  C.roundOf_eq (by simp [index]) (by rw [index, cum_succ]; omega)

/-- Every slot is its own round's, at its own position. -/
theorem index_roundOf_self (g : ℕ) :
    C.index (C.roundOf g) (g - C.cum (C.roundOf g)) = g := by
  have := C.cum_roundOf_le g
  simp only [index]
  omega

/-- **The schedule a configuration gives.** -/
def sched : Slots Validator where
  slotRound := C.roundOf
  leader := fun g => C.lead (C.roundOf g) (g - C.cum (C.roundOf g))
  mono := C.roundOf_mono
  unbounded := fun n => ⟨C.cum n, by rw [C.roundOf_cum]⟩
  keyed := by
    intro g₁ g₂ h
    simp only [Prod.mk.injEq] at h
    obtain ⟨hr, hl⟩ := h
    have h1 : g₁ - C.cum (C.roundOf g₁) < C.slotsAt (C.roundOf g₁) := C.pos_lt_slotsAt g₁
    have h2 : g₂ - C.cum (C.roundOf g₂) < C.slotsAt (C.roundOf g₂) := C.pos_lt_slotsAt g₂
    rw [hr] at h1 hl
    have hi := C.keyed (C.roundOf g₂) _ _ h1 h2 hl
    have e1 := C.cum_roundOf_le g₁
    have e2 := C.cum_roundOf_le g₂
    rw [hr] at e1
    omega

@[simp] theorem sched_slotRound (g : ℕ) : C.sched.slotRound g = C.roundOf g := rfl

@[simp] theorem sched_leader (g : ℕ) :
    C.sched.leader g = C.lead (C.roundOf g) (g - C.cum (C.roundOf g)) := rfl

theorem sched_leader_index {r i : ℕ} (hi : i < C.slotsAt r) :
    C.sched.leader (C.index r i) = C.lead r i := by
  rw [sched_leader, C.roundOf_index hi, index]
  simp

/-- A slot lies below a round's first slot exactly when its round lies
below that round. -/
theorem lt_cum_iff_roundOf_lt {g r : ℕ} : g < C.cum r ↔ C.roundOf g < r := by
  constructor
  · intro h
    by_contra hcon
    exact absurd (C.cum_mono (Nat.le_of_not_lt hcon)) (by
      have := C.cum_roundOf_le g; omega)
  · intro h
    by_contra hcon
    exact absurd ((C.cum_le_iff_le_roundOf).1 (Nat.le_of_not_lt hcon)) (by omega)

/-- **The head of a round**: the leader of its first slot. Every
configuration has one at every round, whatever its widths. -/
def head (ρ : ℕ) : Validator := C.lead ρ 0

@[simp] theorem sched_leader_cum (ρ : ℕ) : C.sched.leader (C.cum ρ) = C.head ρ := by
  rw [sched_leader, roundOf_cum, head, Nat.sub_self]

/-! ## Configurations of one width -/

end Config

/-- **The leaders a round offers are distinct**, up to width `w`: the
obligation `Config.keyed` makes, stated once at the largest width, from
which it follows at every smaller one. -/
def LeadKeyed (lead : ℕ → ℕ → Validator) (w : ℕ) : Prop :=
  ∀ r i j, i < w → j < w → lead r i = lead r j → i = j

/-- **A configuration whose every round is `m` slots wide.** The shape
the paper's mechanism emits, where only the count varies. -/
def Config.uniform (lead : ℕ → ℕ → Validator) {w : ℕ} (hl : LeadKeyed lead w)
    (m : ℕ) (hm : 0 < m) (hmax : m ≤ w) (I : ℕ) : Config Validator where
  slotsAt := fun _ => m
  slotsAt_pos := fun _ => hm
  lead := lead
  keyed := fun r i j hi hj h => hl r i j (lt_of_lt_of_le hi hmax) (lt_of_lt_of_le hj hmax) h
  interval := I

namespace Config

variable (lead : ℕ → ℕ → Validator) {w : ℕ} (hl : LeadKeyed lead w)
variable (m : ℕ) (hm : 0 < m) (hmax : m ≤ w) (I : ℕ)

@[simp] theorem uniform_slotsAt (r : ℕ) : (uniform lead hl m hm hmax I).slotsAt r = m := rfl

@[simp] theorem uniform_lead : (uniform lead hl m hm hmax I).lead = lead := rfl

@[simp] theorem uniform_interval : (uniform lead hl m hm hmax I).interval = I := rfl

@[simp] theorem uniform_cum (r : ℕ) : (uniform lead hl m hm hmax I).cum r = r * m := by
  simp [cum]

@[simp] theorem uniform_roundOf (g : ℕ) : (uniform lead hl m hm hmax I).roundOf g = g / m := by
  refine roundOf_eq _ ?_ ?_ <;> rw [uniform_cum]
  · exact Nat.div_mul_le_self g m
  · have hdm := Nat.div_add_mod g m
    have hlt := Nat.mod_lt g hm
    have hc : (g / m + 1) * m = m * (g / m) + m := by
      rw [Nat.add_mul, Nat.one_mul, Nat.mul_comm]
    omega

end Config

end Barnacle

end LeanDag
