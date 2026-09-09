import LeanDag.Common.Slots
import LeanDag.Network.Delivery
import LeanDag.GC.Chop
/-!
# Decisions survive the cut

`garbage.md` **G3** and **G4**: the construction — `Slots.chop`, the
induced schedule re-indexed from a base slot `d` clearing the horizon —
that `Properties/Arcs/GC.lean` reads to give cross-cut agreement for
any rule with a `Banded` and `Agree`. A joiner's view of the truncation
is arbitrary, not necessarily a truncated full-history view, so the
agreement holds however little the two validators share.
-/

namespace LeanDag

variable {Validator : Type*} [Fintype Validator] [DecidableEq Validator]
variable [F : Faults Validator]
variable {BlockId : Type*} [DecidableEq BlockId] {Payload : Type*}
variable {U : BlockUniverse Validator BlockId Payload}
variable {G : ℕ}

/-! ## The truncated view -/

/-! A validator's view, truncated at the horizon, is the record's
`View.chop` (`Record/Chop.lean`): keep what clears the cut. -/

/-! ## The induced schedule -/

/-- The truncation's slot schedule: slots re-indexed from a base slot `d`
whose round clears the horizon, rounds rebased by `−G`. The base-slot
condition keeps subtraction faithful, which is what keying needs. -/
@[reducible]
def Slots.chop (S : Slots Validator) (G d : ℕ) (hd : G ≤ S.slotRound d) :
    Slots Validator where
  slotRound k := S.slotRound (d + k) - G
  leader k := S.leader (d + k)
  mono _ _ h := Nat.sub_le_sub_right (S.mono (Nat.add_le_add_left h d)) G
  unbounded := by
    intro n
    obtain ⟨k, hk⟩ := S.unbounded (G + n)
    rcases Nat.le_total k d with hkd | hdk
    · refine ⟨0, ?_⟩
      have := S.mono hkd
      simp only [Nat.add_zero]
      omega
    · refine ⟨k - d, ?_⟩
      have hcancel : d + (k - d) = k := by omega
      simp only [hcancel]
      omega
  keyed := by
    intro k₁ k₂ h
    simp only [Prod.mk.injEq] at h
    obtain ⟨hr, hl⟩ := h
    have h₁ := hd.trans (S.mono (Nat.le_add_right d k₁))
    have h₂ := hd.trans (S.mono (Nat.le_add_right d k₂))
    have hpair : (S.slotRound (d + k₁), S.leader (d + k₁))
        = (S.slotRound (d + k₂), S.leader (d + k₂)) := by
      have : S.slotRound (d + k₁) = S.slotRound (d + k₂) := by omega
      rw [this, hl]
    have := S.keyed hpair
    omega

@[simp]
theorem Slots.chop_slotRound (S : Slots Validator) {d : ℕ}
    (hd : G ≤ S.slotRound d) (k : ℕ) :
    (S.chop G d hd).slotRound k = S.slotRound (d + k) - G := rfl

@[simp]
theorem Slots.chop_leader (S : Slots Validator) {d : ℕ}
    (hd : G ≤ S.slotRound d) (k : ℕ) :
    (S.chop G d hd).leader k = S.leader (d + k) := rfl

variable [S : Slots Validator] {d : ℕ}

omit [Fintype Validator] [DecidableEq Validator] F in
/-- Every slot from the base slot on clears the horizon. Stated with the
fault model omitted: a rule with its own universe record still runs on
the core's schedule, and the cut's base-slot condition is about the
schedule alone. -/
theorem horizon_le_slotRound (hd : G ≤ S.slotRound d) (k : ℕ) :
    G ≤ S.slotRound (d + k) :=
  hd.trans (S.mono (Nat.le_add_right d k))

end LeanDag
