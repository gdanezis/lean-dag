import LeanDag.Scheme.Equiv.Proof
import LeanDag.Scheme.Table.Proof
/-!
# A vote-selection rule exists

The scheme's rows are stated for every `VoteSel`; this file builds one, so
those statements are not about an empty class. `leastSel` votes for the
least block of the slot in the voter's history below it, the choice
Mahi-Mahi and Async BlueBottle make. Each row then holds at it.
-/

namespace LeanDagTest

namespace Scheme

open LeanDag LeanDag.Scheme

variable {Validator : Type} [Fintype Validator] [DecidableEq Validator]
variable {BlockId : Type} [LinearOrder BlockId] {Payload : Type}
variable {P : Validity Validator BlockId Payload} {honest : Finset Validator}

/-- The blocks of `(a, r)` in `b`'s history, below `b`. -/
def slotIn (U : BlockRecord Validator BlockId Payload P honest) (b : BlockId) (a : Validator)
    (r : ℕ) : Finset BlockId :=
  if (U.block b).round ≤ r then ∅
  else (history U b).filter (fun x => (U.block x).creator = a ∧ (U.block x).round = r)

/-- **The least block of the slot in the voter's history.** -/
def leastSel : VoteSel Validator BlockId Payload P honest where
  sel U b a r := if h : (slotIn U b a r).Nonempty then some ((slotIn U b a r).min' h) else none
  below U b a r hr := by
    have : slotIn U b a r = ∅ := if_pos hr
    simp only [this, Finset.not_nonempty_empty, dite_false]
  sound U b a r x hx := by
    by_cases hs : (slotIn U b a r).Nonempty
    · rw [dif_pos hs, Option.some.injEq] at hx
      have hm := Finset.min'_mem _ hs
      rw [hx] at hm
      by_cases hr : (U.block b).round ≤ r
      · simp [slotIn, hr] at hm
      · simp only [slotIn, hr, if_false, Finset.mem_filter] at hm
        exact ⟨hm.1, hm.2.1, hm.2.2⟩
    · rw [dif_neg hs] at hx
      exact absurd hx (by simp)
  complete U b a r hr hsel x hx hc hxr := by
    have hmem : x ∈ slotIn U b a r := by
      simp only [slotIn, show ¬ (U.block b).round ≤ r by omega, if_false, Finset.mem_filter]
      exact ⟨hx, hc, hxr⟩
    have hne : (slotIn U b a r).Nonempty := ⟨x, hmem⟩
    rw [dif_pos hne] at hsel
    exact absurd hsel (by simp)

/-- The Mysticeti row at `leastSel`. -/
example [F : Faults Validator] :
    (schemeAnchored (Params.mysticeti (Fintype.card Validator) F.f)
        (leastSel (Validator := Validator) (BlockId := BlockId) (Payload := Payload)
          (P := ValidWrt) (honest := Correct))).toDagRule =
      MysticetiProperties.mysticetiRule (Validator := Validator) (BlockId := BlockId)
        (Payload := Payload) :=
  Equiv.mysticetiRow Validator BlockId Payload leastSel

end Scheme

end LeanDagTest

#print axioms LeanDag.Scheme.Table.holds
#print axioms LeanDag.Scheme.Equiv.holds
#print axioms LeanDagTest.Scheme.leastSel
