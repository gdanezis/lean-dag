import LeanDag.Scheme.Model.LeastSel
import LeanDag.Common.CausalHistory
/-!
# The least vote, searched only as deep as the slot

`leastSel` takes the least block of a slot in the voter's whole
history. In a record whose references sit one round below, a block of
round `r` reachable from `b` lies within `round b − r` steps of it
(`mem_historyUptoFrom_of_round`), so `boundedSel` searches that far and
no further, and selects what `leastSel` selects at every block of the
record (`boundedSel_sel_eq`).
-/

namespace LeanDag

namespace Node

variable {Validator : Type*} [DecidableEq Validator]
variable {BlockId : Type*} [LinearOrder BlockId] {Payload : Type*}
variable {blk : BlockId → Block Validator BlockId Payload} {ids : Finset BlockId}

omit [DecidableEq Validator] in
/-- **A block `d` rounds below `b` and reachable from it lies within `d`
steps.** -/
theorem mem_historyUptoFrom_of_round (C : CausalStructure blk ids) {n : ℕ} {b i : BlockId}
    (hb : b ∈ ids) (hn : (blk b).round ≤ n + (blk i).round) (h : ReachesFrom blk b i) :
    i ∈ historyUptoFrom blk n b := by
  induction n generalizing b with
  | zero =>
    rcases h.cases_head with rfl | ⟨j, hstep, hji⟩
    · exact mem_historyUptoFrom_self
    · have hj := C.refs_round b hb j hstep
      have := C.round_le_of_reaches (C.complete b hb j hstep) hji
      omega
  | succ n ih =>
    rcases h.cases_head with rfl | ⟨j, hstep, hji⟩
    · exact mem_historyUptoFrom_self
    · have hj := C.refs_round b hb j hstep
      exact mem_historyUptoFrom_succ.mpr
        (Or.inr ⟨j, hstep, ih (C.complete b hb j hstep) (by omega) hji⟩)

variable {P : Validity Validator BlockId Payload} {honest : Finset Validator}

/-- The blocks of `(a, r)` within `round b − r` steps of `b`, below `b`. -/
def slotNear (U : BlockRecord Validator BlockId Payload P honest) (b : BlockId) (a : Validator)
    (r : ℕ) : Finset BlockId :=
  if (U.block b).round ≤ r then ∅
  else (historyUptoFrom U.block ((U.block b).round - r) b).filter
    (fun x => (U.block x).creator = a ∧ (U.block x).round = r)

/-- At a block of a record, the near search finds the slot's blocks in
the whole history. -/
theorem slotNear_eq [P.Mechanised] (U : BlockRecord Validator BlockId Payload P honest)
    {b : BlockId} (hb : b ∈ U.ids) (a : Validator) (r : ℕ) :
    slotNear U b a r = Scheme.slotIn U b a r := by
  unfold slotNear Scheme.slotIn
  split
  · rfl
  · ext x
    simp only [Finset.mem_filter]
    constructor
    · rintro ⟨hx, hc⟩
      refine ⟨historyUptoFrom_mono (by omega) b hx, hc⟩
    · rintro ⟨hx, hc, hr⟩
      have hreach : ReachesFrom U.block b x := (mem_history_iff hb).mp hx
      exact ⟨mem_historyUptoFrom_of_round U.causal hb (by omega) hreach, hc, hr⟩

/-- **The least vote, searched as deep as the slot.** -/
def boundedSel [P.Mechanised] : Scheme.VoteSel Validator BlockId Payload P honest where
  sel U b a r := Scheme.leastOf (slotNear U b a r)
  below U b a r hr := by
    have : slotNear U b a r = ∅ := if_pos hr
    simp only [Scheme.leastOf, this, Finset.not_nonempty_empty, dite_false]
  sound U b a r x hx := by
    unfold Scheme.leastOf at hx
    by_cases hs : (slotNear U b a r).Nonempty
    · rw [dif_pos hs, Option.some.injEq] at hx
      have hm := Finset.min'_mem _ hs
      rw [hx] at hm
      by_cases hr : (U.block b).round ≤ r
      · simp [slotNear, hr] at hm
      · simp only [slotNear, hr, if_false, Finset.mem_filter] at hm
        exact ⟨historyUptoFrom_mono (by omega) b hm.1, hm.2.1, hm.2.2⟩
    · rw [dif_neg hs] at hx
      exact absurd hx (by simp)
  complete U b a r hb hr hsel x hx hc hxr := by
    have hmem : x ∈ slotNear U b a r := by
      rw [slotNear_eq U hb]
      simp only [Scheme.slotIn, show ¬ (U.block b).round ≤ r by omega, if_false,
        Finset.mem_filter]
      exact ⟨hx, hc, hxr⟩
    have hne : (slotNear U b a r).Nonempty := ⟨x, hmem⟩
    unfold Scheme.leastOf at hsel
    rw [dif_pos hne] at hsel
    exact absurd hsel (by simp)

/-- **It selects what `leastSel` selects** at every block of a record. -/
theorem boundedSel_sel_eq [P.Mechanised] (U : BlockRecord Validator BlockId Payload P honest)
    {b : BlockId} (hb : b ∈ U.ids) (a : Validator) (r : ℕ) :
    (boundedSel (honest := honest)).sel U b a r = Scheme.leastSel.sel U b a r := by
  change Scheme.leastOf (slotNear U b a r) = Scheme.leastOf (Scheme.slotIn U b a r)
  rw [slotNear_eq U hb]

end Node

end LeanDag
