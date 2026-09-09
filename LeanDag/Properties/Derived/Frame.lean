import LeanDag.Common.Frame
import LeanDag.Properties.Derived.FromBand

namespace LeanDag
namespace Frame

variable {Validator : Type*}

/-- Frames agreeing on the widths of the rounds below `B` agree on how
many slots sit below each of those rounds. -/
theorem cum_congr {F F' : Frame} {B : ℕ}
    (h : ∀ r, r < B → F'.width r = F.width r) {r : ℕ} (hr : r ≤ B) :
    F'.cum r = F.cum r := by
  induction r with
  | zero => simp
  | succ j ih =>
      rw [cum_succ, cum_succ, ih (by omega), h j (by omega)]

/-- **Frames agreeing below a round induce schedules agreeing there.**
Every slot at a round below `B` keeps its round and its leader. -/
theorem toSlots_agree {F F' : Frame} {asg asg' : ℕ → ℕ → Validator} {hk hk'} {B : ℕ}
    (hw : ∀ r, r < B → F'.width r = F.width r)
    (ha : ∀ r i, r < B → i < F.width r → asg' r i = asg r i)
    {m : ℕ} (hm : F.roundOf m < B) :
    (F'.toSlots asg' hk').slotRound m = (F.toSlots asg hk).slotRound m ∧
      (F'.toSlots asg' hk').leader m = (F.toSlots asg hk).leader m := by
  have hlo : F.cum (F.roundOf m) ≤ m := F.cum_roundOf_le m
  have hhi : m < F.cum (F.roundOf m + 1) := F.lt_cum_roundOf_succ m
  have e0 : F'.cum (F.roundOf m) = F.cum (F.roundOf m) := cum_congr hw (by omega)
  have e1 : F'.cum (F.roundOf m + 1) = F.cum (F.roundOf m + 1) := cum_congr hw (by omega)
  have hr : F'.roundOf m = F.roundOf m := F'.roundOf_eq (by omega) (by omega)
  refine ⟨hr, ?_⟩
  simp only [toSlots_leader, hr, e0]
  exact ha _ _ hm (by have := F.pos_lt_width m; omega)

end Frame

namespace Properties

variable {Validator : Type} [Fintype Validator] [DecidableEq Validator]
variable {BlockId : Type} [DecidableEq BlockId] {Payload : Type}
variable {R : DagRule Validator BlockId Payload}

/-- **A verdict survives a change of frame above the rounds it reads.**
Every decided slot has a round bound below which the widths and the
leaders settle it: a schedule built from any frame agreeing there decides
it the same way, whatever the widths above.

This is what a mechanism that varies the round widths needs. Barnacle
records a configuration's verdicts against the uniform schedule at that
configuration's count, extended to every round, which is not the schedule
that runs once the count changes; what makes that sound is that a
configuration's verdicts are settled within its own rounds, and this is
that statement. -/
theorem decided_of_frame_agree (h : Banded R) {F : Frame} {asg : ℕ → ℕ → Validator} {hk}
    {U : R.Universe} {V : R.View U} {g : ℕ} {v : Option BlockId}
    (hd : R.Decided (F.toSlots asg hk) V g v) :
    ∃ B, F.roundOf g < B ∧
      ∀ (F' : Frame) (asg' : ℕ → ℕ → Validator) (hk'),
        (∀ r, r < B → F'.width r = F.width r) →
        (∀ r i, r < B → i < F.width r → asg' r i = asg r i) →
        R.Decided (F'.toSlots asg' hk') V g v := by
  obtain ⟨B, hB, ht⟩ := exists_roundLocal h hd
  refine ⟨B, hB, fun F' asg' hk' hw ha => ht _ ?_ ?_⟩
  · exact fun m hm => (Frame.toSlots_agree hw ha hm).1
  · exact fun m hm => (Frame.toSlots_agree hw ha hm).2

end Properties
end LeanDag
