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

/-- **Frames agreeing below a round agree about which round a slot is
in**, for every slot in a round below it. -/
theorem roundOf_congr {F F' : Frame} {B : ℕ}
    (hw : ∀ r, r < B → F'.width r = F.width r)
    {g : ℕ} (hg : F.roundOf g < B) : F'.roundOf g = F.roundOf g := by
  have hlo : F.cum (F.roundOf g) ≤ g := F.cum_roundOf_le g
  have hhi : g < F.cum (F.roundOf g + 1) := F.lt_cum_roundOf_succ g
  have e0 : F'.cum (F.roundOf g) = F.cum (F.roundOf g) := cum_congr hw (by omega)
  have e1 : F'.cum (F.roundOf g + 1) = F.cum (F.roundOf g + 1) := cum_congr hw (by omega)
  exact F'.roundOf_eq (by omega) (by omega)

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

/-- **A verdict settled below a round.** The schedule below round `B` —
its widths and its leaders — decides slot `g`, and nothing above `B`
changes that. `DecidedBelow` is the same idea with the round structure
held fixed and a bound on the slot index; this is the form a mechanism
that varies the widths can state. -/
def DecidedFrameBelow (R : DagRule Validator BlockId Payload) (F : Frame)
    (a : ℕ → ℕ → Validator) (B : ℕ) {U : R.Universe} (V : R.View U)
    (g : ℕ) (v : Option BlockId) : Prop :=
  ∀ (F' : Frame) (a' : ℕ → ℕ → Validator)
    (hk' : ∀ r i j, i < F'.width r → j < F'.width r → a' r i = a' r j → i = j),
    (∀ r, r < B → F'.width r = F.width r) →
    (∀ r i, r < B → i < F.width r → a' r i = a r i) →
    R.Decided (F'.toSlots a' hk') V g v

/-- A verdict settled below a round is settled below any larger one. -/
theorem DecidedFrameBelow.mono {F : Frame} {a : ℕ → ℕ → Validator} {B B' : ℕ}
    {U : R.Universe} {V : R.View U} {g : ℕ} {v : Option BlockId}
    (h : DecidedFrameBelow R F a B V g v) (hBB : B ≤ B') :
    DecidedFrameBelow R F a B' V g v :=
  fun F' a' hk' hw ha => h F' a' hk' (fun r hr => hw r (by omega))
    (fun r i hr hi => ha r i (by omega) hi)

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
    ∃ B, F.roundOf g < B ∧ DecidedFrameBelow R F asg B V g v := by
  obtain ⟨B, hB, ht⟩ := exists_roundLocal h hd
  refine ⟨B, hB, fun F' asg' hk' hw ha => ht _ ?_ ?_⟩
  · exact fun m hm => (Frame.toSlots_agree hw ha hm).1
  · exact fun m hm => (Frame.toSlots_agree hw ha hm).2

end Properties
end LeanDag
