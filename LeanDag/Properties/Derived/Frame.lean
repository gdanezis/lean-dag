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


/-- **A frame extended past a round.** Below `s` it is the old frame;
above, every round holds `m` slots. A run of finite height leaves the
widths above its last configuration unfixed, and this is what fixes
them. -/
def extend (F : Frame) (s m : ℕ) (hm : 0 < m) : Frame where
  width := fun r => if r ≤ s then F.width r else m
  width_pos := fun r => by
    by_cases h : r ≤ s
    · simpa [h] using F.width_pos r
    · simpa [h] using hm

@[simp] theorem extend_width_le {F : Frame} {s m : ℕ} {hm : 0 < m} {r : ℕ} (h : r ≤ s) :
    (F.extend s m hm).width r = F.width r := by simp [extend, h]

@[simp] theorem extend_width_gt {F : Frame} {s m : ℕ} {hm : 0 < m} {r : ℕ} (h : s < r) :
    (F.extend s m hm).width r = m := by simp [extend, Nat.not_le.mpr h]

/-- **The numbering below the extension is untouched.** -/
theorem extend_cum {F : Frame} {s m : ℕ} {hm : 0 < m} {x : ℕ} (hx : x ≤ s + 1) :
    (F.extend s m hm).cum x = F.cum x :=
  cum_congr (F := F) (F' := F.extend s m hm) (B := s + 1)
    (fun r hr => extend_width_le (by omega)) hx

theorem extend_index {F : Frame} {s m : ℕ} {hm : 0 < m} {r i : ℕ} (hr : r ≤ s) :
    (F.extend s m hm).index r i = F.index r i := by
  simp only [index]
  rw [extend_cum (F := F) (s := s) (m := m) (hm := hm) (x := r) (by omega)]

theorem extend_roundOf {F : Frame} {s m : ℕ} {hm : 0 < m} {g : ℕ}
    (hg : F.roundOf g ≤ s) : (F.extend s m hm).roundOf g = F.roundOf g :=
  roundOf_congr (F := F) (F' := F.extend s m hm) (B := s + 1)
    (fun r hr => extend_width_le (by omega)) (by omega)

/-- A slot below the extension's first round is at a round below it. -/
theorem roundOf_lt_of_lt_cum {F : Frame} {g s : ℕ} (h : g < F.cum s) : F.roundOf g < s := by
  by_contra hc
  push_neg at hc
  have := F.cum_mono hc
  have := F.cum_roundOf_le g
  omega

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

/-- **Extending a frame past a round leaves what lies below it
unchanged**, the settled verdicts included: the clause quantifies over
frames agreeing below `B`, and below `s + 1` the two frames are the
same. -/
theorem decidedFrameBelow_extend {F : Frame} {s m : ℕ} {hm : 0 < m}
    {a : ℕ → ℕ → Validator} {B : ℕ} (hB : B ≤ s + 1) {U : R.Universe} {V : R.View U}
    {g : ℕ} {v : Option BlockId} :
    DecidedFrameBelow R (F.extend s m hm) a B V g v ↔ DecidedFrameBelow R F a B V g v := by
  constructor
  · intro h F' a' hk' hw ha
    exact h F' a' hk' (fun r hr => by rw [hw r hr, Frame.extend_width_le (by omega)])
      (fun r i hr hi => ha r i hr (by rwa [Frame.extend_width_le (by omega)] at hi))
  · intro h F' a' hk' hw ha
    exact h F' a' hk' (fun r hr => by rw [hw r hr]; exact Frame.extend_width_le (by omega))
      (fun r i hr hi => ha r i hr (by rw [Frame.extend_width_le (by omega)]; exact hi))

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
