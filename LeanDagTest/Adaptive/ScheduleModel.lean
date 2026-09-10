import LeanDag.Adaptive.ScheduleRun
import LeanDag.Mysticeti.Properties
import LeanDagTest.Integration.VaryingFrame
import LeanDagTest.Mysticeti.Growth
import LeanDagTest.Integration.ComposedRun
/-!
# A schedule whose epochs and widths both vary

`Schedule.ofFixed` reads no verdict, so its three adaptedness clauses
hold by `rfl` and it may take any epoch lengths and any widths. That is
what this file exhibits: epochs of `3, 4, 5, 3, 4, 5, …` slots over
rounds of `1, 2, 3, 1, 2, 3, …`, neither aligned with the other and
neither constant.

It is the check §12 of `adaptive-schedule.md` asks of steps 3 and 4: the
clauses are satisfiable together at a schedule whose two frames both
move, so `ScheduleRun.agree` is not a theorem about an empty family.
-/

namespace LeanDagTest
namespace ScheduleModel

open LeanDag LeanDag.Adaptive LeanDag.MysticetiProperties LeanDagTest.VaryingFrame

/-- Epochs of `3`, `4`, `5` slots, cycling. -/
def eF : Frame where
  width := fun e => e % 3 + 3
  width_pos := fun _ => by omega

example : eF.width 0 = 3 := rfl
example : eF.width 1 = 4 := rfl
example : eF.width 2 = 5 := rfl

/-- The schedule: `eF`'s epochs over `vF`'s rounds, at `vAsg`. -/
noncomputable def sched : Schedule (mysticetiRule (Validator := Fin 4)
    (BlockId := ℕ) (Payload := Unit)) :=
  Schedule.ofFixed eF vF 3 vF_le vAsg vAsg_keyed

/-- **Both frames move, and they are not aligned.** Round `1` holds two
slots where round `0` holds one, and epoch `1` holds four slots where
epoch `0` holds three. -/
example (v : ℕ → Option ℕ) : sched.widthOf v 0 = 1 := rfl
example (v : ℕ → Option ℕ) : sched.widthOf v 1 = 2 := rfl
example (v : ℕ → Option ℕ) : sched.widthOf v 2 = 3 := rfl
example (v : ℕ → Option ℕ) : sched.len v 0 = 3 := rfl
example (v : ℕ → Option ℕ) : sched.len v 1 = 4 := rfl
example (v : ℕ → Option ℕ) : sched.len v 2 = 5 := rfl

/-- Epoch `0` holds three slots and round `0` holds one, so the epoch
boundary at slot `3` falls inside round `2`, which holds slots `3`, `4`
and `5`. No clause prevents it. -/
example (v : ℕ → Option ℕ) : (sched.frameOf v).cum 2 = 3 := by
  rw [Frame.cum_succ, Frame.cum_succ, Frame.cum_zero]
  rfl
example (v : ℕ → Option ℕ) : (sched.epochFrame v).cum 1 = 3 := by
  rw [Frame.cum_succ, Frame.cum_zero]
  rfl

/-! ## A schedule that reads its verdicts

`sched` above reads nothing, so its clauses hold by `rfl`. `aSched`
reads: both its epoch lengths and its widths depend on whether slot `0`
committed, and the three adaptedness clauses hold because that slot lies
in epoch `0`, two below every epoch either function is consulted for.

It is the smallest schedule that is genuinely adapted in both frames, and
its purpose is to show the clauses do not force the frames to be
constant.
-/

/-- Epochs `0` and `1` hold three slots; later ones hold three or four,
according to whether slot `0` committed. -/
def aLen (v : ℕ → Option ℕ) (e : ℕ) : ℕ :=
  if e < 2 then 3 else if v 0 = none then 3 else 4

/-- Rounds below `6` hold one slot; later ones hold one or two, by the
same reading. -/
def aWid (v : ℕ → Option ℕ) (r : ℕ) : ℕ :=
  if r < 6 then 1 else if v 0 = none then 1 else 2

theorem aLen_pos (v : ℕ → Option ℕ) (e : ℕ) : 0 < aLen v e := by
  unfold aLen; split
  · omega
  · split <;> omega

theorem aWid_pos (v : ℕ → Option ℕ) (r : ℕ) : 0 < aWid v r := by
  unfold aWid; split
  · omega
  · split <;> omega

theorem aWid_le (v : ℕ → Option ℕ) (r : ℕ) : aWid v r ≤ 2 := by
  unfold aWid; split
  · omega
  · split <;> omega

theorem aWid_low {v : ℕ → Option ℕ} {r : ℕ} (h : r < 6) : aWid v r = 1 := if_pos h

/-- The epochs and the rounds the schedule gives at a verdict function. -/
def aE (v : ℕ → Option ℕ) : Frame := ⟨aLen v, aLen_pos v⟩

def aF (v : ℕ → Option ℕ) : Frame := ⟨aWid v, aWid_pos v⟩

@[simp] theorem aE_width (v : ℕ → Option ℕ) (e : ℕ) : (aE v).width e = aLen v e := rfl

@[simp] theorem aF_width (v : ℕ → Option ℕ) (r : ℕ) : (aF v).width r = aWid v r := rfl

theorem aE_cum2 (v : ℕ → Option ℕ) : (aE v).cum 2 = 6 := by
  rw [Frame.cum_succ, Frame.cum_succ, Frame.cum_zero]
  rfl

/-- Slot `0` is in epoch `0`, whatever the verdicts say. -/
theorem aE_roundOf_zero (v : ℕ → Option ℕ) : (aE v).roundOf 0 = 0 :=
  (aE v).roundOf_eq (by simp) (by rw [Frame.cum_succ, Frame.cum_zero]; exact Nat.zero_lt_succ _)

theorem aF_cum_low (v : ℕ → Option ℕ) : ∀ r, r ≤ 6 → (aF v).cum r = r := by
  intro r
  induction r with
  | zero => intro _; simp
  | succ j ih =>
      intro hj
      rw [Frame.cum_succ, ih (by omega), aF_width, aWid_low (show j < 6 by omega)]

/-- A round at or past `6` begins in epoch `2` or later, which is what
the width may read the verdicts of epoch `0` for. -/
theorem aE_two_le (v : ℕ → Option ℕ) {r : ℕ} (h : 6 ≤ r) :
    2 ≤ (aE v).roundOf ((aF v).cum r) := by
  refine (aE v).cum_le_iff_le_roundOf.mp ?_
  rw [aE_cum2]
  have := (aF v).cum_mono h
  rw [aF_cum_low v 6 (le_refl 6)] at this
  omega

/-- **A schedule adapted in both frames.** The leaders are round-robin
over the slots, so `pick_adapted` is `rfl`; the epoch lengths and the
widths read slot `0`'s verdict, and epoch `0` is two below every epoch
either is consulted for. -/
def aSched : Schedule (mysticetiRule (Validator := Fin 4) (BlockId := ℕ) (Payload := Unit)) where
  len := aLen
  len_pos := aLen_pos
  widthOf := aWid
  widthOf_pos := aWid_pos
  maxWidth := 2
  widthOf_le := aWid_le
  pick := fun _ _ _ k => ⟨k % 4, by omega⟩
  keyed := fun _ _ v r i j hi hj h => by
    have hi2 : i < 2 := lt_of_lt_of_le hi (aWid_le v r)
    have hj2 : j < 2 := lt_of_lt_of_le hj (aWid_le v r)
    have := congrArg Fin.val h
    simp only [Frame.index] at this
    omega
  len_adapted := fun v w e h => by
    unfold aLen
    by_cases he : e < 2
    · rw [if_pos he, if_pos he]
    · rw [if_neg he, if_neg he,
        h 0 (show (aE v).roundOf 0 + 2 ≤ e by rw [aE_roundOf_zero]; omega)]
  widthOf_adapted := fun v w r h => by
    unfold aWid
    by_cases hr : r < 6
    · rw [if_pos hr, if_pos hr]
    · rw [if_neg hr, if_neg hr,
        h 0 (show (aE v).roundOf 0 + 2 ≤ (aE v).roundOf ((aF v).cum r) by
          rw [aE_roundOf_zero]; exact aE_two_le v (by omega))]
  pick_adapted := fun _ _ _ _ _ _ _ => rfl

/-- **Both frames move with the verdicts.** -/
example : aSched.len (fun _ => none) 2 = 3 := rfl
example : aSched.len (fun _ => some 0) 2 = 4 := rfl
example : aSched.widthOf (fun _ => none) 6 = 1 := rfl
example : aSched.widthOf (fun _ => some 0) 6 = 2 := rfl

/-- **And the run is inhabited.** At height zero every clause is about an
epoch the run has not closed, so `ScheduleRun` is inhabited outright and
`ScheduleRun.agree` is not a theorem about an empty family. -/
def aRun (U : (mysticetiRule (Validator := Fin 4) (BlockId := ℕ)
      (Payload := Unit)).Universe) (V : View (Fin 4) ℕ Unit U) :
    ScheduleRun aSched U V 0 where
  vdct := fun _ => none
  closed := fun _ _ _ h => absurd h (by omega)

/-! ## A run above height zero

`aRun` closes no epoch, so its `closed` field says nothing. This section
closes one. The leaders are round-robin over `1, 2, 3`, all correct under
`Ugrow`'s fault model, so every slot commits; slot `0` therefore commits,
and the schedule reads that and takes its *wider* frames — epochs of four
slots past the second, rounds of two past the sixth.

The frame is named first and the verdicts read off it, and `bF_eq` is
what closes the circle: the schedule at those verdicts gives back that
frame.
-/

/-- Leaders `1, 2, 3` by slot, all correct. -/
abbrev bPick : ℕ → Fin 4 := fun k => ⟨k % 3 + 1, by omega⟩

theorem bPick_correct (k : ℕ) : bPick k ∈ (Correct : Finset (Fin 4)) := by
  have h : k % 3 = 0 ∨ k % 3 = 1 ∨ k % 3 = 2 := by omega
  have hv : bPick k = 1 ∨ bPick k = 2 ∨ bPick k = 3 := by
    rcases h with h | h | h
    · exact Or.inl (Fin.ext (by simp [h]))
    · exact Or.inr (Or.inl (Fin.ext (by simp [h])))
    · exact Or.inr (Or.inr (Fin.ext (by simp [h])))
  rcases hv with h | h | h <;> rw [h] <;> decide

/-- The frame the wider reading gives: one slot a round below `6`, two
after. -/
def bF : Frame where
  width := fun r => if r < 6 then 1 else 2
  width_pos := fun _ => by split <;> omega

@[simp] theorem bF_width (r : ℕ) : bF.width r = if r < 6 then 1 else 2 := rfl

theorem bF_cum_low : ∀ r, r ≤ 6 → bF.cum r = r := by
  intro r
  induction r with
  | zero => intro _; simp
  | succ j ih => intro hj; rw [Frame.cum_succ, ih (by omega), bF_width, if_pos (by omega)]

theorem bF_roundOf_low {g : ℕ} (h : g < 6) : bF.roundOf g = g :=
  bF.roundOf_eq (by rw [bF_cum_low _ (by omega)]) (by rw [bF_cum_low _ (by omega)]; omega)

/-- The assignment: position `i` of round `r` is led by that slot's
validator. -/
abbrev bAsg : ℕ → ℕ → Fin 4 := fun r i => bPick (bF.index r i)

/-- The verdicts: the block `Ugrow` puts at each slot's round under that
slot's leader. -/
noncomputable def bVdct : ℕ → Option ℕ := Composition.vdctOf bF bAsg

theorem bVdct_zero : bVdct 0 ≠ none := by
  rw [bVdct, Composition.vdctOf]
  exact Option.some_ne_none _

/-- **The schedule at these verdicts gives back this frame.** -/
theorem bF_eq (r : ℕ) : aWid bVdct r = bF.width r := by
  rw [aWid, bF_width]
  split
  · rfl
  · rw [if_neg bVdct_zero]

theorem bE_len (e : ℕ) : aLen bVdct e = if e < 2 then 3 else 4 := by
  rw [aLen]
  split
  · rfl
  · rw [if_neg bVdct_zero]

/-- Leaders `1, 2, 3` are distinct within a round of at most two slots. -/
theorem bPick_keyed (v : ℕ → Option ℕ) :
    ∀ r i j, i < aWid v r → j < aWid v r →
      bPick ((aF v).index r i) = bPick ((aF v).index r j) → i = j := by
  intro r i j hi hj h
  have hi2 : i < 2 := lt_of_lt_of_le hi (aWid_le v r)
  have hj2 : j < 2 := lt_of_lt_of_le hj (aWid_le v r)
  have := congrArg Fin.val h
  simp only [Frame.index] at this
  omega

/-- `aSched` with leaders that are always correct. -/
def bSched : Schedule (mysticetiRule (Validator := Fin 4) (BlockId := ℕ) (Payload := Unit)) where
  len := aLen
  len_pos := aLen_pos
  widthOf := aWid
  widthOf_pos := aWid_pos
  maxWidth := 2
  widthOf_le := aWid_le
  pick := fun _ _ _ k => bPick k
  keyed := fun _ _ v => bPick_keyed v
  len_adapted := aSched.len_adapted
  widthOf_adapted := aSched.widthOf_adapted
  pick_adapted := fun _ _ _ _ _ _ _ => rfl

@[simp] theorem bSched_frameOf (v : ℕ → Option ℕ) : bSched.frameOf v = aF v := rfl

@[simp] theorem bSched_epochFrame (v : ℕ → Option ℕ) : bSched.epochFrame v = aE v := rfl

/-- The epochs the wider reading gives: three slots each for the first
two, four after. -/
def bE : Frame where
  width := fun e => if e < 2 then 3 else 4
  width_pos := fun _ => by split <;> omega

@[simp] theorem bE_width (e : ℕ) : bE.width e = if e < 2 then 3 else 4 := rfl

/-- **The circle closes.** The schedule at these verdicts gives back the
two frames the verdicts were read off. -/
theorem aF_eq_bF : aF bVdct = bF := by
  show (⟨aWid bVdct, aWid_pos bVdct⟩ : Frame) = bF
  have h : aWid bVdct = bF.width := funext bF_eq
  simp only [h]

theorem aE_eq_bE : aE bVdct = bE := by
  show (⟨aLen bVdct, aLen_pos bVdct⟩ : Frame) = bE
  have h : aLen bVdct = bE.width := funext bE_len
  simp only [h]

theorem bE_cum2 : bE.cum 2 = 6 := by
  rw [Frame.cum_succ, Frame.cum_succ, Frame.cum_zero]
  rfl

theorem bE_cum1 : bE.cum 1 = 3 := by rw [Frame.cum_succ, Frame.cum_zero]; rfl

theorem bF_roundOf6 : bF.roundOf 6 = 6 :=
  bF.roundOf_eq (by rw [bF_cum_low 6 (le_refl 6)])
    (by rw [Frame.cum_succ, bF_cum_low 6 (le_refl 6), bF_width, if_neg (by omega)]; omega)

/-- **A run that closes two epochs.** Epochs `0` and `1` hold slots `0`
to `5`, each at its own round, and each is decided below the round its
own window ends at — which is round `6` or later, since a window reaches
two epochs and epoch `2` begins at slot `6`. -/
noncomputable def bRun : ScheduleRun bSched (Ugrow Composition.N)
    (View.full (Ugrow Composition.N)) 2 where
  vdct := bVdct
  closed := fun r i hi hep => by
    have hasg : bSched.asgOf bVdct (Ugrow Composition.N) (View.full (Ugrow Composition.N))
        = fun r' i' => bPick (bF.index r' i') := by
      funext r' i'
      show bPick ((aF bVdct).index r' i') = bPick (bF.index r' i')
      rw [aF_eq_bF]
    simp only [bSched_frameOf, bSched_epochFrame, aF_eq_bF, aE_eq_bE, hasg] at hi hep ⊢
    have hlt : bF.index r i < 6 := by
      have := (Adaptive.roundOf_lt_iff (E := bE) (g := bF.index r i) (e := 2)).mp hep
      rwa [bE_cum2] at this
    have hr6 : r < 6 := by
      by_contra hc
      have h6 : bF.cum 6 ≤ bF.cum r := bF.cum_mono (by omega)
      rw [bF_cum_low 6 (le_refl 6)] at h6
      have : bF.cum r ≤ bF.index r i := by rw [Frame.index]; omega
      omega
    have hwr : bF.width r = 1 := by rw [bF_width, if_pos hr6]
    have hi' : i < bF.width r := hi
    have hi0 : i = 0 := by rw [hwr] at hi'; omega
    subst hi0
    have hidx : bF.index r 0 = r := by
      rw [Frame.index, bF_cum_low r (show r ≤ 6 by omega)]
      omega
    rw [hidx]
    have hbnd : 6 ≤ bF.roundOf (bE.cum (bE.roundOf r + 2)) := by
      have h1 : bE.cum 2 ≤ bE.cum (bE.roundOf r + 2) := bE.cum_mono (by omega)
      rw [bE_cum2] at h1
      have h2 := bF.roundOf_mono h1
      rwa [bF_roundOf6] at h2
    have hv : bVdct r = some (4 * r + (bPick r).val) := by
      show Composition.vdctOf bF bAsg r = _
      rw [Composition.vdctOf, bF_roundOf_low (show r < 6 by omega),
        bF_cum_low r (show r ≤ 6 by omega), Nat.sub_self]
      show some (4 * r + (bPick (bF.index r 0)).val) = _
      rw [hidx]
    rw [hv]
    have hfin := Composition.decidedFrameBelow_of_asg (F := bF)
      (asg := fun r' i' => bPick (bF.index r' i')) (r := r) (i := 0)
      (B := bF.roundOf (bE.cum (bE.roundOf r + 2)))
      (by rw [hwr]; omega) (by omega) (show r + 2 ≤ 24 by omega)
      (bPick_correct _)
    rw [hidx] at hfin
    exact hfin

/-! ## Liveness, applied

`commits_in_epoch` asks two things of the world: that the schedule places
a stretch of reliable slots in every epoch, and that the rule is live
where it reads. `bSched` gives the first outright — its leaders are `1`,
`2`, `3` and its epochs never fall below three slots — and `Ugrow` gives
the second, being synchronised from round `0` and populated to its
height.
-/

theorem aLen_ge (v : ℕ → Option ℕ) (e : ℕ) : 3 ≤ aLen v e := by
  unfold aLen; split
  · omega
  · split <;> omega

/-- **The fairness clause, on the data.** Every epoch of `bSched` holds
at least three slots and every slot is led by a correct validator, so the
first three slots of each epoch are the stretch. -/
theorem bSched_placesRunsIn (U : (mysticetiRule (Validator := Fin 4) (BlockId := ℕ)
      (Payload := Unit)).Universe) (V : View (Fin 4) ℕ Unit U) :
    PlacesRunsIn bSched U V (Correct : Finset (Fin 4)) 3 := by
  intro v e
  refine ⟨(bSched.epochFrame v).cum (e + 1), le_refl _, ?_, fun i _ => bPick_correct _⟩
  have hs : (bSched.epochFrame v).cum (e + 2)
      = (bSched.epochFrame v).cum (e + 1) + aLen v (e + 1) := by
    have he : e + 2 = (e + 1) + 1 := by omega
    rw [he, Frame.cum_succ]
    rfl
  have := aLen_ge v (e + 1)
  omega

/-- **The rule is live where the run reads**, from `Ugrow`'s synchrony
and its populated rounds. -/
theorem bRun_certLive : MysticetiProperties.certLive bRun.sched
    (View.full (Ugrow Composition.N)) (Correct : Finset (Fin 4))
    ((bSched.epochFrame bRun.vdct).cum 1) ((bSched.epochFrame bRun.vdct).cum 2) :=
  MysticetiProperties.certLive_of_coreLive
    (MysticetiProperties.coreLive_of (R₀ := 0) (N := Composition.N) card_correct
      (ugrow_synchronised Composition.N) (Nat.zero_le _)
      (fun _ _ hr => ugrow_populated hr) (View.coversUpto_full _ _)
      (fun k hk => by
        have h1 : bRun.sched.slotRound k = (bSched.frameOf bRun.vdct).roundOf k := rfl
        have h2 : (bSched.frameOf bRun.vdct).roundOf k ≤ k :=
          Composition.frame_roundOf_le _ k
        have h3 : (bSched.epochFrame bRun.vdct).cum 2 = 6 := by
          simp only [bSched_epochFrame, aE_eq_bE]; exact bE_cum2
        rw [h1]
        show (bSched.frameOf bRun.vdct).roundOf k + 2 ≤ 24
        omega))

/-- **Liveness on the data.** Epoch `1` of `bRun` carries three
consecutive commits. -/
theorem bRun_commits_in_epoch :
    ∃ b, (bSched.epochFrame bRun.vdct).cum 1 ≤ b ∧
      b + 3 ≤ (bSched.epochFrame bRun.vdct).cum 2 ∧
      ∀ i, i < 3 → ∃ L, bRun.vdct (b + i) = some L :=
  ScheduleRun.commits_in_epoch MysticetiProperties.leaderCommits_cert
    MysticetiProperties.agree bRun
    (bSched_placesRunsIn (Ugrow Composition.N) (View.full (Ugrow Composition.N)))
    0 (by omega) bRun_certLive

/-! ## Conservativity on the data

`cSched` is the arc where neither frame moves: epochs of three slots,
one leader a round, on the rotation. Its numbering is the identity and
its safety statement is §13.3's.
-/

/-- The schedule that reads nothing and runs one leader a round. -/
noncomputable def cSched : Schedule (mysticetiRule (Validator := Fin 4)
    (BlockId := ℕ) (Payload := Unit)) :=
  Schedule.ofFixed (constFrame 3 (by omega)) (constFrame 1 Nat.one_pos) 1
    (fun _ => le_refl 1) (fun r _ => bPick r)
    (fun r i j hi hj _ => by
      have hi' : i < 1 := hi
      have hj' : j < 1 := hj
      omega)

/-- **The numbering is the base one.** -/
example (U : (mysticetiRule (Validator := Fin 4) (BlockId := ℕ) (Payload := Unit)).Universe)
    (V : View (Fin 4) ℕ Unit U) (Rn : ScheduleRun cSched U V 0) (k : ℕ) :
    Rn.sched.slotRound k = k := ScheduleRun.ofFixed_slotRound Rn k

example (U : (mysticetiRule (Validator := Fin 4) (BlockId := ℕ) (Payload := Unit)).Universe)
    (V : View (Fin 4) ℕ Unit U) (Rn : ScheduleRun cSched U V 0) (k : ℕ) :
    Rn.sched.leader k = bPick k := ScheduleRun.ofFixed_leader Rn k

/-- **And the safety statement is the fixed arc's**, at `epochOf 3` and
with no frame in it. -/
example (U : (mysticetiRule (Validator := Fin 4) (BlockId := ℕ) (Payload := Unit)).Universe)
    (V V' : View (Fin 4) ℕ Unit U) (H : ℕ)
    (Rn : ScheduleRun cSched U V H) (Rn' : ScheduleRun cSched U V' H) :
    ∀ g, epochOf 3 g < H → Rn.vdct g = Rn'.vdct g :=
  ScheduleRun.agree_const MysticetiProperties.agree (by omega) Rn Rn'

end ScheduleModel

end LeanDagTest
