import LeanDagTest.Mysticeti.Growth
import LeanDag.Integration.CompRun
/-!
# A composed run past height zero

`Composed.genesis` inhabits the composed structure at height `0`, where
every clause is about a configuration the run does not have. This file
carries one that does: a configuration that closes, an anchor that a
decision backs, and an epoch every slot of which is decided.

The universe is `Ugrow`, whose height is a parameter, because the
composition's window spans two epochs and the fixed `Fin n` models of
`LeanDagTest` run out of rounds before it closes. The frame is one slot
per round, so the schedule's slot `k` sits at round `k` and the leader is
validator `1`, which is correct under `Ugrow`'s fault model.
-/

namespace LeanDagTest
namespace Composition

open LeanDag LeanDag.Integration LeanDag.Barnacle

/-- The rule: Mysticeti's carrier over an unbounded block type. -/
abbrev gRule : Properties.DagRule (Fin 4) ℕ Unit :=
  MysticetiProperties.mysticetiRule

/-- Rounds `0 … 12`, four blocks each. -/
abbrev N : ℕ := 12

/-- One round past the threshold, four rounds to an epoch, and a gap of
`2 * W` rounds between an anchor and the configuration it sets. -/
def cP : Params := ⟨1, 4, 96, 100, 8, by decide, by decide⟩

/-- The epoch width. -/
abbrev W : ℕ := 4

/-- One slot per round. -/
noncomputable abbrev cF : Frame := constFrame 1 Nat.one_pos

/-- Validator `1` leads every slot; it is not Byzantine. -/
abbrev cAsg : ℕ → ℕ → Fin 4 := fun _ _ => 1

/-- The verdict at slot `k` is validator `1`'s block of round `k`. -/
abbrev cVdct : ℕ → Option ℕ := fun k => some (4 * k + 1)

theorem cF_width (r : ℕ) : cF.width r = 1 := rfl

/-- A frame one slot wide below `B` counts slots the same way there. -/
theorem cum_eq_of_thin {F' : Frame} {B : ℕ} (hw : ∀ r, r < B → F'.width r = 1) :
    ∀ r, r ≤ B → F'.cum r = r := by
  intro r
  induction r with
  | zero => intro _; simp
  | succ j ih =>
      intro hj
      rw [Frame.cum_succ, ih (by omega), hw j (by omega)]

/-- And so it puts slot `k` at round `k`. -/
theorem roundOf_eq_of_thin {F' : Frame} {B : ℕ} (hw : ∀ r, r < B → F'.width r = 1)
    {k : ℕ} (hk : k < B) : F'.roundOf k = k :=
  F'.roundOf_eq (by rw [cum_eq_of_thin hw k (by omega)])
    (by rw [cum_eq_of_thin hw (k + 1) (by omega)]; omega)

/-- **The candidate a slot of `Ugrow` has is the one the layout names.**
`Ugrow` puts validator `v`'s round-`r` block at `4 * r + v`, so a leader
block for a slot at round `r` under validator `1` can only be `4 * r + 1`. -/
theorem leaderBlock_eq {S : Slots (Fin 4)} {k r L : ℕ} {v : Fin 4}
    (h : IsLeaderBlock (S := S) (Ugrow N) k L)
    (hr : S.slotRound k = r) (hl : S.leader k = v) : L = 4 * r + v.val := by
  obtain ⟨_, hround, hcreator⟩ := h
  rw [hr] at hround
  rw [hl] at hcreator
  simp only [ugrow_block, rrBlock_round] at hround
  have hm : L % 4 = v.val := by
    have := congrArg Fin.val hcreator
    simpa [rrBlock] using this
  have : v.val < 4 := v.isLt
  omega

/-- **A slot is decided at the round its schedule puts it at**, provided
the certificate rounds fit under `Ugrow`'s height and the leader is
correct. The block is the one `Ugrow`'s layout puts at that round under
that validator. -/
theorem decided_of_round {F' : Frame} {a' : ℕ → ℕ → Fin 4}
    (hk' : ∀ r i j, i < F'.width r → j < F'.width r → a' r i = a' r j → i = j)
    {g r : ℕ} {v : Fin 4} (hround : F'.roundOf g = r) (hN : r + 2 ≤ N)
    (hlead : (F'.toSlots a' hk').leader g = v)
    (hv : v ∈ (Correct : Finset (Fin 4))) :
    gRule.Decided (F'.toSlots a' hk') (View.full (Ugrow N)) g (some (4 * r + v.val)) := by
  have hsr : (F'.toSlots a' hk').slotRound g = r := hround
  obtain ⟨L, hLB, hdec⟩ :=
    decided_of_correct_leader (S := F'.toSlots a' hk') (R := 0)
      (ugrow_synchronised N) (Nat.zero_le _)
      (ugrow_populated (by rw [hsr]; omega))
      (ugrow_populated (by rw [hsr]; omega))
      (ugrow_populated (by rw [hsr]; omega))
      (by rw [hlead]; exact hv)
  rw [leaderBlock_eq hLB hsr hlead] at hdec
  exact hdec

/-- **What a frame owes for one of its slots.** The round is the frame's
own and the leader the assignment's, and both survive any schedule that
agrees with the frame below the bound. -/
theorem decidedFrameBelow_of_asg {F : Frame} {asg : ℕ → ℕ → Fin 4} {B r i : ℕ}
    (hi : i < F.width r) (hrB : r < B) (hN : r + 2 ≤ N)
    (hv : asg r i ∈ (Correct : Finset (Fin 4))) :
    Properties.DecidedFrameBelow gRule F asg B (View.full (Ugrow N)) (F.index r i)
      (some (4 * r + (asg r i).val)) := by
  intro F' a' hk' hw ha
  have hcum : F'.cum r = F.cum r := Frame.cum_congr hw (le_of_lt hrB)
  have hwid : F'.width r = F.width r := hw r hrB
  have hidx : F'.index r i = F.index r i := by rw [Frame.index, Frame.index, hcum]
  have hround : F'.roundOf (F.index r i) = r := by
    rw [← hidx]; exact F'.roundOf_index (by rw [hwid]; exact hi)
  refine decided_of_round hk' hround hN ?_ hv
  change a' (F'.roundOf (F.index r i)) (F.index r i - F'.cum (F'.roundOf (F.index r i)))
      = asg r i
  rw [hround, hcum, Frame.index, Nat.add_sub_cancel_left]
  exact ha r i hrB hi

/-- The verdict a frame and an assignment name at every slot: the block
`Ugrow` puts at that slot's round under that slot's leader. -/
noncomputable def vdctOf (F : Frame) (asg : ℕ → ℕ → Fin 4) (g : ℕ) : Option ℕ :=
  some (4 * F.roundOf g + (asg (F.roundOf g) (g - F.cum (F.roundOf g))).val)

@[simp] theorem vdctOf_index {F : Frame} {asg : ℕ → ℕ → Fin 4} {r i : ℕ}
    (hi : i < F.width r) :
    vdctOf F asg (F.index r i) = some (4 * r + (asg r i).val) := by
  rw [vdctOf, F.roundOf_index hi, Frame.index, Nat.add_sub_cancel_left]

/-- The leader a frame's own schedule reports is the assignment's. -/
theorem pickOf_index {F : Frame} {asg : ℕ → ℕ → Fin 4} {r i : ℕ} (hi : i < F.width r) :
    asg (F.roundOf (F.index r i)) (F.index r i - F.cum (F.roundOf (F.index r i))) = asg r i := by
  rw [F.roundOf_index hi, Frame.index, Nat.add_sub_cancel_left]

/-- **Every slot below the horizon is decided.** The schedule is any that
agrees with the run's below the window's end; the three certificate
rounds fit under `Ugrow`'s height, and the leader is correct. -/
theorem decided_below {B k : ℕ} (hB : k + 2 ≤ N) (hk : k < B) (_hB' : B ≤ N)
    {F' : Frame} {a' : ℕ → ℕ → Fin 4}
    (hk' : ∀ r i j, i < F'.width r → j < F'.width r → a' r i = a' r j → i = j)
    (hw : ∀ r, r < B → F'.width r = 1) (ha : ∀ r, r < B → a' r 0 = 1) :
    gRule.Decided (F'.toSlots a' hk') (View.full (Ugrow N)) k (cVdct k) := by
  have hround : (F'.toSlots a' hk').slotRound k = k := roundOf_eq_of_thin hw hk
  have hlead : (F'.toSlots a' hk').leader k = 1 := by
    change a' (F'.roundOf k) (k - F'.cum (F'.roundOf k)) = 1
    rw [roundOf_eq_of_thin hw hk, cum_eq_of_thin hw k (by omega), Nat.sub_self]
    exact ha k hk
  obtain ⟨L, hLB, hdec⟩ :=
    decided_of_correct_leader (S := F'.toSlots a' hk') (R := 0)
      (ugrow_synchronised N) (Nat.zero_le _)
      (ugrow_populated (by rw [hround]; omega))
      (ugrow_populated (by rw [hround]; omega))
      (ugrow_populated (by rw [hround]; omega))
      (by rw [hlead]; decide)
  have : L = 4 * k + 1 := leaderBlock_eq hLB hround hlead
  rw [this] at hdec
  exact hdec

/-- **A composed run of height one.** Configuration `0` closes at slot
`2`, which is the least committed slot at or past its threshold; the
next configuration begins `P.gap` rounds later, at round `10`. Epoch `0`
is closed: each of its four slots is decided by the schedule below the
round its window ends at. -/
noncomputable def cRun :
    Composed (R := gRule) W cP (fun _ _ _ _ => 1) (fun _ _ _ _ _ => (1, 0))
      (Ugrow N) (View.full (Ugrow N)) 1 1 where
  start := fun k => if k = 0 then 0 else 10
  count := fun _ => 1
  backoff := fun _ => 0
  anchor := fun _ => 2
  F := cF
  vdct := cVdct
  asg := cAsg
  init := ⟨rfl, rfl, rfl⟩
  count_pos := fun _ => Nat.one_pos
  count_le := fun _ => (by decide : (1 : ℕ) ≤ 4)
  cnt_le := fun _ => (by decide : (1 : ℕ) ≤ 4)
  cnt_zero := rfl
  cnt_eq := fun _ _ _ _ _ => rfl
  anchor_commits := fun k hk => by
    have hk0 : k = 0 := by omega
    subst hk0
    refine ⟨⟨9, rfl⟩, ?_⟩
    norm_num [cP, constFrame_cum]
  anchor_least := fun k hk g hg hlt => by
    have hk0 : k = 0 := by omega
    subst hk0
    norm_num [cP, constFrame_cum] at hg
    omega
  start_succ := fun k hk => by
    have hk0 : k = 0 := by omega
    subst hk0
    norm_num [cP, constFrame_roundOf]
  update := fun k hk _ _ => by
    have hk0 : k = 0 := by omega
    subst hk0
    rfl
  anchor_closed := fun _ _ => by decide
  keyed := fun _ i j hi hj _ => by
    have hi' : i < 1 := hi
    have hj' : j < 1 := hj
    omega
  coherent := fun _ _ _ _ => rfl
  closed := fun r i hi hep => by
    have hi' : i = 0 := by have : i < 1 := hi; omega
    subst hi'
    have hidx : cF.index r 0 = r := by simp [Frame.index, constFrame_cum]
    rw [hidx] at hep ⊢
    have hr : r < 4 := by simpa [epochOf] using hep
    have hep0 : epochOf W r = 0 := Nat.div_eq_of_lt hr
    have hB : cF.roundOf (W * (epochOf W r + 2)) = 8 := by
      rw [hep0]; change cF.roundOf 8 = 8; rw [constFrame_roundOf]
    rw [hB]
    exact fun F' a' hk' hw ha =>
      decided_below (show r + 2 ≤ 12 by omega) (show r < 8 by omega)
        (show (8 : ℕ) ≤ 12 by omega) hk'
        (fun r' hr' => hw r' hr') (fun r' hr' => ha r' 0 hr' Nat.one_pos)

/-- The run has reached its horizon, which is what `Composed.every_height`
consumes: two epochs of slots sit below the round configuration `1`
starts at. -/
theorem cRun_horizon : W * (1 + 1) ≤ cRun.F.cum (cRun.start 1) := by
  change (8 : ℕ) ≤ cF.cum 10
  rw [constFrame_cum]; omega

/-- The anchor is decided, at the block the verdict names, by the run's
own schedule. -/
example : gRule.Decided (cF.toSlots cAsg cRun.keyed) (View.full (Ugrow N)) 2 (some 9) :=
  Composed.decided_self cRun (r := 2) (i := 0) Nat.one_pos (by decide)

example : cRun.anchor 0 = 2 := rfl
example : cRun.start 1 = 10 := rfl
example : cRun.F.width 0 = 1 := rfl

/-! ## Several epochs, and the configuration turning twice

`cRun` and `wRun` close one configuration and one epoch. `mRun` closes
two configurations and five epochs, with the count moving between them:
configuration `0` runs at one leader a round, configuration `1` at two,
and the epochs the run decides straddle the round the change takes effect
at.

The verdicts and the policy are read off the frame rather than written
out — `vdctOf` names the block `Ugrow` puts at a slot's round under that
slot's leader, and the policy hands back the frame's own leader — so
`coherent` and the shape of `closed` hold with no case analysis. What is
left to check by cases is which round each slot of a closed epoch sits
at, and that is `mF_bound`.
-/

/-- One slot per round up to `6`, two after: the width configuration `1`
sets, which takes effect inside the range of epochs the run closes. -/
def mF : Frame where
  width := fun r => if r ≤ 6 then 1 else 2
  width_pos := fun r => by split <;> omega

/-- Two slots to an epoch, and a gap of `2 * W` rounds. -/
def mP : Params := ⟨1, 4, 96, 100, 4, by decide, by decide⟩

/-- The epoch width. -/
abbrev mW : ℕ := 2

/-- Validator `1` leads the first slot of a round, validator `2` the
second. Both are correct. -/
abbrev mAsg : ℕ → ℕ → Fin 4 := fun _ i => if i = 0 then 1 else 2

theorem mAsg_correct (r i : ℕ) : mAsg r i ∈ (Correct : Finset (Fin 4)) := by
  change (if i = 0 then (1 : Fin 4) else 2) ∈ _
  split <;> decide

theorem mF_width_low {r : ℕ} (h : r ≤ 6) : mF.width r = 1 := if_pos h

theorem mF_width_le (r : ℕ) : mF.width r ≤ 2 := by
  change (if r ≤ 6 then 1 else 2) ≤ 2; split <;> omega

theorem mF_cum_low {r : ℕ} (h : r ≤ 7) : mF.cum r = r :=
  cum_eq_of_thin (B := 7) (fun r' hr' => mF_width_low (by omega)) r h

theorem mF_cum8 : mF.cum 8 = 9 := by
  rw [Frame.cum_succ, mF_cum_low (le_refl 7)]; rfl

theorem mF_cum9 : mF.cum 9 = 11 := by rw [Frame.cum_succ, mF_cum8]; rfl

theorem mF_cum10 : mF.cum 10 = 13 := by rw [Frame.cum_succ, mF_cum9]; rfl

theorem mF_cum12 : mF.cum 12 = 17 := by
  rw [Frame.cum_succ, Frame.cum_succ, mF_cum10]; rfl

theorem mF_roundOf_low {g : ℕ} (h : g ≤ 6) : mF.roundOf g = g :=
  mF.roundOf_eq (by rw [mF_cum_low (by omega)]) (by rw [mF_cum_low (by omega)]; omega)

theorem mF_roundOf8 : mF.roundOf 8 = 7 :=
  mF.roundOf_eq (by rw [mF_cum_low (by omega)]; omega) (by rw [mF_cum8]; omega)

theorem mF_roundOf9 : mF.roundOf 9 = 8 :=
  mF.roundOf_eq (by rw [mF_cum8]) (by rw [mF_cum9]; omega)

theorem mF_roundOf10 : mF.roundOf 10 = 8 :=
  mF.roundOf_eq (by rw [mF_cum8]; omega) (by rw [mF_cum9]; omega)

theorem mF_roundOf12 : mF.roundOf 12 = 9 :=
  mF.roundOf_eq (by rw [mF_cum9]; omega) (by rw [mF_cum10]; omega)

/-- **Where the slots of a closed epoch sit.** Every slot below `10` is
at a round below the one its epoch's window ends at, and low enough that
`Ugrow` holds its three certificate rounds. -/
theorem mF_bound {r i : ℕ} (hi : i < mF.width r) (hlt : mF.index r i < 10) :
    r + 2 ≤ N ∧ r < mF.roundOf (mW * (epochOf mW (mF.index r i) + 2)) := by
  have hr8 : r ≤ 8 := by
    by_contra hc
    have h1 : mF.cum 9 ≤ mF.cum r := mF.cum_mono (by omega)
    rw [mF_cum9] at h1
    have : mF.cum r + i < 10 := hlt
    omega
  have hthin : ∀ r' : ℕ, r' ≤ 6 → i = 0 → mF.index r' i = r' := by
    intro r' h hi0; rw [hi0, Frame.index, mF_cum_low (by omega)]; omega
  have hcases : r = 0 ∨ r = 1 ∨ r = 2 ∨ r = 3 ∨ r = 4 ∨ r = 5 ∨ r = 6 ∨ r = 7 ∨ r = 8 := by
    omega
  have hN : r + 2 ≤ N := by change r + 2 ≤ 12; omega
  refine ⟨hN, ?_⟩
  clear hN
  rcases hcases with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
  all_goals try
    (have hi0 : i = 0 := by rw [mF_width_low (by omega)] at hi; omega
     rw [hthin _ (by omega) hi0])
  · change (0 : ℕ) < mF.roundOf 4; rw [mF_roundOf_low (by omega)]; omega
  · change (1 : ℕ) < mF.roundOf 4; rw [mF_roundOf_low (by omega)]; omega
  · change (2 : ℕ) < mF.roundOf 6; rw [mF_roundOf_low (by omega)]; omega
  · change (3 : ℕ) < mF.roundOf 6; rw [mF_roundOf_low (by omega)]; omega
  · change (4 : ℕ) < mF.roundOf 8; rw [mF_roundOf8]; omega
  · change (5 : ℕ) < mF.roundOf 8; rw [mF_roundOf8]; omega
  · change (6 : ℕ) < mF.roundOf 10; rw [mF_roundOf10]; omega
  · -- round 7 holds two slots, in epochs 3 and 4
    have hi2 : i < 2 := lt_of_lt_of_le hi (mF_width_le 7)
    have h7 : mF.index 7 i = 7 + i := by rw [Frame.index, mF_cum_low (by omega)]
    rw [h7]
    have : i = 0 ∨ i = 1 := by omega
    rcases this with rfl|rfl
    · change (7 : ℕ) < mF.roundOf 10; rw [mF_roundOf10]; omega
    · change (7 : ℕ) < mF.roundOf 12; rw [mF_roundOf12]; omega
  · -- round 8: only its first slot is below the horizon
    have h8 : mF.index 8 i = 9 + i := by rw [Frame.index, mF_cum8]
    rw [h8] at hlt ⊢
    have hi0 : i = 0 := by omega
    subst hi0
    change (8 : ℕ) < mF.roundOf 12; rw [mF_roundOf12]; omega

/-- **A composed run of height two, over five epochs.** Configuration `0`
runs at one leader a round and closes at slot `2`; configuration `1` runs
at two, closes at slot `9`, and sets the width from round `7` on.
Epochs `0` to `4` are all closed, and they straddle round `7`: epoch `3`
holds a slot of a one-leader round and a slot of a two-leader one.

The policy hands back the frame's own leader, so `coherent` holds
wherever the frame does. -/
noncomputable def mRun :
    Composed (R := gRule) mW mP
      (fun _ _ _ g => mAsg (mF.roundOf g) (g - mF.cum (mF.roundOf g)))
      (fun _ _ _ _ _ => (2, 0))
      (Ugrow N) (View.full (Ugrow N)) 2 5 where
  start := fun k => if k = 0 then 0 else if k = 1 then 6 else 12
  count := fun k => if k = 0 then 1 else 2
  backoff := fun _ => 0
  anchor := fun k => if k = 0 then 2 else 9
  F := mF
  vdct := vdctOf mF mAsg
  asg := mAsg
  init := ⟨rfl, rfl, rfl⟩
  count_pos := fun _ => by split <;> omega
  count_le := fun _ => by split <;> decide
  cnt_le := fun r => le_trans (mF_width_le r) (by decide)
  cnt_zero := rfl
  cnt_eq := fun k hk r hlo hhi => by
    have hk2 : k = 0 ∨ k = 1 := by omega
    rcases hk2 with rfl | rfl
    · have h6 : r ≤ 6 := hhi
      rw [mF_width_low h6]; rfl
    · have h7 : 6 < r := hlo
      change (if r ≤ 6 then 1 else 2) = 2
      rw [if_neg (by omega)]
  anchor_commits := fun k hk => by
    have hk2 : k = 0 ∨ k = 1 := by omega
    rcases hk2 with rfl | rfl
    · exact ⟨⟨_, rfl⟩, by change mF.cum 2 ≤ 2; rw [mF_cum_low (by omega)]⟩
    · exact ⟨⟨_, rfl⟩, by change mF.cum 8 ≤ 9; rw [mF_cum8]⟩
  anchor_least := fun k hk g hg hlt => by
    have hk2 : k = 0 ∨ k = 1 := by omega
    rcases hk2 with rfl | rfl
    · have h : mF.cum 2 ≤ g := hg
      rw [mF_cum_low (by omega)] at h
      have : g < 2 := hlt
      omega
    · have h : mF.cum 8 ≤ g := hg
      rw [mF_cum8] at h
      have : g < 9 := hlt
      omega
  start_succ := fun k hk => by
    have hk2 : k = 0 ∨ k = 1 := by omega
    rcases hk2 with rfl | rfl
    · change (6 : ℕ) = mF.roundOf 2 + mP.gap
      rw [mF_roundOf_low (by omega)]; rfl
    · change (12 : ℕ) = mF.roundOf 9 + mP.gap
      rw [mF_roundOf9]; rfl
  update := fun k hk _ _ => by
    have hk2 : k = 0 ∨ k = 1 := by omega
    rcases hk2 with rfl | rfl <;> rfl
  anchor_closed := fun k hk => by
    have hk2 : k = 0 ∨ k = 1 := by omega
    rcases hk2 with rfl | rfl <;> decide
  keyed := fun r i j hi hj h => by
    have hi' : i < 2 := lt_of_lt_of_le hi (mF_width_le r)
    have hj' : j < 2 := lt_of_lt_of_le hj (mF_width_le r)
    by_cases h0 : i = 0 <;> by_cases h1 : j = 0
    · omega
    · exact absurd h (by simp [mAsg, h0, h1])
    · exact absurd h (by simp [mAsg, h0, h1])
    · omega
  coherent := fun r i hi _ => (pickOf_index hi).symm
  closed := fun r i hi hep => by
    have hlt : mF.index r i < 10 := by
      have : mF.index r i / 2 < 5 := hep
      omega
    obtain ⟨hN, hrB⟩ := mF_bound hi hlt
    rw [vdctOf_index hi]
    exact decidedFrameBelow_of_asg hi hrB hN (mAsg_correct r i)

/-- Two configurations closed, five epochs closed, and the count moving
between them. -/
example : mRun.count 0 = 1 := rfl
example : mRun.count 1 = 2 := rfl
example : mRun.F.width 6 = 1 := rfl
example : mRun.F.width 7 = 2 := rfl
example : mRun.anchor 0 = 2 := rfl
example : mRun.anchor 1 = 9 := rfl
example : mRun.start 1 = 6 := rfl
example : mRun.start 2 = 12 := rfl

/-- Epoch `3` straddles the width change: slot `6` is the only slot of
round `6`, and slot `7` is the first of two at round `7`. -/
example : mF.index 6 0 = 6 := by rw [Frame.index, mF_cum_low (by omega)]
example : mF.index 7 1 = 8 := by rw [Frame.index, mF_cum_low (by omega)]

/-- Both slots of round `7` are decided, under two different validators. -/
example : gRule.Decided (mF.toSlots mAsg mRun.keyed) (View.full (Ugrow N)) 7
    (some 29) := Composed.decided_self mRun (r := 7) (i := 0) (by decide) (by decide)

example : gRule.Decided (mF.toSlots mAsg mRun.keyed) (View.full (Ugrow N)) 8
    (some 30) := Composed.decided_self mRun (r := 7) (i := 1) (by decide) (by decide)

/-- And it has reached its horizon, so `Composed.every_height` applies. -/
theorem mRun_horizon : mW * (5 + 1) ≤ mRun.F.cum (mRun.start 2) := by
  change (12 : ℕ) ≤ mF.cum 12
  rw [mF_cum12]; omega

end Composition
end LeanDagTest
