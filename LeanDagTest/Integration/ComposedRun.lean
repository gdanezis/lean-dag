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
theorem leaderBlock_eq {S : Slots (Fin 4)} {k r L : ℕ}
    (h : IsLeaderBlock (S := S) (Ugrow N) k L)
    (hr : S.slotRound k = r) (hl : S.leader k = 1) : L = 4 * r + 1 := by
  obtain ⟨_, hround, hcreator⟩ := h
  rw [hr] at hround
  rw [hl] at hcreator
  simp only [ugrow_block, rrBlock_round] at hround
  have hm : L % 4 = 1 := by
    have := congrArg Fin.val hcreator
    simpa [rrBlock] using this
  omega

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

/-! ## A run whose count moves

`cRun` is one slot wide throughout, so nothing in it exercises the
mechanism Barnacle contributes. `wRun` is the same run with `upd`
returning two: rounds past `10`, where configuration `1` is in force, are
two slots wide, and the assignment there names two different validators.
-/

/-- One slot per round up to `10`, two after: the width configuration `1`
sets. -/
def wF : Frame where
  width := fun r => if r ≤ 10 then 1 else 2
  width_pos := fun r => by split <;> omega

theorem wF_width_low {r : ℕ} (h : r ≤ 10) : wF.width r = 1 := if_pos h

theorem wF_width_le (r : ℕ) : wF.width r ≤ 2 := by
  change (if r ≤ 10 then 1 else 2) ≤ 2; split <;> omega

theorem wF_cum {r : ℕ} (h : r ≤ 11) : wF.cum r = r :=
  cum_eq_of_thin (B := 11) (fun r' hr' => wF_width_low (by omega)) r h

theorem wF_roundOf {k : ℕ} (h : k < 11) : wF.roundOf k = k :=
  roundOf_eq_of_thin (B := 11) (fun r' hr' => wF_width_low (by omega)) h

/-- **Below slot `11` the frame is still thin**, so a slot there is its
own round's only slot, and its index is that round. -/
theorem wF_low {r i : ℕ} (hi : i < wF.width r) (h : wF.index r i < 11) :
    i = 0 ∧ wF.index r i = r := by
  have hr : r ≤ 10 := by
    by_contra hc
    have : wF.cum 11 ≤ wF.cum r := wF.cum_mono (by omega)
    rw [wF_cum (le_refl 11)] at this
    have : wF.cum r + i < 11 := h
    omega
  rw [wF_width_low hr] at hi
  have hi0 : i = 0 := by omega
  subst hi0
  exact ⟨rfl, by rw [Frame.index, wF_cum (by omega)]; omega⟩

/-- Validator `1` leads the first slot of a round, validator `2` the
second. -/
abbrev wAsg : ℕ → ℕ → Fin 4 := fun _ i => if i = 0 then 1 else 2

/-- **A composed run whose count moves.** Configuration `0` runs at one
leader a round and closes at slot `2`; configuration `1` runs at two, so
every round past `10` holds two slots under two different validators.
Epoch `0` still closes, because it lies below the round the new count
takes effect at — which is what `Params.gap` is for. -/
noncomputable def wRun :
    Composed (R := gRule) W cP (fun _ _ _ _ => 1) (fun _ _ _ _ _ => (2, 0))
      (Ugrow N) (View.full (Ugrow N)) 1 1 where
  start := fun k => if k = 0 then 0 else 10
  count := fun k => if k = 0 then 1 else 2
  backoff := fun _ => 0
  anchor := fun _ => 2
  F := wF
  vdct := cVdct
  asg := wAsg
  init := ⟨rfl, rfl, rfl⟩
  count_pos := fun _ => by split <;> omega
  count_le := fun _ => by split <;> decide
  cnt_le := fun r => le_trans (wF_width_le r) (by decide)
  cnt_zero := rfl
  cnt_eq := fun k hk r hlo hhi => by
    have hk0 : k = 0 := by omega
    subst hk0
    have hr : r ≤ 10 := hhi
    rw [wF_width_low hr]
    rfl
  anchor_commits := fun k hk => by
    have hk0 : k = 0 := by omega
    subst hk0
    refine ⟨⟨9, rfl⟩, ?_⟩
    change wF.cum (0 + cP.interval + 1) ≤ 2
    rw [show 0 + cP.interval + 1 = 2 from rfl, wF_cum (by omega)]
  anchor_least := fun k hk g hg hlt => by
    have hk0 : k = 0 := by omega
    subst hk0
    have : wF.cum 2 ≤ g := hg
    rw [wF_cum (by omega)] at this
    omega
  start_succ := fun k hk => by
    have hk0 : k = 0 := by omega
    subst hk0
    change (10 : ℕ) = wF.roundOf 2 + cP.gap
    rw [wF_roundOf (by omega)]
    rfl
  update := fun k hk _ _ => by
    have hk0 : k = 0 := by omega
    subst hk0
    rfl
  anchor_closed := fun _ _ => by decide
  keyed := fun r i j hi hj h => by
    have hi' : i < 2 := lt_of_lt_of_le hi (wF_width_le r)
    have hj' : j < 2 := lt_of_lt_of_le hj (wF_width_le r)
    by_cases h0 : i = 0 <;> by_cases h1 : j = 0
    · omega
    · exact absurd h (by simp [wAsg, h0, h1])
    · exact absurd h (by simp [wAsg, h0, h1])
    · omega
  coherent := fun r i hi hep => by
    have hlt : wF.index r i < 8 := by
      have : wF.index r i / 4 < 2 := by simpa [epochOf] using hep
      omega
    obtain ⟨hi0, _⟩ := wF_low hi (by omega)
    subst hi0
    rfl
  closed := fun r i hi hep => by
    have hlt : wF.index r i < 4 := by
      have : wF.index r i / 4 < 1 := by simpa [epochOf] using hep
      omega
    obtain ⟨hi0, hidx⟩ := wF_low hi (by omega)
    subst hi0
    rw [hidx] at hep hlt ⊢
    have hep0 : epochOf W r = 0 := Nat.div_eq_of_lt (by omega)
    have hB : wF.roundOf (W * (epochOf W r + 2)) = 8 := by
      rw [hep0]; change wF.roundOf 8 = 8; exact wF_roundOf (by omega)
    rw [hB]
    exact fun F' a' hk' hw ha =>
      decided_below (show r + 2 ≤ 12 by omega) (show r < 8 by omega)
        (show (8 : ℕ) ≤ 12 by omega) hk'
        (fun r' hr' => by rw [hw r' hr', wF_width_low (by omega)])
        (fun r' hr' => by
          rw [ha r' 0 hr' (by rw [wF_width_low (by omega)]; omega)]; rfl)

/-- The width genuinely changes: round `10` still holds one slot, round
`11` holds two, and they are led by different validators. -/
example : wRun.F.width 10 = 1 := rfl
example : wRun.F.width 11 = 2 := rfl
example : wRun.asg 11 0 ≠ wRun.asg 11 1 := by decide
example : wRun.count 0 = 1 := rfl
example : wRun.count 1 = 2 := rfl

/-- And it too has reached its horizon. -/
theorem wRun_horizon : W * (1 + 1) ≤ wRun.F.cum (wRun.start 1) := by
  change (8 : ℕ) ≤ wF.cum 10
  rw [wF_cum (by omega)]; omega

end Composition
end LeanDagTest
