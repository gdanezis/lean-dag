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

/-- A frame agreeing with `cF` below `B` counts slots the same way there. -/
theorem cum_eq_of_agree {F' : Frame} {B : ℕ}
    (hw : ∀ r, r < B → F'.width r = cF.width r) :
    ∀ r, r ≤ B → F'.cum r = r := by
  intro r
  induction r with
  | zero => intro _; simp
  | succ j ih =>
      intro hj
      rw [Frame.cum_succ, ih (by omega), hw j (by omega), cF_width]

/-- And so it puts slot `k` at round `k`. -/
theorem roundOf_eq_of_agree {F' : Frame} {B : ℕ}
    (hw : ∀ r, r < B → F'.width r = cF.width r) {k : ℕ} (hk : k < B) :
    F'.roundOf k = k :=
  F'.roundOf_eq (by rw [cum_eq_of_agree hw k (by omega)])
    (by rw [cum_eq_of_agree hw (k + 1) (by omega)]; omega)

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
    (hw : ∀ r, r < B → F'.width r = cF.width r)
    (ha : ∀ r i, r < B → i < cF.width r → a' r i = cAsg r i) :
    gRule.Decided (F'.toSlots a' hk') (View.full (Ugrow N)) k (cVdct k) := by
  have hround : (F'.toSlots a' hk').slotRound k = k := roundOf_eq_of_agree hw hk
  have hlead : (F'.toSlots a' hk').leader k = 1 := by
    change a' (F'.roundOf k) (k - F'.cum (F'.roundOf k)) = 1
    rw [roundOf_eq_of_agree hw hk, cum_eq_of_agree hw k (by omega), Nat.sub_self]
    exact ha k 0 hk Nat.one_pos
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
        (show (8 : ℕ) ≤ 12 by omega) hk' hw ha

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

end Composition
end LeanDagTest
