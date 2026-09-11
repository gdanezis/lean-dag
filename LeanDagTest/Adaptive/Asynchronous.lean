import LeanDagTest.Barnacle.Progress
import LeanDag.Adaptive.Ledger.Proof
import LeanDag.Adaptive.Score.Proof
import LeanDagTest.Adaptive.Segmented
/-!
# The segmented run on data: an anchor past the boundary

The case `adaptive-leaders.md` §7 says the fixpoint arc cannot express,
and the reason for the whole exercise: a configuration whose span closes
at a round the anchor sits well above.

`Usk` (`LeanDagTest/Barnacle/Progress.lean`) is eight sunny rounds with
one block referenced by its author alone, so slot `2` is directly
skipped. At one leader a round and an interval of one, configuration `0`
takes force after round `0` and its **boundary** is round `1` — but the
least committed slot past that boundary is slot `3`, two rounds further
up, because slot `2` skips. So:

* configuration `0` **decides** rounds `1`, `2` and `3`, which is how it
  finds its anchor;
* it **outputs** round `1` alone;
* rounds `2` and `3` are decided again under configurations `1` and `2`,
  and block `15` reaches the ledger only from the configuration whose
  span contains round `3`.

`anchor_least` is non-vacuous here: slot `2` lies past the boundary,
below the anchor, and is a skip.
-/

namespace LeanDagTest

namespace Adaptive

open LeanDag LeanDag.Adaptive LeanDag.Barnacle
open LeanDagTest.Barnacle

/-- The verdicts, one function for every segment: the configuration never
moves under the constant rule, so the schedule does not either. -/
def vdSeg : ℕ → ℕ → Option (Fin 32) := fun _ κ =>
  if κ = 1 then some 5 else if κ = 3 then some 15 else if κ = 4 then some 16 else none

/-- Three segments on `Usk`, at one leader a round and an interval of
one: boundaries at rounds `1`, `2` and `3`, anchors at slots `3`, `3`
and `4`. -/
def segRun : SegRun bnRule32 bnPI1 (constRule bnRule32) bnC1I1 Usk (View.full Usk) 3 where
  start := fun k => k
  cfg := fun _ => bnC1I1
  backoff := fun _ => 0
  anchor := fun k => if k = 2 then 4 else 3
  vdct := vdSeg
  init := ⟨rfl, rfl, rfl⟩
  bounds := fun _ => ⟨fun _ => (by decide : (1 : ℕ) ≤ 4), by decide, by decide⟩
  closed := by
    intro k hk κ h1 h2
    simp only [bnC1I1, bnCfg, Config.uniform_roundOf, Nat.div_one] at h1 h2
    have hkk : k = 0 ∨ k = 1 ∨ k = 2 := by omega
    rcases hkk with rfl | rfl | rfl
    · simp only [show ¬((0 : ℕ) = 2) from by decide, if_false] at h2
      have : κ = 1 ∨ κ = 2 ∨ κ = 3 := by omega
      rcases this with rfl | rfl | rfl
      · exact Decided.directCommit (S := bnC1I1.sched) (by decide) (by decide)
      · exact Decided.directSkip (S := bnC1I1.sched) (by decide)
      · exact Decided.directCommit (S := bnC1I1.sched) (by decide) (by decide)
    · simp only [show ¬((1 : ℕ) = 2) from by decide, if_false] at h2
      have : κ = 2 ∨ κ = 3 := by omega
      rcases this with rfl | rfl
      · exact Decided.directSkip (S := bnC1I1.sched) (by decide)
      · exact Decided.directCommit (S := bnC1I1.sched) (by decide) (by decide)
    · simp only [if_true] at h2
      have : κ = 3 ∨ κ = 4 := by omega
      rcases this with rfl | rfl
      · exact Decided.directCommit (S := bnC1I1.sched) (by decide) (by decide)
      · exact Decided.directCommit (S := bnC1I1.sched) (by decide) (by decide)
  anchor_commits := by
    intro k hk
    have hkk : k = 0 ∨ k = 1 ∨ k = 2 := by omega
    rcases hkk with rfl | rfl | rfl
    · exact ⟨⟨15, rfl⟩, by decide⟩
    · exact ⟨⟨15, rfl⟩, by decide⟩
    · exact ⟨⟨16, rfl⟩, by decide⟩
  anchor_least := by
    intro k hk κ hκ h
    simp only [bnC1I1, bnCfg, Config.uniform_roundOf, Nat.div_one] at h
    have hkk : k = 0 ∨ k = 1 ∨ k = 2 := by omega
    rcases hkk with rfl | rfl | rfl
    · simp only [show ¬((0 : ℕ) = 2) from by decide, if_false] at hκ
      have : κ = 2 := by omega
      subst this; rfl
    · simp only [show ¬((1 : ℕ) = 2) from by decide, if_false] at hκ
      omega
    · simp only [if_true] at hκ
      omega
  start_succ := by intro k _; rfl
  update := by intro k _ A _; rfl

/-! ## What the run says

The claims below are `decide`d on the data, and the containments are
`Adaptive.decided_and_not_output` applied. -/

-- The boundaries are the rounds `1`, `2`, `3`, fixed before any anchor.
example : segRun.start 1 = 1 ∧ segRun.start 2 = 2 ∧ segRun.start 3 = 3 := ⟨rfl, rfl, rfl⟩
-- The first anchor is two rounds past the first boundary.
example : segRun.anchor 0 = 3 ∧ bnC1I1.roundOf (segRun.anchor 0) = 3 := by decide

-- Configuration `0` decides rounds `1`, `2` and `3` …
example : segRun.vdct 0 1 = some 5 ∧ segRun.vdct 0 2 = none ∧ segRun.vdct 0 3 = some 15 :=
  ⟨rfl, rfl, rfl⟩
-- … and outputs round `1` alone.
example : segRun.rangeLedger 0 = [5] := by decide
-- Block `15` is decided by configuration `0` and is not its output.
example : (15 : Fin 32) ∉ segRun.rangeLedger 0 := by decide

/-- **`decided_and_not_output` on data.** Slot `3` is at a round above
configuration `0`'s boundary and at or below its anchor's, so
configuration `0` decides it and `rangeLedger 0` does not read it. -/
example : bnRule32.Decided bnC1I1.sched (View.full Usk) 3 (segRun.vdct 0 3) ∧
    bnC1I1.cum (segRun.start 1 + 1) ≤ 3 :=
  decided_and_not_output segRun (by decide) (by decide) (by decide)

-- The same round is decided again by configurations `1` and `2` …
example : segRun.vdct 1 3 = some 15 ∧ segRun.vdct 2 3 = some 15 := ⟨rfl, rfl⟩
-- … and block `15` is output by the one whose span contains round `3`.
example : segRun.rangeLedger 1 = [] := by decide
example : segRun.rangeLedger 2 = [15] := by decide
example : segRun.ledgerUpto 3 = [5, 15] := by decide

-- Every block of the ledger sits at a round at or below the frontier.
example : ∀ L ∈ segRun.ledgerUpto 3,
    segRun.start 0 < (bnRule32.block Usk L).round ∧
      (bnRule32.block Usk L).round ≤ segRun.start 3 :=
  fun _ h => round_of_mem_ledgerUpto candidates32 segRun le_rfl h

/-! ## A score that reassigns, on data

`Score.permute` is D22's family. A score that *reads the anchor's
history* and chooses which permutation to apply is adaptive in the sense
this arc is about — the reassignment is a function of the DAG — and is
still of that family, so `headsRun_perm` covers its liveness. -/

/-- Swap validators `0` and `1`. -/
def swap01 : Equiv.Perm (Fin 4) := Equiv.swap 0 1

/-- Permute when the anchor's history holds block `10`, and leave the
configuration alone otherwise. -/
def swapScore : Score bnRule32 := fun U V C =>
  if (10 : Fin 32) ∈ bnRule32.viewIds V then Score.permute swap01 U V C else C

/-- It keeps the shape, so AL11b gives `UpdBounded` at every parameter
set. -/
theorem swapScore_keeps : swapScore.Keeps := by
  intro U V C
  unfold swapScore
  split <;> exact ⟨rfl, rfl⟩

example : UpdBounded bnPI1 (rule swapScore) := Score.rule_bounded bnPI1 swapScore swapScore_keeps

/-- It stays inside D22's family, so `Permuted` is preserved and AL16b's
liveness hypothesis is discharged by `liveOn_of_permuted`. -/
theorem swapScore_permuted {head : ℕ → Fin 4} (U : bnRule32.Universe)
    (V : bnRule32.View U) (C : Config (Fin 4)) (h : Permuted head C) :
    Permuted head (swapScore U V C) := by
  obtain ⟨σ, hσ⟩ := h
  unfold swapScore
  split
  · exact ⟨σ.trans swap01, by funext ρ; simp [Score.permute_head, hσ]⟩
  · exact ⟨σ, hσ⟩

-- It adapts: on the full view of `Usk` the leaders move off the rotation.
example : bnC1I1.head 0 = 0 := by decide
example : (swapScore Usk (View.full Usk) bnC1I1).head 0 = 1 := by decide
example : (swapScore Usk (View.full Usk) bnC1I1).slotsAt 0 = bnC1I1.slotsAt 0 := rfl
example : (swapScore Usk (View.full Usk) bnC1I1).interval = bnC1I1.interval := rfl

#print axioms segRun
#print axioms swapScore_permuted

end Adaptive

end LeanDagTest
