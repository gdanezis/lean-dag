import LeanDagTest.Mysticeti.Model
import LeanDag.Steelhead.Helpers.Liveness
import Mathlib.Tactic.IntervalCases
/-!
# Steelhead witnesses: the stall on data

The DAG of `steelhead.md` §4, on which SH8 applies. The adversary
delivers every synchronous slot's leader block to exactly `f + 1`
validators before the vote: two vote for it and two blame the slot, so
neither the certificate quorum nor the blame quorum forms, and the slot
is neither directly committed nor directly skipped. One universe,
`st20`: five rounds `0..4` under the period-four wavelength
`periodic 3 5 4`, so rounds `0` and `4` are asynchronous slots at wave
`5` and rounds `1`, `2`, `3` synchronous at wave `3`. On it:

* every synchronous candidate has exactly `f + 1 = 2` voters, no
  certificate, and `2` blamers, short of the quorum `3`;
* the asynchronous slot `0` commits directly at wave `5`, with the whole
  of round `4` certifying its candidate;
* the two hypotheses of SH8 hold at every round, not only at the five
  the universe holds, since every round above `4` is empty;
* **the stall**: slot `3`, at round `3 ≡ 4 − 1`, is undecided in every
  view.

The committee is the standard witness one, validator `0` Byzantine and
`f = 1` (`LeanDagTest/Mysticeti/Model.lean`), so the quorum is `3`. The
schedule is local to this file, slot `k` at round `k` led by
`(k + 1) % 4`. Every non-genesis block references the whole round below
except that at each of rounds `2`, `3`, `4` two validators, never the
leader of the round below, omit that round's leader block: validators
`0` and `3` omit block `6`, validators `0` and `1` omit block `11`, and
validators `2` and `3` omit block `12`. Three references remain, a
quorum, and the self-parent clause holds.
-/

namespace LeanDagTest

open LeanDag LeanDag.Steelhead

set_option maxRecDepth 4096

/-- One slot per round, led by `(k + 1) % 4`. -/
local instance stSlots : Slots (Fin 4) :=
  Slots.uniformSingle 1 (by omega) (fun k => ⟨(k + 1) % 4, by omega⟩)

/-- The period-four wavelength of the 3f+1 pair: `5` at rounds `0` and
`4`, `3` elsewhere. -/
abbrev wst : ℕ → ℕ := periodic 3 5 4

/-! ## `st20`: five rounds, each leader block delivered to `f + 1` -/

/-- The round-`m` leader block that validator `v`'s round-`(m + 1)` block
omits, if any. -/
def stOmit (m v : ℕ) : Option ℕ :=
  if m = 1 ∧ (v = 0 ∨ v = 3) then some 6
  else if m = 2 ∧ (v = 0 ∨ v = 1) then some 11
  else if m = 3 ∧ (v = 2 ∨ v = 3) then some 12
  else none

/-- Block `4m + v` is validator `v`'s round-`m` block; every non-genesis
block references the round below less the leader block `stOmit` names. -/
def stBlk : Fin 20 → Block (Fin 4) (Fin 20) Unit := fun i =>
  { round := (i : ℕ) / 4, creator := ⟨(i : ℕ) % 4, by omega⟩,
    refs := if h : (i : ℕ) < 4 then ∅ else
      (Finset.univ.filter (fun j : Fin 20 => (j : ℕ) / 4 + 1 = (i : ℕ) / 4 ∧
        stOmit ((i : ℕ) / 4 - 1) ((i : ℕ) % 4) ≠ some (j : ℕ))),
    payload := () }

def st20 : BlockUniverse (Fin 4) (Fin 20) Unit where
  ids := Finset.univ
  block := stBlk
  complete := by decide
  valid := by decide
  no_equivocation := by decide

-- The omissions, on data: three references where the leader block is
-- omitted, four elsewhere.
example : (st20.block 8).refs = {4, 5, 7} := by decide
example : (st20.block 9).refs = {4, 5, 6, 7} := by decide
example : (st20.block 12).refs = {8, 9, 10} := by decide
example : (st20.block 18).refs = {13, 14, 15} := by decide

-- Every block sits at round `4` or below.
theorem st20_round_le : ∀ b : Fin 20, (st20.block b).round ≤ 4 := by decide

/-- Rounds above `4` are empty. -/
theorem st20_blocksAt_eq_empty {n : ℕ} (hn : 4 < n) : blocksAt st20 n = ∅ := by
  ext b
  simp only [mem_blocksAt, Finset.notMem_empty, iff_false]
  rintro ⟨_, hb⟩
  have := st20_round_le b
  omega

/-! ## The synchronous slots: `f + 1` votes, no quorum either way -/

-- Slot `1`'s candidate is block `6` (round `1`, author `2`): voted for by
-- validators `1` and `2` at round `2`, certified by nothing at round `3`,
-- blamed by two.
example : IsLeaderBlock st20 1 6 := by decide
example : (blocksAt st20 2).filter (fun q => MahiMahi.Votes st20 q 6) = {9, 10} := by decide
example : ((blocksAt st20 2).filter (fun q => MahiMahi.Votes st20 q 6)).card =
    Faults.f (Fin 4) + 1 := by decide
example : MahiMahi.certificates st20 3 6 1 = ∅ := by decide
example : ¬ MahiMahi.DirectSkipIn st20 (View.full st20) 3 (stSlots.leader 1) 1 := by decide

-- Slot `2`'s candidate is block `11` (round `2`, author `3`): voted for by
-- validators `2` and `3` at round `3`.
example : IsLeaderBlock st20 2 11 := by decide
example : (blocksAt st20 3).filter (fun q => MahiMahi.Votes st20 q 11) = {14, 15} := by decide
example : MahiMahi.certificates st20 3 11 2 = ∅ := by decide
example : ¬ MahiMahi.DirectSkipIn st20 (View.full st20) 3 (stSlots.leader 2) 2 := by decide

-- Slot `3`'s candidate is block `12` (round `3`, author `0`): voted for by
-- validators `0` and `1` at round `4`.
example : IsLeaderBlock st20 3 12 := by decide
example : (blocksAt st20 4).filter (fun q => MahiMahi.Votes st20 q 12) = {16, 17} := by decide
example : MahiMahi.certificates st20 3 12 3 = ∅ := by decide
example : ¬ MahiMahi.DirectSkipIn st20 (View.full st20) 3 (stSlots.leader 3) 3 := by decide

/-! ## The asynchronous slot commits -/

-- Slot `0`'s candidate is block `1` (round `0`, author `1`); at wave `5`
-- the whole of round `4` certifies it.
example : IsLeaderBlock st20 0 1 := by decide
example : MahiMahi.certificates st20 5 1 0 = {16, 17, 18, 19} := by decide
example : MahiMahi.DirectCommit st20 5 1 0 := by decide

theorem st20_slot0 : Steelhead.Decided wst st20 (View.full st20) 0 (some 1) :=
  Decided.directCommit (by decide) (by decide)

/-! ## The hypotheses of SH8, at every round -/

/-- No synchronous candidate is certified: on data through round `4`, and
vacuously above, where no block sits. -/
theorem st20_hcert : ∀ (j : ℕ) (L : Fin 20), ¬ IsAsync 4 j → IsLeaderBlock st20 j L →
    MahiMahi.certificates st20 3 L j = ∅ := by
  intro j L hj hL
  rcases Nat.lt_or_ge 4 j with h4 | h4
  · exfalso
    have hr : (st20.block L).round = 1 * (j / 1) := hL.2.1
    have := st20_round_le L
    omega
  · revert L hj hL
    interval_cases j <;> decide

/-- No synchronous slot is directly skipped in the full view: on data
through round `4`, and above it no voting round has a block. -/
theorem st20_hskip : ∀ j, ¬ IsAsync 4 j →
    ¬ MahiMahi.DirectSkipIn st20 (View.full st20) 3 (stSlots.leader j) j := by
  intro j hj h
  rcases Nat.lt_or_ge 4 j with h4 | h4
  · have he : blocksAt st20 (MahiMahi.votingRound 3 j) = ∅ :=
      st20_blocksAt_eq_empty (by unfold MahiMahi.votingRound; omega)
    change 3 ≤ (heldAuthors st20 (View.full st20) _).card at h
    rw [he, Finset.filter_empty] at h
    simp [heldAuthors, creatorsOf] at h
  · revert hj h
    interval_cases j <;> decide

/-- A view holds fewer blamers than the full view. -/
theorem st20_hskip_view (V : View (Fin 4) (Fin 20) Unit st20) : ∀ j, ¬ IsAsync 4 j →
    ¬ MahiMahi.DirectSkipIn st20 V 3 (stSlots.leader j) j :=
  fun j hj h => st20_hskip j hj (h.mono (by rw [View.full_ids]; exact V.subset_ids))

/-! ## The stall -/

/-- **SH8 on data**: slot `3` is undecided in every view, whatever the
asynchronous slots `0` and `4` do. -/
theorem st20_stall_view (V : View (Fin 4) (Fin 20) Unit st20) (v : Option (Fin 20)) :
    ¬ Steelhead.Decided wst st20 V 3 v :=
  fun h => Steelhead.stall (by decide) (by decide) (fun _ => by simp) st20_hcert
    (st20_hskip_view V) (by decide) h

/-- The stall in the full view. -/
theorem st20_stall : ∀ v, ¬ Steelhead.Decided wst st20 (View.full st20) 3 v :=
  st20_stall_view (View.full st20)

/-! ## Axioms

Nothing here should ever acquire an axiom beyond the standard three. -/

#print axioms st20
#print axioms st20_slot0
#print axioms st20_stall

end LeanDagTest
