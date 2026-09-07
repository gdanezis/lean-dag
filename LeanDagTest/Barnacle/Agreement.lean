import LeanDagTest.Barnacle.Model
import LeanDag.Barnacle.Window.Proof
import LeanDag.Barnacle.Agreement.Proof
import LeanDag.Barnacle.Ledger.Proof
import LeanDag.Barnacle.Aimd.Proof
import LeanDag.Barnacle.Conservativity.Proof
/-!
# Barnacle witnesses — the count moves, and two runs agree

`U7` cannot host a run whose count rises: its round-`5` slot cannot be
committed (certifying round `5` needs round `7`), so no anchor past a
four-round interval exists there. `Usun` is eight rounds of four, every
block referencing the whole previous round, so slots `1` to `5` commit
directly (rounds `6` and `7` have no certifiers above them). At interval
`4` and count `1`:

* slots `1` to `5` of `Sched 1` commit directly; slot `5` (block `21`,
  round `5 > 0 + 4`) is the anchor;
* its window scores rounds `1` and `2` — two slots against an expected
  two — and is healthy: the count rises to `2` and the back-off resets.
  Rounds `3`, `4` and `5` all commit on the full view and none on the
  window: round `3`'s only certifier there is the anchor itself, rounds
  `4` and `5` have none.

`run2` is that run on the full view; `run2'` the same run on a view
missing one round-`7` block, which still holds three certifiers for
slot `5` — the quorum exactly; `run2x` differs from `run2'` in a verdict
*outside* the range, which BN3 does not constrain. At interval `1`,
`runP1` closes two configurations (the back-off doubles, the count stays
at the floor) and `runP1'` one, exercising BN3 at two heights on a
configuration `init` does not pin. BN2, BN3 and BN7 are applied on this
data through their `holds`; BN4 and BN5 are not — see
`barnacle.md` §5 on total runs.
-/

namespace LeanDagTest

namespace Barnacle

set_option maxRecDepth 2000000

open LeanDag LeanDag.Barnacle

/-! ## Eight sunny rounds -/

/-- Round `r`, author `a`, id `4 r + a`; every block references the whole
previous round. -/
def sunBlk : Fin 32 → Block (Fin 4) (Fin 32) Unit := fun i =>
  { round := (i : ℕ) / 4
    creator := ⟨(i : ℕ) % 4, Nat.mod_lt _ (by omega)⟩
    refs := if (i : ℕ) < 4 then ∅ else
      (Finset.univ.filter fun j : Fin 32 => (j : ℕ) / 4 + 1 = (i : ℕ) / 4)
    payload := () }

def Usun : BlockUniverse (Fin 4) (Fin 32) Unit where
  ids := Finset.univ
  block := sunBlk
  complete := by decide
  valid := by decide
  no_equivocation := by decide

/-- The full view. -/
def Vsun : View (Fin 4) (Fin 32) Unit Usun where
  ids := Finset.univ
  subset_ids := by decide
  complete := by decide

/-- A view missing block `31` (round `7`, author `3`), which nothing
references. -/
def Vsun' : View (Fin 4) (Fin 32) Unit Usun where
  ids := Finset.univ.erase 31
  subset_ids := by decide
  complete := by decide

abbrev bnRule32 : BaseRule (Fin 4) (Fin 32) Unit := mysticeti

/-- The verdicts of configuration `0`: slots `1` to `5` commit their
round's first leader's block. -/
def vd2 : ℕ → ℕ → Option (Fin 32) :=
  fun _ κ => if h : 1 ≤ κ ∧ κ ≤ 5 then some ⟨4 * κ + κ % 4, by omega⟩ else none

/-! ## The window, healthy -/

-- Anchor `21`: rounds `1` and `2` score at count `1`; rounds `3` to `5`
-- do not — round `3`'s only certifier in the window is the anchor.
example : observed bnRule32 bnP bnLeader bnWin Usun 21 1 (by decide) (by decide) = 2 := by
  decide
example : expected bnRule32 bnP 1 = 2 := by decide
example : Aimd.rule bnRule32 bnP bnLeader bnWin 1 0 Usun (View.full Usun) 21 = (2, 0) := by decide

/-! ## The run whose count rises -/

/-- Configuration `0` closed at anchor `5`; configuration `1` at count
`2` after round `5`. `anchor_least` is vacuous here — no slot below `5`
has a round above the threshold `4` — as it is for every anchor that is
the first slot past the threshold; a non-vacuous instance needs a
skipped slot there. -/
def run2 : PartialRun bnRule32 bnP bnLeader bnWin (Aimd.rule bnRule32 bnP bnLeader bnWin)
    Usun Vsun 1 where
  start := fun k => if k = 0 then 0 else 5
  count := fun k => if k = 0 then 1 else 2
  backoff := fun _ => 0
  anchor := fun _ => 5
  vdct := vd2
  init := ⟨rfl, rfl, rfl⟩
  count_pos := fun k => by split_ifs <;> decide
  count_le := fun k => by split_ifs <;> decide
  closed := by
    intro k hk κ h1 h2
    have hk0 : k = 0 := by omega
    subst hk0
    simp at h1 h2
    have : κ = 1 ∨ κ = 2 ∨ κ = 3 ∨ κ = 4 ∨ κ = 5 := by omega
    rcases this with rfl | rfl | rfl | rfl | rfl <;>
      exact Decided.directCommit (S := Sched bnLeader bnWin 1 (by decide) (by decide))
        (by decide) (by decide)
  anchor_commits := by
    intro k hk
    have hk0 : k = 0 := by omega
    subst hk0
    exact ⟨⟨21, rfl⟩, by decide⟩
  anchor_least := by
    intro k hk κ hκ h
    have hk0 : k = 0 := by omega
    subst hk0
    simp only [if_true, Nat.div_one] at h
    have hi : bnP.interval = 4 := rfl
    omega
  start_succ := by
    intro k hk
    have hk0 : k = 0 := by omega
    subst hk0
    rfl
  update := by
    intro k hk A hA
    have hk0 : k = 0 := by omega
    subst hk0
    have hA' : A = 21 := by
      simp [vd2] at hA; exact hA.symm
    subst hA'
    decide

/-- The same run on the smaller view. -/
def run2' : PartialRun bnRule32 bnP bnLeader bnWin (Aimd.rule bnRule32 bnP bnLeader bnWin)
    Usun Vsun' 1 where
  start := fun k => if k = 0 then 0 else 5
  count := fun k => if k = 0 then 1 else 2
  backoff := fun _ => 0
  anchor := fun _ => 5
  vdct := vd2
  init := ⟨rfl, rfl, rfl⟩
  count_pos := fun k => by split_ifs <;> decide
  count_le := fun k => by split_ifs <;> decide
  closed := by
    intro k hk κ h1 h2
    have hk0 : k = 0 := by omega
    subst hk0
    simp at h1 h2
    have : κ = 1 ∨ κ = 2 ∨ κ = 3 ∨ κ = 4 ∨ κ = 5 := by omega
    rcases this with rfl | rfl | rfl | rfl | rfl <;>
      exact Decided.directCommit (S := Sched bnLeader bnWin 1 (by decide) (by decide))
        (by decide) (by decide)
  anchor_commits := by
    intro k hk
    have hk0 : k = 0 := by omega
    subst hk0
    exact ⟨⟨21, rfl⟩, by decide⟩
  anchor_least := by
    intro k hk κ hκ h
    have hk0 : k = 0 := by omega
    subst hk0
    simp only [if_true, Nat.div_one] at h
    have hi : bnP.interval = 4 := rfl
    omega
  start_succ := by
    intro k hk
    have hk0 : k = 0 := by omega
    subst hk0
    rfl
  update := by
    intro k hk A hA
    have hk0 : k = 0 := by omega
    subst hk0
    have hA' : A = 21 := by
      simp [vd2] at hA; exact hA.symm
    subst hA'
    decide

-- The count moved: two leaders after round `5`.
example : run2.count 1 = 2 ∧ run2.start 1 = 5 ∧ run2.backoff 1 = 0 := ⟨rfl, rfl, rfl⟩

/-! ## The results, on this data -/

/-- The laws of Mysticeti at this committee, once. -/
abbrev laws32 : bnRule32.Laws := Mysticeti.holds (Fin 4) (Fin 32) Unit

/-- And the two properties the safety results now ask for instead. -/
abbrev agree32 : Properties.Agree bnRule32.toDagRule := MysticetiProperties.agree

abbrev candidates32 : Properties.CommitsCandidate bnRule32.toDagRule :=
  MysticetiProperties.commitsCandidate

/-- BN3 on `run2` and `run2'`: the two views hold one configuration `1`
and one anchor. -/
example : run2.count 1 = run2'.count 1 ∧ run2.start 1 = run2'.start 1 :=
  let h := (Agreement.holds (Fin 4) (Fin 32) Unit bnRule32 agree32 bnP bnLeader bnWin _ (fun _ _ _ _ _ _ => rfl))
    Usun Vsun Vsun' 1 1 run2 run2' 1 (by decide)
  ⟨h.2.1, h.1⟩
example : run2.anchor 0 = run2'.anchor 0 :=
  ((Agreement.holds (Fin 4) (Fin 32) Unit bnRule32 agree32 bnP bnLeader bnWin _ (fun _ _ _ _ _ _ => rfl))
    Usun Vsun Vsun' 1 1 run2 run2' 0 (by decide)).2.2.2 (by decide) |>.1

/-- BN2 on `Usun`: the smaller view holds the anchor, hence its history. -/
example : historyFrom Usun.block 21 ⊆ Vsun'.ids :=
  ((Window.holds (Fin 4) (Fin 32) Unit bnRule32).1 Usun Vsun' 21 (by decide))

/-- BN7a on the witness parameters: the rule stays in range at the values
the run meets. -/
example : 0 < (Aimd.rule bnRule32 bnP bnLeader bnWin 1 0 Usun (View.full Usun) 21).1 ∧
    (Aimd.rule bnRule32 bnP bnLeader bnWin 1 0 Usun (View.full Usun) 21).1 ≤ bnP.maxLeaders :=
  (Aimd.holds (Fin 4) (Fin 32) Unit bnRule32 bnP bnLeader bnWin).1 1 0 Usun
    (View.full Usun) 21
-- BN7b: below the cap, one more leader.
example : Aimd.update bnP 3 0 true = (4, 0) :=
  (Aimd.holds (Fin 4) (Fin 32) Unit bnRule32 bnP bnLeader bnWin).2.1.1 3 0 (by decide)
-- BN7c: from count `4` at back-off `1`, strictly fewer and the back-off
-- incremented; the step is `4 - 2`; at the floor, the floor.
example : (Aimd.update bnP 4 1 false).1 < 4 ∧ (Aimd.update bnP 4 1 false).2 = 2 :=
  (Aimd.holds (Fin 4) (Fin 32) Unit bnRule32 bnP bnLeader bnWin).2.2.1.1 4 1 (by decide)
example : (Aimd.update bnP 4 1 false).1 = 4 - 2 ^ 1 :=
  (Aimd.holds (Fin 4) (Fin 32) Unit bnRule32 bnP bnLeader bnWin).2.2.1.2.1 4 1 (by decide)
example : (Aimd.update bnP 1 3 false).1 = 1 :=
  (Aimd.holds (Fin 4) (Fin 32) Unit bnRule32 bnP bnLeader bnWin).2.2.1.2.2 3
-- BN7d: the rule at anchor `21`, count `2`, is the step of the integer
-- test — `96 · 4 ≤ 100 · 4` here, healthy; at interval one and anchor
-- `20` the test fails, `96 · 1 ≤ 100 · 0`.
example : Aimd.rule bnRule32 bnP bnLeader bnWin 2 0 Usun (View.full Usun) 21 =
    Aimd.update bnP 2 0 (decide (bnP.num * expected bnRule32 bnP 2 ≤
      bnP.den * observed bnRule32 bnP bnLeader bnWin Usun 21 2 (by decide) (by decide))) :=
  (Aimd.holds (Fin 4) (Fin 32) Unit bnRule32 bnP bnLeader bnWin).2.2.2.1 2 0 (by decide)
    (by decide) Usun (View.full Usun) 21
example : Aimd.rule bnRule32 bnP bnLeader bnWin 2 0 Usun (View.full Usun) 21 = (3, 0) := by decide
example : Aimd.rule bnRule32 bnP1 bnLeader bnWin 1 1 Usun (View.full Usun) 20 =
    Aimd.update bnP1 1 1 (decide (bnP1.num * expected bnRule32 bnP1 1 ≤
      bnP1.den * observed bnRule32 bnP1 bnLeader bnWin Usun 20 1 (by decide) (by decide))) :=
  (Aimd.holds (Fin 4) (Fin 32) Unit bnRule32 bnP1 bnLeader bnWin).2.2.2.1 1 1 (by decide)
    (by decide) Usun (View.full Usun) 20
-- On `Usun` at anchor `21` the window is healthy at every count: the
-- count climbs to the cap and stays there.
example : Aimd.rule bnRule32 bnP bnLeader bnWin 4 0 Usun (View.full Usun) 21 = (4, 0) := by decide

/-- BN2b on two views: the views differ, the windows do not. -/
example : historyFrom Usun.block 21 ∩ Vsun.ids = historyFrom Usun.block 21 ∩ Vsun'.ids :=
  (Window.holds (Fin 4) (Fin 32) Unit bnRule32).2 Usun Vsun Vsun' 21 (by decide) (by decide)
example : Vsun.ids ≠ Vsun'.ids := by decide

/-- The `candidates` law through the run: the anchor `run2'` committed is
a candidate of its slot. -/
example : bnRule32.IsLeaderBlock (Sched bnLeader bnWin 1 (by decide) (by decide)) Usun 5 21 :=
  laws32.candidates _ _ Vsun' 5 21 (run2'.closed 0 (by decide) 5 (by decide) (by decide))

/-! ## A verdict outside the range

`run2x` is `run2'` with slot `9` committing block `0` — nonsense, but
outside range `0`, which ends at the anchor, and so unconstrained. BN3
still identifies the two runs on the range, and `decide` shows them
differ beyond it. -/

def vd2x : ℕ → ℕ → Option (Fin 32) := fun k κ => if κ = 9 then some 0 else vd2 k κ

def run2x : PartialRun bnRule32 bnP bnLeader bnWin (Aimd.rule bnRule32 bnP bnLeader bnWin)
    Usun Vsun' 1 where
  start := fun k => if k = 0 then 0 else 5
  count := fun k => if k = 0 then 1 else 2
  backoff := fun _ => 0
  anchor := fun _ => 5
  vdct := vd2x
  init := ⟨rfl, rfl, rfl⟩
  count_pos := fun k => by split_ifs <;> decide
  count_le := fun k => by split_ifs <;> decide
  closed := by
    intro k hk κ h1 h2
    have hk0 : k = 0 := by omega
    subst hk0
    simp at h1 h2
    have : κ = 1 ∨ κ = 2 ∨ κ = 3 ∨ κ = 4 ∨ κ = 5 := by omega
    rcases this with rfl | rfl | rfl | rfl | rfl <;>
      exact Decided.directCommit (S := Sched bnLeader bnWin 1 (by decide) (by decide))
        (by decide) (by decide)
  anchor_commits := by
    intro k hk
    have hk0 : k = 0 := by omega
    subst hk0
    exact ⟨⟨21, rfl⟩, by decide⟩
  anchor_least := by
    intro k hk κ hκ h
    have hk0 : k = 0 := by omega
    subst hk0
    simp only [if_true, Nat.div_one] at h
    have hi : bnP.interval = 4 := rfl
    omega
  start_succ := by
    intro k hk
    have hk0 : k = 0 := by omega
    subst hk0
    rfl
  update := by
    intro k hk A hA
    have hk0 : k = 0 := by omega
    subst hk0
    have hA' : A = 21 := by
      simp [vd2x, vd2] at hA; exact hA.symm
    subst hA'
    decide

example : run2.vdct 0 3 = run2x.vdct 0 3 :=
  ((Agreement.holds (Fin 4) (Fin 32) Unit bnRule32 agree32 bnP bnLeader bnWin _ (fun _ _ _ _ _ _ => rfl))
    Usun Vsun Vsun' 1 1 run2 run2x 0 (by decide)).2.2.2 (by decide) |>.2 3 (by decide) (by decide)
example : run2.vdct 0 9 ≠ run2x.vdct 0 9 := by decide

/-! ## Two heights

At interval `1` on `Usun` two configurations close: anchors at slots `2`
(block `10`) and `4` (block `16`), both windows score nothing, the
back-off goes `0, 1, 2` and the count stays at the floor. `runP1'` is
the same execution from `Vsun'`, closed one configuration lower. BN3 at
heights `2` and `1` identifies configuration `1`, which `init` does not
pin, and the verdicts of range `0`; configuration `2` is not offered. -/

def vdP1 : ℕ → ℕ → Option (Fin 32) := fun k κ =>
  if k = 0 then (if κ = 1 then some 5 else if κ = 2 then some 10 else none)
  else if k = 1 then (if κ = 3 then some 15 else if κ = 4 then some 16 else none)
  else none

def runP1 : PartialRun bnRule32 bnP1 bnLeader bnWin (Aimd.rule bnRule32 bnP1 bnLeader bnWin)
    Usun Vsun 2 where
  start := fun k => if k = 0 then 0 else if k = 1 then 2 else 4
  count := fun _ => 1
  backoff := fun k => if k = 0 then 0 else if k = 1 then 1 else 2
  anchor := fun k => if k = 0 then 2 else 4
  vdct := vdP1
  init := ⟨rfl, rfl, rfl⟩
  count_pos := fun _ => Nat.one_pos
  count_le := fun _ => by decide
  closed := by
    intro k hk κ h1 h2
    have : k = 0 ∨ k = 1 := by omega
    rcases this with rfl | rfl
    · simp at h1 h2
      have : κ = 1 ∨ κ = 2 := by omega
      rcases this with rfl | rfl <;>
        exact Decided.directCommit (S := Sched bnLeader bnWin 1 (by decide) (by decide))
          (by decide) (by decide)
    · simp at h1 h2
      have : κ = 3 ∨ κ = 4 := by omega
      rcases this with rfl | rfl <;>
        exact Decided.directCommit (S := Sched bnLeader bnWin 1 (by decide) (by decide))
          (by decide) (by decide)
  anchor_commits := by
    intro k hk
    have : k = 0 ∨ k = 1 := by omega
    rcases this with rfl | rfl
    · exact ⟨⟨10, rfl⟩, by decide⟩
    · exact ⟨⟨16, rfl⟩, by decide⟩
  anchor_least := by
    intro k hk κ hκ h
    have hi : bnP1.interval = 1 := rfl
    have : k = 0 ∨ k = 1 := by omega
    rcases this with rfl | rfl <;>
      simp only [if_true, Nat.div_one, one_ne_zero, if_false] at hκ h <;> omega
  start_succ := by
    intro k hk
    have : k = 0 ∨ k = 1 := by omega
    rcases this with rfl | rfl <;> rfl
  update := by
    intro k hk A hA
    have : k = 0 ∨ k = 1 := by omega
    rcases this with rfl | rfl
    · have hA' : A = 10 := by simp [vdP1] at hA; exact hA.symm
      subst hA'; decide
    · have hA' : A = 16 := by simp [vdP1] at hA; exact hA.symm
      subst hA'; decide

/-- The same execution seen from `Vsun'`, closed one configuration lower. -/
def runP1' : PartialRun bnRule32 bnP1 bnLeader bnWin (Aimd.rule bnRule32 bnP1 bnLeader bnWin)
    Usun Vsun' 1 where
  start := fun k => if k = 0 then 0 else 2
  count := fun _ => 1
  backoff := fun k => if k = 0 then 0 else 1
  anchor := fun _ => 2
  vdct := fun _ κ => if κ = 1 then some 5 else if κ = 2 then some 10 else none
  init := ⟨rfl, rfl, rfl⟩
  count_pos := fun _ => Nat.one_pos
  count_le := fun _ => by decide
  closed := by
    intro k hk κ h1 h2
    have hk0 : k = 0 := by omega
    subst hk0
    simp at h1 h2
    have : κ = 1 ∨ κ = 2 := by omega
    rcases this with rfl | rfl <;>
      exact Decided.directCommit (S := Sched bnLeader bnWin 1 (by decide) (by decide))
        (by decide) (by decide)
  anchor_commits := by
    intro k hk
    have hk0 : k = 0 := by omega
    subst hk0
    exact ⟨⟨10, rfl⟩, by decide⟩
  anchor_least := by
    intro k hk κ hκ h
    have hk0 : k = 0 := by omega
    subst hk0
    simp only [if_true, Nat.div_one] at h
    have hi : bnP1.interval = 1 := rfl
    omega
  start_succ := by
    intro k hk
    have hk0 : k = 0 := by omega
    subst hk0
    rfl
  update := by
    intro k hk A hA
    have hk0 : k = 0 := by omega
    subst hk0
    have hA' : A = 10 := by simp at hA; exact hA.symm
    subst hA'
    decide

-- The back-off doubles across two configurations; the count never leaves the floor.
example : runP1.backoff 0 = 0 ∧ runP1.backoff 1 = 1 ∧ runP1.backoff 2 = 2 ∧ runP1.count 2 = 1 :=
  ⟨rfl, rfl, rfl, rfl⟩
-- BN3 at heights `2` and `1`: agreement on configuration `1` — not pinned by `init` —
-- and on the verdicts of range `0`; `k = 2` is not offered (`2 ≤ min 2 1` fails).
example : runP1.backoff 1 = runP1'.backoff 1 ∧ runP1.start 1 = runP1'.start 1 :=
  let h := (Agreement.holds (Fin 4) (Fin 32) Unit bnRule32 agree32 bnP1 bnLeader bnWin _ (fun _ _ _ _ _ _ => rfl))
    Usun Vsun Vsun' 2 1 runP1 runP1' 1 (by decide)
  ⟨h.2.2.1, h.1⟩
example : runP1.vdct 0 2 = runP1'.vdct 0 2 :=
  ((Agreement.holds (Fin 4) (Fin 32) Unit bnRule32 agree32 bnP1 bnLeader bnWin _ (fun _ _ _ _ _ _ => rfl))
    Usun Vsun Vsun' 2 1 runP1 runP1' 0 (by decide)).2.2.2 (by decide) |>.2 2 (by decide) (by decide)


/-! ## The ledger, through the theorem

`run2`'s range `0` commits blocks `5, 10, 15, 16, 21` — round `4`'s
leader is validator `0`; BN5 applied to
the run gives the ledger agreed with `run2'`, a prefix of itself, and
without repetition. -/

example : run2.rangeLedger 0 = [5, 10, 15, 16, 21] := by decide
example : run2.ledgerUpto 1 = [5, 10, 15, 16, 21] := by decide
example : run2.ledgerUpto 1 = run2'.ledgerUpto 1 :=
  ((Ledger.holds (Fin 4) (Fin 32) Unit bnRule32 agree32 candidates32 bnP bnLeader bnWin _ (fun _ _ _ _ _ _ => rfl)).1
    Usun Vsun Vsun' 1 1 run2 run2').2 1 (by decide)
example : run2.ledgerUpto 0 <+: run2.ledgerUpto 1 :=
  (Ledger.holds (Fin 4) (Fin 32) Unit bnRule32 agree32 candidates32 bnP bnLeader bnWin _ (fun _ _ _ _ _ _ => rfl)).2.1
    Usun Vsun 1 run2 0 1 (by decide)
example : (run2.ledgerUpto 1).Nodup :=
  (Ledger.holds (Fin 4) (Fin 32) Unit bnRule32 agree32 candidates32 bnP bnLeader bnWin _ (fun _ _ _ _ _ _ => rfl)).2.2
    Usun Vsun 1 run2 1 le_rfl
-- Two ranges at interval one: `[5, 10]` then `[15, 16]`, one list without
-- repetition.
example : runP1.ledgerUpto 2 = [5, 10, 15, 16] := by decide
example : (runP1.ledgerUpto 2).Nodup :=
  (Ledger.holds (Fin 4) (Fin 32) Unit bnRule32 agree32 candidates32 bnP1 bnLeader bnWin _ (fun _ _ _ _ _ _ => rfl)).2.2
    Usun Vsun 2 runP1 2 le_rfl

/-! ## Conservativity, through the theorem -/

/-- `run1` again, under the constant rule: the same verdicts, the anchor
at slot `2`, and the configuration after it unchanged. -/
def run1c : PartialRun bnRule bnP1 bnLeader bnWin (constRule bnRule) U7 V7 1 where
  start := fun k => if k = 0 then 0 else 2
  count := fun _ => 1
  backoff := fun _ => 0
  anchor := fun _ => 2
  vdct := vd1
  init := ⟨rfl, rfl, rfl⟩
  count_pos := fun _ => Nat.one_pos
  count_le := fun _ => by decide
  closed := by
    intro k hk κ h1 h2
    have hk0 : k = 0 := by omega
    subst hk0
    simp at h1 h2
    have : κ = 1 ∨ κ = 2 := by omega
    rcases this with rfl | rfl
    · exact Decided.directCommit (S := bnSched1) (by decide) (by decide)
    · exact Decided.directCommit (S := bnSched1) (by decide) (by decide)
  anchor_commits := by
    intro k hk
    have hk0 : k = 0 := by omega
    subst hk0
    exact ⟨⟨10, rfl⟩, by decide⟩
  anchor_least := by
    intro k hk κ hκ h
    have hk0 : k = 0 := by omega
    subst hk0
    simp at h
    have hi : bnP1.interval = 1 := rfl
    omega
  start_succ := by
    intro k hk
    have hk0 : k = 0 := by omega
    subst hk0
    rfl
  update := by
    intro k hk A hA
    have hk0 : k = 0 := by omega
    subst hk0
    rfl

example : run1c.count 1 = 1 ∧ run1c.backoff 1 = 0 :=
  (Conservativity.holds (Fin 4) (Fin 24) Unit bnRule bnP1 bnLeader bnWin).1 U7 V7 1 run1c 1 le_rfl
example : bnRule.Decided bnSched1 V7 2 (run1c.vdct 0 2) :=
  (Conservativity.holds (Fin 4) (Fin 24) Unit bnRule bnP1 bnLeader bnWin).2 U7 V7 1 run1c 0
    (by decide) 2 (by decide) (by decide)

#print axioms run2
#print axioms runP1
#print axioms run1c

end Barnacle

end LeanDagTest
