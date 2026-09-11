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

set_option maxRecDepth 2048

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

/-- The AIMD rule at the four-round interval, and the configuration it
produces from the anchor of range `0`. -/
abbrev bnUpd32 : UpdateRule bnRule32 := Aimd.rule bnRule32 bnP bnLead bnLeadKeyed

abbrev sunNext : Config (Fin 4) × ℕ := bnUpd32 bnC1 0 Usun Vsun 21

/-- The constant rule at the one-round interval, for the two-height run. -/
abbrev bnUpdC : UpdateRule bnRule32 := constRule bnRule32

/-- The verdicts of configuration `0`: slots `1` to `5` commit their
round's first leader's block. -/
def vd2 : ℕ → ℕ → Option (Fin 32) :=
  fun _ κ => if h : 1 ≤ κ ∧ κ ≤ 5 then some ⟨4 * κ + κ % 4, by omega⟩ else none

/-! ## The window, healthy -/

-- Anchor `21`: rounds `1` and `2` score at count `1`; rounds `3` to `5`
-- do not — round `3`'s only certifier in the window is the anchor.
example : observed bnRule32 bnC1 Usun 21 = 2 := by decide
example : expected bnRule32 bnC1 5 = 2 := by decide
example : sunNext.1.slotsAt 0 = 2 ∧ sunNext.2 = 0 := by decide

/-! ## The run whose count rises -/

/-- Configuration `0` closed at anchor `5`; configuration `1` at count
`2` after round `5`. `anchor_least` is vacuous here — no slot below `5`
has a round above the threshold `4` — as it is for every anchor that is
the first slot past the threshold; a non-vacuous instance needs a
skipped slot there. -/
def run2 : PartialRun bnRule32 bnP bnUpd32 bnC1 Usun Vsun 1 where
  start := fun k => if k = 0 then 0 else 5
  cfg := fun k => if k = 0 then bnC1 else sunNext.1
  backoff := fun k => if k = 0 then 0 else sunNext.2
  anchor := fun _ => 5
  vdct := vd2
  init := ⟨rfl, rfl, rfl⟩
  bounds := by
    intro k
    by_cases h : k = 0
    · subst h
      exact ⟨fun _ => (by decide : (1 : ℕ) ≤ 4), (by decide : (0 : ℕ) < 4),
        (by decide : (4 : ℕ) ≤ 4)⟩
    · simp only [h, if_false]
      exact ⟨fun r => Aimd.count_le bnP _ _ _, (by decide : (0 : ℕ) < 4),
        (by decide : (4 : ℕ) ≤ 4)⟩
  closed := by
    intro k hk κ h1 h2
    have hk0 : k = 0 := by omega
    subst hk0
    simp only [if_true, bnC1, bnCfg, Config.uniform_roundOf, Nat.div_one,
      show (0 : ℕ) + 1 = 1 from rfl, one_ne_zero, if_false] at h1 h2 ⊢
    have : κ = 1 ∨ κ = 2 ∨ κ = 3 ∨ κ = 4 ∨ κ = 5 := by omega
    rcases this with rfl | rfl | rfl | rfl | rfl <;>
      exact Decided.directCommit (S := bnC1.sched) (by decide) (by decide)
  anchor_commits := by
    intro k hk
    have hk0 : k = 0 := by omega
    subst hk0
    exact ⟨⟨21, rfl⟩, by decide⟩
  anchor_least := by
    intro k hk κ hκ h
    have hk0 : k = 0 := by omega
    subst hk0
    simp only [if_true, bnC1, bnCfg, Config.uniform_roundOf, Config.uniform_interval,
      Nat.div_one] at h
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
    rfl

/-- The same run on the smaller view. -/
def run2' : PartialRun bnRule32 bnP bnUpd32 bnC1 Usun Vsun' 1 where
  start := fun k => if k = 0 then 0 else 5
  cfg := fun k => if k = 0 then bnC1 else sunNext.1
  backoff := fun k => if k = 0 then 0 else sunNext.2
  anchor := fun _ => 5
  vdct := vd2
  init := ⟨rfl, rfl, rfl⟩
  bounds := by
    intro k
    by_cases h : k = 0
    · subst h
      exact ⟨fun _ => (by decide : (1 : ℕ) ≤ 4), (by decide : (0 : ℕ) < 4),
        (by decide : (4 : ℕ) ≤ 4)⟩
    · simp only [h, if_false]
      exact ⟨fun r => Aimd.count_le bnP _ _ _, (by decide : (0 : ℕ) < 4),
        (by decide : (4 : ℕ) ≤ 4)⟩
  closed := by
    intro k hk κ h1 h2
    have hk0 : k = 0 := by omega
    subst hk0
    simp only [if_true, bnC1, bnCfg, Config.uniform_roundOf, Nat.div_one,
      show (0 : ℕ) + 1 = 1 from rfl, one_ne_zero, if_false] at h1 h2 ⊢
    have : κ = 1 ∨ κ = 2 ∨ κ = 3 ∨ κ = 4 ∨ κ = 5 := by omega
    rcases this with rfl | rfl | rfl | rfl | rfl <;>
      exact Decided.directCommit (S := bnC1.sched) (by decide) (by decide)
  anchor_commits := by
    intro k hk
    have hk0 : k = 0 := by omega
    subst hk0
    exact ⟨⟨21, rfl⟩, by decide⟩
  anchor_least := by
    intro k hk κ hκ h
    have hk0 : k = 0 := by omega
    subst hk0
    simp only [if_true, bnC1, bnCfg, Config.uniform_roundOf, Config.uniform_interval,
      Nat.div_one] at h
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
    rfl

-- The count moved: two leaders after round `5`.
example : (run2.cfg 1).slotsAt 0 = 2 ∧ run2.start 1 = 5 ∧ run2.backoff 1 = 0 := by decide

/-! ## The results, on this data -/

/-- The laws of Mysticeti at this committee, once. -/
abbrev laws32 : bnRule32.Laws := Mysticeti.holds (Fin 4) (Fin 32) Unit

/-- And the two properties the safety results now ask for instead. -/
abbrev agree32 : Properties.Agree bnRule32.toDagRule := MysticetiProperties.agree

abbrev candidates32 : Properties.CommitsCandidate bnRule32.toDagRule :=
  MysticetiProperties.commitsCandidate

/-- BN3 on `run2` and `run2'`: the two views hold one configuration `1`
and one anchor. -/
example : run2.cfg 1 = run2'.cfg 1 ∧ run2.start 1 = run2'.start 1 :=
  let h := (Agreement.holds (Fin 4) (Fin 32) Unit bnRule32 agree32 bnP bnUpd32 bnC1
    (fun _ _ _ _ _ _ => rfl)) Usun Vsun Vsun' 1 1 run2 run2' 1 (by decide)
  ⟨h.2.1, h.1⟩
example : run2.anchor 0 = run2'.anchor 0 :=
  ((Agreement.holds (Fin 4) (Fin 32) Unit bnRule32 agree32 bnP bnUpd32 bnC1
    (fun _ _ _ _ _ _ => rfl))
    Usun Vsun Vsun' 1 1 run2 run2' 0 (by decide)).2.2.2 (by decide) |>.1

/-- BN2 on `Usun`: the smaller view holds the anchor, hence its history. -/
example : historyFrom Usun.block 21 ⊆ Vsun'.ids :=
  ((Window.holds (Fin 4) (Fin 32) Unit bnRule32).1 Usun Vsun' 21 (by decide))

/-- BN7a on the witness parameters: the rule stays in range at the values
the run meets. -/
example : (∀ r, (bnUpd32 bnC1 0 Usun (View.full Usun) 21).1.slotsAt r ≤ bnP.maxLeaders) ∧
    (bnUpd32 bnC1 0 Usun (View.full Usun) 21).1.interval = bnC1.interval :=
  (Aimd.holds (Fin 4) (Fin 32) Unit bnRule32 bnP bnLead bnLeadKeyed).1 bnC1 0 Usun
    (View.full Usun) 21
-- BN7b: below the cap, one more leader.
example : Aimd.count bnP 3 0 true = 4 :=
  (Aimd.holds (Fin 4) (Fin 32) Unit bnRule32 bnP bnLead bnLeadKeyed).2.1.1 3 0 (by decide)
-- BN7c: from count `4` at back-off `1`, strictly fewer; the step is
-- `4 - 2`; at the floor, the floor.
example : Aimd.count bnP 4 1 false < 4 :=
  (Aimd.holds (Fin 4) (Fin 32) Unit bnRule32 bnP bnLead bnLeadKeyed).2.2.1.1 4 1
    (by decide) (by decide)
example : Aimd.count bnP 4 1 false = 4 - 2 ^ 1 :=
  (Aimd.holds (Fin 4) (Fin 32) Unit bnRule32 bnP bnLead bnLeadKeyed).2.2.1.2.1 4 1
    (by decide) (by decide)
example : Aimd.count bnP 1 3 false = 1 :=
  (Aimd.holds (Fin 4) (Fin 32) Unit bnRule32 bnP bnLead bnLeadKeyed).2.2.1.2.2 3
-- BN7d: at anchor `21` and count `2` the integer test passes, so the
-- rule takes the healthy step with the back-off reset; and the
-- unhealthy branch of the same theorem is what a failing test gives.
example : (bnUpd32 bnC2 0 Usun (View.full Usun) 21).1.slotsAt =
      (fun _ => Aimd.count bnP (bnC2.slotsAt 5) 0 true) ∧
    (bnUpd32 bnC2 0 Usun (View.full Usun) 21).2 = 0 :=
  let h := (Aimd.holds (Fin 4) (Fin 32) Unit bnRule32 bnP bnLead bnLeadKeyed).2.2.2.1 bnC2 0 Usun
    (View.full Usun) 21
  ⟨h.2.2.1 (by decide), h.2.2.2.1 (by decide)⟩
example : (bnUpd32 bnC2 0 Usun (View.full Usun) 21).1.slotsAt 0 = 3 := by decide
-- `Usun` is sunny at every count, so BN7d's other branch is exercised
-- where a window does fail: on `Unemo` (`Instances.lean`).
-- On `Usun` at anchor `21` the window is healthy at the cap too — eight
-- slots score against the eight the four-wide scoring rounds offered —
-- so the count stays at the cap and the back-off stays reset.
example : observed bnRule32 bnC4 Usun 21 = 8 := by decide
example : expected bnRule32 bnC4 5 = 8 := by decide
example : (bnUpd32 bnC4 0 Usun (View.full Usun) 21).1.slotsAt 0 = 4 ∧
    (bnUpd32 bnC4 0 Usun (View.full Usun) 21).2 = 0 := by decide

/-- BN2b on two views: the views differ, the windows do not. -/
example : historyFrom Usun.block 21 ∩ Vsun.ids = historyFrom Usun.block 21 ∩ Vsun'.ids :=
  (Window.holds (Fin 4) (Fin 32) Unit bnRule32).2 Usun Vsun Vsun' 21 (by decide) (by decide)
example : Vsun.ids ≠ Vsun'.ids := by decide

/-- The `candidates` law through the run: the anchor `run2'` committed is
a candidate of its slot. -/
example : bnRule32.IsLeaderBlock bnC1.sched Usun 5 21 :=
  laws32.candidates _ _ Vsun' 5 21 (run2'.closed 0 (by decide) 5 (by decide) (by decide))

/-! ## A verdict outside the range

`run2x` is `run2'` with slot `9` committing block `0` — nonsense, but
outside range `0`, which ends at the anchor, and so unconstrained. BN3
still identifies the two runs on the range, and `decide` shows them
differ beyond it. -/

def vd2x : ℕ → ℕ → Option (Fin 32) := fun k κ => if κ = 9 then some 0 else vd2 k κ

def run2x : PartialRun bnRule32 bnP bnUpd32 bnC1 Usun Vsun' 1 where
  start := fun k => if k = 0 then 0 else 5
  cfg := fun k => if k = 0 then bnC1 else sunNext.1
  backoff := fun k => if k = 0 then 0 else sunNext.2
  anchor := fun _ => 5
  vdct := vd2x
  init := ⟨rfl, rfl, rfl⟩
  bounds := by
    intro k
    by_cases h : k = 0
    · subst h
      exact ⟨fun _ => (by decide : (1 : ℕ) ≤ 4), (by decide : (0 : ℕ) < 4),
        (by decide : (4 : ℕ) ≤ 4)⟩
    · simp only [h, if_false]
      exact ⟨fun r => Aimd.count_le bnP _ _ _, (by decide : (0 : ℕ) < 4),
        (by decide : (4 : ℕ) ≤ 4)⟩
  closed := by
    intro k hk κ h1 h2
    have hk0 : k = 0 := by omega
    subst hk0
    simp only [if_true, bnC1, bnCfg, Config.uniform_roundOf, Nat.div_one,
      show (0 : ℕ) + 1 = 1 from rfl, one_ne_zero, if_false] at h1 h2 ⊢
    have : κ = 1 ∨ κ = 2 ∨ κ = 3 ∨ κ = 4 ∨ κ = 5 := by omega
    rcases this with rfl | rfl | rfl | rfl | rfl <;>
      exact Decided.directCommit (S := bnC1.sched) (by decide) (by decide)
  anchor_commits := by
    intro k hk
    have hk0 : k = 0 := by omega
    subst hk0
    exact ⟨⟨21, rfl⟩, by decide⟩
  anchor_least := by
    intro k hk κ hκ h
    have hk0 : k = 0 := by omega
    subst hk0
    simp only [if_true, bnC1, bnCfg, Config.uniform_roundOf, Config.uniform_interval,
      Nat.div_one] at h
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
    rfl

example : run2.vdct 0 3 = run2x.vdct 0 3 :=
  ((Agreement.holds (Fin 4) (Fin 32) Unit bnRule32 agree32 bnP bnUpd32 bnC1
    (fun _ _ _ _ _ _ => rfl))
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

def runP1 : PartialRun bnRule32 bnPI1 bnUpdC bnC1I1 Usun Vsun 2 where
  start := fun k => if k = 0 then 0 else if k = 1 then 2 else 4
  cfg := fun _ => bnC1I1
  backoff := fun _ => 0
  anchor := fun k => if k = 0 then 2 else 4
  vdct := vdP1
  init := ⟨rfl, rfl, rfl⟩
  bounds := fun _ => ⟨fun _ => (by decide : (1 : ℕ) ≤ 4), by decide, by decide⟩
  closed := by
    intro k hk κ h1 h2
    have hkk : k = 0 ∨ k = 1 := by omega
    rcases hkk with rfl | rfl
    · simp only [bnC1I1, bnCfg, Config.uniform_roundOf, Nat.div_one] at h1 h2
      simp at h1 h2
      have : κ = 1 ∨ κ = 2 := by omega
      rcases this with rfl | rfl <;>
        exact Decided.directCommit (S := bnC1I1.sched) (by decide) (by decide)
    · simp only [bnC1I1, bnCfg, Config.uniform_roundOf, Nat.div_one] at h1 h2
      simp at h1 h2
      have : κ = 3 ∨ κ = 4 := by omega
      rcases this with rfl | rfl <;>
        exact Decided.directCommit (S := bnC1I1.sched) (by decide) (by decide)
  anchor_commits := by
    intro k hk
    have : k = 0 ∨ k = 1 := by omega
    rcases this with rfl | rfl
    · exact ⟨⟨10, rfl⟩, by decide⟩
    · exact ⟨⟨16, rfl⟩, by decide⟩
  anchor_least := by
    intro k hk κ hκ h
    have : k = 0 ∨ k = 1 := by omega
    rcases this with rfl | rfl <;>
      simp only [bnC1I1, bnCfg, Config.uniform_roundOf, Config.uniform_interval, Nat.div_one,
        if_true, one_ne_zero, if_false] at hκ h <;> omega
  start_succ := by
    intro k hk
    have : k = 0 ∨ k = 1 := by omega
    rcases this with rfl | rfl <;> rfl
  update := by
    intro k hk A hA
    have : k = 0 ∨ k = 1 := by omega
    rcases this with rfl | rfl
    · have hA' : A = 10 := by simp [vdP1] at hA; exact hA.symm
      subst hA'; rfl
    · have hA' : A = 16 := by simp [vdP1] at hA; exact hA.symm
      subst hA'; rfl

/-- The same execution seen from `Vsun'`, closed one configuration lower. -/
def runP1' : PartialRun bnRule32 bnPI1 bnUpdC bnC1I1 Usun Vsun' 1 where
  start := fun k => if k = 0 then 0 else 2
  cfg := fun _ => bnC1I1
  backoff := fun _ => 0
  anchor := fun _ => 2
  vdct := fun _ κ => if κ = 1 then some 5 else if κ = 2 then some 10 else none
  init := ⟨rfl, rfl, rfl⟩
  bounds := fun _ => ⟨fun _ => (by decide : (1 : ℕ) ≤ 4), by decide, by decide⟩
  closed := by
    intro k hk κ h1 h2
    have hk0 : k = 0 := by omega
    subst hk0
    simp only [bnC1I1, bnCfg, Config.uniform_roundOf, Nat.div_one, if_true,
      show (0 : ℕ) + 1 = 1 from rfl, one_ne_zero, if_false] at h1 h2
    have : κ = 1 ∨ κ = 2 := by omega
    rcases this with rfl | rfl <;>
      exact Decided.directCommit (S := bnC1I1.sched) (by decide) (by decide)
  anchor_commits := by
    intro k hk
    have hk0 : k = 0 := by omega
    subst hk0
    exact ⟨⟨10, rfl⟩, by decide⟩
  anchor_least := by
    intro k hk κ hκ h
    have hk0 : k = 0 := by omega
    subst hk0
    simp only [bnC1I1, bnCfg, Config.uniform_roundOf, Config.uniform_interval,
      Nat.div_one, if_true] at h
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

-- Two configurations close, at rounds `2` and `4`.
example : runP1.start 1 = 2 ∧ runP1.start 2 = 4 := ⟨rfl, rfl⟩
-- BN3 at heights `2` and `1`: agreement on the start of configuration `1` — not
-- pinned by `init` — and on the verdicts of range `0`; `k = 2` is not offered
-- (`2 ≤ min 2 1` fails).
example : runP1.cfg 1 = runP1'.cfg 1 ∧ runP1.start 1 = runP1'.start 1 :=
  let h := (Agreement.holds (Fin 4) (Fin 32) Unit bnRule32 agree32 bnPI1 bnUpdC bnC1I1
    (fun _ _ _ _ _ _ => rfl)) Usun Vsun Vsun' 2 1 runP1 runP1' 1 (by decide)
  ⟨h.2.1, h.1⟩
example : runP1.vdct 0 2 = runP1'.vdct 0 2 :=
  ((Agreement.holds (Fin 4) (Fin 32) Unit bnRule32 agree32 bnPI1 bnUpdC bnC1I1
    (fun _ _ _ _ _ _ => rfl))
    Usun Vsun Vsun' 2 1 runP1 runP1' 0 (by decide)).2.2.2 (by decide) |>.2 2 (by decide) (by decide)


/-! ## The ledger, through the theorem

`run2`'s range `0` commits blocks `5, 10, 15, 16, 21` — round `4`'s
leader is validator `0`; BN5 applied to
the run gives the ledger agreed with `run2'`, a prefix of itself, and
without repetition. -/

example : run2.rangeLedger 0 = [5, 10, 15, 16, 21] := by decide
example : run2.ledgerUpto 1 = [5, 10, 15, 16, 21] := by decide
example : run2.ledgerUpto 1 = run2'.ledgerUpto 1 :=
  ((Ledger.holds (Fin 4) (Fin 32) Unit bnRule32 agree32 candidates32 bnP bnUpd32 bnC1 (fun _ _ _ _ _ _ => rfl)).1
    Usun Vsun Vsun' 1 1 run2 run2').2 1 (by decide)
example : run2.ledgerUpto 0 <+: run2.ledgerUpto 1 :=
  (Ledger.holds (Fin 4) (Fin 32) Unit bnRule32 agree32 candidates32 bnP bnUpd32 bnC1 (fun _ _ _ _ _ _ => rfl)).2.1
    Usun Vsun 1 run2 0 1 (by decide)
example : (run2.ledgerUpto 1).Nodup :=
  (Ledger.holds (Fin 4) (Fin 32) Unit bnRule32 agree32 candidates32 bnP bnUpd32 bnC1 (fun _ _ _ _ _ _ => rfl)).2.2
    Usun Vsun 1 run2 1 le_rfl
-- Two ranges at interval one: `[5, 10]` then `[15, 16]`, one list without
-- repetition.
example : runP1.ledgerUpto 2 = [5, 10, 15, 16] := by decide
example : (runP1.ledgerUpto 2).Nodup :=
  (Ledger.holds (Fin 4) (Fin 32) Unit bnRule32 agree32 candidates32 bnPI1 bnUpdC bnC1I1 (fun _ _ _ _ _ _ => rfl)).2.2
    Usun Vsun 2 runP1 2 le_rfl

/-! ## Conservativity, through the theorem -/

/-- `run1` again, under the constant rule: the same verdicts, the anchor
at slot `2`, and the configuration after it unchanged. -/
def run1c : PartialRun bnRule bnPI1 (constRule bnRule) bnC1I1 U7 V7 1 where
  start := fun k => if k = 0 then 0 else 2
  cfg := fun _ => bnC1I1
  backoff := fun _ => 0
  anchor := fun _ => 2
  vdct := vd1
  init := ⟨rfl, rfl, rfl⟩
  bounds := fun _ => ⟨fun _ => (by decide : (1 : ℕ) ≤ 4), by decide, by decide⟩
  closed := by
    intro k hk κ h1 h2
    have hk0 : k = 0 := by omega
    subst hk0
    simp only [bnC1I1, bnCfg, Config.uniform_roundOf, Nat.div_one, if_true,
      show (0 : ℕ) + 1 = 1 from rfl, one_ne_zero, if_false] at h1 h2
    have : κ = 1 ∨ κ = 2 := by omega
    rcases this with rfl | rfl
    · exact Decided.directCommit (S := bnC1I1.sched) (by decide) (by decide)
    · exact Decided.directCommit (S := bnC1I1.sched) (by decide) (by decide)
  anchor_commits := by
    intro k hk
    have hk0 : k = 0 := by omega
    subst hk0
    exact ⟨⟨10, rfl⟩, by decide⟩
  anchor_least := by
    intro k hk κ hκ h
    have hk0 : k = 0 := by omega
    subst hk0
    simp only [bnC1I1, bnCfg, Config.uniform_roundOf, Config.uniform_interval,
      Nat.div_one, if_true] at h
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

example : run1c.cfg 1 = bnC1I1 ∧ run1c.backoff 1 = 0 :=
  (Conservativity.holds (Fin 4) (Fin 24) Unit bnRule bnPI1 bnC1I1).1 U7 V7 1 run1c 1 le_rfl
example : bnRule.Decided bnC1I1.sched V7 2 (run1c.vdct 0 2) :=
  (Conservativity.holds (Fin 4) (Fin 24) Unit bnRule bnPI1 bnC1I1).2 U7 V7 1 run1c 0
    (by decide) 2 (by decide) (by decide)

#print axioms run2
#print axioms runP1
#print axioms run1c

end Barnacle

end LeanDagTest
