import LeanDagTest.Mysticeti.Model
import LeanDagTest.Odontoceti.Model
import LeanDag.Barnacle.Model.Run
import LeanDagTest.Barnacle.Rules.Mysticeti.Proof
import LeanDag.Barnacle.Helpers.Schedule
import LeanDag.Barnacle.Helpers.Cover
import LeanDag.Barnacle.Healthy.Proof
/-!
# Barnacle witnesses — the definitions on data

Every definition of `LeanDag/Barnacle/Model/` settled by `decide`
on the existing four- and six-validator universes before anything is
proved from it (`barnacle.md` §9). What this file exhibits:

* `Sched` genuinely has `m` slots per round: at count `2` slots `10`
  and `11` share round `5`, are led by different validators, and slot
  `(5, 1)` has exactly one candidate — block `22` — that no slot has at
  count `1`; at the cap, count `4`, every validator leads every round,
  and `Keyed` fails one past it.
* `observed` reads the window, and the window matters: on `U7` with an
  anchor at round `5` and an interval of four rounds, two slots score
  at count `1`, three at count `2`, five at count `4`; on `Uodo` the
  count is `m` at every `m`. Slot `(3, 1)` — block `12`, two rounds
  below the anchor — is directly committed on the full view and *not*
  on the window, where its only certifier is the anchor itself. This is
  the data point behind the `expected` formula (`barnacle.md` §4,
  F2): the round `r − 2` cannot score inside a window that ends at `r`.
* The `d ≤ round` guard of `observed` is needed: at an anchor below the
  interval the unguarded count would score round `0` twice.
* `Aimd.update` on both branches: the cap, the floor, the doubling and
  the reset; `Aimd.rule` on real windows in both directions, at the cap
  and at the floor; `constRule`; `ledgerOf`.
* A slot with two candidates — the equivocator of `U6` — has one
  directly committed block: the slot count and the paper's block count
  agree.
* `PartialRun` at height `1`, every clause discharged on data: at
  interval `1` slots `1` and `2` commit directly, slot `2` is the anchor,
  the window is unhealthy, and the back-off moves.

The schedules are local to this file, and every use names its
schedule: `Fin 4` and `Fin 6` carry other `Slots` instances in the test
library.
-/

namespace LeanDagTest

namespace Barnacle

set_option maxRecDepth 2048

open LeanDag LeanDag.Barnacle

/-! ## The committee, the leader function, the parameters -/

/-- The witness leader function on four validators. -/
def bnLeader : ℕ → Fin 4 := roundRobin 4 (by omega)

/-- Round-robin's distinctness, from `Helpers/Schedule.lean`. -/
theorem bnWin : Keyed bnLeader 4 := roundRobin_keyed 4 (by omega)

/-- Four-round interval, at most four leaders, threshold `96 / 100`. -/
def bnP : Params := ⟨4, 4, 96, 100, 0, by decide, by decide⟩

/-- One-round interval; `expected` truncates to `m`. -/
def bnP1 : Params := ⟨1, 4, 96, 100, 0, by decide, by decide⟩

/-- Three-round interval — one wave. -/
def bnP3 : Params := ⟨3, 4, 96, 100, 0, by decide, by decide⟩

/-- Mysticeti over the four-validator committee of `LeanDagTest/Model.lean`. -/
abbrev bnRule : BaseRule (Fin 4) (Fin 24) Unit := mysticeti

/-- The schedule at count `1`. -/
abbrev bnSched1 : Slots (Fin 4) := Sched bnLeader bnWin 1 (by decide) (by decide)

/-- The schedule at count `2`. -/
abbrev bnSched2 : Slots (Fin 4) := Sched bnLeader bnWin 2 (by decide) (by decide)

/-- The schedule at the cap, count `4`. -/
abbrev bnSched4 : Slots (Fin 4) := Sched bnLeader bnWin 4 (by decide) (by decide)

/-! ## The schedule of a configuration -/

-- At count `2`, slots `10` and `11` share round `5`; at count `1` slot `5`
-- is round `5`.
example : bnSched2.slotRound 10 = 5 := by decide
example : bnSched2.slotRound 11 = 5 := by decide
example : bnSched1.slotRound 5 = 5 := by decide

-- The two slots of round `5` are led by different validators — `(5 + 0) % 4`
-- and `(5 + 1) % 4` — which is what `Slots.keyed` needs; and slot `(5, 0)`
-- has the same leader at both counts: the leader function does not depend
-- on the count.
example : bnSched2.leader 10 = 1 := by decide
example : bnSched2.leader 11 = 2 := by decide
example : bnSched1.leader 5 = 1 := by decide

-- At the cap every validator leads every round.
example : (Finset.range 4).image (fun l => bnSched4.leader (20 + l)) = Finset.univ := by decide

/-- One past the cap the leaders of a round repeat: slots `0` and `4` of
a five-count round `0` are both led by validator `0`. `Keyed` is a
`∀ ℕ`, so its failure is a term, not a `decide`. -/
example : ¬ Keyed bnLeader 5 :=
  fun h => absurd (h 5 (by decide) le_rfl 0 4 rfl rfl) (by decide)

-- Slot `(5, 1)` has exactly one candidate at count `2`: block `22`, round
-- `5`, author `2`. At count `1` no slot of round `5` is led by validator `2`.
example : Finset.univ.filter (fun L => bnRule.IsLeaderBlock bnSched2 U7 11 L) = {22} := by
  decide
example : bnRule.IsLeaderBlock bnSched2 U7 10 21 := by decide
example : ¬ bnRule.IsLeaderBlock bnSched1 U7 5 22 := by decide

/-! ## The window -/

-- The window of anchor `20` (round `5`, author `0`) is its causal history,
-- not the full view: eighteen of the twenty-four blocks.
example : bnRule.viewIds (bnRule.historyView U7 20 (by decide)) =
    {0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 12, 13, 14, 16, 17, 18, 20} := by decide

-- Interval four: window rounds `1` to `5`.
example : observed bnRule bnP bnLeader bnWin U7 20 1 (by decide) (by decide) = 2 := by decide
example : observed bnRule bnP bnLeader bnWin U7 20 2 (by decide) (by decide) = 3 := by decide
example : observed bnRule bnP bnLeader bnWin U7 20 4 (by decide) (by decide) = 5 := by decide
example : expected bnRule bnP 1 = 2 := by decide
example : expected bnRule bnP 2 = 4 := by decide

-- Which slots score at count `2`: round `1` at both offsets and round `2`
-- at offset `0` — rounds `r − 4` and `r − 3`.
example : bnRule.SlotDirect bnSched2 U7 (bnRule.historyView U7 20 (by decide)) (2 * 1 + 0) := by
  decide
example : bnRule.SlotDirect bnSched2 U7 (bnRule.historyView U7 20 (by decide)) (2 * 1 + 1) := by
  decide
example : bnRule.SlotDirect bnSched2 U7 (bnRule.historyView U7 20 (by decide)) (2 * 2 + 0) := by
  decide
-- Slot `(2, 1)`'s candidate, block `11`, has no certificate anywhere.
example : ¬ bnRule.SlotDirect bnSched2 U7 (bnRule.historyView U7 20 (by decide)) (2 * 2 + 1) := by
  decide
example : certificates U7 11 2 = ∅ := by decide

-- **The window is what stops round `r − 2`.** Slot `(3, 1)`'s candidate,
-- block `12`, has three certifiers on the full view and is directly
-- committed there; on the window its only certifier is the anchor itself,
-- one short of the quorum's three, and it is not.
example : bnRule.IsLeaderBlock bnSched2 U7 7 12 := by decide
example : certificates U7 12 3 ∩ V7.ids = {20, 21, 22} := by decide
example : certificates U7 12 3 ∩ (U7.historyView 20 (by decide)).ids = {20} := by decide
example : bnRule.SlotDirect bnSched2 U7 (bnRule.full U7) 7 := by decide
example : ¬ bnRule.SlotDirect bnSched2 U7 (bnRule.historyView U7 20 (by decide)) 7 := by decide
-- Slot `(3, 0)`'s candidate, block `15`, has no certificate anywhere: it
-- fails on the DAG, not on the window.
example : certificates U7 15 3 = ∅ := by decide

-- **The guard `d ≤ round`.** Anchor `12` sits at round `3`, below the
-- interval; without the guard round `0` would be counted twice.
example : observed bnRule bnP bnLeader bnWin U7 12 2 (by decide) (by decide) = 1 := by decide
example : bnRule.SlotDirect bnSched2 U7 (bnRule.historyView U7 12 (by decide)) 1 := by decide

-- `expected` truncates below one wave: intervals `1` and `3` give the same
-- number at count `2`.
example : expected bnRule bnP1 2 = 2 := by decide
example : expected bnRule bnP3 2 = 2 := by decide

/-! ## The AIMD rule -/

-- Healthy: one more leader, back-off reset; capped at `maxLeaders`.
example : Aimd.update bnP 2 3 true = (3, 0) := by decide
example : Aimd.update bnP 4 0 true = (4, 0) := by decide
-- Unhealthy: `2^backoff` fewer, back-off doubled; floored at one.
example : Aimd.update bnP 4 1 false = (2, 2) := by decide
example : Aimd.update bnP 1 3 false = (1, 4) := by decide

-- On `U7` at count `2` the window is unhealthy (`100 · 3 < 96 · 4`); at
-- count `4` too (`100 · 5 < 96 · 8`); at count `1` it is healthy
-- (`100 · 2 ≥ 96 · 2`).
example : Aimd.rule bnRule bnP bnLeader bnWin 2 0 U7 (View.full U7) 20 = (1, 1) := by decide

/-! ## BN12 on data: a healthy window, and the step it forces

At count `1` the anchor `20` scores both of its scoring rounds — `d = 3`
and `d = 4`, the wave and the interval — so the window is healthy in the
sense of `Healthy.WindowHealthy`, and BN12 turns that into the count's
rise with no appeal to `decide` on the rule itself. -/

theorem u7_window_healthy :
    Healthy.WindowHealthy bnRule bnP bnLeader bnWin U7 20 (by decide) 1
      (by decide) (by decide) := by
  intro d h1 h2 l hl
  change 3 ≤ d at h1
  change d ≤ 4 at h2
  change l < 1 at hl
  interval_cases d <;> interval_cases l <;> decide

/-- **BN12b applied**: the rule raises the count to `2` and resets the
back-off, because the window is healthy — not because the arithmetic was
computed. -/
example : Aimd.rule bnRule bnP bnLeader bnWin 1 0 U7 (View.full U7) 20 = (2, 0) :=
  (Healthy.holds (Fin 4) (Fin 24) Unit bnRule bnP bnLeader bnWin
      MysticetiProperties.commitsDirect).2.1 U7 20 (by decide) 1
    (by decide) (by decide) 0 (View.full U7) (by decide) (by decide) (by decide)
    u7_window_healthy

/-- And `observed` meets `expected` there, which is BN12a. -/
example : expected bnRule bnP 1 ≤ observed bnRule bnP bnLeader bnWin U7 20 1
    (by decide) (by decide) :=
  (Healthy.holds (Fin 4) (Fin 24) Unit bnRule bnP bnLeader bnWin
      MysticetiProperties.commitsDirect).1 U7 20 (by decide) 1
    (by decide) (by decide) (by decide) (by decide) u7_window_healthy

/-- **BN12c applied**: every slot the healthy window counted is a
commit *verdict*, not merely a slot whose direct predicate held. -/
example : ∀ d, bnRule.waveLength ≤ d → d ≤ bnP.interval → ∀ l, l < 1 →
    ∃ L, bnRule.Decided (Sched bnLeader bnWin 1 (by decide) (by decide))
      (bnRule.historyView U7 20 (by decide)) (1 * ((bnRule.block U7 20).round - d) + l)
      (some L) :=
  (Healthy.holds (Fin 4) (Fin 24) Unit bnRule bnP bnLeader bnWin
      MysticetiProperties.commitsDirect).2.2
    U7 20 (by decide) 1 (by decide) (by decide) u7_window_healthy

#print axioms LeanDag.Barnacle.Healthy.holds
example : Aimd.rule bnRule bnP bnLeader bnWin 4 0 U7 (View.full U7) 20 = (3, 1) := by decide
example : Aimd.rule bnRule bnP bnLeader bnWin 1 0 U7 (View.full U7) 20 = (2, 0) := by decide
-- At the floor, an unhealthy window (anchor `12`, nothing scores at
-- count `1`) leaves the count at one and doubles the back-off.
example : Aimd.rule bnRule bnP bnLeader bnWin 1 3 U7 (View.full U7) 12 = (1, 4) := by decide
-- Outside `[1, maxLeaders]` the rule returns the initial state.
example : Aimd.rule bnRule bnP bnLeader bnWin 5 0 U7 (View.full U7) 20 = (1, 0) := by decide

-- The constant rule reconfigures nothing.
example : constRule bnRule 2 3 U7 (View.full U7) 20 = (2, 3) := by decide

-- The ledger of a slot interval: `lo` inclusive, `hi` exclusive, skips dropped.
example : ledgerOf (fun k => if k = 3 then some (7 : Fin 24) else if k = 5 then some 9 else none)
    2 6 = [7, 9] := by decide
example : ledgerOf (fun k => if k = 3 then some (7 : Fin 24) else if k = 5 then some 9 else none)
    3 5 = [7] := by decide

/-! ## Six validators: `Uodo` -/

/-- Mysticeti over the six-validator committee of the Odontoceti model;
`Faults5` supplies `Faults`. -/
abbrev bnRule6 : BaseRule (Fin 6) (Fin 24) Unit := mysticeti

def bnLeader6 : ℕ → Fin 6 := roundRobin 6 (by omega)

theorem bnWin6 : Keyed bnLeader6 6 := roundRobin_keyed 6 (by omega)

/-- Three-round interval, at most six leaders. -/
def bnP6 : Params := ⟨3, 6, 96, 100, 0, by decide, by decide⟩

-- Anchor `20` (round `3`); one scoring round, every slot of it scores.
example : observed bnRule6 bnP6 bnLeader6 bnWin6 Uodo 20 1 (by decide) (by decide) = 1 := by
  decide
example : observed bnRule6 bnP6 bnLeader6 bnWin6 Uodo 20 2 (by decide) (by decide) = 2 := by
  decide
example : observed bnRule6 bnP6 bnLeader6 bnWin6 Uodo 20 6 (by decide) (by decide) = 6 := by
  decide
example : expected bnRule6 bnP6 6 = 6 := by decide
-- Healthy at every count: the count rises, and stays capped at six.
example : Aimd.rule bnRule6 bnP6 bnLeader6 bnWin6 1 0 Uodo (View.full Uodo) 20 = (2, 0) := by decide
example : Aimd.rule bnRule6 bnP6 bnLeader6 bnWin6 6 0 Uodo (View.full Uodo) 20 = (6, 0) := by decide

/-! ## Slots against blocks: the equivocator of `U6`

`U6` (`LeanDagTest/Model.lean`) has Byzantine validator `0` proposing two
round-`0` blocks, `0` and `4`. Slot `0` of `Sched 1` therefore has two
candidates, of which exactly one is directly committed on the full view:
the slot count `SlotDirect` and the paper's count over leader blocks
agree, as the interface's `agree` law says they must. -/

abbrev bnRule13 : BaseRule (Fin 4) (Fin 13) Unit := mysticeti

example : Finset.univ.filter (fun L => bnRule13.IsLeaderBlock bnSched1 U6 0 L) = {0, 4} := by
  decide
example : bnRule13.SlotDirect bnSched1 U6 (bnRule13.full U6) 0 := by decide
example : Finset.univ.filter (fun L => bnRule13.IsLeaderBlock bnSched1 U6 0 L ∧
    bnRule13.DirectCommitIn (bnRule13.full U6) L 0) = {0} := by decide

/-! ## The laws, exercised through the interface

`Mysticeti.holds` applied at `U7`: a directly committed candidate is a
commit verdict, on the full view `V7` and on the smaller `V7small`. What
the witness exercises is the proved statement, not a restatement. -/

example : bnRule.Decided bnSched2 V7 7 (some 12) :=
  (Mysticeti.holds (Fin 4) (Fin 24) Unit).commitsDirect bnSched2 _ V7 7 12
    (by decide) (by decide)
example : bnRule.Decided bnSched1 V7small 2 (some 10) :=
  (Mysticeti.holds (Fin 4) (Fin 24) Unit).commitsDirect bnSched1 _ V7small 2 10
    (by decide) (by decide)

/-! ## The run, at height one

At interval `1` and count `1`, slots `1` and `2` of `Sched 1` (blocks `5`
and `10`) commit directly; slot `2`, at round `2 > 0 + 1`, is the anchor.
Its window scores nothing (`observed = 0` against `expected = 1`), so
the count stays at the floor and the back-off moves to `1`. Every clause
of `PartialRun` is discharged on data. A run whose count *rises* needs a
healthy window — an interval of at least three rounds and an anchor
committed on `V7` at round `4` or above — and `U7` has no committed slot
there; that is Phase 2's witness, on a taller universe. -/

/-- The verdicts of configuration `0`. -/
def vd1 : ℕ → ℕ → Option (Fin 24) :=
  fun _ κ => if κ = 1 then some 5 else if κ = 2 then some 10 else none

def run1 : PartialRun bnRule bnP1 bnLeader bnWin (Aimd.rule bnRule bnP1 bnLeader bnWin) U7 V7 1
    where
  start := fun k => if k = 0 then 0 else 2
  count := fun _ => 1
  backoff := fun k => if k = 0 then 0 else 1
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
    have hA' : A = 10 := by
      simp [vd1] at hA; exact hA.symm
    subst hA'
    decide

-- The configuration the anchor produced: count at the floor, back-off one,
-- in force after round `2`.
example : run1.count 1 = 1 ∧ run1.backoff 1 = 1 ∧ run1.start 1 = 2 := ⟨rfl, rfl, rfl⟩
example : observed bnRule bnP1 bnLeader bnWin U7 10 1 (by decide) (by decide) = 0 := by decide

/-! ## Axioms

Nothing here should ever acquire an axiom beyond the standard three. -/

#print axioms LeanDag.Barnacle.Mysticeti.holds
#print axioms LeanDag.Barnacle.roundRobin_keyed
#print axioms run1

end Barnacle

end LeanDagTest
