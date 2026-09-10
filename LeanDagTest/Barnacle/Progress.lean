import LeanDagTest.Barnacle.Agreement
import LeanDag.Barnacle.Progress.Proof
import Mathlib.Tactic.IntervalCases

/-!
# Barnacle witnesses — progress on data

`LiveOn` quantifies over every DAG the rule calls good, so it cannot be
decided in general; a *test rule* makes it finite. `bnLive` is Mysticeti
with `Good U Rnd N := U = Usun ∧ Rnd = 1 ∧ N = 8` — `Usun` decides
rounds up to `5`, one wave below `8` — so `bnLive.LiveOn` at a schedule
is a statement about five slots and five rounds of `Usun`, settled leaf
by leaf: a wrong verdict fails the build. `Good` is a bare data field
that no law constrains, which is what makes the test rule legitimate.

What the file exhibits:

* **BN8a applied on data.** From the height-`0` run at interval `4` and
  gap `0`, `Progress.holds` yields a height-`1` run. Its configuration
  `1` is read through BN3 against `run2`: `count 1 = 2`, `start 1 = 5`,
  `anchor 0 = 5` — the healthy step. The theorem supplies existence; the
  values are forced on every inhabitant of the type by `update` and
  BN3, which is the strongest reading a `Nonempty` conclusion admits.
* **Progress from height one.** At interval `1` a height-`1` run on the
  full view extends to height `2` by the theorem at gap `0`, and BN3
  identifies the result with `runP1`; at gap `1` the margin `2c + w`
  above the threshold no longer fits under `8`.
* **A gap that matters.** `Usk` is `Usun` with one block referenced by
  its author alone, so slot `2` is directly skipped: `LiveOn` at gap
  `0` is *false* there and at gap `1` true, and the theorem's anchor —
  slot `3` — skips slot `2`, which lies past the threshold:
  `anchor_least` is exercised through the theorem.
* **`LiveOn` is not automatic.** One round further, `N = 9`, `Usun` is
  not live at gap `0`: round `6` has no committed slot. And `UpdBounded`
  fails for rules that leave the range.
* `EveryHeight` reaches height `1` under horizon `8` at interval `4` and
  height `2` at interval `1`; height `2` at interval `4` needs `13`.
-/

namespace LeanDagTest
namespace Barnacle

set_option maxRecDepth 4096

open LeanDag LeanDag.Barnacle

/-- (E) the `with` spelling -/
def bnLive : LiveRule (Fin 4) (Fin 32) Unit :=
  { mysticeti with Good := fun U Rnd N => U = Usun ∧ Rnd = 1 ∧ N = 8 }

/-- (E) the `where` spelling -/
def bnLive' : LiveRule (Fin 4) (Fin 32) Unit where
  toBaseRule := mysticeti
  Good := fun U Rnd N => U = Usun ∧ Rnd = 1 ∧ N = 8

example : bnLive.toBaseRule = bnRule32 := rfl
example : bnLive.full Usun = Vsun := rfl
example : bnLive.full Usun = LeanDag.View.full Usun := rfl
example : bnLive.waveLength = 3 := rfl

-- `Good` is a genuine predicate.
example : bnLive.Good Usun 1 8 := ⟨rfl, rfl, rfl⟩
example : ¬ bnLive.Good Usun 1 9 := fun h => absurd h.2.2 (by decide)

abbrev sched1 : Slots (Fin 4) := bnC1.sched

/-- **The configurations the AIMD rule emits**: one width throughout, on
the witness leaders. Whatever it reads, `Aimd.rule` writes a
`Config.uniform`, so this is the clause BN8b's liveness hypothesis has to
cover — and not every configuration inside the bounds. -/
def BnUniform (C : Config (Fin 4)) : Prop :=
  ∃ m I, ∃ hm : 0 < m, ∃ hmax : m ≤ 4, C = Config.uniform bnLead bnLeadKeyed m hm hmax I

theorem bnC1_uniform : BnUniform bnC1 := ⟨1, 4, by decide, by decide, rfl⟩
theorem bnC1I1_uniform : BnUniform bnC1I1 := ⟨1, 1, by decide, by decide, rfl⟩

/-- At one leader a round, slot `κ` is round `κ`. -/
@[simp] theorem sched1_slotRound (κ : ℕ) : sched1.slotRound κ = κ := by
  simp only [sched1, Config.sched_slotRound, bnC1, bnCfg, Config.uniform_roundOf, Nat.div_one]

/-- **The full view's verdicts transport to any view caught up to `8`.**
Every block of `Usun` lies at a round at or below `8`, so a view covering
that far holds the whole universe and `decided_mono` carries each verdict
across. This is what lets the checks below stay `decide`-shaped while the
statement quantifies over a validator's own view. -/
theorem transport_full {V : bnLive.View Usun}
    (hcov : bnLive.toBaseRule.CoversUpto Usun V 8) {S : Slots (Fin 4)} {κ : ℕ}
    {v : Option (Fin 32)} (h : Decided (S := S) Usun (View.full Usun) κ v) :
    Decided (S := S) Usun V κ v := by
  have hround : ∀ b ∈ Usun.ids, (Usun.block b).round ≤ 8 := by decide
  exact AnchoredRule.decided_mono coreLaws trivial (S := S) (fun b hb => hcov b hb (hround b hb)) h

/-- `LiveOn` at count `1`, gap `0`, on `Usun`: slots `1`–`5` commit directly. -/
theorem bnLive_liveOn : bnLive.LiveOn sched1 0 := by
  rintro U V Rnd N ⟨rfl, rfl, rfl⟩ hcov
  have hw : bnLive.waveLength = 3 := rfl
  -- every block of `Usun` lies at a round the view covers, so the view holds
  -- the whole universe and the full-view verdicts transport to it
  have hcom : ∀ (κ : ℕ) (L : Fin 32), bnLive.Decided sched1 (bnLive.full Usun) κ (some L) →
      bnLive.Decided sched1 V κ (some L) := fun _ _ h => transport_full hcov h
  have h1 : bnLive.Decided sched1 (bnLive.full Usun) 1 (some 5) :=
    Decided.directCommit (S := sched1) (by decide) (by decide)
  have h2 : bnLive.Decided sched1 (bnLive.full Usun) 2 (some 10) :=
    Decided.directCommit (S := sched1) (by decide) (by decide)
  have h3 : bnLive.Decided sched1 (bnLive.full Usun) 3 (some 15) :=
    Decided.directCommit (S := sched1) (by decide) (by decide)
  have h4 : bnLive.Decided sched1 (bnLive.full Usun) 4 (some 16) :=
    Decided.directCommit (S := sched1) (by decide) (by decide)
  have h5 : bnLive.Decided sched1 (bnLive.full Usun) 5 (some 21) :=
    Decided.directCommit (S := sched1) (by decide) (by decide)
  refine ⟨?_, ?_⟩
  · intro κ ha hb
    simp only [sched1_slotRound] at ha hb
    have : κ = 1 ∨ κ = 2 ∨ κ = 3 ∨ κ = 4 ∨ κ = 5 := by omega
    rcases this with rfl | rfl | rfl | rfl | rfl
    · exact ⟨some 5, hcom _ _ h1⟩
    · exact ⟨some 10, hcom _ _ h2⟩
    · exact ⟨some 15, hcom _ _ h3⟩
    · exact ⟨some 16, hcom _ _ h4⟩
    · exact ⟨some 21, hcom _ _ h5⟩
  · intro r ha hb
    have : r = 1 ∨ r = 2 ∨ r = 3 ∨ r = 4 ∨ r = 5 := by omega
    rcases this with rfl | rfl | rfl | rfl | rfl
    · exact ⟨1, by rw [sched1_slotRound]; try omega, by rw [sched1_slotRound]; try omega, 5, hcom _ _ h1⟩
    · exact ⟨2, by rw [sched1_slotRound]; try omega, by rw [sched1_slotRound]; try omega, 10, hcom _ _ h2⟩
    · exact ⟨3, by rw [sched1_slotRound]; try omega, by rw [sched1_slotRound]; try omega, 15, hcom _ _ h3⟩
    · exact ⟨4, by rw [sched1_slotRound]; try omega, by rw [sched1_slotRound]; try omega, 16, hcom _ _ h4⟩
    · exact ⟨5, by rw [sched1_slotRound]; try omega, by rw [sched1_slotRound]; try omega, 21, hcom _ _ h5⟩

abbrev bnUpdL : UpdateRule bnLive.toBaseRule := Aimd.rule bnRule32 bnP bnLead bnLeadKeyed

theorem bnUpdL_bounded : UpdBounded bnP bnUpdL := by
  intro C b U V A _ hpos hle
  exact ⟨fun r => Aimd.count_le bnP _ _ _, hpos, hle⟩

theorem bnUpdL_uniform : UpdKeeps bnUpdL BnUniform := by
  intro C b U V A _
  exact ⟨_, _, Aimd.count_pos bnP _ _ _, Aimd.count_le bnP _ _ _, rfl⟩

/-- The height-`0` run. -/
def run0 : PartialRun bnLive.toBaseRule bnP bnUpdL bnC1 Usun (bnLive.full Usun) 0 :=
  PartialRun.zero _ bnP bnUpdL bnC1 (fun _ => (by decide : (1 : ℕ) ≤ 4))
    (by decide) (by decide) Usun (bnLive.full Usun)

/-- BN8a applied on data: a height-`1` run exists, and BN3 identifies its
configuration `1` with `run2`'s — two leaders after round `5`. -/
example :
    ∃ Rn1 : PartialRun bnLive.toBaseRule bnP bnUpdL bnC1 Usun (bnLive.full Usun) 1,
    (Rn1.cfg 1).slotsAt 0 = 2 ∧ Rn1.start 1 = 5 ∧ Rn1.anchor 0 = 5 := by
  obtain ⟨Rn1⟩ := (Progress.holds (Fin 4) (Fin 32) Unit bnLive MysticetiProperties.agree bnP
    bnUpdL bnUpdL_bounded bnC1 BnUniform bnUpdL_uniform 0).1 Usun (bnLive.full Usun) 1 8 0
    (coversUpto_full laws32.full_ids Usun 8) run0 bnLive_liveOn
    (show bnLive.Good Usun 1 8 from ⟨rfl, rfl, rfl⟩) (by decide) (by decide)
  refine ⟨Rn1, ?_⟩
  have h := (Agreement.holds (Fin 4) (Fin 32) Unit bnRule32 agree32 bnP bnUpdL bnC1
    (fun _ _ _ _ _ _ => rfl)) Usun (bnLive.full Usun) Vsun 1 1 Rn1 run2 1 (by decide)
  have h0 := (Agreement.holds (Fin 4) (Fin 32) Unit bnRule32 agree32 bnP bnUpdL bnC1
    (fun _ _ _ _ _ _ => rfl)) Usun (bnLive.full Usun) Vsun 1 1 Rn1 run2 0 (by decide)
  exact ⟨by rw [h.2.1]; decide, h.1, (h0.2.2.2 (by decide)).1⟩

-- The bound form too.
example :
    ∃ Rn1 : PartialRun bnLive.toBaseRule bnP bnUpdL bnC1 Usun (bnLive.full Usun) 1,
    Rn1.start 1 ≤ 0 + 4 + 1 + 0 := by
  obtain ⟨Rn1, hb, -⟩ := progress_exists MysticetiProperties.agree bnUpdL_bounded bnUpdL_uniform
    (coversUpto_full laws32.full_ids Usun 8) run0 bnLive_liveOn bnC1_uniform
    (show bnLive.Good Usun 1 8 from ⟨rfl, rfl, rfl⟩) (by decide) (by decide)
  exact ⟨Rn1, hb⟩

-- horizon values
example : horizon bnP bnLive 0 1 = 8 := by decide
example : horizon bnP bnLive 0 2 = 13 := by decide

/-- `LiveOn` at every uniform configuration, gap `0`, on `Usun`: the
schedule of `Config.uniform … m …` is `Sched … m`, so the four counts
`1`–`4` are the whole hypothesis. -/
theorem bnLive_liveOn_all : ∀ C : Config (Fin 4), BnUniform C → bnLive.LiveOn C.sched 0 := by
  rintro C ⟨m, I, hm, hmax, rfl⟩
  rw [bnUniform_sched m I hm hmax]
  have hmax' : m ≤ 4 := hmax
  rintro U V Rnd N ⟨rfl, rfl, rfl⟩ hcov
  have hw : bnLive.waveLength = 3 := rfl
  refine ⟨?_, ?_⟩
  · intro κ h1 h2
    simp only [Sched_slotRound] at h1 h2
    refine ⟨some ⟨(4 * (κ / m) + (κ / m + κ % m) % 4) % 32, Nat.mod_lt _ (by decide)⟩,
      ?_⟩
    interval_cases m
    · obtain ⟨hlo, hhi⟩ : 1 ≤ κ ∧ κ < 6 := by omega
      interval_cases κ <;>
        exact transport_full hcov <| Decided.directCommit
          (S := Sched bnLeader bnWin 1 (by decide) (by decide))
          (by decide) (by decide)
    · obtain ⟨hlo, hhi⟩ : 2 ≤ κ ∧ κ < 12 := by omega
      interval_cases κ <;>
        exact transport_full hcov <| Decided.directCommit
          (S := Sched bnLeader bnWin 2 (by decide) (by decide))
          (by decide) (by decide)
    · obtain ⟨hlo, hhi⟩ : 3 ≤ κ ∧ κ < 18 := by omega
      interval_cases κ <;>
        exact transport_full hcov <| Decided.directCommit
          (S := Sched bnLeader bnWin 3 (by decide) (by decide))
          (by decide) (by decide)
    · obtain ⟨hlo, hhi⟩ : 4 ≤ κ ∧ κ < 24 := by omega
      interval_cases κ <;>
        exact transport_full hcov <| Decided.directCommit
          (S := Sched bnLeader bnWin 4 (by decide) (by decide))
          (by decide) (by decide)
  · intro r h1 h2
    refine ⟨m * r, ?_, ?_, ⟨(4 * r + r % 4) % 32, Nat.mod_lt _ (by decide)⟩, ?_⟩
    · simp only [Sched_slotRound, Nat.mul_div_cancel_left _ hm]; omega
    · simp only [Sched_slotRound, Nat.mul_div_cancel_left _ hm]; omega
    · obtain ⟨hlo, hhi⟩ : 1 ≤ r ∧ r ≤ 5 := by omega
      interval_cases m <;> interval_cases r <;>
        exact transport_full hcov <| Decided.directCommit
          (S := Sched bnLeader bnWin _ (by decide) (by decide)) (by decide) (by decide)

/-- BN8b applied on data: height `1` under horizon `8`. -/
example : Nonempty (PartialRun bnLive.toBaseRule bnP bnUpdL bnC1 Usun (bnLive.full Usun) 1) :=
  everyHeight MysticetiProperties.agree bnUpdL_bounded bnUpdL_uniform
    (fun C _ _ _ hC => bnLive_liveOn_all C hC) (fun _ => (by decide : (1 : ℕ) ≤ 4))
    (by decide) (by decide) bnC1_uniform (coversUpto_full laws32.full_ids Usun 8)
    (show bnLive.Good Usun 1 8 from ⟨rfl, rfl, rfl⟩) le_rfl 1 (by decide)

-- Through `holds`.
example : Nonempty (PartialRun bnLive.toBaseRule bnP bnUpdL bnC1 Usun (bnLive.full Usun) 1) :=
  ((Progress.holds (Fin 4) (Fin 32) Unit bnLive MysticetiProperties.agree bnP bnUpdL
    bnUpdL_bounded bnC1 BnUniform bnUpdL_uniform 0).2
    (fun C _ _ _ hC => bnLive_liveOn_all C hC) (fun _ => (by decide : (1 : ℕ) ≤ 4))
    (by decide) (by decide) bnC1_uniform Usun (bnLive.full Usun) 1 8 ⟨rfl, rfl, rfl⟩
    (coversUpto_full laws32.full_ids Usun 8) le_rfl 1 (by decide))
example : Nonempty (PartialRun bnLive.toBaseRule bnP bnUpdL bnC1 Usun (bnLive.full Usun) 1) :=
  ((Progress.holds (Fin 4) (Fin 32) Unit bnLive MysticetiProperties.agree bnP bnUpdL
    bnUpdL_bounded bnC1 BnUniform bnUpdL_uniform 0).1
    Usun (bnLive.full Usun) 1 8 0 (coversUpto_full laws32.full_ids Usun 8) run0 bnLive_liveOn
    ⟨rfl, rfl, rfl⟩ (by decide) (by decide))

-- Height 2 at interval 4 is out of the horizon: `13 ≤ 8` is false.
example : ¬ (horizon bnP bnLive 0 2 ≤ 8) := by decide

/-! ## Rules that leave the range are not bounded

A round wider than the committee is not among the failures available
here: `Config.keyed` asks the leaders of a round to be distinct, so on
four validators no configuration has a round of five slots at all. What
a rule can still do is emit an interval outside `[1, maxInterval]`. -/

/-- A rule that reconfigures to a zero interval: `interval_pos` fails. -/
example : ¬ UpdBounded bnP
    (fun _ b _ _ _ => (Config.uniform bnLead bnLeadKeyed 4 (by decide) (by decide) 0, b)
      : UpdateRule bnRule32) :=
  fun h => absurd (h bnC1 0 Usun (View.full Usun) 0
    (fun _ => (by decide : (1 : ℕ) ≤ 4)) (by decide) (by decide)).2.1 (by decide)

/-- A rule that reconfigures past the interval bound: `interval_le` fails. -/
example : ¬ UpdBounded bnP
    (fun _ b _ _ _ => (Config.uniform bnLead bnLeadKeyed 4 (by decide) (by decide) 5, b)
      : UpdateRule bnRule32) :=
  fun h => absurd (h bnC1 0 Usun (View.full Usun) 0
    (fun _ => (by decide : (1 : ℕ) ≤ 4)) (by decide) (by decide)).2.2 (by decide)

/-! ## Progress from height one, at interval one

`runP1v` is `runP1'` on the full view. At interval `1` its configuration
`1` starts at round `2`, and `2 + 1 + 1 + 2 · c + 3 ≤ 8` at gap `0`: the
theorem extends it and BN3 identifies the result with `runP1` at height
`2`; at gap `1` the margin no longer fits. -/

theorem bnLive_liveOn1 : bnLive.LiveOn sched1 1 := by
  rintro U V Rnd N ⟨rfl, rfl, rfl⟩ hcov
  have hw : bnLive.waveLength = 3 := rfl
  refine ⟨fun κ h1 h2 =>
    (bnLive_liveOn Usun V 1 8 ⟨rfl, rfl, rfl⟩ hcov).1 κ h1 (by omega), ?_⟩
  intro r h1 h2
  have : r = 1 ∨ r = 2 ∨ r = 3 ∨ r = 4 := by omega
  rcases this with rfl | rfl | rfl | rfl
  · exact ⟨2, by rw [sched1_slotRound]; try omega, by rw [sched1_slotRound]; try omega, 10, transport_full hcov <| Decided.directCommit
        (S := sched1) (by decide) (by decide)⟩
  · exact ⟨3, by rw [sched1_slotRound]; try omega, by rw [sched1_slotRound]; try omega, 15, transport_full hcov <| Decided.directCommit
        (S := sched1) (by decide) (by decide)⟩
  · exact ⟨4, by rw [sched1_slotRound]; try omega, by rw [sched1_slotRound]; try omega, 16, transport_full hcov <| Decided.directCommit
        (S := sched1) (by decide) (by decide)⟩
  · exact ⟨5, by rw [sched1_slotRound]; try omega, by rw [sched1_slotRound]; try omega, 21, transport_full hcov <| Decided.directCommit
        (S := sched1) (by decide) (by decide)⟩

/-! ## (i) Progress from height `1` at interval `1` on `Usun` -/

theorem bnUpdC_bounded : UpdBounded bnPI1 bnUpdC := by
  intro C b U V A hle hpos hint
  exact ⟨hle, hpos, hint⟩

theorem bnUpdC_keeps (Q : Config (Fin 4) → Prop) : UpdKeeps bnUpdC Q := fun _ _ _ _ _ h => h

/-- `runP1'` on the full view, under the constant rule — the same rule
`runP1` follows, so BN3 can identify the two. -/
def runP1v : PartialRun bnLive.toBaseRule bnPI1 bnUpdC bnC1I1 Usun (bnLive.full Usun) 1 where
  start := fun k => if k = 0 then 0 else 2
  cfg := fun _ => bnC1I1
  backoff := fun _ => 0
  anchor := fun _ => 2
  vdct := fun _ κ => if κ = 1 then some 5 else if κ = 2 then some 10 else none
  init := ⟨rfl, rfl, rfl⟩
  slotsAt_le := fun _ _ => (by decide : (1 : ℕ) ≤ 4)
  interval_pos := fun _ => (by decide : (0 : ℕ) < 1)
  interval_le := fun _ => (by decide : (1 : ℕ) ≤ 1)
  closed := by
    intro k hk κ h1 h2
    have hk0 : k = 0 := by omega
    subst hk0
    simp only [bnC1I1, bnCfg, Config.uniform_roundOf, Nat.div_one] at h1 h2
    simp at h1 h2
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

-- gap 0: 2 + 1 + 1 + 0 + 3 = 7 ≤ 8
example :
    ∃ Rn2 : PartialRun bnLive.toBaseRule bnPI1 bnUpdC bnC1I1 Usun (bnLive.full Usun) 2,
    Rn2.start 2 = 4 ∧ Rn2.cfg 2 = bnC1I1 ∧ Rn2.backoff 2 = 0 ∧ Rn2.anchor 1 = 4 := by
  obtain ⟨Rn2⟩ := (Progress.holds (Fin 4) (Fin 32) Unit bnLive MysticetiProperties.agree bnPI1
    bnUpdC bnUpdC_bounded bnC1I1 BnUniform (bnUpdC_keeps _) 0).1 Usun (bnLive.full Usun) 1 8 1
    (coversUpto_full laws32.full_ids Usun 8) runP1v bnLive_liveOn
    ⟨rfl, rfl, rfl⟩ (by decide) (by decide)
  refine ⟨Rn2, ?_⟩
  have h := (Agreement.holds (Fin 4) (Fin 32) Unit bnRule32 agree32 bnPI1 bnUpdC bnC1I1
    (fun _ _ _ _ _ _ => rfl)) Usun (bnLive.full Usun) Vsun 2 2 Rn2 runP1 2 (by decide)
  have h1 := (Agreement.holds (Fin 4) (Fin 32) Unit bnRule32 agree32 bnPI1 bnUpdC bnC1I1
    (fun _ _ _ _ _ _ => rfl)) Usun (bnLive.full Usun) Vsun 2 2 Rn2 runP1 1 (by decide)
  exact ⟨h.1, h.2.1, h.2.2.1, (h1.2.2.2 (by decide)).1⟩

-- Gap 1 does not fit at height 1: the margin `2 · c + w` above the
-- threshold makes `2 + 1 + 1 + 2 + 3 = 9 > 8`.
example : ¬ (runP1.start 1 + bnPI1.maxInterval + 1 + 2 * 1 + bnLive.waveLength ≤ 8) := by decide

-- Height 3 at interval 1 is out of the horizon: 4 + 1 + 1 + 0 + 3 = 9 > 8.
example : ¬ (runP1.start 2 + bnPI1.maxInterval + 1 + 0 + bnLive.waveLength ≤ 8) := by decide

-- EveryHeight at interval 1, gap 0: horizon 2 * 2 + 3 = 7 ≤ 8 gives height 2.
example : horizon bnPI1 bnLive 0 2 = 7 := by decide
example :
    Nonempty (PartialRun bnLive.toBaseRule bnPI1 bnUpdC bnC1I1 Usun (bnLive.full Usun) 2) :=
  ((Progress.holds (Fin 4) (Fin 32) Unit bnLive MysticetiProperties.agree bnPI1 bnUpdC
    bnUpdC_bounded bnC1I1 BnUniform (bnUpdC_keeps _) 0).2
    (fun C _ _ _ hC => bnLive_liveOn_all C hC)
    (fun _ => (by decide : (1 : ℕ) ≤ 4)) (by decide) (by decide) bnC1I1_uniform
    Usun (bnLive.full Usun) 1 8 ⟨rfl, rfl, rfl⟩ (coversUpto_full laws32.full_ids Usun 8) le_rfl 2
    (by decide))
example : ¬ (horizon bnPI1 bnLive 0 3 ≤ 8) := by decide

/-! ## Not live one round further

With the horizon at `9`, gap `0` asks round `6` for a committed slot;
its candidate, block `26`, has no certificate in `Usun`, so no
derivation commits it, direct or indirect. -/

def bnLive9 : LiveRule (Fin 4) (Fin 32) Unit :=
  { mysticeti with Good := fun U Rnd N => U = Usun ∧ Rnd = 1 ∧ N = 9 }

/-- Slot 6's only candidate is block 26 … -/
theorem hall6 : ∀ L : Fin 32, bnRule32.IsLeaderBlock sched1 Usun 6 L → L = 26 := by decide
/-- … which has no certificate anywhere (a certificate would sit at round 8). -/
theorem cert26 : certificates Usun 26 6 = ∅ := by decide

/-- No commit at round `6` on `Usun`, by either commit rule. -/
theorem no_commit6 : ∀ L, ¬ bnRule32.Decided sched1 (bnLive9.full Usun) 6 (some L) := by
  intro L hL
  cases hL with
  | directCommit hcand hdir =>
    have := hall6 L hcand; subst this
    exact absurd hdir (by decide)
  | indirectCommit _ _ _ _ _ _ hcand hcert _ =>
    have := hall6 L hcand; subst this
    obtain ⟨C, hC⟩ := certificates_nonempty_of_certifiedIn hcert
    simp only [sched1_slotRound, cert26] at hC
    exact absurd hC (Finset.notMem_empty C)

theorem bnLive9_not_liveOn0 : ¬ bnLive9.LiveOn sched1 0 := by
  intro h
  obtain ⟨-, h2⟩ := h Usun (View.full Usun) 1 9 ⟨rfl, rfl, rfl⟩ (coversUpto_full laws32.full_ids Usun 9)
  obtain ⟨κ, hlo, hhi, L, hL⟩ := h2 6 (by decide) (by decide)
  simp only [sched1_slotRound] at hlo hhi
  have hκ : κ = 6 := by omega
  subst hκ
  exact no_commit6 L hL

-- and the horizon-9 application of Progress at interval 4, gap 1, would need exactly this:
example : (0 : ℕ) + bnP.maxInterval + 1 + 1 + bnLive9.waveLength ≤ 9 := by decide

#print axioms bnLive9_not_liveOn0

/-! ## A skipped slot past the threshold: the anchor skips it

`Usk` is `Usun` with block `10` (round `2`, author `2`) referenced only
by its author's own next block, so three round-`3` blocks blame it and
slot `2` of `Sched 1` is directly skipped; everything else commits. At
gap `0` the clause fails at round `2`; at gap `1` it holds, answered by
slot `3`. From the height-`0` run at interval `1`, the theorem's anchor
is slot `3`, past the skipped slot `2` which lies past the threshold —
`anchor_least` with content, obtained from the theorem. -/

def skBlk : Fin 32 → Block (Fin 4) (Fin 32) Unit := fun i =>
  { round := (i : ℕ) / 4
    creator := ⟨(i : ℕ) % 4, Nat.mod_lt _ (by omega)⟩
    refs := if (i : ℕ) < 4 then ∅ else
      (Finset.univ.filter fun j : Fin 32 =>
        (j : ℕ) / 4 + 1 = (i : ℕ) / 4 ∧ ((j : ℕ) = 10 → (i : ℕ) = 14))
    payload := () }

def Usk : BlockUniverse (Fin 4) (Fin 32) Unit where
  ids := Finset.univ
  block := skBlk
  complete := by decide
  valid := by decide
  no_equivocation := by decide

def bnLiveSk : LiveRule (Fin 4) (Fin 32) Unit :=
  { mysticeti with Good := fun U Rnd N => U = Usk ∧ Rnd = 1 ∧ N = 8 }

-- Slot 2's candidate is block 10, blamed by 12, 13, 15.
theorem hallSk : ∀ L : Fin 32, bnRule32.IsLeaderBlock sched1 Usk 2 L → L = 10 := by decide
example : bnRule32.IsLeaderBlock sched1 Usk 2 10 := by decide
example : ¬ bnRule32.DirectCommitIn (bnLiveSk.full Usk) 10 2 := by decide
example : bnRule32.Decided sched1 (bnLiveSk.full Usk) 2 none :=
  Decided.directSkip (S := sched1) (by decide)
-- Slot 3 (block 15) commits.
example : bnRule32.Decided sched1 (bnLiveSk.full Usk) 3 (some 15) :=
  Decided.directCommit (S := sched1) (by decide) (by decide)

theorem bnLiveSk_not_liveOn0 : ¬ bnLiveSk.LiveOn sched1 0 := by
  intro h
  obtain ⟨-, h2⟩ := h Usk (View.full Usk) 1 8 ⟨rfl, rfl, rfl⟩ (coversUpto_full laws32.full_ids Usk 8)
  obtain ⟨κ, hlo, hhi, L, hL⟩ := h2 2 (by decide) (by decide)
  simp only [sched1_slotRound] at hlo hhi
  have hκ : κ = 2 := by omega
  subst hκ
  have hskip : bnRule32.Decided sched1 (bnLiveSk.full Usk) 2 none :=
    Decided.directSkip (S := sched1) (by decide)
  exact Option.some_ne_none L (laws32.agree sched1 _ _ 2 _ _ hL hskip)

/-- The same transport on `Usk`, whose blocks also lie at rounds up to `8`. -/
theorem transport_full_sk {V : bnLiveSk.View Usk}
    (hcov : bnLiveSk.toBaseRule.CoversUpto Usk V 8) {S : Slots (Fin 4)} {κ : ℕ}
    {v : Option (Fin 32)} (h : Decided (S := S) Usk (View.full Usk) κ v) :
    Decided (S := S) Usk V κ v := by
  have hround : ∀ b ∈ Usk.ids, (Usk.block b).round ≤ 8 := by decide
  exact AnchoredRule.decided_mono coreLaws trivial (S := S) (fun b hb => hcov b hb (hround b hb)) h

/-- Gap `1`: the round-`2` window is answered by slot `3`. -/
theorem bnLiveSk_liveOn1 : bnLiveSk.LiveOn sched1 1 := by
  rintro U V Rnd N ⟨rfl, rfl, rfl⟩ hcov
  have hw : bnLiveSk.waveLength = 3 := rfl
  refine ⟨?_, ?_⟩
  · intro κ h1 h2
    simp only [sched1_slotRound] at h1 h2
    have : κ = 1 ∨ κ = 2 ∨ κ = 3 ∨ κ = 4 ∨ κ = 5 := by omega
    rcases this with rfl | rfl | rfl | rfl | rfl
    · exact ⟨some 5, transport_full_sk hcov <| Decided.directCommit
        (S := sched1) (by decide) (by decide)⟩
    · exact ⟨none, transport_full_sk hcov <| Decided.directSkip (S := sched1) (by decide)⟩
    · exact ⟨some 15, transport_full_sk hcov <| Decided.directCommit
        (S := sched1) (by decide) (by decide)⟩
    · exact ⟨some 16, transport_full_sk hcov <| Decided.directCommit
        (S := sched1) (by decide) (by decide)⟩
    · exact ⟨some 21, transport_full_sk hcov <| Decided.directCommit
        (S := sched1) (by decide) (by decide)⟩
  · intro r h1 h2
    have : r = 1 ∨ r = 2 ∨ r = 3 ∨ r = 4 := by omega
    rcases this with rfl | rfl | rfl | rfl
    · exact ⟨1, by rw [sched1_slotRound]; try omega, by rw [sched1_slotRound]; try omega, 5, transport_full_sk hcov <| Decided.directCommit
        (S := sched1) (by decide) (by decide)⟩
    · exact ⟨3, by rw [sched1_slotRound]; try omega, by rw [sched1_slotRound]; try omega, 15, transport_full_sk hcov <| Decided.directCommit
        (S := sched1) (by decide) (by decide)⟩
    · exact ⟨3, by rw [sched1_slotRound]; try omega, by rw [sched1_slotRound]; try omega, 15, transport_full_sk hcov <| Decided.directCommit
        (S := sched1) (by decide) (by decide)⟩
    · exact ⟨4, by rw [sched1_slotRound]; try omega, by rw [sched1_slotRound]; try omega, 16, transport_full_sk hcov <| Decided.directCommit
        (S := sched1) (by decide) (by decide)⟩

abbrev bnUpdSk : UpdateRule bnLiveSk.toBaseRule := Aimd.rule bnRule32 bnPI1 bnLead bnLeadKeyed

theorem bnUpdSk_bounded : UpdBounded bnPI1 bnUpdSk := by
  intro C b U V A _ hpos hle
  exact ⟨fun r => Aimd.count_le bnPI1 _ _ _, hpos, hle⟩

theorem bnUpdSk_uniform : UpdKeeps bnUpdSk BnUniform := by
  intro C b U V A _
  exact ⟨_, _, Aimd.count_pos bnPI1 _ _ _, Aimd.count_le bnPI1 _ _ _, rfl⟩

def run0sk : PartialRun bnLiveSk.toBaseRule bnPI1 bnUpdSk bnC1I1 Usk (bnLiveSk.full Usk) 0 :=
  PartialRun.zero _ bnPI1 bnUpdSk bnC1I1 (fun _ => (by decide : (1 : ℕ) ≤ 4))
    (by decide) (by decide) Usk (bnLiveSk.full Usk)

/-- The configuration the anchor of range `0` produces. -/
abbrev skNext : Config (Fin 4) × ℕ := bnUpdSk bnC1I1 0 Usk (bnLiveSk.full Usk) 15

-- The rule at anchor 15, interval 1: nothing scores, but at an interval
-- below one wave nothing is expected either, so the count rises.
example : observed bnRule32 bnC1I1 Usk 15 = 0 := by decide
example : expected bnRule32 bnC1I1 3 = 0 := by decide
example : skNext.1.slotsAt 0 = 2 ∧ skNext.2 = 0 := by decide

def vdSk : ℕ → ℕ → Option (Fin 32) :=
  fun _ κ => if κ = 1 then some 5 else if κ = 3 then some 15 else none

/-- Anchor at slot `3`, past the skipped slot `2`: `anchor_least` is
non-vacuous at `κ = 2`. -/
def runSk :
    PartialRun bnLiveSk.toBaseRule bnPI1 bnUpdSk bnC1I1 Usk (bnLiveSk.full Usk) 1 where
  start := fun k => if k = 0 then 0 else 3
  cfg := fun k => if k = 0 then bnC1I1 else skNext.1
  backoff := fun k => if k = 0 then 0 else skNext.2
  anchor := fun _ => 3
  vdct := vdSk
  init := ⟨rfl, rfl, rfl⟩
  slotsAt_le := by
    intro k r
    by_cases h : k = 0
    · subst h; simp only [if_true]; exact (by decide : (1 : ℕ) ≤ 4)
    · simp only [h, if_false]; exact Aimd.count_le bnPI1 _ _ _
  interval_pos := by
    intro k
    by_cases h : k = 0
    · subst h; simp only [if_true]; exact (by decide : (0 : ℕ) < 1)
    · simp only [h, if_false]; exact (by decide : (0 : ℕ) < 1)
  interval_le := by
    intro k
    by_cases h : k = 0
    · subst h; simp only [if_true]; exact (by decide : (1 : ℕ) ≤ 1)
    · simp only [h, if_false]; exact (by decide : (1 : ℕ) ≤ 1)
  closed := by
    intro k hk κ h1 h2
    have hk0 : k = 0 := by omega
    subst hk0
    simp only [if_true, bnC1I1, bnCfg, Config.uniform_roundOf, Nat.div_one] at h1 h2 ⊢
    simp at h1 h2
    have : κ = 1 ∨ κ = 2 ∨ κ = 3 := by omega
    rcases this with rfl | rfl | rfl
    · exact Decided.directCommit (S := bnC1I1.sched) (by decide) (by decide)
    · exact Decided.directSkip (S := bnC1I1.sched) (by decide)
    · exact Decided.directCommit (S := bnC1I1.sched) (by decide) (by decide)
  anchor_commits := by
    intro k hk
    have hk0 : k = 0 := by omega
    subst hk0
    exact ⟨⟨15, rfl⟩, by decide⟩
  anchor_least := by
    intro k hk κ hκ h
    have hk0 : k = 0 := by omega
    subst hk0
    simp only [if_true, bnC1I1, bnCfg, Config.uniform_roundOf, Config.uniform_interval,
      Nat.div_one] at h hκ
    have : κ = 2 := by omega
    subst this
    rfl
  start_succ := by
    intro k hk
    have hk0 : k = 0 := by omega
    subst hk0
    rfl
  update := by
    intro k hk A hA
    have hk0 : k = 0 := by omega
    subst hk0
    have hA' : A = 15 := by simp [vdSk] at hA; exact hA.symm
    subst hA'
    rfl

-- BN8a at gap 1 (0 + 1 + 1 + 1 + 3 = 6 ≤ 8): the anchor the theorem finds is slot 3,
-- not slot 2, which lies past the threshold and is skipped.
example :
    ∃ Rn1 : PartialRun bnLiveSk.toBaseRule bnPI1 bnUpdSk bnC1I1 Usk (bnLiveSk.full Usk) 1,
    Rn1.anchor 0 = 3 ∧ Rn1.start 1 = 3 ∧ Rn1.cfg 1 = skNext.1 ∧ Rn1.backoff 1 = skNext.2 ∧
      Rn1.vdct 0 2 = none ∧
      Rn1.start 0 + (Rn1.cfg 0).interval < (Rn1.cfg 0).roundOf 2 := by
  obtain ⟨Rn1⟩ := (Progress.holds (Fin 4) (Fin 32) Unit bnLiveSk MysticetiProperties.agree bnPI1
    bnUpdSk bnUpdSk_bounded bnC1I1 BnUniform bnUpdSk_uniform 1).1 Usk (bnLiveSk.full Usk) 1 8 0
    (coversUpto_full laws32.full_ids Usk 8) run0sk bnLiveSk_liveOn1 ⟨rfl, rfl, rfl⟩
    (by decide) (by decide)
  refine ⟨Rn1, ?_⟩
  have h := (Agreement.holds (Fin 4) (Fin 32) Unit bnRule32 agree32 bnPI1 bnUpdSk bnC1I1
    (fun _ _ _ _ _ _ => rfl))
    Usk (bnLiveSk.full Usk) (bnLiveSk.full Usk) 1 1 Rn1 runSk 1 (by decide)
  have h0 := (Agreement.holds (Fin 4) (Fin 32) Unit bnRule32 agree32 bnPI1 bnUpdSk bnC1I1
    (fun _ _ _ _ _ _ => rfl))
    Usk (bnLiveSk.full Usk) (bnLiveSk.full Usk) 1 1 Rn1 runSk 0 (by decide)
  have hv := (h0.2.2.2 (by decide)).2 2
  rw [h0.1, h0.2.1, h.1] at hv
  refine ⟨(h0.2.2.2 (by decide)).1, h.1, h.2.1, h.2.2.1, hv (by decide) (by decide), ?_⟩
  rw [h0.1, h0.2.1]
  decide

#print axioms bnLiveSk_not_liveOn0
#print axioms runSk

#print axioms bnLive_liveOn_all
#print axioms Progress.holds

end Barnacle
end LeanDagTest
