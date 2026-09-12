import LeanDagTest.Barnacle.Model
import LeanDag.Barnacle.Live.Proof
import LeanDagTest.Barnacle.Rules.MysticetiLive.Proof
import LeanDag.Barnacle.Validity.Proof
import LeanDag.Barnacle.Helpers.Delivery
import LeanDag.Barnacle.Aimd.Proof
import LeanDagTest.Mysticeti.Growth
/-!
# Barnacle witnesses — progress against the real rule

`Progress.lean` exercises BN8 on `bnLive`, a *test* rule whose `Good`
pins one universe so that `LiveOn` becomes finite and a witness can
supply it. That was the only way to run BN8 on data while its liveness
clause was a hypothesis: the clause quantifies over every good DAG and
cannot be decided.

BN11 removes the need. It discharges the clause as a theorem — round
robin is live at every count, from the committee bound alone — so the
real Mysticeti rule with its real `Good` can be run on data with nothing
assumed. This file does that.

The DAG is the development's own grown family, `Ugrow N`: four
validators, every block referencing the whole round below, defined at
every `N`. Its synchrony and population are proved once and for all
(`ugrow_synchronised`, `ugrow_populated`), so no height needs `decide`,
and `mysticetiLive.Good (Ugrow N) 0 N` follows at every `N` with the
correct validators as the quorum. The schedule is `bnLeader`, which *is*
`roundRobin 4`, so BN11 applies to it directly.

The result is runs of every height on a real DAG under the real rule,
where the run's own horizon fixes how tall the DAG must be: height `K`
needs `11K + 9` rounds at `bnP`'s four-round interval and Mysticeti's
gap of `n + 2 = 6`.
-/

namespace LeanDagTest

namespace Barnacle

open LeanDag LeanDag.Barnacle

/-- Mysticeti as a live rule over the grown family's types. -/
abbrev realRule : LiveRule (Fin 4) ℕ Unit := mysticetiLive

/-- **The grown family is good, at every height.** The correct validators
are a quorum, the family is synchronised from round `0`, and it is
populated at every round up to `N`. -/
theorem ugrow_good (N : ℕ) : realRule.Good (Ugrow N) 0 N :=
  ⟨(Correct : Finset (Fin 4)), ⟨Finset.Subset.refl _, card_correct⟩,
    ugrow_synchronised N, fun _ _ hr => ugrow_populated hr⟩

/-- The AIMD rule over the real base rule. -/
abbrev realUpd : UpdateRule realRule.toBaseRule :=
  Aimd.rule realRule.toBaseRule bnP bnLead bnLeadKeyed

theorem realUpd_bounded : UpdBounded bnP realUpd := by
  intro C b U V v A h
  exact ⟨fun r => Aimd.count_le bnP _ _ _, h.2.1, h.2.2⟩

/-- The rule emits the rotation's heads, whatever it reads. -/
theorem realUpd_heads : UpdKeeps realUpd (fun C => C.head = bnLeader) := by
  intro C b U V v A _
  funext ρ
  rfl

/-- The genesis configuration: one leader a round, four-round interval,
on the rotation. -/
theorem bnC1_head : bnC1.head = bnLeader := by funext ρ; rfl

/-- **BN11 on data, with the real rule and the real `Good`.** A run of
every height exists on the grown family, at the height's own horizon —
`11K + 9` rounds. Nothing is assumed: the liveness clause comes from
BN11, the bound from BN7a, and the goodness from the family itself. -/
theorem real_runs (K : ℕ) :
    Nonempty (PartialRun realRule.toBaseRule bnP realUpd bnC1
      (Ugrow (11 * K + 9)) (realRule.full (Ugrow (11 * K + 9))) K) :=
  Live.runsExist_roundRobin (by omega) realRule MysticetiProperties.agree
    (MysticetiLive.descent (Fin 4) ℕ Unit) (Nat.succ_pos 2) (by decide) bnP realUpd
    realUpd_bounded realUpd_heads bnC1 bnC1_head
    ⟨fun _ => (by decide : (1 : ℕ) ≤ 4), by decide, by decide⟩
    (Ugrow (11 * K + 9)) (realRule.full (Ugrow (11 * K + 9))) 0 (11 * K + 9)
    (ugrow_good _)
    (coversUpto_full (Mysticeti.holds (Fin 4) ℕ Unit).full_ids _ _) (by omega) K
    (by show K * (4 + 1 + 6) + 6 + 3 ≤ 11 * K + 9; omega)

/-- **The horizon is exact.** The family stops at `N`: a taller run needs
a taller DAG, so the `11K + 9` above is the height's cost and not a
convenience. -/
example (K : ℕ) : ¬ Populated (Ugrow (11 * K + 9)) (11 * K + 9 + 1) :=
  ugrow_not_populated_succ _

/-- And what comes back is a run: its first configuration is Algorithm
1's, one leader after round `0`. -/
example (K : ℕ) : (real_runs K).some.cfg 0 = bnC1 ∧ (real_runs K).some.start 0 = 0 :=
  ⟨(real_runs K).some.init.2.1, (real_runs K).some.init.1⟩

/-- Its every range is decided against its own configuration's schedule —
the `closed` field, which is what makes the run a run rather than a
sequence of numbers. -/
example (K k : ℕ) (hk : k < K) (κ : ℕ)
    (h₁ : (real_runs K).some.start k < ((real_runs K).some.cfg k).roundOf κ)
    (h₂ : ((real_runs K).some.cfg k).roundOf κ ≤ (real_runs K).some.start (k + 1)) :
    realRule.Decided ((real_runs K).some.cfg k).sched
      (realRule.full (Ugrow (11 * K + 9))) κ ((real_runs K).some.vdct k κ) :=
  (real_runs K).some.closed k hk κ h₁ h₂

/-! ## BN14 on the same run: a correct validator's block is delivered

The run above commits an anchor at each configuration it closes. Every
block of the good set two rounds below such an anchor is in that anchor's
causal history, so the run delivers it — no rotation hypothesis, and the
author need never lead again. -/

theorem real_delivers (K : ℕ) :
    ∃ T : Finset (Fin 4), Fintype.card (Fin 4) ≤ T.card + Faults.f (Fin 4) ∧
      ∀ b ∈ (Ugrow (11 * K + 9)).ids, ((Ugrow (11 * K + 9)).block b).creator ∈ T →
        ((Ugrow (11 * K + 9)).block b).round + 1 ≤ 11 * K + 9 →
        ∀ k, k < K → ((Ugrow (11 * K + 9)).block b).round + 2 ≤ (real_runs K).some.start (k + 1) →
          ∃ A, (real_runs K).some.vdct k ((real_runs K).some.anchor k) = some A ∧
            b ∈ historyFrom (Ugrow (11 * K + 9)).block A := by
  obtain ⟨T, hcard, hT⟩ :=
    Validity.holds (Fin 4) ℕ Unit realRule
      MysticetiProperties.commitsCandidate bnP realUpd bnC1
      (Faults.f (Fin 4)) (delivers_core _) (Ugrow (11 * K + 9))
      (realRule.full (Ugrow (11 * K + 9))) K (real_runs K).some 0 (11 * K + 9)
      (ugrow_good _)
  exact ⟨T, hcard, fun b hb hbT hN k hk hround => hT b hb hbT (Nat.zero_le _) hN k hk hround⟩

#print axioms real_delivers

#print axioms real_runs

end Barnacle

end LeanDagTest
