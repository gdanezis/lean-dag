import LeanDag.Scheme.Reactive.Proof
import LeanDag.Scheme.Model.LeastSel
import LeanDagTest.Reactive.Model
/-!
# The family, run reactively, on data

`ugrowReactive` is a Reactive Mysticeti execution on `Ugrow` in which no
validator ever waits a timeout. Converted (`ofReactiveM`), it is the family
run reactively at the Mysticeti row and the least vote; it meets the
family's reactive precondition, and a reliably-led slot commits by the
generic `LeaderCommits`.
-/

namespace LeanDagTest

namespace Scheme

open LeanDag LeanDag.Scheme

attribute [local instance 2000] rrSlots

/-- The least vote on `Ugrow`. -/
abbrev σU : VoteSel (Fin 4) ℕ Unit ValidWrt Correct := leastSel

/-- The Mysticeti row at four validators. -/
abbrev mystU : Params := Params.mysticeti (Fintype.card (Fin 4)) (Faults.f (Fin 4))

/-- `Ugrow` as a universe of the row's carrier. -/
abbrev ugrowU (N : ℕ) : (schemeRule mystU σU Correct).Universe :=
  ⟨Ugrow N, (Ugrow N).noEquivOn_honest⟩

/-- The full view of `Ugrow`, as a view of the carrier. -/
abbrev ugrowV (N : ℕ) : (schemeRule mystU σU Correct).View (ugrowU N) :=
  BlockRecord.View.full (Ugrow N)

/-- The family run reactively, from `ugrowReactive`. -/
def ugrowScheme (N : ℕ) : SchemeReactive (S := rrSlots) mystU σU (Ugrow N) {1, 2, 3} N :=
  ofReactiveM σU (by decide) (ugrowReactive N)

/-- **The family's reactive precondition holds on this execution.** -/
theorem ugrowScheme_live (N k : ℕ) (hN : rrSlots.slotRound k + 2 ≤ N) :
    reactiveLive mystU σU Correct rrSlots (ugrowV N)
      ({1, 2, 3} : Finset (Fin 4)) k (k + 1) := by
  refine ⟨by decide, by decide, by decide, N, 0, ugrowScheme N, Nat.le_refl 0,
    (fun n _ => by change 2 * 2 + 5 ≤ 9; omega), Nat.zero_le _,
    BlockRecord.View.coversUpto_full (Ugrow N) N, ?_⟩
  intro j hj
  have := rrSlots.mono (Nat.lt_succ_iff.mp hj)
  have hw : mystU.waveLength - 1 = 2 := rfl
  omega

/-- **And a reliably-led slot commits**, by the generic `LeaderCommits`. -/
theorem ugrowScheme_commits (N k : ℕ) (hN : rrSlots.slotRound k + 2 ≤ N)
    (hlead : rrSlots.leader k ∈ ({1, 2, 3} : Finset (Fin 4))) :
    ∃ L, Properties.DecidedBelow (schemeRule mystU σU Correct) rrSlots (k + 1) (ugrowV N) k
      (some L) :=
  ReactiveRun.commits (Fin 4) ℕ Unit ValidWrt Correct mystU σU Correct (by decide)
    (fun _ => ⟨by decide, by decide⟩) (by decide) rrSlots (ugrowV N)
    ({1, 2, 3} : Finset (Fin 4)) k (k + 1) (ugrowScheme_live N k hN) k (Nat.le_refl k)
    (Nat.lt_succ_self k) hlead

end Scheme

end LeanDagTest

#print axioms LeanDag.Scheme.ReactiveRun.holds
#print axioms LeanDagTest.Scheme.ugrowScheme_commits
