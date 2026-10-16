import LeanDag.Scheme.Reactive.Proof
import LeanDag.Scheme.Model.LeastSel
import LeanDagTest.Reactive.Model
/-!
# The family, run reactively, on data

`ugrowReactive` is a Reactive Mysticeti execution on `Ugrow` in which no
validator ever waits a timeout. Converted (`ofReactiveM`), it is the family
run reactively at the Mysticeti row and the least vote; it meets the
family's reactive precondition, and a reliably-led slot commits by the
generic `LeaderCommits`; and validator `2`'s round-`1` block (id `6`)
enters the ledger through a slot `2` leads.
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
def ugrowScheme (N : ℕ) :
    SchemeReactive (S := rrSlots) (quorumCard (Fin 4)) mystU σU (Ugrow N) {1, 2, 3} N :=
  ofReactiveM σU (by decide) (ugrowReactive N)

/-- **The family's reactive precondition holds on this execution.** -/
theorem ugrowScheme_live (N k : ℕ) (hN : rrSlots.slotRound k + 2 ≤ N) :
    reactiveLive mystU σU Correct (coreReliability (Fin 4)) rrSlots (ugrowV N)
      ({1, 2, 3} : Finset (Fin 4)) k (k + 1) := by
  refine ⟨⟨by decide, by decide⟩, by decide, N, 0, ugrowScheme N, Nat.le_refl 0,
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
  ReactiveRun.commits (Fin 4) ℕ Unit ValidWrt Correct mystU σU Correct (coreReliability (Fin 4))
    (by decide)
    (fun _ => ⟨by decide, by decide⟩) (by decide) rrSlots (ugrowV N)
    ({1, 2, 3} : Finset (Fin 4)) k (k + 1) (ugrowScheme_live N k hN) k (Nat.le_refl k)
    (Nat.lt_succ_self k) hlead

/-- **No reliable block is censored, on data.** Validator `2`'s round-`1`
block (id `6`) is in the history of the leader block a slot led by `2`
commits. -/
theorem ugrowScheme_includes : ∃ k', 1 ≤ rrSlots.slotRound k' ∧ rrSlots.leader k' = 2 ∧
    ∀ N, rrSlots.slotRound k' + 2 ≤ N →
      ∃ L, (schemeRule mystU σU Correct).Decided rrSlots (ugrowV N) k' (some L) ∧
        6 ∈ historyFrom (Ugrow N).block L := by
  obtain ⟨k', hm, hlead, h⟩ := ReactiveRun.includes (Fin 4) ℕ Unit ValidWrt Correct mystU σU
    Correct (coreReliability (Fin 4)) (fun _ _ h => h.self_parent) le_rfl (by decide)
    (fun _ => ⟨by decide, by decide⟩) (by decide) rrSlots ({1, 2, 3} : Finset (Fin 4))
    (by decide) rrSlots_fairToEach 1 2 (by decide)
  refine ⟨k', hm, hlead, fun N hN => ?_⟩
  obtain ⟨L, hdec, hb⟩ := h (ugrowU N) (ugrowV N) (ugrowScheme_live N k' hN)
  refine ⟨L, hdec, (hb 6 ?_ ?_ ?_).1⟩
  · show 6 ∈ (Ugrow N).ids
    simp only [ugrow_ids, Finset.mem_range]
    omega
  · apply Fin.ext
    show ((Ugrow N).block 6).creator.val = 2
    simp only [ugrow_block, rrBlock_creator_val]
  · show ((Ugrow N).block 6).round = 1
    simp only [ugrow_block, rrBlock_round]

end Scheme

end LeanDagTest

#print axioms LeanDag.Scheme.ReactiveRun.holds
#print axioms LeanDagTest.Scheme.ugrowScheme_commits
#print axioms LeanDagTest.Scheme.ugrowScheme_includes
