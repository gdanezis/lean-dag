import LeanDag.Nemo.Properties
import LeanDag.Nemo.Liveness
import LeanDag.Common.Schedule
import Mathlib.Tactic.IntervalCases

/-!
# Nemo-Nemo on a concrete crash universe

A three-validator committee at the tight bound `n = 2f + 1 = 3`, where
validator `2` authors at rounds 0–1 and then **halts**. Validators `0` and
`1` carry the DAG to round 5 — six rounds, fourteen blocks, every round-`r+1`
block referencing every round-`r` block that exists.

What the model certifies:

* the crash `Universe` obligations (`complete`, `valid`, universal
  `no_equivocation`) hold of concrete data, by `decide` — including the
  majority parent quorum at its tight value (rounds 3–5 carry exactly
  `majority = 2` distinct parent creators);
* the decision layer runs end-to-end: the live-led slots 0, 1, 3, 4 commit
  **directly**, and slot 2 — whose leader crashed and left no candidate —
  is settled by `indirectSkip` off the adjacent committed pair 3–4, the
  wave-two shadow/anchor mechanics of `Nemo/Liveness.lean`'s docstring made
  concrete (slot 3 is *not* eligible for slot 2, so the intermediate
  premise is vacuous; slot 4 is the anchor);
* the liveness hypotheses are jointly satisfiable: `Populated` up to the
  horizon (and *not* beyond — anti-vacuity), `Synchronised` from round 0,
  `FairRunOn (Live) 2` for the round-robin identity schedule, and
  `SpansEligible 2` via the identity-round lemma; the headline
  `all_decided_below_of_fairRun_live` is instantiated at the schedule.

The `#print axioms` block at the end guards against drift: everything
should show the repo baseline (`propext`, `Classical.choice`, `Quot.sound`)
— Mathlib's `Finset` machinery carries choice transitively — and nothing
(`sorryAx` in particular) beyond it.
-/

namespace LeanDagTest

open LeanDag LeanDag.Nemo

/-! ## The crash committee: `n = 3`, `f = 1`, validator `2` crashed -/

instance nemoFaults : CrashFaults (Fin 3) where
  f := 1
  crashed := {2}
  card_crashed := by decide
  card_validators := by decide

example : majority (Fin 3) = 2 := by decide
example : Live (Fin 3) = {0, 1} := by decide
-- The bridge, pinned on data: the live class carries the majority.
example : majority (Fin 3) ≤ (Live (Fin 3)).card := by decide

/-! ## The universe: six rounds, validator `2` halts after round 1 -/

/-- Rounds in contiguous id blocks: `0-2` round 0 (all three validators),
`3-5` round 1 (all three), then two blocks per round — creators `0` and `1`
only — up to round 5. -/
def nemoBlk : Fin 14 → Block (Fin 3) (Fin 14) Unit := fun i =>
  if h : (i : ℕ) < 3 then
    { round := 0, creator := ⟨i, by omega⟩, refs := ∅, payload := () }
  else if h : (i : ℕ) < 6 then
    { round := 1, creator := ⟨(i : ℕ) - 3, by omega⟩, refs := {0, 1, 2}, payload := () }
  else if h : (i : ℕ) < 8 then
    { round := 2, creator := ⟨(i : ℕ) - 6, by omega⟩, refs := {3, 4, 5}, payload := () }
  else if h : (i : ℕ) < 10 then
    { round := 3, creator := ⟨(i : ℕ) - 8, by omega⟩, refs := {6, 7}, payload := () }
  else if h : (i : ℕ) < 12 then
    { round := 4, creator := ⟨(i : ℕ) - 10, by omega⟩, refs := {8, 9}, payload := () }
  else
    { round := 5, creator := ⟨(i : ℕ) - 12, by have := i.isLt; omega⟩,
      refs := {10, 11}, payload := () }

def Unemo : Nemo.Universe (Fin 3) (Fin 14) Unit where
  ids := Finset.univ
  block := nemoBlk
  complete := by decide
  valid := by decide
  no_equivocation := by decide

/-! ## The schedule: identity rounds, round-robin leaders -/

instance nemoSlots : Slots (Fin 3) :=
  Slots.uniformSingle 1 (by omega) (fun k => ⟨k % 3, by omega⟩)

@[simp]
theorem nemoSlots_slotRound (k : ℕ) : nemoSlots.slotRound k = k := by
  simp

theorem nemoSlots_leader_val (k : ℕ) : (nemoSlots.leader k).val = k % 3 := rfl

/-! ## Decisions: four direct commits, one indirect skip -/

/-- Slot 0 (leader `0`, block `0`): directly committed. -/
theorem nemo_slot0 : Decided Unemo (View.full Unemo) 0 (some 0) :=
  Decided.directCommit (by decide) (by decide)

/-- Slot 1 (leader `1`, block `4`): directly committed. -/
theorem nemo_slot1 : Decided Unemo (View.full Unemo) 1 (some 4) :=
  Decided.directCommit (by decide) (by decide)

/-- Slot 3 (leader `0`, block `8`): directly committed. -/
theorem nemo_slot3 : Decided Unemo (View.full Unemo) 3 (some 8) :=
  Decided.directCommit (by decide) (by decide)

/-- Slot 4 (leader `1`, block `11`): directly committed — slot 2's anchor. -/
theorem nemo_slot4 : Decided Unemo (View.full Unemo) 4 (some 11) :=
  Decided.directCommit (by decide) (by decide)

-- Slot 2's leader crashed before its round: no candidate exists.
example : ∀ M : Fin 14, ¬ IsLeaderBlock Unemo 2 M := by decide

/-- **Slot 2 — the crashed slot.** Settled by `indirectSkip` off the
adjacent committed pair 3–4: slot 4 is the anchor, slot 3 is *not eligible*
for slot 2 (wave-two geometry: `slotRound 2 + 2 > slotRound 3`), so the
nearest-anchor premise is vacuous, and no candidate leader block exists at
all. This is the derivation the crash arc cannot obtain any other way —
there is no `directSkip`. -/
theorem nemo_slot2 : Decided Unemo (View.full Unemo) 2 none := by
  refine Decided.indirectSkip (j := 4) (A := 11) (by omega) (by decide) nemo_slot4 ?_ ?_
  · intro i h1 h2 h3
    have : i = 3 := by omega
    subst this
    exact absurd h3 (by decide)
  · have hall : ∀ M : Fin 14, ¬ IsLeaderBlock Unemo 2 M := by decide
    exact fun _ _ L hL => absurd hL (hall L)

-- Agreement, hypothesis-free: any verdict for slot 1 names block 4.
example : ∀ v, Decided Unemo (View.full Unemo) 1 v → v = some 4 :=
  fun _ hv => AnchoredRule.decided_agree Nemo.nemoLaws trivial hv nemo_slot1

-- The decidable indirect test, exercised positively and negatively: the
-- anchor's cone holds a vote for slot 1's leader block, and a round-5
-- block has no voters at all (the horizon's edge).
example : CertifiedIn Unemo 11 4 1 := by decide
example : ¬ DirectCommit Unemo 12 5 := by decide

/-! ## The liveness hypotheses, satisfied concretely -/

/-- Both live validators author at every round up to the horizon. -/
theorem unemo_populated {r : ℕ} (h : r ≤ 5) : Populated Unemo r := by
  interval_cases r <;> decide

-- Anti-vacuity: the horizon is real.
example : ¬ Populated Unemo 6 := by decide

private theorem unemo_round_le : ∀ b : Fin 14, (Unemo.block b).round ≤ 5 := by decide

/-- Live-to-live coverage from round 0: every live-authored block references
every live-authored block of the round below. -/
theorem unemo_synchronised : Synchronised Unemo 0 := by
  intro n _ b hb hbr hbc a ha har hac
  by_cases hn : n ≤ 4
  · revert b hb hbr hbc a ha har hac
    interval_cases n <;> decide
  · exfalso
    have := unemo_round_le b
    omega

theorem mem_live_of_val_lt : ∀ {v : Fin 3}, (v : ℕ) < 2 → v ∈ Live (Fin 3) := by
  decide

/-- Round-robin over `2f + 1 = 3` with one crash has adjacent live leaders
at every multiple of three — the pigeonhole fact, witnessed. -/
theorem nemo_fairRun : FairRunOn (S := nemoSlots) (Live (Fin 3)) 2 := by
  intro k
  refine ⟨3 * k, by omega, ?_⟩
  intro i hi
  exact mem_live_of_val_lt (by rw [nemoSlots_leader_val]; omega)

-- The identity schedule spans at `c = 2`.
example : (Nemo.nemoAnchored (Fin 3) (Fin 14) Unit).SpansEligible 2 :=
  (Nemo.nemoAnchored (Fin 3) (Fin 14) Unit).spansEligible_of_identity nemoSlots_slotRound
    (fun _ => le_rfl)

/-- **The headline applied.** Fairness and spanning discharged at the
concrete schedule; growth and coverage left abstract, exactly as the
theorem quantifies them. -/
example (R k : ℕ) :
    ∃ b, k ≤ b ∧ R ≤ nemoSlots.slotRound b ∧
      ∀ (U : Nemo.Universe (Fin 3) (Fin 14) Unit) (N : ℕ),
        (∀ r ≤ N, Populated U r) → Synchronised U R →
        nemoSlots.slotRound (b + 2 - 1) + 1 ≤ N →
        ∀ i, i < b → ∃ v, Decided U (View.full U) i v := by
  obtain ⟨b, hk, hR, hrest⟩ :=
    Nemo.all_decided_below_of_fairRun_live (BlockId := Fin 14) (Payload := Unit)
      (by omega) ((Nemo.nemoAnchored (Fin 3) (Fin 14) Unit).spansEligible_of_identity
        nemoSlots_slotRound (fun _ => le_rfl)) nemo_fairRun R k
  exact ⟨b, hk, hR, fun U N hpop hs hN =>
    hrest U N (View.full U) hpop hs hN (View.coversUpto_full U N)⟩

/-! ## Axiom hygiene

All checks print the repo's baseline axiom set (`propext`,
`Classical.choice`, `Quot.sound`) — Mathlib's `Finset` machinery carries
choice transitively into everything, exactly as in the other arcs. The
point is drift detection: nothing here should ever acquire an axiom beyond
that baseline (`sorryAx` in particular). -/

#print axioms LeanDag.AnchoredRule.decided_unique
#print axioms LeanDag.AnchoredRule.outputAt_agree
#print axioms LeanDag.Nemo.all_decided_below_of_fairRun
#print axioms LeanDag.Nemo.majority_le_card_live
#print axioms nemo_slot2

end LeanDagTest
