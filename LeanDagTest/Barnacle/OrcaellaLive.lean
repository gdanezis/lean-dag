import LeanDagTest.Hybrid.Model
import LeanDag.Barnacle.Orcaella.Proof
import LeanDag.Barnacle.Helpers.Cover
/-!
# Barnacle over Orcaella — round-robin liveness, witnessed

`Orcaella.RoundRobinLive` on the four-validator committee needs a DAG
tall enough for its gap: with `c = n + 1 = 5` and a two-round wave, a
slot needs `slotRound + 7 ≤ N`, so `Uhyb4`'s four rounds witness both
clauses only vacuously. `UL` is the tall model: nine rounds
(`0`–`8`), validator `3` silent after genesis, the survivors at quorum
`3` throughout — 28 blocks.

The theorem is applied at counts one and two with both clauses
non-vacuous (slots of rounds `0` and `1` under the first, `r ∈ {0, 1}`
under the second), and its verdicts are pinned through `agree`: slot
`0` is the direct commit of the genesis block, and at count one the
committed slot the second clause finds in `[0, 5]` is never the crashed
validator's slot `3`, whose verdict is the vacuous direct skip. This is
the paper's "gap `n + 1`" claim on data — previously evidenced only for
Nemo-Nemo.

Same import discipline as `Orcaella.lean`: nothing that pulls in
`LeanDagTest.Model`'s competing `Faults (Fin 4)`.
-/

namespace LeanDagTest

namespace Barnacle

namespace OrcaellaLive

open LeanDag LeanDag.Barnacle LeanDag.Hybrid

/-- Genesis from all four; rounds `1`–`8` from the three survivors,
each block citing the full surviving quorum below it. -/
def blkL : Fin 28 → Block (Fin 4) (Fin 28) Unit := fun i =>
  if h : (i : ℕ) < 4 then
    { round := 0, creator := ⟨i, by omega⟩, refs := ∅, payload := () }
  else if h : (i : ℕ) < 7 then
    { round := 1, creator := ⟨(i : ℕ) - 4, by omega⟩, refs := {0, 1, 2}, payload := () }
  else
    { round := ((i : ℕ) - 4) / 3 + 1, creator := ⟨((i : ℕ) - 4) % 3, by omega⟩,
      refs := {⟨(i : ℕ) - ((i : ℕ) - 4) % 3 - 3, by have := i.isLt; omega⟩,
        ⟨(i : ℕ) - ((i : ℕ) - 4) % 3 - 2, by have := i.isLt; omega⟩,
        ⟨(i : ℕ) - ((i : ℕ) - 4) % 3 - 1, by have := i.isLt; omega⟩},
      payload := () }

def UL : BlockUniverse (Fin 4) (Fin 28) Unit where
  ids := Finset.univ
  block := blkL
  complete := by decide
  valid := by decide
  no_equivocation := by decide

abbrev OL : BaseRule (Fin 4) (Fin 28) Unit := orcaella 2

/-- The subtype universe. -/
def OUL : OL.Universe := ⟨UL, by decide⟩

/-- The model's own synchrony from round `0`, over the fully-correct
class. -/
theorem ul_sync : SynchronisedOn UL {0, 1, 2} 0 := by
  intro n hn b hb hround hbT a ha hround' haT
  have h8 : ∀ b : Fin 28, (UL.block b).round ≤ 8 := by decide
  have hn7 : n ≤ 7 := by have := h8 b; omega
  interval_cases n <;> revert b a <;> decide

theorem ul_good :
    (orcaellaLive (Validator := Fin 4) (BlockId := Fin 28) (Payload := Unit) 2).Good
      OUL 0 8 :=
  ⟨{0, 1, 2}, ⟨by decide, by decide⟩, ul_sync, fun r h1 h2 => by interval_cases r <;> decide⟩

abbrev rr4 : ℕ → Fin 4 := roundRobin 4 (by omega)
theorem rr4_keyed : Keyed rr4 4 := roundRobin_keyed 4 (by omega)
abbrev S1 : Slots (Fin 4) := Sched rr4 rr4_keyed 1 (by omega) (by omega)
abbrev S2 : Slots (Fin 4) := Sched rr4 rr4_keyed 2 (by omega) (by omega)

/-- `Orcaella.RoundRobinLive` applied at `n = 4`, count `1`, gap `5`,
horizon `8`. -/
theorem live_o1 :
    (∀ κ, 0 ≤ S1.slotRound κ → S1.slotRound κ + 5 + 2 ≤ 8 →
      ∃ v, OL.Decided S1 (OL.full OUL) κ v) ∧
    (∀ r, 0 ≤ r → r + 5 + 2 ≤ 8 →
      ∃ κ, r ≤ S1.slotRound κ ∧ S1.slotRound κ ≤ r + 5 ∧
        ∃ L, OL.Decided S1 (OL.full OUL) κ (some L)) :=
  LeanDag.Barnacle.Orcaella.holds.2.2 4 (by omega) (Fin 28) Unit 2 (by decide) 4 rr4_keyed
    1 (by omega) (by omega) OUL (OL.full OUL) 0 8 ul_good
    (coversUpto_full (LeanDag.Barnacle.Orcaella.holds.1 (Fin 4) (Fin 28) Unit 2 (by decide))
      OUL 8)

/-- The same at count `2`. -/
theorem live_o2 :
    (∀ κ, 0 ≤ S2.slotRound κ → S2.slotRound κ + 5 + 2 ≤ 8 →
      ∃ v, OL.Decided S2 (OL.full OUL) κ v) ∧
    (∀ r, 0 ≤ r → r + 5 + 2 ≤ 8 →
      ∃ κ, r ≤ S2.slotRound κ ∧ S2.slotRound κ ≤ r + 5 ∧
        ∃ L, OL.Decided S2 (OL.full OUL) κ (some L)) :=
  LeanDag.Barnacle.Orcaella.holds.2.2 4 (by omega) (Fin 28) Unit 2 (by decide) 4 rr4_keyed
    2 (by omega) (by omega) OUL (OL.full OUL) 0 8 ul_good
    (coversUpto_full (LeanDag.Barnacle.Orcaella.holds.1 (Fin 4) (Fin 28) Unit 2 (by decide))
      OUL 8)

/-! ### The verdicts, pinned -/

/-- Slot `0` (round `0`, leader `0`): the genesis block, committed
directly. -/
theorem ul_slot0 : Hybrid.Decided (S := S1) 2 UL (View.full UL) 0 (some 0) :=
  Decided.directCommit (S := S1) (by decide) (by decide)

/-- Slot `3` (round `3`, leader `3`): the crashed validator has no
candidate, and under the repaired skip rule that is **not** enough. A
skip is now a quorum of round-`4` blocks referencing no candidate, so a
slot with no candidate is skipped only when the DAG carries the
evidence — which is the whole point of the repair
(`LeanDagTest/Hybrid.lean`, `docs/porting-plan.md`). -/
theorem ul_slot3 : Hybrid.Decided (S := S1) 2 UL (View.full UL) 3 none :=
  Decided.directSkip (S := S1) (by decide)

/-- The theorem's verdict for slot `0` is the hand commit. -/
theorem promise_slot0 :
    ∃ v, OL.Decided S1 (OL.full OUL) 0 v ∧ v = some 0 := by
  obtain ⟨v, hv⟩ := live_o1.1 0 (by omega) (by decide)
  exact ⟨v, hv, (LeanDag.Barnacle.Orcaella.holds.1 (Fin 4) (Fin 28) Unit 2 (by decide)).agree
    S1 _ _ 0 v (some 0) hv ul_slot0⟩

/-- Clause 2 at `r = 0`: the committed slot the theorem finds in
`[0, 5]` is never the crashed validator's slot `3`. -/
theorem promise_r0 :
    ∃ κ, κ ≤ 5 ∧ κ ≠ 3 ∧ ∃ L, OL.Decided S1 (OL.full OUL) κ (some L) := by
  obtain ⟨κ, h1, h2, L, hL⟩ := live_o1.2 0 (by omega) (by omega)
  simp only [Sched_slotRound, Nat.div_one] at h1 h2
  refine ⟨κ, by omega, fun h => ?_, L, hL⟩
  subst h
  exact absurd ((LeanDag.Barnacle.Orcaella.holds.1 (Fin 4) (Fin 28) Unit 2 (by decide)).agree
    S1 _ _ 3 _ _ hL ul_slot3) (by simp)

#print axioms live_o1
#print axioms live_o2
#print axioms promise_slot0
#print axioms promise_r0

end OrcaellaLive

end Barnacle

end LeanDagTest
