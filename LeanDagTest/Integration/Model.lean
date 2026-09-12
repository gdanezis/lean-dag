import LeanDag.Integration.Coverage
import LeanDag.Integration.Retention
import LeanDag.Integration.ReGenesis
import LeanDag.Integration.Exposure
import LeanDag.Integration.DeliveryFill
import LeanDag.Integration.Margin
import LeanDag.Integration.CommonTarget
import LeanDag.Integration.HydrozoanMechanisms
import LeanDagTest.SafeSkip.Model
import Mathlib.Tactic.IntervalCases
/-!
# The integration lemmas, witnessed

The house rule applies with particular force to a *negative* result:
`not_synchronisedOn_skipFill` (I5) refutes coverage under the Safe Skip
fill, and a refutation whose hypotheses cannot be met refutes nothing.
This file discharges them on `Ucrash`, the crashed round-robin family
of `LeanDagTest/SafeSkip.lean`, so the failure is exhibited rather than
merely asserted.

The instantiation is the natural one, not a contrived one: the reliable
set is everybody once validator `3` is restored — exactly the set SS2
(`skipFill_populatedOn`) hands to the liveness account — the gap round
is the one the message fills, and the block above it is an ordinary
round-`2` block of a validator that never crashed.
-/

namespace LeanDagTest

open LeanDag LeanDag.Integration

/-- The fill of `Ucrash 2` targeting round `1`: validator `3` crashed
after its genesis block and rejoins with one message. -/
abbrev skTight : SkipMsg (Ucrash 2) := ucrashMsg 2 1 (by omega)

-- The fill's parameters, on data: the gap is the single round `1`.
example : skTight.v1 = 3 := rfl
example : skTight.r = 1 := rfl
example : skTight.r0 = 0 := by simp [SkipData.r0, ucrashMsg]

/-- Block `8` is validator `0`'s round-`2` block — old, reliable, and
sitting directly above the filled round. -/
example : ((Ucrash 2).block 8).round = 2 ∧ ((Ucrash 2).block 8).creator = 0 := by
  decide

/-- **I5 bites.** Coverage genuinely fails in the extension: with the
recovering validator counted reliable, no round-`2` block references
the block the fill supplies at round `1`, because no old block can
reference a fresh identifier. This is the same fact SS3 uses to prove
the fill cannot conjure a commit. -/
theorem ucrash_not_synchronisedOn :
    ¬ SynchronisedOn skTight.skipFill (Finset.univ : Finset (Fin 4)) 0 :=
  not_synchronisedOn_skipFill skTight (k := 1) (b := 8)
    (hv1 := Finset.mem_univ _) (hk1 := by simp [SkipData.r0, ucrashMsg])
    (hk2 := le_refl _) (hk := Nat.zero_le _)
    (hb := by decide) (hbround := by decide) (hbc := Finset.mem_univ _)

/-- And the positive form holds where it should: strictly above the
fill, every block is old and coverage transfers unchanged. Vacuously
true of `Ucrash 2` past round `1`, which is the honest reading — the
family stops there — but the *statement* is the one liveness consumes
after recovery. -/
example (hs : SynchronisedOn (Ucrash 2) (Finset.univ : Finset (Fin 4)) 0) :
    SynchronisedOn skTight.skipFill (Finset.univ : Finset (Fin 4)) 2 :=
  synchronisedOn_skipFill_above skTight hs (Nat.zero_le _) (by decide)

#print axioms LeanDag.Integration.addGenesis
#print axioms LeanDag.Integration.dosValid_addGenesis
#print axioms LeanDag.Integration.history_B1_subset_fill
#print axioms LeanDag.Integration.exposedIn_skipFill_old
#print axioms LeanDag.Integration.dosValid_skipFill
#print axioms LeanDag.Integration.fill_cone_subset
#print axioms LeanDag.Integration.dosValid_skipFill_of_covered
#print axioms LeanDag.Integration.exists_commonAt
#print axioms LeanDag.Integration.fill_refs_available
#print axioms LeanDag.Integration.card_severed_le
#print axioms LeanDag.Integration.card_novelty_le_of_donor
#print axioms LeanDag.Integration.skipFillD
#print axioms LeanDag.Integration.uniformBudget_skipFillD
#print axioms LeanDag.Integration.not_refsAccepted_skipFillD
#print axioms LeanDag.Integration.regenesis_converges
#print axioms LeanDag.Integration.hB1uniq_of_addGenesis
#print axioms LeanDag.Integration.recoveryMsg
#print axioms LeanDag.Integration.populatedOn_addGenesis
#print axioms LeanDag.Integration.no_blocks_of_no_genesis
#print axioms LeanDag.Integration.severed_of_pruned_anchor
#print axioms LeanDag.Integration.anchor_pruned
#print axioms LeanDag.Integration.chopMsg
#print axioms LeanDag.Integration.outage_bounded_by_lag
/-! ## The constructions, witnessed

The house rule of report §18 applies with particular force to the
structures this arc introduces: `recoveryMsg` and `skipFillD` carry
many hypotheses, and hypotheses that cannot be met jointly make every
theorem above them vacuous. The severed-validator scenario is the one
they all describe, and `Ucrash` exhibits it: validator `3` crashed
after its genesis block, so a horizon at round `1` prunes its entire
history. -/

/-- The truncation at which validator `3` is severed — its only block
sat at round `0`. -/
abbrev Ucut : BlockUniverse (Fin 4) ℕ Unit := chop (Ucrash 2) 1

example : (3 : ℕ) ∉ Ucut.ids := by decide

/-- **Severance, on data.** No block of the truncation is validator
`3`'s, which is the hypothesis `addGenesis` needs and the conclusion
`severed_of_pruned_anchor` reaches in general. -/
theorem ucut_severed : ∀ b ∈ Ucut.ids, (Ucut.block b).creator ≠ 3 := by decide

/-- **Re-genesis, on data.** The stranded validator restarts at the cut
with a reference-free block; the universe laws hold by the same
argument `chop` uses for the layer it flattened. -/
abbrev Uregen : BlockUniverse (Fin 4) ℕ Unit :=
  addGenesis Ucut 3 999 () (by decide) ucut_severed

example : (999 : ℕ) ∈ Uregen.ids := mem_addGenesis
example : (Uregen.block 999).round = 0 ∧ (Uregen.block 999).creator = 3 := by
  constructor <;> rw [addGenesis_block_new]

/-- The re-genesis block is a lawful Safe Skip anchor, on data: unique
at its round because its author has no other block anywhere. -/
example : ∀ j ∈ Uregen.ids, (Uregen.block j).creator = 3 →
    (Uregen.block j).round = (Uregen.block 999).round → j = 999 :=
  hB1uniq_of_addGenesis

/-- **The exposure condition survives re-genesis, on data.** -/
example : DoSValid Ucut → DoSValid Uregen := dosValid_addGenesis

/-- **The catch-up fill, on data.** After re-genesis the stranded
validator rejoins production with one message, anchored on its new
block and filling the retained window: donor line `1` (blocks `5` at
the cut and `9` above it), target round `1`.

This is the arc's most hypothesis-heavy construction, and exhibiting it
is what rules out the possibility that its clauses cannot be met
together. -/
def urecover : SkipMsg Uregen :=
  recoveryMsg (V := Ucut) (v := 3) (g := 999) (p := ())
    (hg := by decide) (hsev := ucut_severed)
    1 (fun k => if k = 0 then 5 else 9) (fun k => 1000 + k) (fun b => b - 1000)
    1 (by decide)
    (by intro k hk; interval_cases k <;> decide)
    (by intro k hk; interval_cases k <;> decide)
    (by
      intro k hk
      have h0 : (Uregen.block 999).round = 0 := by rw [addGenesis_block_new]
      rw [h0]
      interval_cases k <;> decide)
    (by intro k hk1 hk2; interval_cases k <;> decide)
    (by
      intro k
      simp only [Uregen, addGenesis, BlockRecord.addGenesis_ids, Finset.mem_insert]
      push Not
      refine ⟨by omega, ?_⟩
      intro hc
      rw [mem_chop_ids, ucrash_ids, Finset.mem_filter, Finset.mem_range] at hc
      omega)
    (fun k => by omega)

-- The recovery message's shape, on data: anchored at the re-genesis
-- block, filling to the target.
example : urecover.B1 = 999 := rfl
example : urecover.v1 = 3 := rfl
example : urecover.r = 1 := by
  show (Uregen.block 999).round + 1 = 1
  rw [addGenesis_block_new]

#print axioms urecover

#print axioms ucut_severed

#print axioms LeanDag.Timed.not_synchronisedOn_of_extends
#print axioms LeanDag.Timed.synchronisedOn_of_extends
#print axioms LeanDag.Integration.not_synchronisedOn_copyFill_hz
#print axioms LeanDag.Integration.honestNoEquiv_chop
#print axioms LeanDag.Integration.honestNoEquiv_skipFill
#print axioms LeanDag.Integration.synchronisedOn_chop
#print axioms LeanDag.Integration.not_synchronisedOn_skipFill
#print axioms LeanDag.Integration.synchronisedOn_skipFill_above
#print axioms ucrash_not_synchronisedOn

end LeanDagTest
