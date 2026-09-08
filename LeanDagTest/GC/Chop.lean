import LeanDag.Properties.Arcs.GC
import LeanDag.GC.Window
import LeanDag.GC.AttestedBase
import LeanDag.GC.ChopDecided
import LeanDagTest.DoS.Exposure
import LeanDagTest.DoS.Exclusion
import LeanDagTest.DoS.Novelty
import LeanDag.Network.Quorum
import LeanDag.Mysticeti.Record
/-!
# The horizon, witnessed

`garbage.md` P0 and the data half of P8. Four things on the existing
models, all by `decide`:

**The cut, computed** (`chop Uexcl 2`): the post-exclusion DAG re-based —
the round-2 layer becomes the genesis layer (references emptied, rounds
shifted), and the slot-1 commit survives verbatim: `DirectCommit Uexcl 11 3`
becomes `DirectCommit (chop Uexcl 2) 11 1`, decided on the data.

**The statute of limitations, on data** (`chop Umerge 1`): validator 0's
equivocation — the two geneses `0` and `4` — falls strictly below the cut,
and the exposure that debarred it *vanishes*: `ExposedIn Umerge 9 0` holds,
`ExposedIn (chop Umerge 1) 9 0` does not. Truncation forgives; this is the
converse direction `dosValid_chop` deliberately does not have.

**Bounded storage on data** (`Dtwin`): with horizon `G = 1` and lag
`Λ = 1`, validator 1's retained store at round 2 is 4 blocks against the
G6 constant of 9 — and the constant does not grow with `t`.

**The attested base on data** (`Utwin`, `Uexcl`): `Base Utwin 1 0` is
exactly `{1, 2, 3}` — the shared correct layer, with both equivocation
halves (each attested once) filtered out: the sandwich `C ⊆ Base` tight at
the bottom. On `Uexcl`, completeness applied: the correct round-2 blocks
all clear the filter at attestation round 4, through the backbone.
-/

namespace LeanDagTest

open LeanDag

/-! ## The cut, computed -/

-- The base layer keeps its blocks, loses its references, and rebases:
-- round-2 block 8 becomes a genesis of the truncation.
example : ((chop Uexcl 2).block 8).refs = ∅ := by decide
example : ((chop Uexcl 2).block 8).round = 0 := by decide
example : ((chop Uexcl 2).block 11).round = 1 := by decide
example : (8 : Fin 20) ∈ (chop Uexcl 2).ids ∧ (4 : Fin 20) ∉ (chop Uexcl 2).ids := by
  decide

-- The truncation still satisfies the DoS condition (the one-way door).
example : DoSValid (chop Uexcl 2) := dosValid_chop uexcl_dosValid

/-! ## Verdict invariance on data -/

-- The slot-1 commit of `Uexcl` (round 3, certificates at round 5)
-- survives the cut at G = 2 verbatim: same certificates, same verdict,
-- at rebased indices.
example : DirectCommit Uexcl 11 3 := by decide
example : DirectCommit (chop Uexcl 2) 11 1 := by decide

/-! ## The decision relation across the cut (G3/G4) -/

-- The induced schedule: `fairSlots` (slot `k` at round `3k`) chopped at
-- `G = 2` from base slot `d = 1` puts slot 0 at rebased round 1 — where
-- `Uexcl`'s slot-1 commit now lives.
example : (fairSlots.chop 2 1 (by decide)).slotRound 0 = 1 := by decide
example : (fairSlots.chop 2 1 (by decide)).leader 0 = 1 := by decide

-- The full-history decision at slot 1, concretely: leader block 11.
example : Decided Uexcl (View.full Uexcl) 1 (some 11) :=
  Decided.directCommit (by decide) (by decide)

-- G3 applied: the truncated view re-decides it as slot 0 of the truncation.
example : Decided (S := fairSlots.chop 2 1 (by decide)) (chop Uexcl 2)
    ((View.full Uexcl).chop 2) 0 (some 11) :=
  (MysticetiProperties.decided_chop_iff (by decide)).mp
    (Decided.directCommit (by decide) (by decide))

-- A joiner's decision, derived *inside the truncation alone*: the full view
-- of `chop Uexcl 2` is not `V.chop` for any full-history `V`, and the
-- direct rule fires on the truncated data by computation.
example : Decided (S := fairSlots.chop 2 1 (by decide)) (chop Uexcl 2)
    (View.full (chop Uexcl 2)) 0 (some 11) :=
  Decided.directCommit (S := fairSlots.chop 2 1 (by decide)) (by decide) (by decide)

/-- **G4 on data**: whatever verdicts a joiner (any view of the truncation,
slot 0) and a full-history validator (any view of `Uexcl`, slot 1) reach,
they are the same verdict. -/
example {w v : Option (Fin 20)}
    (hW : Decided (S := fairSlots.chop 2 1 (by decide)) (chop Uexcl 2)
      (View.full (chop Uexcl 2)) 0 w)
    (hV : Decided Uexcl (View.full Uexcl) 1 v) : w = v :=
  MysticetiProperties.decided_agree_chop (by decide) hW hV

/-! ## The statute of limitations, on data -/

-- In the full universe, validator 0 is exposed in every cone that merges
-- its two geneses…
example : ExposedIn Umerge 9 0 := by decide

-- …and the cut at G = 1 places the witnessing pair strictly below the
-- horizon: the exposure vanishes, in every surviving cone.
example : ¬ ExposedIn (chop Umerge 1) 9 0 := by decide
example : ¬ ExposedIn (chop Umerge 1) 12 0 := by decide

-- A pair *at* the cut survives (garbage.md §3): chopping `Umerge` at the
-- equivocation round itself keeps both geneses in the base layer, and the
-- merge cone is still exposed.
example : ExposedIn (chop Umerge 0) 9 0 := by decide

/-! ## Bounded storage on data (G6) -/

/-- G6 applied to `Dtwin` at horizon `G = 1`, lag `Λ = 1`, round `t = 2`:
the retained store is bounded by the constant `3·2 + (3 + 1·0) = 9`. -/
example : ((viewUpto Dtwin 1 2).filter
      fun i => 1 ≤ (Utwin.block i).round).card ≤
    (Correct : Finset (Fin 4)).card * (1 + 1) +
      ((Correct : Finset (Fin 4)).card * Faults.f (Fin 4) +
        1 * ((Correct : Finset (Fin 4)).card * (Faults.f (Fin 4) * 0))) :=
  card_retained_le dtwin_byz dtwin_refsAccepted (by decide) (by omega)
    (by omega)

example : ((viewUpto Dtwin 1 2).filter
    fun i => 1 ≤ (Utwin.block i).round).card = 4 := by decide

/-- G5 applied: the truncation of `Utwin` at its horizon is populated —
liveness transfers through the cut. -/
example : ∀ r ≤ 0, Populated (chop Utwin 1) r :=
  populated_chop utwin_populated (le_refl 1)

/-! ## The attested base on data (G10) -/

/-- The inexact certificate on `Utwin`: the base at attestation round 1 is
**exactly the shared correct layer** — both equivocation halves (geneses
`0` and `4`, each attested by a single author) fail the `f+1` filter. The
sandwich `C ⊆ Base ⊆ ∪ correct cones`, tight at the bottom. -/
example : Base Utwin 1 0 = {1, 2, 3} := by decide

-- Soundness applied: everything in the base has a correct attester.
example : ∃ a ∈ Utwin.ids, (Utwin.block a).round = 1 ∧
    (Utwin.block a).creator ∈ (Correct : Finset (Fin 4)) ∧
    (1 : Fin 9) ∈ history Utwin a :=
  exists_correct_attester_of_mem_base (G := 0) (by decide)

-- Completeness applied on `Uexcl` (synchronised from round 0, populated
-- through round 5): every correct round-2 block clears the filter at
-- attestation round 4, through the backbone.
example : (8 : Fin 20) ∈ Base Uexcl 4 2 :=
  correct_mem_base (SynchronisedOn.mono (by decide) uexcl_synchronised)
    (by omega) (by omega) (uexcl_populated 4 (by omega)) (by decide)
    (by decide) (by decide)

example : Base Uexcl 4 2 = {8, 9, 10} := by decide

#print axioms dosValid_chop
#print axioms card_retained_le
#print axioms correct_mem_base

end LeanDagTest
