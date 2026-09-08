import LeanDag.Properties.Arcs.GC
import LeanDag.GC.Horizon
import LeanDagTest.GC.Bootstrap
import LeanDag.Mysticeti.Record
/-!
# The horizon policy, witnessed

`garbage.md` P7's data half. Three facts on `Uexcl`/`Dexcl`:

**The composition law on data**: cutting at 1 and then cutting once more
is cutting at 2 — as a theorem instance and recomputed blockwise on the
data.

**G9 on data — possession universalises in one round**: validator 3 never
accepted equivocation half `0`, and does not hold it at round 0; one
round later it does, delivered inside carrier 5's cone. The subset
statement `viewUpto Dexcl 1 0 ⊆ viewUpto Dexcl 3 1` is checked by
computation and derived from the theorem.

**G8 on data — heterogeneous horizons agree**: a joiner truncated at
`G = 1` and one truncated at `G = 2` each decide their own slot 0 — the
same absolute slot 1 — and cross-horizon agreement pins the verdicts to
each other. Both actually decide `some 11`, by computation inside each
truncation.
-/

namespace LeanDagTest

open LeanDag

/-! ## The composition law on data -/

example : chop (chop Uexcl 1) 1 = chop Uexcl 2 :=
  chop_chop (G₁ := 1) (G₂ := 2) (by omega)

example : (chop (chop Uexcl 1) 1).ids = (chop Uexcl 2).ids := by decide

example : ∀ i : Fin 20,
    ((chop (chop Uexcl 1) 1).block i).round = ((chop Uexcl 2).block i).round ∧
    ((chop (chop Uexcl 1) 1).block i).refs = ((chop Uexcl 2).block i).refs := by
  decide

/-! ## G9 on data — one round to universal possession -/

-- Validator 3 never accepted equivocation half 0, and does not hold it…
example : (0 : Fin 20) ∉ viewUpto Dexcl 3 0 := by decide

-- …but one round later it does: carrier 5's cone hands it over.
example : (0 : Fin 20) ∈ viewUpto Dexcl 3 1 := by decide

-- The subset on data…
example : viewUpto Dexcl 1 0 ⊆ viewUpto Dexcl 3 1 := by decide

-- …and from the theorem.
example : viewUpto Dexcl 1 0 ⊆ viewUpto Dexcl 3 1 :=
  viewUpto_subset_viewUpto_succ dexcl_eventuallyDelivers
    (uexcl_populated 1 (by omega)) (by decide) (by decide) (by omega)

/-! ## G8 on data — heterogeneous horizons agree -/

-- Each truncation decides its own slot 0 — the same absolute slot 1 —
-- by computation inside the truncation alone.
example : Decided (S := fairSlots.chop 1 1 (by decide)) (chop Uexcl 1)
    (View.full (chop Uexcl 1)) 0 (some 11) :=
  Decided.directCommit (S := fairSlots.chop 1 1 (by decide))
    (by decide) (by decide)

example : Decided (S := fairSlots.chop 2 1 (by decide)) (chop Uexcl 2)
    (View.full (chop Uexcl 2)) 0 (some 11) :=
  Decided.directCommit (S := fairSlots.chop 2 1 (by decide))
    (by decide) (by decide)

/-- **G8 applied.** Whatever views the two joiners hold of their
respective truncations, their verdicts for the shared slot coincide. -/
example {w₁ w₂ fv : Option (Fin 20)}
    (hW₁ : Decided (S := fairSlots.chop 1 1 (by decide)) (chop Uexcl 1)
      (View.full (chop Uexcl 1)) 0 w₁)
    (hW₂ : Decided (S := fairSlots.chop 2 1 (by decide)) (chop Uexcl 2)
      (View.full (chop Uexcl 2)) 0 w₂)
    (hV : Decided Uexcl (View.full Uexcl) 1 fv) :
    w₁ = w₂ :=
  MysticetiProperties.decided_agree_horizons_chop (by decide) (by decide) rfl hW₁ hW₂ hV

#print axioms chop_chop
#print axioms viewUpto_subset_viewUpto_succ
#print axioms LeanDag.MysticetiProperties.decided_agree_horizons_chop

end LeanDagTest
