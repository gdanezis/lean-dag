import LeanDag.OptimalHydrozoan.Delivery.Proof
import LeanDagTest.OptimalHydrozoan.PrefixAgreement
/-!
# Witness: Optimal delivered sequences

`delivered` computed on the settled slots of `OD`, whose committed
leaders below horizon 7 are `[3, 8, 13, 22]`. `OD` holds no two blocks of
one author and round, so the paper's key and a block's own id deliver the
same list here; a third, coarser key (the author alone) shows the filter
following whatever key it is given. The listing `linD` is a toy that
makes consecutive leaders' lists overlap; it is not `OD`'s causal
history.

Then the conjuncts of `holds` applied on this data, across the
one-vote-short view and the full one.
-/

namespace LeanDagTest

namespace OptimalHydrozoan

open LeanDagTest.Hydrozoan
open LeanDag LeanDag.Hydrozoan LeanDag.OptimalHydrozoan
open LeanDag.Hydrozoan.PrefixAgreement (ledger)
open LeanDag.Hydrozoan.Delivery (delivered authorRound)

/-- A toy per-leader listing: block 3 (the first leader), then the
leader itself. -/
def linD (b : Fin 30) : List (Fin 30) := [3, b]

-- The unfiltered ledger repeats block 3 at every leader.
example : ledger linD gD 7 = [3, 3, 3, 8, 3, 13, 3, 22] := rfl

-- By block id, and by author and round: the repeats dropped.
example : delivered id linD gD 7 = [3, 8, 13, 22] := by decide
example : delivered (authorRound OD.toBlockRecord.block) linD gD 7 = [3, 8, 13, 22] := by decide

-- By author alone: leaders 8 and 22 share author 1, so 22 is dropped.
example : delivered (fun b => (OD.toBlockRecord.block b).creator) linD gD 7 = [3, 8, 13] := by
  decide

-- The shorter replica.
example : delivered id linD gDs 2 = [3] := by decide

-- `holds`, first conjunct.
example : ((delivered (authorRound OD.toBlockRecord.block) linD gD 7).map
    (authorRound OD.toBlockRecord.block)).Nodup :=
  (OptimalHydrozoan.Delivery.holds (Fin 4) (Fin 30) OD).1 _ _ linD gD 7

-- Second conjunct, across the two views and horizons.
example : delivered (authorRound OD.toBlockRecord.block) linD gDs 2 <+:
    delivered (authorRound OD.toBlockRecord.block) linD gD 7 :=
  (OptimalHydrozoan.Delivery.holds (Fin 4) (Fin 30) OD).2.1 _ _ linD VDs' VD gDs gD 2 7
    (by omega) vds_gDs vd_gD

-- Third conjunct: what is delivered is a subsequence of the ledger.
example : (delivered id linD gD 7).Sublist (ledger linD gD 7) :=
  ((OptimalHydrozoan.Delivery.holds (Fin 4) (Fin 30) OD).2.2 _ id linD gD 7).1

end OptimalHydrozoan

end LeanDagTest
