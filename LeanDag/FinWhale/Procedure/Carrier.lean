import LeanDag.FinWhale.View
import LeanDag.FinWhale.Band
import LeanDag.FinWhale.Least
import LeanDag.FinWhale.Procedure.Pass
import LeanDag.Common.Anchored.Band
import LeanDag.Properties.Agree
import LeanDag.Properties.Candidate
import LeanDag.Properties.Optional.Direct
import LeanDag.Properties.Optional.Quorate
import LeanDag.Properties.Optional.SelfParent
import LeanDag.Properties.Derived.LeaderCommits
import LeanDag.Properties.Support
import LeanDag.Timed.Coverage
import LeanDag.Properties.Arcs.Headline
import LeanDag.FinWhale.Carrier
import LeanDag.FinWhale.Procedure.View
/-!
# FinWhale — the pass a view runs, and that it lands in the relation

Procedure side: these mention a verdict assignment or the reverse pass.
-/

namespace LeanDag
namespace FinWhaleProperties
open LeanDag.Properties
open LeanDag.Timed (SynchronisedOn CoversToward OfCoverage coversToward_of_synchronisedOn)
open LeanDag.FinWhale
variable {Validator : Type} [Fintype Validator] [DecidableEq Validator]
variable [F : Faults Validator] [P : LeanDag.FinWhale.Params Validator]
variable {BlockId : Type} [LinearOrder BlockId] {Payload : Type}
variable [LinearOrder BlockId]

/-- The pass a view runs. -/
noncomputable def passOf (S : Slots Validator) (D : Dag Validator BlockId Payload)
    (V : D.View) : ℕ → Verdict BlockId :=
  decOf S (EligibleAt (S := S) 2) (V.toRecord) (chooseLeast S D) (dagHorizon D)

/-- It is well formed, at every schedule. -/
theorem wellFormed_passOf {D : Dag Validator BlockId Payload} {S : Slots Validator}
    (V : D.View) :
    WellFormed (EligibleAt (S := S) 2) (viewCommit S D V) (viewSkip S D V) (chooseLeast S D)
      (passOf S D V) :=
  wellFormed_decOf (view_bounded D V) (fun _ _ => lt_of_eligibleAt) (rle S D) (chooseLeast S D)

/-- **And every verdict it reaches is the relation's.** -/
theorem decided_of_passOf {D : Dag Validator BlockId Payload} {S : Slots Validator}
    {V : D.View} {k : ℕ} (h : passOf S D V k ≠ Verdict.undecided) :
    (finWhaleRule (Payload := Payload)).Decided S V k (passOf S D V k).optOf :=
  decided_of_wellFormed (wellFormed_passOf V) (N := dagHorizon D + 1)
    (fun _ hs => decOf_of_gt (by omega)) k h

end FinWhaleProperties

end LeanDag
