import LeanDag.GC.Window
import LeanDag.DoS.Novelty
/-!
# The DoS capstones, bundling growth with the storage bound

**An analysis** (`Analyses`): the composed capstones, bundling the
DoS arc's growth bound with the storage bound. It names no commit rule
and transforms no universe.

The composed statements — DoS resistance in one theorem — with production
taken as a hypothesis, discharged elsewhere by the `ViewPace` route
(`ViewPace.populatedOn`, report §6.9).
-/

namespace LeanDag

variable {Validator : Type*} [Fintype Validator] [DecidableEq Validator]
variable [F : Faults Validator]
variable {BlockId : Type*} [DecidableEq BlockId] {Payload : Type*}
variable {U : BlockUniverse Validator BlockId Payload}
variable {D : Delivery U} {G N : ℕ}

/-- **DoS resistance, with post-`R` delivery.** Production, delivery, an
enforceable budget and the reference discipline together give liveness
and a linear bound on retained view growth. -/
theorem populated_and_card_viewUpto_le' {κ R N : ℕ}
    (hpop : ∀ r ≤ N, Populated U r)
    (hED : EventuallyDelivers D R)
    (hbyz : ByzBudget D κ) (hra : RefsAccepted D) :
    (∀ r ≤ N, Populated U r) ∧
      ∀ v ∈ (Correct : Finset Validator), ∀ n, R + 1 ≤ n →
        (viewUpto D v n).card ≤ (viewUpto D v (R + 1)).card +
          (n - (R + 1)) *
            ((Correct : Finset Validator).card * (F.f * κ + 1) + F.f * κ) :=
  ⟨hpop, fun _v hv _n hn => card_viewUpto_le' hbyz hED hra hv hn⟩

/-- **DoS resistance, unconditionally.** Production, an enforceable
budget and the reference discipline give liveness and linear storage
from round 0, with no delivery hypothesis. -/
theorem populated_and_card_viewUpto_le {κ N : ℕ}
    (hpop : ∀ r ≤ N, Populated U r)
    (hbyz : ByzBudget D κ) (hra : RefsAccepted D) :
    (∀ r ≤ N, Populated U r) ∧
      ∀ v ∈ (Correct : Finset Validator), ∀ n,
        (viewUpto D v n).card ≤
          (Correct : Finset Validator).card * (n + 1) +
            ((Correct : Finset Validator).card * F.f +
              n * ((Correct : Finset Validator).card * (F.f * κ))) :=
  ⟨hpop, fun _v hv n => card_viewUpto_le hbyz hra hv n⟩

end LeanDag
