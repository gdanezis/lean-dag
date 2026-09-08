import LeanDag.FinWhale.Decision
import LeanDag.Mysticeti.ViewPace
/-!
# FinWhale — the bridge to the development's pacing line

Carries a `ViewPace`'s production and coverage results
(`ViewPace.populatedOn`, `ViewPace.synchronisedOn_of_converges`) to a
FinWhale DAG, for compatibility with the development's main line. It is
not the route FinWhale's own liveness runs on: that comes from the
block-creation conditions in `Creation.lean`, since a reactive builder
has no waiting floor to derive coverage from.
-/

namespace LeanDag

namespace FinWhale

variable {Validator : Type} [Fintype Validator] [DecidableEq Validator]
variable [F : Faults Validator] [P : Params Validator]
variable {BlockId : Type} [DecidableEq BlockId] {Payload : Type}
variable {D : Dag Validator BlockId Payload}

/-- **Production, from the pacing line.** Every correct validator authors
a block at every round below the horizon. This is the pacemaker's
progress rule, not a timing argument: `PaceCore.populatedOn` reads a
round a validator reached as a round it built in. -/
theorem populated_of_viewPace {U : BlockUniverse Validator BlockId Payload} {N : ℕ}
    (vp : ViewPace U (Correct : Finset Validator) N)
    (hids : D.ids = U.ids) (hblk : D.block = U.block) :
    ∀ r ≤ N, PopulatedFrom D.block D.ids (Correct : Finset Validator) r := by
  intro r hr
  rw [hids, hblk]
  exact vp.populatedOn card_correct r hr

/-- **Coverage, from the pacing line.** From any round past GST, once the
timeout clears `2∆ + proc`, every correct block references every correct
block of the round below. View convergence supplies the drift bound and
the race against the timeout supplies coverage; neither is assumed here.

A reactive builder has no such property, which is why FinWhale's liveness
does not run on it. -/
theorem synchronised_of_viewPace {U : BlockUniverse Validator BlockId Payload} {N R : ℕ}
    (vp : ViewPace U (Correct : Finset Validator) N)
    (hids : D.ids = U.ids) (hblk : D.block = U.block)
    (hgst : vp.gst ≤ R)
    (hbackoff : ∀ n, R ≤ n → 2 * vp.delay + vp.proc ≤ vp.timeout n) :
    SynchronisedFrom D.block D.ids (Correct : Finset Validator) R := by
  rw [hids, hblk]
  exact vp.synchronisedOn_of_converges card_correct hgst hbackoff

end FinWhale

end LeanDag
