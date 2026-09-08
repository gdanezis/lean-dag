import LeanDag.Hydrozoan.Model.View
import LeanDag.Common.Participation
/-!
# Liveness hypotheses

The structural rendering of "after GST": every liveness theorem is
exactly as strong as the hypotheses here. Their derivation from delivery
primitives (received sets, timeouts, view convergence) is out of scope;
they are assumed.
-/

namespace LeanDag

namespace Hydrozoan

variable {Replica BlockId : Type*} [Fintype Replica] [DecidableEq Replica]
  [F : LeanDag.Hydrozoan.Faults Replica]

/-! **`PopulatedOn U T r`** (`Participation.lean`): every replica in `T`
authors a round-`r` block in `U`. `T ⊆ Correct` and `q ≤ T.card` are
hypotheses of the consuming theorems, not of this predicate. -/

/-- The all-of-`Correct` case. -/
abbrev Populated (U : BlockUniverse Replica BlockId) (r : ℕ) : Prop :=
  PopulatedOn U (Correct : Finset Replica) r

/-! **`SynchronisedOn U T R`** (`Participation.lean`): from round `R` on,
every `T`-authored block references every `T`-authored block of the
round below. An assumption, not a theorem: it is what the protocol's
waiting rule and timely post-stabilization delivery give in good
periods, not derived here from those primitives. `R` is a round index,
not GST — no clock or `Δ` appears in the model. Both quantifiers are
`T`-restricted deliberately, since assuming a Byzantine replica's blocks
get referenced would assume it behaves. Round-jumping recovery is not
modeled: a replica that jumps to the frontier sits outside `T`
permanently, even after rejoining the steady quorum. -/

/-- The all-of-`Correct` case. -/
abbrev Synchronised (U : BlockUniverse Replica BlockId) (R : ℕ) : Prop :=
  SynchronisedOn U (Correct : Finset Replica) R

/-! **The eventual view** is `View.full`; **a view caught up to round
`N`** is `View.CoversUpto`. The full view discharges every `CoversUpto`
hypothesis (`View.coversUpto_full`). -/

end Hydrozoan

end LeanDag
