import LeanDag.Common.Frame
import LeanDag.Adaptive.Basic
/-!
# Epochs as a frame

Epochs stand to slots as slots stand to rounds. `epochOf W k = k / W` is
the lookup of a frame of constant width `W`, so the epoch structure is a
`Frame` and generalising it is the substitution of an arbitrary one for
`constFrame W`.

This file records the identity and the one arithmetic fact the agreement
argument reads of it, which at a frame is the negation of
`Frame.cum_le_iff_le_roundOf` and needs no positivity hypothesis.
-/

namespace LeanDag
namespace Adaptive

/-- **The epoch structure is a frame of constant width.** -/
theorem epochOf_eq_roundOf (W : ℕ) (hW : 0 < W) (k : ℕ) :
    epochOf W k = (constFrame W hW).roundOf k :=
  (constFrame_roundOf W hW k).symm

/-- **A slot's epoch is below `e` exactly when the slot is below epoch
`e`'s first slot.** `epochOf_lt_iff` at a frame, and unconditional: the
positivity `epochOf` needs is `Frame.width_pos`. -/
theorem roundOf_lt_iff {E : Frame} {g e : ℕ} : E.roundOf g < e ↔ g < E.cum e := by
  constructor
  · intro h
    by_contra hc
    exact absurd (E.cum_le_iff_le_roundOf.mp (Nat.le_of_not_lt hc)) (by omega)
  · intro h
    by_contra hc
    exact absurd (E.cum_le_iff_le_roundOf.mpr (Nat.le_of_not_lt hc)) (by omega)

end Adaptive

end LeanDag
