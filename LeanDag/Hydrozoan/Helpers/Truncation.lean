import LeanDag.Hydrozoan.Helpers.Banded
import LeanDag.Properties.Truncate
/-!
# Hydrozoan's rules across a truncation

Not part of the audit surface. The transfer lemmas
`Properties.LocalTruncate` needs: a truncation prunes below a horizon
and renumbers what remains, and `no_base_of_naive_shift` records why a
pure renumbering (no pruning) admits no non-empty model — a round-zero
block would need empty refs, which validity forbids past genesis.
-/

namespace LeanDag

namespace Hydrozoan

open LeanDag.Properties

variable {Replica : Type} [Fintype Replica] [DecidableEq Replica]
variable {BlockId : Type} [DecidableEq BlockId] [LinearOrder BlockId]
variable [LeanDag.Hydrozoan.Faults Replica]
variable {U U' : LeanDag.Hydrozoan.BlockUniverse Replica BlockId}
variable {S S' : LeanDag.Slots Replica} {G d : ℕ}

/-! ## The dead end -/

/-- A pure renumbering: every block kept, every round lower by `G`. -/
structure NaiveShift (U U' : LeanDag.Hydrozoan.BlockUniverse Replica BlockId) (G : ℕ) :
    Prop where
  mem : ∀ b, b ∈ U.ids ↔ b ∈ U'.ids
  round : ∀ b, b ∈ U.ids → (U'.block b).round + G = (U.block b).round
  refs : ∀ b, b ∈ U.ids → (U'.block b).refs = (U.block b).refs

/-- A block at round zero has no refs: the predecessor condition is
unsatisfiable there. -/
theorem refs_empty_of_round_zero {b : BlockId} (hb : b ∈ U.ids)
    (hr : (U.block b).round = 0) : (U.block b).refs = ∅ := by
  rw [Finset.eq_empty_iff_forall_notMem]
  intro j hj
  have := (U.valid b hb).predecessor j hj
  omega

/-- **A pure shift by a positive horizon admits no round-zero block**,
and a non-empty valid universe must have one. So the naive factoring of
a truncation into a restriction and a renumbering has no models, and a
property quantified over it is vacuously true. -/
theorem no_base_of_naive_shift (h : NaiveShift U U' G) (hG : 0 < G)
    (hq : 0 < LeanDag.Hydrozoan.q Replica)
    (b : BlockId) (hb : b ∈ U'.ids) : (U'.block b).round ≠ 0 := by
  intro hr
  have hbU : b ∈ U.ids := (h.mem b).mpr hb
  have hround : (U.block b).round = G := by have := h.round b hbU; omega
  have hparU : (U.block b).refs = ∅ := by
    rw [← h.refs b hbU]; exact refs_empty_of_round_zero hb hr
  have hqq := (U.valid b hbU).quorum (by omega)
  simp only [LeanDag.creators, LeanDag.creatorsOf, hparU,
    Finset.image_empty, Finset.card_empty, Nat.le_zero] at hqq
  omega

end Hydrozoan

end LeanDag
