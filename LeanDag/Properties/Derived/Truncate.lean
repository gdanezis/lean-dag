import LeanDag.Properties.Truncate
import LeanDag.Properties.Compose
import LeanDag.Properties.Band
/-!
# Truncation invariance

`docs/target-properties.md` §3.4b. No longer an obligation: it follows
from the band, now that `AgreeBand` reads both universes in a common
frame — a cut is the instance `g = 0, g' = G`, and reading it backwards
swaps the pairs, so both directions of the `↔` are instances of one
property. The band's references clause is guarded strictly above the
floor, which is exactly the licence a cut needs to empty its bottom
layer.
-/

namespace LeanDag

namespace Properties

variable {Validator : Type} [Fintype Validator] [DecidableEq Validator]
variable {BlockId : Type} [DecidableEq BlockId] {Payload : Type}
variable {R : DagRule Validator BlockId Payload}

/-- **Truncation invariance.** A replica that has pruned below the
horizon reaches exactly the verdicts it would have reached with its
whole history, at its own numbering.

An `↔`, because both directions are consumed: a joiner needs verdicts
to survive the cut, and cross-cut agreement needs them to come back. -/
def LocalTruncate (R : DagRule Validator BlockId Payload) : Prop :=
  ∀ (S S' : Slots Validator) (U U' : R.Universe) (G d : ℕ),
    Truncates R U U' S S' G d →
    ∀ (V : R.View U) (V' : R.View U'), ViewAgreeAbove R V V' G →
    ∀ (k : ℕ) (v : Option BlockId), R.Decided S V (d + k) v ↔ R.Decided S' V' k v

/-- **Truncation invariance at a period.** `LocalTruncate` for a rule whose
band needs the cut to be by a whole number of periods, which is what a wave
repeating every `p` rounds survives. At `p = 1` every cut qualifies. -/
def LocalTruncateAt (p : ℕ) (R : DagRule Validator BlockId Payload) : Prop :=
  ∀ (S S' : Slots Validator) (U U' : R.Universe) (G d : ℕ), (∃ t, t * p = G) →
    Truncates R U U' S S' G d →
    ∀ (V : R.View U) (V' : R.View U'), ViewAgreeAbove R V V' G →
    ∀ (k : ℕ) (v : Option BlockId), R.Decided S V (d + k) v ↔ R.Decided S' V' k v

/-- **Truncation invariance at a period falls out of the band at that
period**: `decided_of_rebased_at` at a cut, whose settling round is its
horizon. -/
theorem LocalTruncateAt.of_bandedAt {p : ℕ} (h : BandedAt p R) : LocalTruncateAt p R :=
  fun S _S' _U _U' _G d hp ht _V _V' hv k v =>
    decided_of_rebased_at h hp (Rebased.of_truncates ht) hv k
      (le_trans ht.base (S.mono (Nat.le_add_right d k))) v

/-- **Truncation invariance falls out of the band**: `LocalTruncateAt` at
period one, where every cut is by a whole number of periods. -/
theorem LocalTruncate.of_banded (h : Banded R) : LocalTruncate R :=
  fun S S' U U' G d ht V V' hv k v =>
    LocalTruncateAt.of_bandedAt (bandedAt_one_iff.mpr h) S S' U U' G d ⟨G, by omega⟩ ht V V' hv k v

end Properties

end LeanDag
