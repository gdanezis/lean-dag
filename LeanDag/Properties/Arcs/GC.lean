import LeanDag.Properties.Truncate
import LeanDag.Properties.Sustain
import LeanDag.Properties.Band
import LeanDag.Properties.Derived.Truncate
import LeanDag.Properties.Record
/-!
# Garbage collection, for any protocol with a band

`docs/target-properties.md` G2. Garbage collection is `LocalTruncate`
applied; the two corollaries below are the directions a deployment
uses. `Properties.LocalTruncate.of_banded` derives it from `Banded` and
`ViewSound`, so a protocol proves nothing new — what a mechanism owes
is the witness that its cut stands in the `Truncates` relation.
-/

namespace LeanDag

namespace Properties

namespace Arcs

variable {Validator : Type} [Fintype Validator] [DecidableEq Validator]
variable {BlockId : Type} [DecidableEq BlockId] {Payload : Type}
variable {R : DagRule Validator BlockId Payload}
variable {S S' : Slots Validator} {U U' : R.Universe} {G d : ℕ}
variable {V : R.View U} {V' : R.View U'}

/-- **A verdict survives the cut**, at the replica's own numbering. -/
theorem decided_of_truncate (h : LocalTruncate R) (ht : Truncates R U U' S S' G d)
    (hv : ViewAgreeAbove R V V' G) {k : ℕ} {v : Option BlockId}
    (hd : R.Decided S V (d + k) v) : R.Decided S' V' k v :=
  (h S S' U U' G d ht V V' hv k v).mp hd

/-- **And a verdict of the truncation is a verdict of the whole DAG**,
which is what lets a pruned replica be compared with one that never
pruned. -/
theorem decided_of_truncated (h : LocalTruncate R) (ht : Truncates R U U' S S' G d)
    (hv : ViewAgreeAbove R V V' G) {k : ℕ} {v : Option BlockId}
    (hd : R.Decided S' V' k v) : R.Decided S V (d + k) v :=
  (h S S' U U' G d ht V V' hv k v).mpr hd

/-! ## The agreement half

A deployment needs more than `decided_of_truncate`: a validator that
joined from the truncation holds an arbitrary view of it and must still
agree with a full-history one. `Agree` and `LocalTruncate` compose to
give this for any rule with both, with nothing proved per protocol. -/

/-- **Cross-cut agreement.** A validator holding any view of the
truncation agrees, slot for slot, with a full-history validator. -/
theorem decided_agree_truncate (ha : Agree R) (hlt : LocalTruncate R)
    (ht : Truncates R U U' S S' G d) (hv : ViewAgreeAbove R V V' G)
    {W : R.View U'} {k : ℕ} {w v : Option BlockId}
    (hW : R.Decided S' W k w) (hV : R.Decided S V (d + k) v) : w = v :=
  ha S' W V' k w v hW ((hlt S S' U U' G d ht V V' hv k v).mp hV)

/-- **And across two horizons.** Validators cut at different depths
agree on every shared slot, matched through the absolute slot index.
Horizons need never be negotiated. -/
theorem decided_agree_horizons (ha : Agree R) (hlt : LocalTruncate R)
    {U₁ U₂ : R.Universe} {S₁ S₂ : Slots Validator} {G₁ d₁ G₂ d₂ : ℕ}
    (ht₁ : Truncates R U U₁ S S₁ G₁ d₁) (ht₂ : Truncates R U U₂ S S₂ G₂ d₂)
    {V₁ : R.View U₁} {V₂ : R.View U₂}
    (hv₁ : ViewAgreeAbove R V V₁ G₁) (hv₂ : ViewAgreeAbove R V V₂ G₂)
    {W₁ : R.View U₁} {W₂ : R.View U₂} {k₁ k₂ : ℕ}
    (halign : d₁ + k₁ = d₂ + k₂) {w₁ w₂ v : Option BlockId}
    (hW₁ : R.Decided S₁ W₁ k₁ w₁) (hW₂ : R.Decided S₂ W₂ k₂ w₂)
    (hV : R.Decided S V (d₁ + k₁) v) : w₁ = w₂ :=
  (decided_agree_truncate ha hlt ht₁ hv₁ hW₁ hV).trans
    (decided_agree_truncate ha hlt ht₂ hv₂ hW₂ (halign ▸ hV)).symm






end Arcs

end Properties

end LeanDag
