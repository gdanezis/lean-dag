import LeanDag.Mysticeti.Model.Rule
import LeanDag.Nemo.Decision
import LeanDag.MahiMahi.Model.Decision
/-!
# Three rules the scheme's rows name and this development did not have

`docs/scheme.md` §4. The scheme writes a rule with no direct skip as a
skip threshold of `n`:

* **Cordial Miners PS** is Mysticeti's rule with that threshold. On the
  core's universe every block references its author's previous block, so
  `n` blames cannot occur and the rule is the core's with no direct skip,
  `cordialAnchored`.
* **Cordial Miners Async** is, for the same reason, Mahi-Mahi's rule at
  wave five with no direct skip, `cordialAsyncAnchored`.
* **Nemo-Nemo**, at that threshold, skips directly when every validator's
  vote-round block references no candidate. Nemo's universe has no
  self-parent clause, so this can happen; the rule is Nemo's with that
  skip, `nemoBlameAnchored`, whose anchors are blocks of the record.

Definitions only; the laws and the readings are `Helpers/Variants.lean`
and `Helpers/Buffered.lean`.
-/

namespace LeanDag

namespace Scheme

/-- **Cordial Miners PS**: the core's rule with no direct skip. -/
def cordialAnchored (Validator BlockId Payload : Type) [Fintype Validator]
    [DecidableEq Validator] [Faults Validator] [DecidableEq BlockId] :
    AnchoredRule Validator BlockId Payload ValidWrt Correct :=
  { coreAnchored Validator BlockId Payload with Skip := fun _ _ _ _ => False }

/-- **Cordial Miners Async**: Mahi-Mahi's rule at wave `w` with no direct
skip. -/
def cordialAsyncAnchored (Validator BlockId Payload : Type) [Fintype Validator]
    [DecidableEq Validator] [Faults Validator] [LinearOrder BlockId] (w : ℕ) :
    AnchoredRule Validator BlockId Payload ValidWrt Correct :=
  { MahiMahi.mahiMahiAnchored Validator BlockId Payload w with Skip := fun _ _ _ _ => False }

/-- **The scheme's Nemo-Nemo**: Nemo's rule, skipping a slot directly when
every validator's vote-round block references no candidate of it. -/
def nemoBlameAnchored (Validator BlockId Payload : Type) [Fintype Validator]
    [DecidableEq Validator] [DecidableEq BlockId] :
    AnchoredRule Validator BlockId Payload Nemo.ValidWrt Finset.univ :=
  { Nemo.nemoAnchored Validator BlockId Payload with
    Skip := fun U V _ k => HoldsAtLeast U V (Fintype.card Validator) (slotBlamers U k)
    Anchor := fun U A => A ∈ U.ids }

end Scheme

end LeanDag
