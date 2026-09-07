import LeanDag.Common.Support
import LeanDag.Common.Leader
import LeanDag.Common.History

/-!
# The shapes of a commit rule

Every direct rule of this development is a threshold on a set the view
holds, and every rung a certificate, or a count of support, in the
anchor's cone. A rule is these shapes at its own thresholds
(`Common/Anchored.lean`); what a rule has beyond them is its own.
-/

namespace LeanDag

variable {Validator : Type*} [Fintype Validator] [DecidableEq Validator]
variable {BlockId : Type*} [DecidableEq BlockId] {Payload : Type*}
variable {P : Validity Validator BlockId Payload} {honest : Finset Validator}

/-- **Commit by support**: the view holds `t` authors voting for the
candidate one round above it. -/
abbrev supportCommit (t : ℕ) (U : BlockRecord Validator BlockId Payload P honest) (V : U.View)
    (L : BlockId) (r : ℕ) : Prop :=
  HoldsAtLeast U V t (votesFor U L (r + 1))

/-- **Commit by certificate**: the view holds `t` authors of certificates
for the candidate — the blocks `off` rounds above it carrying `t'` votes
for it under the vote relation `Vote`. -/
abbrev certCommit
    (Vote : (U : BlockRecord Validator BlockId Payload P honest) → BlockId → BlockId → Prop)
    [∀ U b L, Decidable (Vote U b L)]
    (t t' off : ℕ) (U : BlockRecord Validator BlockId Payload P honest) (V : U.View)
    (L : BlockId) (r : ℕ) : Prop :=
  HoldsAtLeast U V t (certificatesAt U (Vote U) t' L (r + off))

/-- **Skip by blame**: the view holds `t` authors whose voting-round block
references no candidate of the slot. -/
abbrev blameSkip [S : Slots Validator] (t : ℕ) (U : BlockRecord Validator BlockId Payload P honest)
    (V : U.View) (k : ℕ) : Prop :=
  HoldsAtLeast U V t (slotBlamers U k)

/-- **Link by certificate**: a certificate for the candidate lies in the
anchor's cone. -/
abbrev certifiedLink
    (Vote : (U : BlockRecord Validator BlockId Payload P honest) → BlockId → BlockId → Prop)
    [∀ U b L, Decidable (Vote U b L)]
    (t' off : ℕ) (U : BlockRecord Validator BlockId Payload P honest) (A L : BlockId) (r : ℕ) :
    Prop :=
  LinkedVia U A (certificatesAt U (Vote U) t' L (r + off))

/-- **Link by support in the cone**: `t` authors of votes for the candidate
lie in the anchor's cone. -/
abbrev coneLink (t : ℕ) (U : BlockRecord Validator BlockId Payload P honest)
    (A L : BlockId) (r : ℕ) : Prop :=
  t ≤ (coneSupporters U A L (r + 1)).card

omit [Fintype Validator] in
/-- Blame reads the schedule only at its own slot. -/
theorem blameSkip_congr {S₁ S₂ : Slots Validator} {t : ℕ}
    {U : BlockRecord Validator BlockId Payload P honest} {V : U.View} {k : ℕ}
    (hround : S₁.slotRound k = S₂.slotRound k) (hk : S₁.leader k = S₂.leader k)
    (h : blameSkip (S := S₁) t U V k) : blameSkip (S := S₂) t U V k := by
  show HoldsAtLeast U V _ (slotBlamers (S := S₂) U k)
  rwa [← slotBlamers_congr hround hk]

end LeanDag
