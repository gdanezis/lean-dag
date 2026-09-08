import LeanDag.MahiMahi.Model.Rules
import LeanDag.Common.Anchored
import LeanDag.Common.History
/-!
# Mahi-Mahi — the decision relation at wave `w`

The slot-indexed layer: eligibility, the view-relative direct rules, the
indirect test, and `Decided` — the core's Stages B and C with the wave
length substituted, apart from one departure at `Decided.directSkip`.
Definitions only; unlike the Odontoceti arc there is no canonicity
clause, since two certificates at one slot already name the same
candidate (MM1b).
-/

namespace LeanDag

namespace MahiMahi

variable {Validator : Type} [Fintype Validator] [DecidableEq Validator]
variable [F : Faults Validator]
variable {BlockId : Type} [LinearOrder BlockId] {Payload : Type}
variable {U : BlockUniverse Validator BlockId Payload}

/-! ## View-relative direct rules

A validator applies the direct rules to what it holds. Stated on a
`View` by intersecting with `V.ids`, so that a view can only
under-report the universe-level rule. -/

/-- Direct commit, as judged from a single view: the view holds
certificates for `L` from a quorum of distinct validators. -/
abbrev DirectCommitIn (U : BlockUniverse Validator BlockId Payload)
    (V : View Validator BlockId Payload U) (w : ℕ) (L : BlockId) (r : ℕ) : Prop :=
  HoldsAtLeast U V (quorumCard Validator) (certificates U w L r)

/-- Direct skip, as judged from a single view: the view holds
voting-round blocks blaming the slot `(a, r)` from a quorum of distinct
validators. -/
abbrev DirectSkipIn (U : BlockUniverse Validator BlockId Payload)
    (V : View Validator BlockId Payload U) (w : ℕ) (a : Validator) (r : ℕ) : Prop :=
  HoldsAtLeast U V (quorumCard Validator)
    ((blocksAt U (votingRound w r)).filter (fun q => Blames U q a r))

/-- **The indirect test**: a certificate for `L` lies in the causal
history of the anchor `A`. The core's `CertifiedIn` at wave `w`. Not
decidable as stated — `Reaches` is a `Prop` — and not made so: the
witnesses exhibit the certificate. -/
abbrev CertifiedIn (U : BlockUniverse Validator BlockId Payload)
    (w : ℕ) (A L : BlockId) (r : ℕ) : Prop :=
  LinkedVia U A (certificates U w L r)

/-! ## The relation -/

/-- **Mahi-Mahi as an anchored rule** at wave `w`: certificate-quorum
direct commit, slot-level direct skip, and one rung of link (a
certificate in the anchor's cone), with no tie needed since two
certificates at one slot already name the same candidate (MM1b). The
one departure from the core: skip is judged on the slot as a whole,
not per candidate. -/
def mahiMahiAnchored (Validator BlockId Payload : Type) [Fintype Validator]
    [DecidableEq Validator] [Faults Validator] [LinearOrder BlockId] (w : ℕ) :
    AnchoredRule Validator BlockId Payload ValidWrt Correct where
  wave := w - 1
  Commit := fun U V L r => MahiMahi.DirectCommitIn U V w L r
  decCommit := fun _ _ _ _ => inferInstance
  Skip := fun U V S k => MahiMahi.DirectSkipIn U V w (S.leader k) (S.slotRound k)
  rungs := 1
  Link := fun _ U A L S k => MahiMahi.CertifiedIn U w A L (S.slotRound k)
  tie := fun _ _ _ => False

section Slots

variable [S : Slots Validator]

/-- **The decision relation at wave `w`**: the anchored relation at
Mahi-Mahi's data. `Decided w U V k (some L)`: a validator holding `V`
may commit `L` at `k`; `Decided w U V k none`: it may skip the slot;
*undecided* is the absence of any derivation. -/
abbrev Decided (w : ℕ) (U : BlockUniverse Validator BlockId Payload)
    (V : View Validator BlockId Payload U) : ℕ → Option BlockId → Prop :=
  (mahiMahiAnchored Validator BlockId Payload w).Decided (S := S) U V

namespace Decided
export AnchoredRule.Decided (directCommit directSkip indirectCommit indirectSkip)
end Decided

instance {V : View Validator BlockId Payload U} (w : ℕ) (L : BlockId) (r : ℕ) :
    Decidable ((mahiMahiAnchored Validator BlockId Payload w).Commit U V L r) :=
  inferInstanceAs (Decidable (MahiMahi.DirectCommitIn U V w L r))

instance {V : View Validator BlockId Payload U} (w k : ℕ) :
    Decidable ((mahiMahiAnchored Validator BlockId Payload w).Skip U V S k) :=
  inferInstanceAs (Decidable (MahiMahi.DirectSkipIn U V w (S.leader k) (S.slotRound k)))

end Slots

end MahiMahi

end LeanDag
