import LeanDag.Common.Support
import LeanDag.Common.Ledger
import LeanDag.Common.Anchored
import LeanDag.Common.Slots
import LeanDag.Common.History
import LeanDag.Mysticeti.Model.Validity
/-!
# Mysticeti — the commit rule, as definitions

Trusted core of the arc: definitions only. A block is certified by a
round-`(r+1)` block carrying `n − f` votes for it; the direct rules
count certificates and blames at the round above; `coreAnchored` is the
rule those two make, at wave two with a single rung and no tie-break,
and `Decided` is the relation it generates. The universe these read is
`Mysticeti/Model/Validity.lean`.

Everything proved *about* them is `Mysticeti/Rule.lean`.
-/

namespace LeanDag

variable {Validator : Type*} [Fintype Validator] [DecidableEq Validator]
variable [F : Faults Validator]
variable {BlockId : Type*} [DecidableEq BlockId] {Payload : Type*}
variable {U : BlockUniverse Validator BlockId Payload}
variable [S : Slots Validator]

/-- The references of `C` that vote for `L`: the record's carried votes,
in the plain sense. -/
abbrev votesIn (U : BlockUniverse Validator BlockId Payload) (C L : BlockId) : Finset BlockId :=
  carriedVotes U (IsVote U) C L

/-- A round-`(r+2)` block certifies `L` when its votes for `L` come from a
quorum of distinct validators: the record's certificate at `n − f`. -/
abbrev Certifies (U : BlockUniverse Validator BlockId Payload) (C L : BlockId) : Prop :=
  CarriesVotes U (IsVote U) (quorumCard Validator) C L

/-- The certificates for a round-`r` block `L`: the round-`(r+2)` blocks that
certify it. -/
abbrev certificates (U : BlockUniverse Validator BlockId Payload) (L : BlockId) (r : ℕ) :
    Finset BlockId :=
  certificatesAt U (IsVote U) (quorumCard Validator) L (r + 2)

/-- `L` is directly committed when its certificates come from a quorum of
distinct validators. -/
def DirectCommit (U : BlockUniverse Validator BlockId Payload) (L : BlockId) (r : ℕ) : Prop :=
  quorumCard Validator ≤ (creatorsOf U.block (certificates U L r)).card

/-- `L` is directly skipped when a quorum of distinct validators declined to
vote for it. -/
def DirectSkip (U : BlockUniverse Validator BlockId Payload) (L : BlockId) (r : ℕ) : Prop :=
  quorumCard Validator ≤ (blames U L (r + 1)).card

instance decidableDirectCommit (L : BlockId) (r : ℕ) : Decidable (DirectCommit U L r) :=
  inferInstanceAs (Decidable (quorumCard Validator ≤ (creatorsOf U.block (certificates U L r)).card))

instance decidableDirectSkip (L : BlockId) (r : ℕ) : Decidable (DirectSkip U L r) :=
  inferInstanceAs (Decidable (quorumCard Validator ≤ (blames U L (r + 1)).card))

/-- The indirect rule's test: a certificate for `L` lies in the causal
history of the anchor `A`. -/
abbrev CertifiedIn (U : BlockUniverse Validator BlockId Payload) (A L : BlockId) (r : ℕ) : Prop :=
  certifiedLink IsVote (quorumCard Validator) 2 U A L r

/-- Direct commit, as judged from a single view: the view holds
certificates for `L` from a quorum of distinct validators. -/
abbrev DirectCommitIn (U : BlockUniverse Validator BlockId Payload)
    (V : View Validator BlockId Payload U) (L : BlockId) (r : ℕ) : Prop :=
  certCommit IsVote (quorumCard Validator) (quorumCard Validator) 2 U V L r

/-- Direct skip, as judged from a single view: the view holds blocks at
the round above `L` that omit it, from a quorum of distinct validators. -/
abbrev DirectSkipIn (U : BlockUniverse Validator BlockId Payload)
    (V : View Validator BlockId Payload U) (L : BlockId) (r : ℕ) : Prop :=
  HoldsAtLeast U V (quorumCard Validator) (omissionsOf U L (r + 1))

/-- **The slot is directly skipped, as judged from a view**: a quorum of
distinct validators holds a voting-round block, in view, that
references no candidate of the slot. Strictly stronger than the
per-candidate `DirectSkipIn`, which it implies. -/
abbrev DirectSkipSlotIn (U : BlockUniverse Validator BlockId Payload)
    (V : View Validator BlockId Payload U) (k : ℕ) : Prop :=
  blameSkip (quorumCard Validator) U V k

/-- **The core as an anchored rule.** -/
def coreAnchored (Validator BlockId Payload : Type*) [Fintype Validator]
    [DecidableEq Validator] [Faults Validator] [DecidableEq BlockId] :
    AnchoredRule Validator BlockId Payload ValidWrt Correct where
  wave := 2
  Commit := fun U V L r => DirectCommitIn U V L r
  decCommit := fun _ _ _ _ => inferInstance
  Skip := fun U V S k => DirectSkipSlotIn (S := S) U V k
  rungs := 1
  Link := fun _ U A L S k => CertifiedIn U A L (S.slotRound k)
  tie := fun _ _ _ => False

instance {V : View Validator BlockId Payload U} (L : BlockId) (r : ℕ) :
    Decidable ((coreAnchored Validator BlockId Payload).Commit U V L r) :=
  inferInstanceAs (Decidable (DirectCommitIn U V L r))

instance {V : View Validator BlockId Payload U} (k : ℕ) :
    Decidable ((coreAnchored Validator BlockId Payload).Skip U V S k) :=
  inferInstanceAs (Decidable (DirectSkipSlotIn (S := S) U V k))

/-- **The decision relation**: the anchored relation at the core's data. -/
abbrev Decided (U : BlockUniverse Validator BlockId Payload) (V : View Validator BlockId Payload U) :
    ℕ → Option BlockId → Prop :=
  (coreAnchored Validator BlockId Payload).Decided (S := S) U V

namespace Decided
export AnchoredRule.Decided (directCommit directSkip indirectCommit indirectSkip)
end Decided

end LeanDag
