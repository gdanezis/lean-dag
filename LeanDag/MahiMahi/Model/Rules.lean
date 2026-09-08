import LeanDag.Mysticeti.Rule
import LeanDag.Common.History
/-!
# Mahi-Mahi — the rule at wave `w`

**A commit rule** (`Protocols`), asynchronous, at wave `w`, on the
core's universes and validity. The rule is `mahiMahiAnchored`; the
carrier and properties are `Properties.lean`; the record witness is
`Record.lean`.

Mysticeti's commit rule stretched to a wave of `w` rounds, with votes
counted through a voting block's causal cone rather than its direct
references; at `w = 3` this coincides with the core (`mahi-mahi.md` §1).
Definitions only — results live in `<Result>/Statement.lean` and
`Proof.lean`. Canonical support, which block in a cone a vote picks, is
chosen by a `[LinearOrder BlockId]` since references carry no order;
only the choice's uniqueness matters for safety.
-/

namespace LeanDag

namespace MahiMahi

variable {Validator : Type*} [Fintype Validator] [DecidableEq Validator]
variable [F : Faults Validator]
variable {BlockId : Type*} [LinearOrder BlockId] {Payload : Type*}
variable {U : BlockUniverse Validator BlockId Payload}

/-! ## The rounds of a wave -/

/-- The round at which a candidate proposed at `r` is voted on. The last
round before the decision round, as `Wave::voting_round` computes it for
every `w ≥ 3`. -/
def votingRound (w r : ℕ) : ℕ := r + w - 2

/-- The round at which a candidate proposed at `r` is decided: its
certificates live here (`Wave::decision_round`). Named with the suffix
because `decisionRound`, on slots, is the name the core's schedule layer
uses. -/
def decisionRoundAt (w r : ℕ) : ℕ := r + w - 1

/-! ## Support through the cone -/

/-- The blocks of author `a` at round `r` in `q`'s cone — the set a vote
is chosen from. A correct author has at most one; an equivocator may
have several, arbitrated by `Votes`'s minimality clause. -/
def candidatesAt (U : BlockUniverse Validator BlockId Payload)
    (q : BlockId) (a : Validator) (r : ℕ) : Finset BlockId :=
  (blocksAt U r).filter (fun b => (U.block b).creator = a ∧ b ∈ history U q)

/-- **`q` votes for `L`**: `L` is the least block of its own author and
round in `q`'s cone, the canonical-support choice (`mahi-mahi.md` §2).
Stated as `¬ L' < L` rather than `L ≤ L'` so agreement closes by
`le_antisymm` on two `not_lt`s. -/
def Votes (U : BlockUniverse Validator BlockId Payload) (q L : BlockId) : Prop :=
  L ∈ candidatesAt U q (U.block L).creator (U.block L).round ∧
    ∀ L' ∈ candidatesAt U q (U.block L).creator (U.block L).round, ¬ L' < L

/-- **`q` blames the slot `(a, r)`**: no block of that author and round
lies in its cone. On the slot rather than on a block, as the
implementation's `enough_leader_blame` has it — a blame is the absence
of any supported block, not a vote against a particular twin. -/
def Blames (U : BlockUniverse Validator BlockId Payload)
    (q : BlockId) (a : Validator) (r : ℕ) : Prop :=
  candidatesAt U q a r = ∅

/-- `Votes` is a conjunction of a membership and a bounded quantification
over a `Finset`, so it is decidable; Lean needs telling. -/
instance (q L : BlockId) : Decidable (Votes U q L) :=
  inferInstanceAs (Decidable (_ ∧ _))

/-- `Blames` is an equation between `Finset`s. -/
instance (q : BlockId) (a : Validator) (r : ℕ) : Decidable (Blames U q a r) :=
  inferInstanceAs (Decidable (_ = _))

/-! ## Certificates and the direct rules -/

/-- The references of `C` that vote for `L`. Counted among the
*references* of the decision-round block, as `is_certificate` counts
them, and not through `C`'s whole cone. -/
abbrev votesIn (U : BlockUniverse Validator BlockId Payload) (C L : BlockId) : Finset BlockId :=
  carriedVotes U (Votes U) C L

/-- A decision-round block certifies `L` when its votes for `L` come from
a quorum of distinct validators: the record's certificate at `n − f`,
with Mahi-Mahi's vote. -/
abbrev Certifies (U : BlockUniverse Validator BlockId Payload) (C L : BlockId) : Prop :=
  CarriesVotes U (Votes U) (quorumCard Validator) C L

/-- The certificates for a candidate `L` proposed at `r`: the blocks of
the decision round `r + w − 1` that certify it. -/
abbrev certificates (U : BlockUniverse Validator BlockId Payload)
    (w : ℕ) (L : BlockId) (r : ℕ) : Finset BlockId :=
  certificatesAt U (Votes U) (quorumCard Validator) L (decisionRoundAt w r)

/-- **Direct commit**: a quorum of distinct validators certify `L`. -/
def DirectCommit (U : BlockUniverse Validator BlockId Payload)
    (w : ℕ) (L : BlockId) (r : ℕ) : Prop :=
  quorumCard Validator ≤ (creatorsOf U.block (certificates U w L r)).card

/-- The validators whose voting-round block blames the slot `(a, r)`. -/
def blamers (U : BlockUniverse Validator BlockId Payload)
    (w : ℕ) (a : Validator) (r : ℕ) : Finset Validator :=
  creatorsOf U.block ((blocksAt U (votingRound w r)).filter (fun q => Blames U q a r))

/-- **Direct skip**: a quorum of distinct validators blame the slot. On
the slot `(a, r)`, not on a candidate: at `w = 3` this is the core's
`DirectSkip` quantified over every candidate of the slot, which is how
the core's `directSkip` constructor consumes it. -/
def DirectSkip (U : BlockUniverse Validator BlockId Payload)
    (w : ℕ) (a : Validator) (r : ℕ) : Prop :=
  quorumCard Validator ≤ (blamers U w a r).card

instance (w : ℕ) (L : BlockId) (r : ℕ) : Decidable (DirectCommit U w L r) :=
  inferInstanceAs (Decidable (_ ≤ _))

instance (w : ℕ) (a : Validator) (r : ℕ) : Decidable (DirectSkip U w a r) :=
  inferInstanceAs (Decidable (_ ≤ _))

end MahiMahi

end LeanDag
