import LeanDag.Mysticeti.Rule
import LeanDag.Common.History
/-!
# Mahi-Mahi — the rule at wave `w`

Mysticeti's commit rule stretched to a wave of `w` rounds: a candidate
proposed at round `r` is voted on at round `r + w − 2` and decided at
round `r + w − 1`, and a vote is counted through the **causal cone** of
the voting block rather than among its direct references. At `w = 3`
the two readings coincide and the definitions below are the core's
(`mahi-mahi.md` §1); at `w ≥ 4` the cone is what lets a candidate be
reached through intermediate rounds, which is the mechanism of the
common-core argument (`mahi-mahi.md` §4).

**Trusted core of the arc: definitions only.** No theorem lives in this
file or in `Decision.lean`; the `Decidable` instances are definitions
by `inferInstanceAs` and carry no proof content. Results are stated in
`<Result>/Statement.lean` files and proved in their `Proof.lean`
(`mahi-mahi.md` §9).

**Canonical support.** A voting block's cone may hold two twins of a
Byzantine leader, reached by different paths, so "the block `q`
supports at `(a, r)`" must be a choice. The reference implementation
chooses by depth-first order over the block's stored references; this
development's references carry no order, so the choice is the
`≤`-least block at `(a, r)` in the cone under a `[LinearOrder BlockId]`
— hash order, in a deployment. Safety consumes only that the choice is
unique per block; which block a shared rule picks is immaterial
(`mahi-mahi.md` §2).

**Wave length.** `w` is an explicit argument, not a class, so that the
`w = 3` conservativity statement can mention both sides. The rounds use
truncated subtraction, which is harmless: every result assumes `3 ≤ w`,
and at the literal `w = 3` the rounds are definitionally `r + 1` and
`r + 2`. Wave length two — where the vote is the certificate — is the
Odontoceti and Nemo arcs' territory and is not covered here.
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

/-- The blocks of author `a` at round `r` in the cone of `q` — the set the
vote is chosen from. A correct author has at most one; an equivocator may
have several, which is what the minimality clause of `Votes` arbitrates.
Stated with `blocksAt` outermost so that membership unfolds through
`mem_blocksAt`, as the Odontoceti arc's `coneSupports` does. -/
def candidatesAt (U : BlockUniverse Validator BlockId Payload)
    (q : BlockId) (a : Validator) (r : ℕ) : Finset BlockId :=
  (blocksAt U r).filter (fun b => (U.block b).creator = a ∧ b ∈ history U q)

/-- **`q` votes for `L`**: `L` is the least block of its own author and
round in `q`'s cone. The minimality clause is the canonical-support
choice (`mahi-mahi.md` §2), written `¬ L' < L` rather than `L ≤ L'` so
that agreement closes by `le_antisymm` on two `not_lt`s, the form the
Odontoceti arc's canonicity premise takes. `L`'s author and round are
read off `L` itself, so the rules keep the proposal round `r` as a
separate parameter exactly as the core does. -/
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
