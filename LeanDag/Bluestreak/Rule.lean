import LeanDag.Common.Rules
import LeanDag.Common.Anchored
/-!
# Bluestreak: the sparse DAG and its commit rule

**A commit rule** (`Rules`), at the core's committee `n ≥ 3f+1` and
quorum `n − f`. A non-leader block references its author's previous
block and, optionally, the previous round's leader block; the round's
leader block references a quorum. In place of the certificate the core
reads at `r+2` — a block carrying `n − f` votes — a block *claims* the
leader certified, by a field naming it, or, for a leader block, by the
votes it carries. The claim's justification lies outside the claiming
block's causal history, so an honest validator builds only on
*referenceable* blocks, those whose every inherited claim it can prove
from its own view; `Disciplined` is the trace of that discipline on the
record, and `Certified` is what a committed anchor is known to be. Both
clauses of `Disciplined` read the record alone, which is what lets the
arc meet the properties of `Properties/`.
-/

namespace LeanDag

namespace Bluestreak

/-- The certificate-claim field: the block a non-leader block claims
certified, if any. Fixed once per development, as the schedule is. -/
class ClaimMap (BlockId : Type*) where
  claim : BlockId → Option BlockId

export ClaimMap (claim)

variable {Validator : Type*} [Fintype Validator] [DecidableEq Validator] [F : Faults Validator]
variable {BlockId : Type*} [DecidableEq BlockId] {Payload : Type*}

/-! ## The universe -/

/-- Bluestreak's validity: references one round below with distinct
creators, and a self-parent. No quorum, since a non-leader block carries
at most two references; what safety asks of a leader block's quorum is
`Disciplined.certified_quorate`. -/
abbrev ValidWrt : Validity Validator BlockId Payload :=
  ValidAt 0 (Clause.distinct.and Clause.selfParent)

instance : Validity.Distinct (ValidWrt (Validator := Validator) (BlockId := BlockId)
    (Payload := Payload)) :=
  Validity.Distinct.of_validAt (fun _ _ => Iff.rfl) fun _ _ h => h.1

/-- The block record at Bluestreak's validity, non-equivocation asked of
the correct validators. -/
abbrev Universe (Validator BlockId Payload : Type*) [Fintype Validator] [DecidableEq Validator]
    [DecidableEq BlockId] [Faults Validator] :=
  BlockRecord Validator BlockId Payload ValidWrt (Correct : Finset Validator)

variable {U : Universe Validator BlockId Payload}

/-! ## Certification and claims -/

/-- `L` is certified: `n − f` validators reference it one round above. -/
def Certified (U : Universe Validator BlockId Payload) (L : BlockId) : Prop :=
  quorumCard Validator ≤ (supporters U L ((U.block L).round + 1)).card

instance (L : BlockId) : Decidable (Certified U L) := inferInstanceAs (Decidable (_ ≤ _))

/-- `L` is quorate: a non-genesis `L` references `n − f` distinct
creators. What a receiver checks of a leader block, read at one block
rather than at a slot. -/
def Quorate (U : Universe Validator BlockId Payload) (L : BlockId) : Prop :=
  0 < (U.block L).round → quorumCard Validator ≤ (creators U.block (U.block L)).card

instance (L : BlockId) : Decidable (Quorate U L) := inferInstanceAs (Decidable (_ → _ ≤ _))

/-- `B` claims `L` certified: by its claim field, or by carrying `n − f`
votes for `L` among its references. -/
def Claims [ClaimMap BlockId] (U : Universe Validator BlockId Payload) (B L : BlockId) : Prop :=
  claim B = some L ∨ CarriesVotes U (IsVote U) (quorumCard Validator) B L

instance [ClaimMap BlockId] (B L : BlockId) : Decidable (Claims U B L) :=
  inferInstanceAs (Decidable (_ ∨ _))

/-- The blocks two rounds above `L` that claim it certified. -/
def claimers [ClaimMap BlockId] (U : Universe Validator BlockId Payload) (L : BlockId) :
    Finset BlockId :=
  (blocksAt U ((U.block L).round + 2)).filter fun B => Claims U B L

/-! ## The direct rules, judged from a view -/

/-- Direct commit: the view holds claims for `L` from `n − f` validators. -/
abbrev DirectCommitIn [ClaimMap BlockId] (U : Universe Validator BlockId Payload) (V : U.View)
    (L : BlockId) : Prop :=
  HoldsAtLeast U V (quorumCard Validator) (claimers U L)

/-- Direct skip: the view holds `n − f` voting-round blocks, and for every
candidate of the slot `n − f` of them omit it. -/
abbrev DirectSkipIn [S : Slots Validator] (U : Universe Validator BlockId Payload) (V : U.View)
    (k : ℕ) : Prop :=
  HoldsAtLeast U V (quorumCard Validator) (blocksAt U (S.slotRound k + 1)) ∧
    ∀ L ∈ leaderBlocksAt U k,
      HoldsAtLeast U V (quorumCard Validator) (omissionsOf U L (S.slotRound k + 1))

/-- `A`'s cone carries only backed claims: what an honest validator
checks before building on `A`, and what a certified block satisfies. -/
def Backed [ClaimMap BlockId] (U : Universe Validator BlockId Payload) (A : BlockId) : Prop :=
  ∀ X, Reaches U A X → ∀ L, claim X = some L → Certified U L

/-- The indirect link: a claim for `L` lies in the anchor's causal history. -/
abbrev ClaimedIn [ClaimMap BlockId] (U : Universe Validator BlockId Payload) (A L : BlockId) :
    Prop :=
  LinkedVia U A (claimers U L)

/-! ## The discipline -/

/-- **What a Bluestreak universe owes beyond its record**: a certified
block is quorate — what the receivers' format check on leader blocks
leaves of itself where safety reads it — and every claim an honest
block inherits, for a candidate the universe holds, is certified: the
honest validators build on referenceable blocks only. Both clauses read
the record alone, so a universe is disciplined or not with no schedule
in sight. -/
structure Disciplined [ClaimMap BlockId] (U : Universe Validator BlockId Payload) : Prop where
  certified_quorate : ∀ A ∈ U.ids, Certified U A → Quorate U A
  honest_backed : ∀ B ∈ U.ids, (U.block B).creator ∈ (Correct : Finset Validator) →
    ∀ X, Reaches U B X → ∀ L, claim X = some L → Certified U L

/-! ## The relation -/

/-- **Bluestreak as an anchored rule**: wave two, commit by claims, skip by
per-candidate omission, one rung — a claim in the anchor's cone — with no
tie, and an anchor a certified block whose cone carries only backed
claims. -/
def bluestreakAnchored (Validator BlockId Payload : Type*) [Fintype Validator]
    [DecidableEq Validator] [DecidableEq BlockId] [Faults Validator] [ClaimMap BlockId] :
    AnchoredRule Validator BlockId Payload ValidWrt (Correct : Finset Validator) where
  waveAt := fun _ => 2
  Commit := fun U V L _ _ => DirectCommitIn U V L
  decCommit := fun _ _ _ _ _ => inferInstance
  Skip := fun U V S k => DirectSkipIn (S := S) U V k
  rungs := 1
  Link := fun _ U A L _ _ => ClaimedIn U A L
  tie := fun _ _ _ => False
  Anchor := fun U A => Certified U A ∧ Backed U A

variable [ClaimMap BlockId]

@[simp] theorem bluestreakAnchored_waveAt (κ : ℕ) :
    (bluestreakAnchored Validator BlockId Payload).waveAt κ = 2 := rfl
@[simp] theorem bluestreakAnchored_rungs :
    (bluestreakAnchored Validator BlockId Payload).rungs = 1 := rfl

instance {V : U.View} (L : BlockId) (r κ : ℕ) :
    Decidable ((bluestreakAnchored Validator BlockId Payload).Commit U V L r κ) :=
  inferInstanceAs (Decidable (DirectCommitIn U V L))

instance {V : U.View} (S : Slots Validator) (k : ℕ) :
    Decidable ((bluestreakAnchored Validator BlockId Payload).Skip U V S k) :=
  inferInstanceAs (Decidable (DirectSkipIn (S := S) U V k))

/-- **The decision relation**: the anchored relation at Bluestreak's data. -/
abbrev Decided [S : Slots Validator] (U : Universe Validator BlockId Payload) (V : U.View) :
    ℕ → Option BlockId → Prop :=
  (bluestreakAnchored Validator BlockId Payload).Decided (S := S) U V

namespace Decided
export AnchoredRule.Decided (directCommit directSkip indirectCommit indirectSkip)
end Decided

end Bluestreak

end LeanDag
