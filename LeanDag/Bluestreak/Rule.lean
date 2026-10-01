import LeanDag.Common.Rules
import LeanDag.Common.Anchored
/-!
# Bluestreak: the sparse DAG and its commit rule

**A commit rule** (`Rules`), at the core's committee `n ≥ 3f+1` and
quorum `n − f`. A non-leader block references its author's previous
block and, optionally, the previous round's leader block; the round's
leader block references a quorum. A block's payload carries its role
and its claim (`Format`), and validity checks the format: a leader block
references a quorum, and an ordinary block references only its own
author's blocks and leader blocks. In place of the certificate the core
reads at `r+2` — a block carrying `n − f` votes — a block *claims* the
leader certified, by a field naming it, or, for a leader block, by the
votes it carries. The claim's justification lies outside the claiming
block's causal history, so an honest validator builds only on
*referenceable* blocks, those whose every inherited claim it can prove
from its own view; `Disciplined` is the trace of that discipline on the
record, and `Certified` is what a committed anchor is known to be.
`Disciplined` reads the record alone, which is what lets the arc meet
the properties of `Properties/`.
-/

namespace LeanDag

namespace Bluestreak

/-- **What a Bluestreak payload carries**: whether the block is a
leader block, and the block it claims certified, if any. -/
class Format (BlockId : Type*) (Payload : Type*) where
  leader : Payload → Bool
  claim : Payload → Option BlockId

/-- The bare payload: the role and the claim, and nothing else. -/
instance {BlockId : Type*} : Format BlockId (Bool × Option BlockId) := ⟨Prod.fst, Prod.snd⟩

variable {Validator : Type*} [Fintype Validator] [DecidableEq Validator] [F : Faults Validator]
variable {BlockId : Type*} [DecidableEq BlockId] {Payload : Type*} [Format BlockId Payload]

/-! ## The format -/

/-- **The block format**: a leader block references `n − f` distinct
creators, and an ordinary block references only blocks by its own
author and leader blocks. -/
def roleClause : Clause Validator BlockId Payload := fun blk b =>
  (Format.leader (BlockId := BlockId) b.payload = true → 0 < b.round →
    quorumCard Validator ≤ (creators blk b).card) ∧
  (Format.leader (BlockId := BlockId) b.payload = false → ∀ j ∈ b.refs,
    (blk j).creator = b.creator ∨ Format.leader (BlockId := BlockId) (blk j).payload = true)

instance (blk : BlockId → Block Validator BlockId Payload) (b : Block Validator BlockId Payload) :
    Decidable (roleClause blk b) :=
  inferInstanceAs (Decidable (_ ∧ _))

instance : Clause.Mechanised (roleClause (Validator := Validator) (BlockId := BlockId)
    (Payload := Payload)) where
  reads := fun blk blk' _ b _ hb hag h => by
    have hc : creators blk' b = creators blk b := by
      unfold creators creatorsOf
      exact Finset.image_congr fun j hj => by rw [hag j (hb j hj)]
    refine ⟨fun ht h0 => hc ▸ h.1 ht h0, fun hf j hj => ?_⟩
    rw [hag j (hb j hj)]
    exact h.2 hf j hj
  base := fun _ b h0 hr =>
    ⟨fun _ hp => absurd hp (by omega), fun _ j hj => by rw [hr] at hj; simp at hj⟩
  chops := fun blk G b h _ hG => by
    refine ⟨fun ht _ => ?_, fun hf j hj => ?_⟩
    · change quorumCard Validator ≤ (creatorsOf (chopBlk blk G) b.refs).card
      rw [creatorsOf_chopBlk]
      exact h.1 ht (by omega)
    · rw [chopBlk_creator, chopBlk_payload]
      exact h.2 hf j hj

/-! ## The universe -/

/-- Bluestreak's validity: references one round below with distinct
creators, a self-parent, and the format. No quorum outside the format,
since an ordinary block carries at most two references. -/
abbrev ValidWrt : Validity Validator BlockId Payload :=
  ValidAt 0 ((Clause.distinct.and Clause.selfParent).and roleClause)

instance : Validity.Distinct (ValidWrt (Validator := Validator) (BlockId := BlockId)
    (Payload := Payload)) :=
  Validity.Distinct.of_validAt (fun _ _ => Iff.rfl) fun _ _ h => h.1.1

/-- The block record at Bluestreak's validity, non-equivocation asked of
the correct validators. -/
abbrev Universe (Validator BlockId Payload : Type*) [Fintype Validator] [DecidableEq Validator]
    [DecidableEq BlockId] [Faults Validator] [Format BlockId Payload] :=
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

/-- `L` is tagged a leader block. -/
abbrev Tagged (U : Universe Validator BlockId Payload) (L : BlockId) : Prop :=
  Format.leader (BlockId := BlockId) (U.block L).payload = true

/-- The block `X` claims certified, read from its payload. -/
abbrev claimOf (U : Universe Validator BlockId Payload) (X : BlockId) : Option BlockId :=
  Format.claim (U.block X).payload

/-- **A tagged block is quorate**, by the format. -/
theorem quorate_of_tagged {L : BlockId} (hL : L ∈ U.ids) (ht : Tagged U L) : Quorate U L :=
  (U.valid L hL).clause.2.1 ht

/-- `B` claims `L` certified: by its claim field, or by carrying `n − f`
votes for `L` among its references. -/
def Claims (U : Universe Validator BlockId Payload) (B L : BlockId) : Prop :=
  claimOf U B = some L ∨ CarriesVotes U (IsVote U) (quorumCard Validator) B L

instance (B L : BlockId) : Decidable (Claims U B L) :=
  inferInstanceAs (Decidable (_ ∨ _))

/-- The blocks two rounds above `L` that claim it certified. -/
def claimers (U : Universe Validator BlockId Payload) (L : BlockId) :
    Finset BlockId :=
  (blocksAt U ((U.block L).round + 2)).filter fun B => Claims U B L

/-! ## The direct rules, judged from a view -/

/-- Direct commit: the view holds claims for `L` from `n − f` validators. -/
abbrev DirectCommitIn (U : Universe Validator BlockId Payload) (V : U.View)
    (L : BlockId) : Prop :=
  HoldsAtLeast U V (quorumCard Validator) (claimers U L)

/-- Direct skip: the view holds `n − f` voting-round blocks, and for every
candidate of the slot `n − f` of them omit it. -/
abbrev DirectSkipIn [S : Slots Validator] (U : Universe Validator BlockId Payload) (V : U.View)
    (k : ℕ) : Prop :=
  HoldsAtLeast U V (quorumCard Validator) (blocksAt U (S.slotRound k + 1)) ∧
    ∀ L ∈ leaderBlocksAt U k,
      HoldsAtLeast U V (quorumCard Validator) (omissionsOf U L (S.slotRound k + 1))

/-- `X`'s claim is backed: from round two up, it names a certified block
two rounds below. A claim at rounds `0` and `1` names a block below the
record and is read by no slot. -/
def BackedClaim (U : Universe Validator BlockId Payload) (X : BlockId) :
    Prop :=
  ∀ L, claimOf U X = some L → 2 ≤ (U.block X).round →
    (U.block L).round + 2 = (U.block X).round ∧ Certified U L

/-- `A`'s cone carries only backed claims: what an honest validator
checks before building on `A`, and what a certified block satisfies. -/
def Backed (U : Universe Validator BlockId Payload) (A : BlockId) : Prop :=
  ∀ X, Reaches U A X → BackedClaim U X

/-- The indirect link: a claim for `L` lies in the anchor's causal history. -/
abbrev ClaimedIn (U : Universe Validator BlockId Payload) (A L : BlockId) :
    Prop :=
  LinkedVia U A (claimers U L)

/-! ## The discipline -/

/-- **What a Bluestreak universe owes beyond its record**: every claim
an honest block inherits from round two up names a certified block two
rounds below — the honest validators build on referenceable blocks only.
It reads the record alone, so a universe is disciplined or not with no
schedule in sight. -/
structure Disciplined (U : Universe Validator BlockId Payload) : Prop where
  honest_backed : ∀ B ∈ U.ids, (U.block B).creator ∈ (Correct : Finset Validator) →
    ∀ X, Reaches U B X → BackedClaim U X

/-! ## The relation -/

/-- **Bluestreak as an anchored rule**: wave two, commit of a tagged
candidate by claims, skip by per-candidate omission, one rung — a claim
for a tagged candidate in the anchor's cone — with no tie, and an anchor
a tagged certified block whose cone carries only backed claims. -/
def bluestreakAnchored (Validator BlockId Payload : Type*) [Fintype Validator]
    [DecidableEq Validator] [DecidableEq BlockId] [Faults Validator] [Format BlockId Payload] :
    AnchoredRule Validator BlockId Payload ValidWrt (Correct : Finset Validator) where
  waveAt := fun _ => 2
  Commit := fun U V L _ _ => DirectCommitIn U V L ∧ Tagged U L
  decCommit := fun _ _ _ _ _ => inferInstance
  Skip := fun U V S k => DirectSkipIn (S := S) U V k
  rungs := 1
  Link := fun _ U A L _ _ => ClaimedIn U A L ∧ Tagged U L
  tie := fun _ _ _ => False
  Anchor := fun U A => Certified U A ∧ Backed U A ∧ Tagged U A

@[simp] theorem bluestreakAnchored_waveAt (κ : ℕ) :
    (bluestreakAnchored Validator BlockId Payload).waveAt κ = 2 := rfl
@[simp] theorem bluestreakAnchored_rungs :
    (bluestreakAnchored Validator BlockId Payload).rungs = 1 := rfl

instance {V : U.View} (L : BlockId) (r κ : ℕ) :
    Decidable ((bluestreakAnchored Validator BlockId Payload).Commit U V L r κ) :=
  inferInstanceAs (Decidable (DirectCommitIn U V L ∧ Tagged U L))

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
