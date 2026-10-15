import LeanDag.Common.Rules
import LeanDag.Common.Anchored
import LeanDag.Scheme.Model.Params
/-!
# The unified decider — its rule

`docs/scheme.md` §3: Algorithm 2 of the scheme as an anchored rule. A
slot proposed at round `r` is voted on at `r + voteOffset p` and decided
at `r + p.waveLength − 1`; the direct commit counts certifying blocks of
the decision round, the direct skip counts blames at the vote round, the
indirect rule counts certifying blocks in the anchor's history, and twins
are broken by the least identifier.

The scheme's `VotedBlock` walks a block's references in their stored
order. A block's references here form a set, so the vote is a
`VoteSel`: any rule that returns a block of the slot in the voter's
history when there is one and nothing otherwise.

Definitions only; the claims are `Scheme/Equiv/Statement.lean`.
-/

namespace LeanDag

namespace Scheme

variable {Validator : Type*} [Fintype Validator] [DecidableEq Validator]
variable {BlockId : Type*} [DecidableEq BlockId] {Payload : Type*}
variable {P : Validity Validator BlockId Payload} {honest : Finset Validator}

variable (Validator BlockId Payload P honest) in
/-- **A vote-selection rule** (the scheme's `VotedBlock`): the block of
author `a` at round `r` that the block `b` votes for, a block of that slot
in `b`'s history, and one exactly when the history holds one below `b`. -/
structure VoteSel where
  /-- The block of `(a, r)` that `b` votes for. -/
  sel : BlockRecord Validator BlockId Payload P honest → BlockId → Validator → ℕ →
    Option BlockId
  /-- A block votes for nothing at or above its own round. -/
  below : ∀ U b a r, (U.block b).round ≤ r → sel U b a r = none
  /-- A selected block is a block of the slot in the voter's history. -/
  sound : ∀ U b a r x, sel U b a r = some x →
    x ∈ history U b ∧ (U.block x).creator = a ∧ (U.block x).round = r
  /-- Nothing is selected only when the history holds no block of the slot. -/
  complete : ∀ U b a r, r < (U.block b).round → sel U b a r = none →
    ∀ x ∈ history U b, (U.block x).creator = a → (U.block x).round ≠ r

namespace VoteSel

variable (σ : VoteSel Validator BlockId Payload P honest)

/-- **`b` votes for `L`**: the block `b` selects for `L`'s slot is `L`. -/
def Votes (U : BlockRecord Validator BlockId Payload P honest) (b L : BlockId) : Prop :=
  σ.sel U b (U.block L).creator (U.block L).round = some L

instance (U : BlockRecord Validator BlockId Payload P honest) (b L : BlockId) :
    Decidable (σ.Votes U b L) :=
  inferInstanceAs (Decidable (_ = _))

end VoteSel

namespace Params

/-- The vote round's offset above the propose round: the decision round
when a vote is its certificate, otherwise the round below it, and at
least one. -/
def voteOffset (p : Params) : ℕ :=
  if p.voteIsCert then p.waveLength - 1 else max 1 (p.waveLength - 2)

end Params

variable (p : Params) (σ : VoteSel Validator BlockId Payload P honest)

/-- **`C` certifies `L`** (the scheme's `IsCert`): its vote, or votes for
`L` among its references from `certThreshold` distinct authors. -/
def IsCert (U : BlockRecord Validator BlockId Payload P honest) (C L : BlockId) : Prop :=
  if p.voteIsCert then σ.Votes U C L else CarriesVotes U (σ.Votes U) p.certThreshold C L

instance (U : BlockRecord Validator BlockId Payload P honest) (C L : BlockId) :
    Decidable (IsCert p σ U C L) := by
  unfold IsCert; split <;> infer_instance

/-- The decision-round blocks certifying the round-`r` candidate `L`. -/
def certsAt (U : BlockRecord Validator BlockId Payload P honest) (L : BlockId) (r : ℕ) :
    Finset BlockId :=
  (blocksAt U (r + (p.waveLength - 1))).filter (fun C => IsCert p σ U C L)

/-- The vote-round blocks that vote for no block of slot `k`: its blames. -/
def blamersAt [S : Slots Validator] (U : BlockRecord Validator BlockId Payload P honest)
    (k : ℕ) : Finset BlockId :=
  (blocksAt U (S.slotRound k + p.voteOffset)).filter
    (fun b => σ.sel U b (S.leader k) (S.slotRound k) = none)

variable [LinearOrder BlockId]

/-- **The decider as an anchored rule** (Algorithm 2): the supported-leader
test is the direct commit, the skipped-leader test the direct skip, the
certified-link test the single rung, and the least identifier breaks ties. -/
def schemeAnchored : AnchoredRule Validator BlockId Payload P honest where
  waveAt := fun _ => p.waveLength - 1
  Commit := fun U V L r _ => HoldsAtLeast U V p.commitThreshold (certsAt p σ U L r)
  decCommit := fun _ _ _ _ _ => inferInstance
  Skip := fun U V _ k => HoldsAtLeast U V p.skipThreshold (blamersAt p σ U k)
  rungs := 1
  Link := fun _ U A L S k =>
    p.linkSize ≤ (creatorsOf U.block ((certsAt p σ U L (S.slotRound k)).filter
      (fun C => C ∈ history U A))).card
  tie := fun _ L L' => L < L'

end Scheme

end LeanDag
