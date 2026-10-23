import LeanDag.Node.Sync.Model.Net
/-!
# Sync by causal streams — statements

`docs/sync.md` §4.

* **A sync completes** (`Completes`): from a responder whose blocks are
  closed under references, each one round below its referrer, a sync of
  a block it holds leaves the block held within `2e + 1` passes, for `e`
  the equivocators of the responder's blocks against the requester's. A
  pass whose stream leaves a block unready has met a twin of a block the
  requester held, and the pass after the next has detected its author.
  With no equivocator, one pass suffices.
* **Pending is bounded** (`PendingBounded`): under any inputs, a node's
  pending blocks are at most one for each other node it has not
  detected.
* **No amplification** (`NoAmplification`): over a trace in which honest
  nodes stream only what they hold, the blocks of authors outside the
  honest set `H` on an honest disk number at most the blocks that honest
  nodes received from nodes outside `H`.
* **The rate bound** (`RateBound`): if moreover an honest node receives
  at most `k` blocks at a time from each node outside `H`, then by time
  `t` those blocks number at most `|H| · |Hᶜ| · k · (t + 1)`.

Statements only; the proofs are `Proof.lean`.
-/

namespace LeanDag

namespace Node

namespace Sync

/-- **A sync completes** within `2e + 1` passes. -/
def Completes : Prop :=
  ∀ (Validator BlockId Payload : Type) [DecidableEq Validator] [LinearOrder BlockId]
    (blk : BlockId → Block Validator BlockId Payload) (R : Finset BlockId) (t : BlockId)
    (s : Pass Validator BlockId),
    CausalStructure blk R → t ∈ R →
    t ∈ ((pass blk R t)^[2 * (equivocators blk R s.held).card + 1] s).held

/-- **Pending is bounded**: one pending block for each other node not
detected. -/
def PendingBounded : Prop :=
  ∀ (Validator BlockId Payload : Type) [Fintype Validator] [DecidableEq Validator]
    [LinearOrder BlockId] (blk : BlockId → Block Validator BlockId Payload) (me : Validator)
    (ins : List (Input Validator BlockId)),
    (pending (run blk me State.init ins)).card ≤
      ((Finset.univ.erase me) \ (run blk me State.init ins).detected).card

/-- **No amplification**: the blocks of authors outside `H` on an honest
disk number at most those honest nodes received from outside `H`. -/
def NoAmplification : Prop :=
  ∀ (Validator BlockId Payload : Type) [Fintype Validator] [DecidableEq Validator]
    [LinearOrder BlockId] (blk : BlockId → Block Validator BlockId Payload)
    (H : Finset Validator) (tr : Trace Validator BlockId),
    Faithful blk H tr → ∀ v ∈ H, ∀ i,
      ((stateBefore blk tr i v).disk.filter fun x => (blk x).creator ∉ H).card ≤
        fromOutside H tr i

/-- **The rate bound**: by time `t`, at most `|H| · |Hᶜ| · k · (t + 1)`
blocks of authors outside `H` on an honest disk. -/
def RateBound : Prop :=
  ∀ (Validator BlockId Payload : Type) [Fintype Validator] [DecidableEq Validator]
    [LinearOrder BlockId] (blk : BlockId → Block Validator BlockId Payload)
    (H : Finset Validator) (tr : Trace Validator BlockId) (time : ℕ → ℕ) (k t : ℕ),
    Faithful blk H tr → RateBounded H tr time k → ∀ v ∈ H, ∀ i, (∀ j < i, time j ≤ t) →
      ((stateBefore blk tr i v).disk.filter fun x => (blk x).creator ∉ H).card ≤
        H.card * Hᶜ.card * k * (t + 1)

/-- **Sync by causal streams**: the four claims. -/
def Statement : Prop := Completes ∧ PendingBounded ∧ NoAmplification ∧ RateBound

end Sync

end Node

end LeanDag
