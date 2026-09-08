import LeanDag.BlackMarlin.Model.Decision
import LeanDag.Common.Ledger
/-!
# Black Marlin — the flush record

`commit(B)` descends through the undelivered anchors of `strong(B)`,
flushing one segment per anchor round from the lowest up (Algorithm 1,
L18–L32), so a validator's output is segmented by anchor round whether
or not it applied the rule there itself (`black-marlin.md` §11). That
segmentation is what makes two validators' orders agree: one that
committed at rounds `3` and `5` and one that committed only at `7` flush
the same segments, since the second one's descent visits `5`, `4` and
`3` on the way down. A validator's record is modelled here rather than
the recursion that builds it, as the core models `Decided` rather than
the implementation deciding it.

**The descent steps by one round, and that pins it.** The candidates at
round `ρ` below a round-`(ρ+1)` block are that block's references, and
`distinct_creators` allows one block per author, so a consecutive step
needs no tie-break. The paper's L21–L24 supplies one for the case where
the descent skips an anchor round; that rule is block-intrinsic — its
minimised quantity depends on the candidate and its own cone alone — but
is not modelled here, which would mean modelling `maxAnchor` and the
sort `τ`. `step` and `dense` are what the descent guarantees where it
does not skip; §11 records what is left over.

**Trusted core of the arc: definitions only.**
-/

namespace LeanDag

namespace BlackMarlin

variable {Validator : Type*} [Fintype Validator] [DecidableEq Validator]
variable [F : Faults Validator] [Rot : Rotation Validator]
variable {BlockId : Type*} [DecidableEq BlockId] {Payload : Type*}
variable {U : BlockUniverse Validator BlockId Payload}

/-- The anchors of round `ρ` in `A`'s causal history — the candidates the
descent chooses among when it arrives at that round. -/
def coneAnchors (U : BlockUniverse Validator BlockId Payload)
    (A : BlockId) (ρ : ℕ) : Finset BlockId :=
  (blocksAt U ρ).filter (fun X => (U.block X).creator = Rot.anchor ρ ∧ X ∈ history U A)

/-- **A flush record**: the anchor block a validator flushed at each
round. `step` is the descent's own shape — the anchor at `ρ` is a
reference of the anchor at `ρ + 1` — and `dense` says it does not pass
over a round its reference set contains; neither says anything about a
round the descent skips. -/
structure Flush (U : BlockUniverse Validator BlockId Payload) where
  /-- The anchor flushed at each round, where the descent flushed one. -/
  block : ℕ → Option BlockId
  /-- What is flushed at a round is that round's anchor. -/
  isAnchor : ∀ ρ L, block ρ = some L → IsAnchor U ρ L
  /-- **The descent steps by one round.** -/
  step : ∀ ρ L M, block ρ = some L → block (ρ + 1) = some M → L ∈ (U.block M).refs
  /-- **And does not pass over an anchor it references.** -/
  dense : ∀ ρ M, block (ρ + 1) = some M → (coneAnchors U M ρ).Nonempty →
    (block ρ).isSome

/-! **What a record outputs** is the record's ledger (`Ledger.lean`) at
the flush's blocks: `ledgerSet` holds everything in the causal history
of an anchor flushed below `n`, and `OutputAt` gives a block's segment
position, the first flushed anchor whose history holds it. Ordering
*within* a segment, the sort `τ`, is not modelled, so the ledger is a
set and the record's rounds are its positions. -/

end BlackMarlin

end LeanDag
