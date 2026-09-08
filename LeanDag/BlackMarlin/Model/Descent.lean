import LeanDag.BlackMarlin.Model.Ledger
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.Finset.Max

/-!
# Black Marlin — `maxAnchor`, and the record the descent generates

Algorithm 1, L18–L25 (`black-marlin.md` §11). `commit(B)` sets
`𝒜 ← strong(B) \ 𝒟` and recurses on the highest-round anchor of `𝒜`,
choosing among ties by the metric of L24. `Model/Ledger.lean` takes the
record that descent leaves as given; this file computes it.

The choice is **block-intrinsic**: L24's metric reads only the candidate
and its own cone, so every validator evaluates it identically and the
descent from a block is a function of that block alone — what lets the
record's agreement be derived rather than carried as a hypothesis
(`Ledger/Statement.lean`'s BMD3). **`𝒟` is dropped**: it only removes
what an earlier descent already visited, so a validator's flushed
anchors over all its commits are one chain read from its highest commit
down, and the record below is that chain. **Ties break at the
`≤`-least survivor** under a `LinearOrder` on identifiers, as Odontoceti
and Mahi-Mahi read their own canonical choices; nothing below depends on
which rule it is. **Fuel, not well-founded recursion**: a step drops the
round strictly, so `round B` steps exhaust the descent, and the fuelled
form needs no termination argument, as `historyUpto` uses for the causal
walk.

**Trusted core of the arc: definitions only.**
-/

namespace LeanDag

namespace BlackMarlin

variable {Validator : Type*} [Fintype Validator] [DecidableEq Validator]
variable [F : Faults Validator] [Rot : Rotation Validator]
variable {BlockId : Type*} [LinearOrder BlockId] {Payload : Type*}
variable {U : BlockUniverse Validator BlockId Payload}

/-- A block that anchors its own round. The round-free reading of
`IsAnchor`, which is what a set of blocks of mixed rounds needs. -/
def IsAnchorBlock (U : BlockUniverse Validator BlockId Payload) (X : BlockId) : Prop :=
  (U.block X).creator = Rot.anchor (U.block X).round

instance (X : BlockId) : Decidable (IsAnchorBlock U X) :=
  inferInstanceAs (Decidable (_ = _))

/-- The anchors among a set of blocks. -/
def anchorsOf (U : BlockUniverse Validator BlockId Payload) (s : Finset BlockId) :
    Finset BlockId :=
  s.filter (IsAnchorBlock U)

/-- **`strong(B)`**: the blocks strictly below `B` in its cone.
`history` is reflexive where the paper's `strong` is not, so the block
itself is removed. -/
def strongOf (U : BlockUniverse Validator BlockId Payload) (B : BlockId) : Finset BlockId :=
  (history U B).erase B

/-- The highest round at which a set holds an anchor, and `0` when it
holds none — which is the case L20's guard does not exclude and L21–L24
need. -/
def maxAnchorRound (U : BlockUniverse Validator BlockId Payload) (s : Finset BlockId) : ℕ :=
  (anchorsOf U s).sup (fun X => (U.block X).round)

/-- **`maxAnchor(s)`**: the anchors of `s` at the highest round they
reach. A set, as L21 reads it. -/
def maxAnchor (U : BlockUniverse Validator BlockId Payload) (s : Finset BlockId) :
    Finset BlockId :=
  (anchorsOf U s).filter (fun X => (U.block X).round = maxAnchorRound U s)

/-- **The metric of L24**: how far a candidate's round stands above the
highest anchor of its own cone. Truncated subtraction is exact here —
an anchor below `A` sits below `A`'s round — so no absolute value is
needed. -/
def anchorGap (U : BlockUniverse Validator BlockId Payload) (A : BlockId) : ℕ :=
  (U.block A).round - maxAnchorRound U (strongOf U A)

/-- The `≤`-least member of a set, as an `Option`. -/
def pick (s : Finset BlockId) : Option BlockId :=
  if h : s.Nonempty then some (s.min' h) else none

/-- **The descent's choice** (L21–L24): the `≤`-least of the highest-round
anchors below `B` that minimise the metric. At `|maxAnchor| = 1` this is
L22, and otherwise L24. -/
def descend (U : BlockUniverse Validator BlockId Payload) (B : BlockId) : Option BlockId :=
  pick ((maxAnchor U (strongOf U B)).filter
    (fun A => ∀ C ∈ maxAnchor U (strongOf U B), anchorGap U A ≤ anchorGap U C))

/-- The descent from `B`, read at a round, with fuel. -/
def descentUpto (U : BlockUniverse Validator BlockId Payload) :
    ℕ → BlockId → ℕ → Option BlockId
  | 0, B, ρ => if (U.block B).round = ρ then some B else none
  | (n + 1), B, ρ =>
      if (U.block B).round = ρ then some B
      else (descend U B).bind (fun A => descentUpto U n A ρ)

/-- **The flush record of `commit(B)`**: the anchor its descent visits at
each round. A step drops the round strictly, so `round B` steps are
enough and the fuel is not a parameter of the result. -/
def flushRecord (U : BlockUniverse Validator BlockId Payload) (B : BlockId) (ρ : ℕ) :
    Option BlockId :=
  descentUpto U ((U.block B).round) B ρ

end BlackMarlin

end LeanDag
