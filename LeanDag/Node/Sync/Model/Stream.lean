import LeanDag.Common.Causality
import Mathlib.Data.Finset.Sort
/-!
# Sync by causal streams — one sync

`docs/sync.md` §2. A node syncs the history of a target block `t` from
the target's creator. It sends with each request its frontier: for each
author, the least round at which it holds no block of that author, and
`0` for the authors it has detected equivocating (`frontier`,
`frontierOf`). The creator, holding `R`, answers with the blocks of `R`
in `t`'s history whose rounds are at or above their author's frontier,
with `t` and the identifiers asked for by name, in order of round
(`streamed`, `stream`).

The requester takes each streamed block that is ready on arrival, its
references held and one round below it, and drops the rest (`Ready`,
`absorb`). A pass then records the authors of streamed blocks that have
a twin among the blocks it held (`exposes`), and the references of
streamed blocks that are still missing (`missing`), which the next pass
asks for by name (`pass`).

Blocks are named by identifier, and `blk` gives what each identifier
denotes: the hash is taken to be injective.

Definitions only.
-/

namespace LeanDag

namespace Node

namespace Sync

variable {Validator BlockId Payload : Type} [DecidableEq Validator] [LinearOrder BlockId]
variable (blk : BlockId → Block Validator BlockId Payload)

/-- **`S` holds a block of `a` at round `k`.** -/
def HoldsAt (S : Finset BlockId) (a : Validator) (k : ℕ) : Prop :=
  ∃ i ∈ S, (blk i).creator = a ∧ (blk i).round = k

instance (S : Finset BlockId) (a : Validator) (k : ℕ) : Decidable (HoldsAt blk S a k) :=
  inferInstanceAs (Decidable (∃ i ∈ S, _))

/-- **The least round from `k` up at which `S` holds no block of `a`**,
searched over `fuel` rounds. -/
def gapFrom (S : Finset BlockId) (a : Validator) : ℕ → ℕ → ℕ
  | 0, k => k
  | fuel + 1, k => if HoldsAt blk S a k then gapFrom S a fuel (k + 1) else k

/-- **The frontier of `S` for `a`**: the least round at which `S` holds no
block of `a`. -/
def frontier (S : Finset BlockId) (a : Validator) : ℕ :=
  gapFrom blk S a (S.card + 1) 0

/-- **The frontier a request carries**: `0` for the detected authors
`D`. -/
def frontierOf (S : Finset BlockId) (D : Finset Validator) (a : Validator) : ℕ :=
  if a ∈ D then 0 else frontier blk S a

/-- **Twins**: two distinct blocks of one author at one round. -/
def Twins (i j : BlockId) : Prop :=
  i ≠ j ∧ (blk i).creator = (blk j).creator ∧ (blk i).round = (blk j).round

instance (i j : BlockId) : Decidable (Twins blk i j) := inferInstanceAs (Decidable (_ ∧ _))

open Classical in
/-- **What a responder holding `R` streams** for the target `t`, to a
requester with frontier `fr` asking for `X` by name: the blocks of `R` in
`t`'s history that are `t`, asked for, or at or above their author's
frontier. -/
noncomputable def streamed (R : Finset BlockId) (t : BlockId) (fr : Validator → ℕ)
    (X : Finset BlockId) : Finset BlockId :=
  R.filter fun i => ReachesFrom blk t i ∧ (i = t ∨ i ∈ X ∨ fr (blk i).creator ≤ (blk i).round)

/-- **The stream**: the streamed blocks in order of round. -/
noncomputable def stream (R : Finset BlockId) (t : BlockId) (fr : Validator → ℕ)
    (X : Finset BlockId) : List BlockId :=
  ((streamed blk R t fr X).sort (· ≤ ·)).mergeSort fun i j => decide ((blk i).round ≤ (blk j).round)

/-- **A block is ready on `S`**: its references are in `S`, one round
below it. -/
def Ready (S : Finset BlockId) (i : BlockId) : Prop :=
  (blk i).refs ⊆ S ∧ ∀ j ∈ (blk i).refs, (blk j).round + 1 = (blk i).round

instance (S : Finset BlockId) (i : BlockId) : Decidable (Ready blk S i) :=
  inferInstanceAs (Decidable (_ ∧ _))

/-- **Take a stream in**: each block ready on arrival is accepted, and the
others are dropped. -/
def absorb : Finset BlockId → List BlockId → Finset BlockId
  | S, [] => S
  | S, i :: L => absorb (if Ready blk S i then insert i S else S) L

/-- **The authors a stream exposes against `S`**: the authors of streamed
blocks outside `S` with a twin in `S`. -/
def exposes (S : Finset BlockId) (L : List BlockId) : Finset Validator :=
  ((L.filter fun i => decide (i ∉ S ∧ ∃ j ∈ S, Twins blk i j)).map
    fun i => (blk i).creator).toFinset

/-- **The references still missing after a stream**: those of streamed
blocks outside `S`. -/
def missing (S : Finset BlockId) (L : List BlockId) : Finset BlockId :=
  (L.toFinset.biUnion fun i => (blk i).refs).filter (· ∉ S)

variable (Validator BlockId) in
/-- **A sync at the requester**: the blocks it holds, the authors it has
detected, and the identifiers it asks for by name. -/
structure Pass where
  /-- The blocks the requester holds. -/
  held : Finset BlockId
  /-- The authors it has detected equivocating. -/
  detected : Finset Validator
  /-- The identifiers it asks for by name. -/
  asked : Finset BlockId

/-- **One pass** of a sync of `t` from a responder holding `R`: request,
take the stream in, record the exposed authors and the missing
references. -/
noncomputable def pass (R : Finset BlockId) (t : BlockId) (s : Pass Validator BlockId) :
    Pass Validator BlockId :=
  let L := stream blk R t (frontierOf blk s.held s.detected) s.asked
  let S := absorb blk s.held L
  ⟨S, s.detected ∪ exposes blk s.held L, s.asked ∪ missing blk S L⟩

/-- **The equivocators of `R` against `S`**: the authors of blocks of `R`
with a twin in `R` or `S`. -/
def equivocators (R S : Finset BlockId) : Finset Validator :=
  ((R ×ˢ (R ∪ S)).filter fun p => Twins blk p.1 p.2).image fun p => (blk p.1).creator

end Sync

end Node

end LeanDag
