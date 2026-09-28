import LeanDag.RedSnapper.Model.Faults

/-!
# Stances, transactions, blocks, and block validity

Trusted core: the block schema of the paper's Preliminaries and §7
("Block schema"), the transaction data the predicates read, and block
validity. Definitions only — every lemma about them lives in `Helpers/`.

A block is its round, its author, the ids of the blocks it references,
the transactions it carries, and its *stance map*: for each object
version, optionally a declaration — an ACK for a transaction or `⊥`.
Blocks reference other blocks by `BlockId`, never by value, so `Block` is
non-recursive; an id is resolved through a total lookup
`blk : BlockId → Block`, and validity is a predicate on `(blk, b)`.
Acyclicity is a consequence of the predecessor condition, not a
structural constraint.

Transactions are opaque: a transaction has one owned input
(`docs/red-snapper.md`, D2), a history-independent validity (the
paper's `Valid`: signatures, authorisation, syntax), and a tag saying
whether it also touches shared state (D9). Object versions are opaque
too (D3): `Obj` is the type of versions, with no successor structure.

**Fidelity gaps** (stated once, here): parents point only to the
immediately preceding round, so the paper's `RoundParents(b)` is
`b.parents` — the model has no weak links; and a transaction has exactly
one owned input, so the paper's `OwnedInputs(tx)` is `{input tx}`. The
first removes a Byzantine capability the paper allows: a block cannot
shape its causal history by referencing an old block directly, so every
reachability fact is a chain through consecutive rounds. The safety
results are stated for this adversary.
-/

namespace LeanDag

namespace RedSnapper

/-- A declared stance on an object version: an ACK for a transaction, or
`⊥` — support for no transaction. The paper's third value `none` (no
declaration) is `Option.none` where a stance is read. -/
inductive Stance (Tx : Type*) where
  /-- An ACK: the author supports `tx` for this object version. -/
  | ack (tx : Tx)
  /-- `⊥`: the author supports no transaction for this object version. -/
  | bot
  deriving DecidableEq

/-- The transaction data every predicate reads. The object type is
determined by the transaction type (`outParam`): a transaction says what
it spends. -/
class Transactions (Tx : Type*) (Obj : outParam Type*) where
  /-- The one owned input of a transaction: the object version it
  spends. -/
  input : Tx → Obj
  /-- History-independent validity — signatures, authorisation, syntax.
  Only valid transactions become candidates. -/
  Valid : Tx → Prop
  /-- Whether the transaction also accesses shared state, and so must be
  ordered by consensus before it finalises. -/
  Mixed : Tx → Prop
  /-- Validity is decidable. -/
  [decValid : DecidablePred Valid]
  /-- The tag is decidable. -/
  [decMixed : DecidablePred Mixed]

attribute [reducible] Transactions.decValid Transactions.decMixed
attribute [instance] Transactions.decValid Transactions.decMixed

section Transactions

variable {Tx Obj : Type*} [T : Transactions Tx Obj]

/-- Two transactions conflict when they are distinct and spend the same
object version — the paper's `IsConflict`. -/
def Conflict (tx tx' : Tx) : Prop :=
  tx ≠ tx' ∧ T.input tx = T.input tx'

/-- An owned-object transaction: one that touches no shared state — the
paper's `IsOwned`. -/
def Owned (tx : Tx) : Prop :=
  ¬ T.Mixed tx

end Transactions

/-- A block: its round, its author, the ids of the blocks it references
from the preceding round, the transactions it carries, and its stance
map. `BlockId` is the block's identity — two blocks by the same author
in the same round (equivocation) are two distinct ids. -/
structure Block (Validator BlockId Tx Obj : Type*) where
  /-- The round this block was produced in. -/
  round : ℕ
  /-- The validator that authored the block. -/
  author : Validator
  /-- Ids of the blocks this one references, all from the preceding
  round. -/
  parents : Finset BlockId
  /-- The transactions this block carries. Carrying a transaction
  disseminates it; it is not an endorsement. -/
  txs : Finset Tx
  /-- The stance map: for each object version, the declaration this
  block makes, if any. `none` is no declaration — the author's earlier
  declaration, if any, stays in effect. -/
  declares : Obj → Option (Stance Tx)
  /-- The freeze markers of the `5f+1` recovery (§8's `b.freeze`): for
  each object version, the trigger anchor this block freezes on, if
  any. Defaults to none everywhere — the `3f+1` protocol never reads
  the field, and only `Model/Five/Freeze.lean` consumes it. -/
  freezes : Obj → Option BlockId := fun _ => none

section Authors

variable {Validator BlockId Tx Obj : Type*} [DecidableEq Validator]

/-- The validators that authored a set of ids, resolved through `blk`.
Defined on an arbitrary `Finset BlockId`, not just on a block's parents:
later counting hypotheses quantify over id-sets that are nobody's
parents. -/
def authorsOf (blk : BlockId → Block Validator BlockId Tx Obj) (s : Finset BlockId) :
    Finset Validator :=
  s.image fun i => (blk i).author

/-- The validators behind a block's parents. -/
def authors (blk : BlockId → Block Validator BlockId Tx Obj)
    (b : Block Validator BlockId Tx Obj) : Finset Validator :=
  authorsOf blk b.parents

end Authors

section Validity

variable {Validator BlockId Tx Obj : Type*} [Fintype Validator] [DecidableEq Validator]
  [F : Faults Validator]

/-- Block validity, relative to a lookup function — every block
references a quorum of distinct valid blocks from the previous round.

The predecessor condition is additive (`+ 1 =`, never `− 1`): this
avoids natural-number subtraction, and it makes the genesis case
derivable rather than assumed — at round `0` the equation
`(blk i).round + 1 = 0` is unsatisfiable, so `parents = ∅` follows.
Only the quorum condition needs a round guard.

The quorum counts **authors**, not `parents.card`: the protocol means
`quorum` distinct *validators'* blocks, and the author-set form is what
every counting argument consumes (with `distinct_authors` the two
coincide). -/
structure ValidWrt (blk : BlockId → Block Validator BlockId Tx Obj)
    (b : Block Validator BlockId Tx Obj) : Prop where
  /-- Every parent sits in the immediately preceding round. -/
  predecessor : ∀ i ∈ b.parents, (blk i).round + 1 = b.round
  /-- A block never references the same author twice. -/
  distinct_authors : ∀ i ∈ b.parents, ∀ j ∈ b.parents,
    (blk i).author = (blk j).author → i = j
  /-- Non-genesis blocks reference a quorum of distinct authors. -/
  quorum : 0 < b.round → quorum Validator ≤ (authors blk b).card

end Validity

end RedSnapper

end LeanDag
