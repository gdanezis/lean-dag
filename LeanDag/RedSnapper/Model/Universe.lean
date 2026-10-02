import LeanDag.RedSnapper.Model.Block

/-!
# The block universe

Trusted core: every block that exists across the whole execution —
authored by anyone, Byzantine or correct. Later phases carve
per-validator views out of this universe; the safety theorems quantify
over it.

Here "exists" means **accepted by the DAG-building layer**, not merely
emitted: a validator stores a block only after its entire causal history
has been validated, and every rule operates on stored blocks alone.
Malformed Byzantine emissions — dangling parent ids, wrong rounds,
duplicate authors — are filtered before entering any DAG, which is why
`complete` and `valid` below hold for Byzantine-authored blocks too. The
Byzantine power that survives the filter, and that the model does
represent, is equivocation, the adversarial choice of parents and
transactions, withholding, and a stance map that follows no rule. The
filtering itself is assumed from Mysticeti, not formalised.

Two properties of correct validators are stated **here**, at the
universe level, rather than on any individual local DAG. Non-equivocation:
per-DAG would be too weak, since two local DAGs could each hold at most
one block per correct author per round while holding *different* such
blocks — which is exactly that author equivocating. The self-parent
chain: a correct validator links its own previous block in every round,
which is what makes its blocks totally ordered by reachability and its
declarations a sequence (`docs/red-snapper.md`, Phase 3 choice 1). Both
are guarded by `Correct`; Byzantine validators are unconstrained, so a
Byzantine validator may skip rounds, equivocate, or reference either
twin of its own.

The self-parent chain is indispensable, not a convenience: it is what
puts a correct validator's earlier ACK inside every later block of its
own, so that a skip vote — `⊥` from a validator that never ACKed — can
be told from an unlock vote by reading the DAG, which the ack-versus-skip
exclusivity argument needs. With `predecessor` and `no_equivocation` it
entails that a correct validator with a block at round `r` has a block
at every round below `r`, each in the later one's history — the paper's
"honest validators propose in every round", stated once here
(`docs/red-snapper.md` §3, finding 17).
-/

namespace LeanDag

namespace RedSnapper

/-- Every block that exists, together with the well-formedness conditions
the DAG-building layer guarantees. -/
structure Universe (Validator BlockId Tx Obj : Type*) [Fintype Validator]
    [DecidableEq Validator] [F : Faults Validator] where
  /-- Which blocks exist. -/
  ids : Finset BlockId
  /-- What each id denotes. Total, with junk outside `ids`; every
  hypothesis below quantifies over `i ∈ ids`, so the junk is never
  observed. -/
  block : BlockId → Block Validator BlockId Tx Obj
  /-- Every referenced block is itself present. -/
  complete : ∀ i ∈ ids, ∀ j ∈ (block i).parents, j ∈ ids
  /-- Every block present is valid. -/
  valid : ∀ i ∈ ids, ValidWrt block (block i)
  /-- Correct validators do not equivocate: at most one block per correct
  author per round. Byzantine validators are unconstrained. -/
  no_equivocation : ∀ i ∈ ids, ∀ j ∈ ids,
    (block i).author ∈ (Correct : Finset Validator) →
    (block i).author = (block j).author →
    (block i).round = (block j).round → i = j
  /-- Correct validators chain their blocks: a correct block above
  genesis references a block by its own author — by `predecessor` at the
  previous round, by `no_equivocation` the unique one. -/
  self_parent : ∀ i ∈ ids,
    (block i).author ∈ (Correct : Finset Validator) →
    0 < (block i).round →
    ∃ j ∈ (block i).parents, (block j).author = (block i).author

end RedSnapper

end LeanDag
