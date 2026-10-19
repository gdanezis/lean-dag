import LeanDag.Node.Runs.Statement
/-!
# Safe Skip — statement

`docs/validator.md` §3.5, V6. A node back from a restart that finds its
store's top two rounds or more above its own top fills the rounds in
between with blocks of its own, each the references of another author's
line plus its own block of the round below, persists them, and sends one
jump message naming its last block and the other author's; a receiver
derives the filled blocks from its own store. Under authenticated jumps
and the hash:

* **every block an honest node derived from a jump message in an honest
  node's name is one of that node's own** (`Derives`): where both stores
  hold a block above the sender's last block they read it alike, so the
  receiver derives the blocks the sender made.

The node's own blocks, the filled ones among them, lie one a round
(`Local.OneEach`), and the self-referencing filled block is valid at the
row's validity at any quorum (`BlockRecord.selfBlock_valid`, L0).

Statements only; the proofs are `Proof.lean`.
-/

namespace LeanDag

namespace Node

namespace Jump

/-- **A derived block is the sender's own**: every block an honest node
derived from a jump message in an honest node's name is one of that
node's own. -/
def Derives : Prop :=
  ∀ (Validator BlockId Payload : Type) [Fintype Validator] [DecidableEq Validator]
    [LinearOrder BlockId] (cfg : Config Validator BlockId Payload) (H : Finset Validator)
    (ins : Validator → List (Input Validator BlockId Payload)),
    Runs.AuthenticJumps cfg H ins → Runs.HashInjective cfg H ins →
    ∀ v ∈ H, ∀ x ∈ derived (cfg.at v) (State.init (cfg.at v)) (ins v), x.2.creator ∈ H →
      x ∈ persists (runOf cfg ins x.2.creator).2

/-- Safe Skip. -/
def Statement : Prop := Derives

end Jump

end Node

end LeanDag
