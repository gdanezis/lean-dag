import LeanDag.Node.Model.Run
import LeanDag.Node.Vote
/-!
# Many honest nodes — statement

`docs/validator.md` §4, V3. Honest nodes `H` run one configuration but
for their identity, each over its own sequence of inputs, which the
network and the adversary choose. Three assumptions constrain them:

* **authentication** (`Authentic`): a block delivered to an honest node
  with an honest author's identity is one of that author's own;
* **authenticated jumps** (`AuthenticJumps`): a jump message delivered
  to an honest node in an honest node's name is one that node sent;
* **the hash** (`HashInjective`): no two different blocks the honest
  nodes knew have one identifier.

Then, at the bounded vote, with an admissible row and at most `f` nodes
outside `H`, **any two honest nodes' decisions are prefix-comparable**
(`Safety`), whatever horizons they raise and whenever they jump.

Statements only; the proofs are `Proof.lean`.
-/

namespace LeanDag

namespace Node

namespace Runs

variable {Validator BlockId Payload : Type} [Fintype Validator] [DecidableEq Validator]
variable [LinearOrder BlockId]

/-- **Authentication**: a block delivered to an honest node with an honest
author's identity is one of that author's own. -/
def Authentic (cfg : Config Validator BlockId Payload) (H : Finset Validator)
    (ins : Validator → List (Input Validator BlockId Payload)) : Prop :=
  ∀ v ∈ H, ∀ x ∈ delivered (cfg.at v) (ins v), x.2.creator ∈ H →
    x ∈ persists (runOf cfg ins x.2.creator).2

/-- **Authenticated jumps**: a jump message delivered to an honest node in
an honest node's name is one that node sent. -/
def AuthenticJumps (cfg : Config Validator BlockId Payload) (H : Finset Validator)
    (ins : Validator → List (Input Validator BlockId Payload)) : Prop :=
  ∀ v ∈ H, ∀ v1 B1 v2 B2, Input.jump v1 B1 v2 B2 ∈ ins v → v1 ∈ H →
    Output.jump v1 B1 v2 B2 ∈ (runOf cfg ins v1).2

/-- **The hash** is injective on the blocks the honest nodes knew. -/
def HashInjective (cfg : Config Validator BlockId Payload) (H : Finset Validator)
    (ins : Validator → List (Input Validator BlockId Payload)) : Prop :=
  ∀ v ∈ H, ∀ w ∈ H, ∀ x ∈ knownOf cfg ins v, ∀ y ∈ knownOf cfg ins w,
    cfg.idOf x.2 = cfg.idOf y.2 → x.2 = y.2

/-- **Run safety**: any two honest nodes' decisions are prefix-comparable. -/
def Safety : Prop :=
  ∀ (Validator BlockId Payload : Type) [Fintype Validator] [DecidableEq Validator]
    [LinearOrder BlockId] (cfg : Config Validator BlockId Payload) (H : Finset Validator)
    (ins : Validator → List (Input Validator BlockId Payload)),
    cfg.σ = boundedSel → cfg.Admissible → Hᶜ.card ≤ cfg.f →
    Authentic cfg H ins → AuthenticJumps cfg H ins → HashInjective cfg H ins →
    ∀ v ∈ H, ∀ w ∈ H,
      commitsOf (runOf cfg ins v).2 <+: commitsOf (runOf cfg ins w).2 ∨
        commitsOf (runOf cfg ins w).2 <+: commitsOf (runOf cfg ins v).2

/-- Many honest nodes. -/
def Statement : Prop := Safety

end Runs

end Node

end LeanDag
