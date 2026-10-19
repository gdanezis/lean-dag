import LeanDag.Node.Converge.Statement
import LeanDag.Node.Vote
/-!
# Many honest nodes — statement

`docs/validator.md` §4, V3. Over a trace of honest nodes `H` and an
adversary, assume:

* **timely authentication** (`Converge.TimelyAuthentic`): a block
  delivered or offered to an honest node with an honest author's
  identity and its hash was broadcast by that author earlier;
* **the hash** (`Converge.HashInjective`): no two different blocks the
  honest nodes knew have one identifier;
* no honest node is given a base offer (`Converge.NoRejoin`).

Then, at the bounded vote, with an admissible row and at most `f` nodes
outside `H`, **any two honest nodes' decisions are prefix-comparable**
(`Safety`), whatever horizons they raise and whenever they restart and
resume. A node that bootstraps skips the slots below its new horizon;
two honest nodes then still decide each slot alike
(`Node/Boot/Statement.lean`).

Statements only; the proofs are `Proof.lean`.
-/

namespace LeanDag

namespace Node

namespace Runs

/-- **Run safety**: any two honest nodes' decisions are prefix-comparable. -/
def Safety : Prop :=
  ∀ (Validator BlockId Payload : Type) [Fintype Validator] [DecidableEq Validator]
    [LinearOrder BlockId] (cfg : Config Validator BlockId Payload) (H : Finset Validator)
    (tr : Trace Validator BlockId Payload),
    cfg.σ = boundedSel → cfg.Admissible → Hᶜ.card ≤ cfg.f →
    Converge.TimelyAuthentic cfg H tr → Converge.HashInjective cfg H tr →
    Converge.NoRejoin H tr →
    ∀ v ∈ H, ∀ w ∈ H, decisionsOf cfg tr v <+: decisionsOf cfg tr w ∨
      decisionsOf cfg tr w <+: decisionsOf cfg tr v

/-- Many honest nodes. -/
def Statement : Prop := Safety

end Runs

end Node

end LeanDag
