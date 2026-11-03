import LeanDag.Node.Converge.Statement
import LeanDag.Node.Live.Statement
import LeanDag.Node.Model.Step
/-!
# The blocks a node orders — statement

`docs/dos-bounds.md` §5, Phase 3.1. Over a trace with timely authentication
and an injective hash, of nodes that do not drop (`cfg.drops = false`), at
the bounded vote of an admissible configuration with at most `f` nodes
outside the honest set `H`, before any events:

* **two honest nodes order the same blocks** after any number of slots both
  have decided (`Agrees`);
* **an honest node holds what it ordered** (`Held`).

Statements only; the proofs are `Proof.lean`.
-/

namespace LeanDag

namespace Node

namespace Order

/-- **Two honest nodes order the same blocks** after `n` slots, when both
have decided them. -/
def Agrees : Prop :=
  ∀ (Validator BlockId Payload : Type) [Fintype Validator] [DecidableEq Validator]
    [LinearOrder BlockId] (cfg : Config Validator BlockId Payload) (H : Finset Validator)
    (tr : Trace Validator BlockId Payload) (v w : Validator) (i j n : ℕ),
    cfg.σ = boundedSel → cfg.Admissible → Hᶜ.card ≤ cfg.f →
    Converge.TimelyAuthentic cfg H tr → Converge.HashInjective cfg H tr → cfg.drops = false →
    v ∈ H → w ∈ H →
    n ≤ (stateBefore cfg tr i v).lo → n ≤ (stateBefore cfg tr j w).lo →
    (stateBefore cfg tr i v).ordered (S := cfg.slots) cfg.q n =
      (stateBefore cfg tr j w).ordered (S := cfg.slots) cfg.q n

/-- **An honest node holds what it ordered.** -/
def Held : Prop :=
  ∀ (Validator BlockId Payload : Type) [Fintype Validator] [DecidableEq Validator]
    [LinearOrder BlockId] (cfg : Config Validator BlockId Payload) (H : Finset Validator)
    (tr : Trace Validator BlockId Payload) (v : Validator) (i n : ℕ),
    cfg.σ = boundedSel → cfg.Admissible → Hᶜ.card ≤ cfg.f →
    Converge.TimelyAuthentic cfg H tr → Converge.HashInjective cfg H tr → cfg.drops = false →
    v ∈ H → n ≤ (stateBefore cfg tr i v).lo →
    (stateBefore cfg tr i v).ordered (S := cfg.slots) cfg.q n ⊆
      (stateBefore cfg tr i v).disk.ids

/-- What a node orders. -/
def Statement : Prop := Agrees ∧ Held

end Order

end Node

end LeanDag
