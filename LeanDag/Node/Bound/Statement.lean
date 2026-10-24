import LeanDag.Node.Converge.Statement
/-!
# The blocks a node holds a round — statement

`docs/validator.md` §4, V13. Over a trace with timely authentication and
an injective hash, let fewer than `q` nodes lie outside the honest set
`H`, and let every block of an honest author at round `m + 1` on honest
`v`'s disk expose every author `v` convicted. Then **`v`'s disk holds at
most `n + |D|` blocks of each round from `m + 1` on**, for `D` the authors
`v` convicted (`Bounded`): one of each author not convicted, and two of
each convicted.

Statements only; the proofs are `Proof.lean`.
-/

namespace LeanDag

namespace Node

namespace Bound

/-- **At most `n + |D|` blocks a round from the exposure on.** -/
def Bounded : Prop :=
  ∀ (Validator BlockId Payload : Type) [Fintype Validator] [DecidableEq Validator]
    [LinearOrder BlockId] (cfg : Config Validator BlockId Payload) (H : Finset Validator)
    (tr : Trace Validator BlockId Payload) (v : Validator) (i m k : ℕ),
    Converge.TimelyAuthentic cfg H tr → Converge.HashInjective cfg H tr → v ∈ H →
    Hᶜ.card < cfg.q →
    let s := stateBefore cfg tr i v
    (∀ c ∈ s.disk.ids, (s.disk.blk c).round = m + 1 → (s.disk.blk c).creator ∈ H →
      ∀ X ∈ s.detected, X ∈ cfg.xp.ex (s.disk.blk c).payload) →
    m + 1 ≤ k → (s.disk.atRound k).card ≤ Fintype.card Validator + s.detected.card

/-- The blocks a node holds a round. -/
def Statement : Prop := Bounded

end Bound

end Node

end LeanDag
