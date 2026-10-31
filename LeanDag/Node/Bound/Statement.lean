import LeanDag.Node.Converge.Statement
import LeanDag.Node.Live.Statement
/-!
# The blocks a node holds a round — statement

`docs/validator.md` §4, V13. Over a trace with timely authentication and
an injective hash, let fewer than `q` nodes lie outside the honest set
`H`, and let every block of an honest author at round `m + 1` on honest
`v`'s disk expose every author `v` convicted. Then **`v`'s disk holds at
most `n + |D|` blocks of each round from `m + 1` on**, for `D` the authors
`v` convicted (`Bounded`): one of each author not convicted, and two of
each convicted.

Under spread evidence (`Live.Spread`) for a set `D` and a round `nE`, at
the bounded vote of an admissible configuration with a faithful payload
source and at most `f` nodes outside `H`, every honest block above `nE`
exposes the authors an honest node convicted, so the bound holds from
round `nE + 1` (`Spreads`).

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

/-- **At most `n + |D|` blocks a round above `nE`, under spread
evidence.** -/
def Spreads : Prop :=
  ∀ (Validator BlockId Payload : Type) [Fintype Validator] [DecidableEq Validator]
    [LinearOrder BlockId] (cfg : Config Validator BlockId Payload) (H : Finset Validator)
    (tr : Trace Validator BlockId Payload) (D : Finset Validator) (nE : ℕ) (v : Validator)
    (i k : ℕ),
    cfg.σ = boundedSel → cfg.Admissible → cfg.Faithful → Hᶜ.card ≤ cfg.f → Hᶜ.card < cfg.q →
    Converge.TimelyAuthentic cfg H tr → Converge.HashInjective cfg H tr →
    Live.Spread cfg H tr D nE → v ∈ H → nE + 1 ≤ k →
    ((stateBefore cfg tr i v).disk.atRound k).card ≤
      Fintype.card Validator + (stateBefore cfg tr i v).detected.card

/-- The blocks a node holds a round. -/
def Statement : Prop := Bounded ∧ Spreads

end Bound

end Node

end LeanDag
