import LeanDag.RedSnapper.Model.Universe

/-!
# Structural synchrony

Trusted core: the structural rendering of "after GST" — no clock and no
`Δ` appear; what the network must eventually supply is stated as two
round-indexed properties of the universe, the shape Hydrozoan's
liveness package established.

`PopulatedOn U T r` — every member of `T` authors a block at round `r`.
`SynchronisedOn U T R` — from round `R` on, every `T`-authored block
references every `T`-authored block of the round below.

Both are `T`-relative definitions; the liveness results consume them at
`T := Correct`, because the fast path counts `quorum = n − f` ACKs and
`half = 2f + 1` retractions, and nothing short of all-correct
participation reaches those thresholds at the tight committee. Both are
assumptions and recorded as such: what makes them true in good periods
is the DAG-building layer's waiting rule, whose derivation from delivery
primitives is out of scope, as in Hydrozoan.
-/

namespace LeanDag

namespace RedSnapper

variable {Validator BlockId Tx Obj : Type*} [Fintype Validator] [DecidableEq Validator]
  [F : Faults Validator]

/-- Every member of `T` authors a block at round `r`. -/
def PopulatedOn (U : Universe Validator BlockId Tx Obj) (T : Finset Validator)
    (r : ℕ) : Prop :=
  ∀ v ∈ T, ∃ b ∈ U.ids, (U.block b).author = v ∧ (U.block b).round = r

/-- From round `R` on, every `T`-authored block references every
`T`-authored block of the round below. -/
def SynchronisedOn (U : Universe Validator BlockId Tx Obj) (T : Finset Validator)
    (R : ℕ) : Prop :=
  ∀ b ∈ U.ids, (U.block b).author ∈ T → R < (U.block b).round →
    ∀ b' ∈ U.ids, (U.block b').author ∈ T →
      (U.block b').round + 1 = (U.block b).round → b' ∈ (U.block b).parents

end RedSnapper

end LeanDag
