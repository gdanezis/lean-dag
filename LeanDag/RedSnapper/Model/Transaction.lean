import LeanDag.RedSnapper.Model.CausalHistory

/-!
# Inclusion, candidates, and conflicts

Trusted core: the paper's `Includes`, `Candidates` and `ConflictedObjs`
(`Alg:FastPathPredicates`), as predicates over the universe.

`Includes(b, tx)` is inclusion, not endorsement: the transaction lies in
the causal history of `b`. A *candidate* for an object version at `b` is
a valid transaction spending it that `b` includes — owned or mixed, both
contend. An object version is *conflicted* at `b` when `b` includes two
distinct candidates for it; since causal histories only grow, a conflict
once visible stays visible in every descendant.

**Fidelity gap** (D3, `docs/red-snapper.md`): the paper's `Candidates`
also requires the version to be *spendable* at `b` — the previous
version decided in `b`'s history. Object versions are opaque here, so the
gate is dropped; no safety claim reads it. Dropping it enlarges
`Candidates` and so `Conflicted`: skip and unlock votes become available
in more states than the paper's, which is the conservative direction
for the safety claims.

With one owned input per transaction (D2), the paper's `RecoveryObjs(b)`
— conflicted versions closed under the inputs of dead candidates —
collapses to `ConflictedObjs(b)`: every disjunct of `Dead` already
implies a visible conflict on the one input. `Conflicted` is therefore
also the set the voting rule recovers.
-/

namespace LeanDag

namespace RedSnapper

variable {Validator BlockId Tx Obj : Type*} [Fintype Validator] [DecidableEq Validator]
  [F : Faults Validator] [T : Transactions Tx Obj]

/-- `b` includes `tx` (the paper's `Includes`): some block in `b`'s
causal history carries it. -/
def Includes (U : Universe Validator BlockId Tx Obj) (b : BlockId) (tx : Tx) : Prop :=
  ∃ b' ∈ U.ids, tx ∈ (U.block b').txs ∧ Reaches U b b'

/-- `tx` is a candidate for `o` at `b` (membership in the paper's
`Candidates(b, o)`): valid, spending `o`, and included by `b`. -/
def IsCandidate (U : Universe Validator BlockId Tx Obj) (b : BlockId) (o : Obj) (tx : Tx) :
    Prop :=
  T.Valid tx ∧ T.input tx = o ∧ Includes U b tx

/-- `o` is conflicted at `b` (membership in the paper's
`ConflictedObjs(b)`): `b` includes two distinct candidates for it. -/
def Conflicted (U : Universe Validator BlockId Tx Obj) (b : BlockId) (o : Obj) : Prop :=
  ∃ tx tx', IsCandidate U b o tx ∧ IsCandidate U b o tx' ∧ tx ≠ tx'

end RedSnapper

end LeanDag
