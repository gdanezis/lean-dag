import LeanDag.Scheme.Model.Rule
/-!
# The scheme's vote

`docs/scheme.md` §3: the scheme's `VotedBlock`, a depth-first search of a
block's parents in a fixed order, returning the first block of the slot
it meets. `ord b s` lists the parent set `s` of `b` in its stored order.

Definitions only; that it is a vote-selection rule is
`Scheme/Safety/Statement.lean`.
-/

namespace LeanDag

namespace Scheme

variable {Validator : Type*} [Fintype Validator] [DecidableEq Validator]
variable {BlockId : Type*} [DecidableEq BlockId] {Payload : Type*}
variable {P : Validity Validator BlockId Payload} {honest : Finset Validator}

/-- `VotedBlock` with `n` levels of recursion. -/
def votedBlockUpto (ord : BlockId → Finset BlockId → List BlockId)
    (U : BlockRecord Validator BlockId Payload P honest) :
    ℕ → BlockId → Validator → ℕ → Option BlockId
  | 0, _, _, _ => none
  | n + 1, b, a, r =>
    if (U.block b).round ≤ r then none
    else (ord b (U.block b).refs).findSome? fun b' =>
      if (U.block b').creator = a ∧ (U.block b').round = r then some b'
      else votedBlockUpto ord U n b' a r

/-- **The scheme's `VotedBlock`**: the block of `(a, r)` that `b` votes
for, searched to the depth of `b`'s round. -/
def votedBlock (ord : BlockId → Finset BlockId → List BlockId)
    (U : BlockRecord Validator BlockId Payload P honest) (b : BlockId) (a : Validator) (r : ℕ) :
    Option BlockId :=
  votedBlockUpto ord U ((U.block b).round + 1) b a r

end Scheme

end LeanDag
