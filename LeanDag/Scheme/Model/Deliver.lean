import LeanDag.Scheme.Model.TryDecide
import LeanDag.Scheme.Model.AsyncPace
import LeanDag.Common.CausalHistory
import Mathlib.Data.Prod.Lex
import LeanDag.Barnacle.Model.Schedule
/-!
# The delivered sequence

What a validator `a_deliver`s, in the vocabulary of Byzantine atomic
broadcast (Sailfish, Definition 1; Sui and Duan, Definition 2.1). A
delivered message is a block, which carries its round `r` and its author
`P_k`.

* `flush U L`: the causal history of the committed leader `L`, ordered by
  round and then by block id.
* `keepFirst key seen l`: the blocks of `l` in order, each kept unless an
  earlier kept block, or `seen`, has the same key.
* `deliverOf U D`: the flushes of the leaders the decisions `D` commit, in
  slot order, keeping the first block of each pair of round and author.
* `deliverSeq p σ U V N`: `deliverOf` the loop's output from slot `0`,
  scanned to slot `N` on the view `V`.
* `AsyncPace.deliverAt`: a reliable validator's delivered sequence at
  time `t` of a run, its loop scanning to slot `M` on its own view.
* `roundRobinSlots n`: round-robin on one slot per round.
* `AsyncPace.Delivers`: a reliable validator eventually delivers a block.
* `Before s x y`: `x` occurs before `y` in `s`.

Definitions only; the claims are `Scheme/AtomicBroadcast/Statement.lean`.
-/

namespace LeanDag

/-- **The first element of each key**: the elements of `l` in order, each
kept unless `seen` or an earlier kept element has its key. -/
def keepFirst {α β : Type*} [DecidableEq β] (key : α → β) : List β → List α → List α
  | _, [] => []
  | seen, a :: l =>
    if key a ∈ seen then keepFirst key seen l else a :: keepFirst key (key a :: seen) l

/-- **`x` occurs before `y` in `s`.** -/
def Before {α : Type*} (s : List α) (x y : α) : Prop :=
  ∃ i j : ℕ, i < j ∧ s[i]? = some x ∧ s[j]? = some y

namespace Scheme

variable {Validator : Type} [Fintype Validator] [DecidableEq Validator]
variable {BlockId : Type} [LinearOrder BlockId] {Payload : Type}
variable {P : Validity Validator BlockId Payload} {honest : Finset Validator}

/-- The round and the author of the block `b`. -/
def roundAuthor (U : BlockRecord Validator BlockId Payload P honest) (b : BlockId) :
    ℕ × Validator :=
  ((U.block b).round, (U.block b).creator)

open Classical in
/-- **A committed leader's flush**: the blocks of `U` in the causal history
of `L`, ordered by round and then by block id. -/
noncomputable def flush (U : BlockRecord Validator BlockId Payload P honest) (L : BlockId) :
    List BlockId :=
  (U.ids.filter (fun b => Reaches U L b)).toList.mergeSort
    (fun a b => decide (toLex ((U.block a).round, a) ≤ toLex ((U.block b).round, b)))

/-- **The blocks delivered for the decisions `D`**: the flushes of the
leaders `D` commits, in slot order, keeping the first block of each round
and author. -/
noncomputable def deliverOf (U : BlockRecord Validator BlockId Payload P honest)
    (D : List (ℕ × Option BlockId)) : List BlockId :=
  keepFirst (roundAuthor U) [] ((D.filterMap Prod.snd).flatMap (flush U))

variable (p : Params) (σ : VoteSel Validator BlockId Payload P honest) [S : Slots Validator]

/-- **The delivered sequence** on the view `V`, the loop scanning from slot
`0` to slot `N`. -/
noncomputable def deliverSeq (U : BlockRecord Validator BlockId Payload P honest) (V : U.View)
    (N : ℕ) : List BlockId :=
  deliverOf U (tryDecide p σ U V 0 N)

/-- **Round-robin on one slot per round**: slot `k` at round `k`, led by
validator `k mod n`. -/
@[reducible] def roundRobinSlots (n : ℕ) [NeZero n] : Slots (Fin n) :=
  Slots.identity (Barnacle.roundRobin n (NeZero.pos n))

/-- **A reliable validator's delivered sequence at time `t`** of the run
`ap`, its loop scanning to slot `M` on its own view. -/
noncomputable def AsyncPace.deliverAt {q N : ℕ} {U : BlockRecord Validator BlockId Payload P honest}
    {T : Finset Validator} (ap : AsyncPace q U T N) {v : Validator} (hv : v ∈ T) (M t : ℕ) :
    List BlockId :=
  deliverSeq p σ U (ap.viewAt hv t) M

/-- **The reliable validator `v` eventually delivers `b`** in the run `ap`:
scanning far enough, `b` is in its delivered sequence from some time on. -/
def AsyncPace.Delivers {q N : ℕ} {U : BlockRecord Validator BlockId Payload P honest}
    {T : Finset Validator} (ap : AsyncPace q U T N) {v : Validator} (hv : v ∈ T) (b : BlockId) :
    Prop :=
  ∃ M₀, ∀ M, M₀ ≤ M → ∃ t, ∀ t', t ≤ t' → b ∈ ap.deliverAt p σ hv M t'

end Scheme

end LeanDag
