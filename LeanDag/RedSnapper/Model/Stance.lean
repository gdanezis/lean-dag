import LeanDag.RedSnapper.Model.CausalHistory

/-!
# Stances read from the DAG, and the stance discipline

Trusted core: the paper's `Stance` and `AckedBefore`
(`Alg:FastPathPredicates`), and the one behavioural hypothesis the
safety results make about correct validators.

`Stance(id, o, b)` is the latest declaration validator `id` made on `o`
in the causal history of `b`: `tx`, `⊥`, or `none` if `id` never
declared — or if `id` equivocated at the latest declaring round, two
distinct blocks of that round both declaring, in which case an
equivocating validator contributes no vote (D7: equivocation at the
latest declaring round only). The paper writes it as a procedure; here
it is a relation `StanceIs U id o b s`, so that the trusted core never
decides reachability and needs no choice. That the relation is total and
functional is proved in `Helpers/`, not assumed.

`StanceDiscipline` is the safety-side honest predicate of D5: what a
correct validator's declarations on one object may look like along its
chain. The paper's `held` automaton moves along `none → {tx, ⊥}`,
`tx → {tx, ⊥}`, `⊥ → ⊥` — a validator never moves from one transaction
to another, and once at `⊥` never returns to a transaction. Stated on
declarations, this is two clauses: a correct block declaring `ack tx`
has, in its author's own history, no declaration of `⊥` on that object
and no ACK for a different transaction. This is **all** that the safety
results consume about correct validators' votes; when a correct
validator adopts, keeps or retracts is the liveness-side rule of a later
phase.
-/

namespace LeanDag

namespace RedSnapper

variable {Validator BlockId Tx Obj : Type*} [Fintype Validator] [DecidableEq Validator]
  [F : Faults Validator]

/-- `b'` is a block of `id` in the causal history of `b` that declares on
`o`. -/
def Declaring (U : Universe Validator BlockId Tx Obj) (id : Validator) (o : Obj)
    (b b' : BlockId) : Prop :=
  b' ∈ U.ids ∧ (U.block b').author = id ∧ Reaches U b b' ∧ (U.block b').declares o ≠ none

/-- `b'` is a latest declaring block of `id` on `o` below `b`: declaring,
and no declaring block sits at a higher round. -/
def Latest (U : Universe Validator BlockId Tx Obj) (id : Validator) (o : Obj)
    (b b' : BlockId) : Prop :=
  Declaring U id o b b' ∧
    ∀ b'', Declaring U id o b b'' → (U.block b'').round ≤ (U.block b').round

/-- `StanceIs U id o b s` — the stance of `id` on `o` read at `b` is `s`
(the paper's `Stance(id, o, b) = s`). `some s`: there is exactly one
latest declaring block, and it declares `s`. `none`: `id` never declared
on `o` below `b`, or two distinct blocks are latest — equivocation at the
latest declaring round. -/
def StanceIs (U : Universe Validator BlockId Tx Obj) (id : Validator) (o : Obj) (b : BlockId) :
    Option (Stance Tx) → Prop
  | some s => ∃ b', Latest U id o b b' ∧ (U.block b').declares o = some s ∧
      ∀ b'', Latest U id o b b'' → b'' = b'
  | none => (¬ ∃ b', Declaring U id o b b') ∨
      (∃ b₁ b₂, Latest U id o b b₁ ∧ Latest U id o b b₂ ∧ b₁ ≠ b₂)

/-- `id` ACKed some transaction on `o` at or below `b` (the paper's
`AckedBefore`): some block of `id` in `b`'s history reads a stance of
`ack tx`. What tells an unlock vote from a skip vote.

Under D7 the stance a declaring block reads at itself is its own
declaration — a block reaches no other block of its round, so it is the
unique latest declarer below itself — and `AckedBefore` is therefore
equivalent to "some block of `id` in `b`'s history declares `ack tx`".
The equivocation-voiding of `StanceIs` does no filtering here; the
paper's form is kept for fidelity. -/
def AckedBefore (U : Universe Validator BlockId Tx Obj) (id : Validator) (o : Obj)
    (b : BlockId) : Prop :=
  ∃ b' tx, b' ∈ U.ids ∧ (U.block b').author = id ∧ Reaches U b b' ∧
    StanceIs U id o b' (some (Stance.ack tx))

/-- The stance discipline of correct validators: along a correct
validator's own chain, a declaration `ack tx` on `o` is preceded by no
`⊥` on `o` and by no ACK for another transaction on `o`. Equivalently,
the `held` automaton `none → {tx, ⊥}`, `tx → {tx, ⊥}`, `⊥ → ⊥`. -/
structure StanceDiscipline (U : Universe Validator BlockId Tx Obj) : Prop where
  /-- Once at `⊥`, never back to a transaction. -/
  no_return : ∀ b ∈ U.ids, (U.block b).author ∈ (Correct : Finset Validator) →
    ∀ p ∈ U.ids, (U.block p).author = (U.block b).author → Reaches U b p → p ≠ b →
    ∀ (o : Obj) (tx : Tx), (U.block b).declares o = some (Stance.ack tx) →
      (U.block p).declares o ≠ some Stance.bot
  /-- Never from one transaction to another. -/
  no_switch : ∀ b ∈ U.ids, (U.block b).author ∈ (Correct : Finset Validator) →
    ∀ p ∈ U.ids, (U.block p).author = (U.block b).author → Reaches U b p → p ≠ b →
    ∀ (o : Obj) (tx tx' : Tx), (U.block b).declares o = some (Stance.ack tx) →
      (U.block p).declares o = some (Stance.ack tx') → tx' = tx

end RedSnapper

end LeanDag
