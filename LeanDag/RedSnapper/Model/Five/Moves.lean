import LeanDag.RedSnapper.Model.Five.Certificates

/-!
# The 5f+1 move rule

Trusted core: the safety-side behavioural hypothesis of §8 — a correct
validator changes its stance only on a refutation of the old one — as a
one-clause predicate on the universe, the `5f+1` counterpart of
`StanceDiscipline`.

The paper splits the argument by which rule made the change (the
uncontested rule never overwrites a stance differently, the freeze rule
preserves it, only the contested rule moves — and it requires a
refutation among the round parents). The single clause subsumes the
split: **any** correct block that declares a stance different from the
one read at its self-parent carries a refutation of the old stance
among its parents. A first declaration — no stance at the self-parent —
is unconstrained, as are re-declarations of the same value.

`StanceDiscipline` is deliberately **not** part of this: the coin
legitimately moves a validator from `⊥` back to a transaction here,
which the `3f+1` automaton forbids — the reason every earlier result
was gated on its own hypothesis. The freeze-constancy clause joins this
structure with the recovery layer in the next phase.
-/

namespace LeanDag

namespace RedSnapper

variable {Validator BlockId Tx Obj : Type*} [Fintype Validator] [DecidableEq Validator]
  [F : Faults Validator] [T : Transactions Tx Obj]

/-- The move rule of correct validators at `5f+1`: a declared stance
change carries a refutation of the old stance among the block's
parents. -/
structure MoveDiscipline (U : Universe Validator BlockId Tx Obj) : Prop where
  /-- A correct block declaring `s'` on `o`, where its self-parent reads
  `s ≠ s'`, carries a refutation of `s`. -/
  move_on_refutation : ∀ b ∈ U.ids,
    (U.block b).author ∈ (Correct : Finset Validator) →
    ∀ p ∈ (U.block b).parents, (U.block p).author = (U.block b).author →
    ∀ (o : Obj) (s s' : Stance Tx),
      StanceIs U (U.block b).author o p (some s) →
      (U.block b).declares o = some s' → s' ≠ s →
      IsRefutation U b o s

end RedSnapper

end LeanDag
