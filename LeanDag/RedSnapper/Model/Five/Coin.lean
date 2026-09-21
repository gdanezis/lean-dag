import LeanDag.RedSnapper.Model.Five.Freeze

/-!
# The coin round

Trusted core: the liveness half of the contested rule at `5f+1` —
phase 3 of `CastVotes` (`Alg:Voting5f+1`) for one attempt, as a
hypothesis-predicate on the universe. The safety results consumed
`MoveDiscipline` (a change *needs* a refutation); the coin lemma
additionally consumes what a correct validator *does* at the attempt's
round: keep the standing value when it is not refuted, and follow the
coin when it is.

The coin itself is the selected validator `w`, a parameter (D8): Lemma
coin-success conditions on all correct validators outputting the same
coin, and its probability bound is rendered as a cardinality claim over
the good targets (`Five/CoinSuccess/Statement.lean`).

`AgreeUpto` is the measurability side (Mahi-Mahi's MM2′ pattern): two
universes that agree up to the attempt round are indistinguishable to
everything the good-target set is built from, so whatever decides which
targets are good is fixed *before* a coin revealed after the round —
the statement that licenses reading `CoinSuccessCount`'s cardinality as
a probability under a uniform draw.

Three conditionings, stated here once. The rule binds one round pair
`(ρ, ρ + 1)` — one attempt; the algorithm's `lastAttempt` guard (at
most one move per coin index) is a throttle across attempts that the
lemma conditions past. The paper's "no correct validator has yet
frozen" needs no separate premise: a frozen validator does not follow
the coin, so an execution where one froze simply does not satisfy the
rule. And the `Adopt` fallbacks (target unreadable, target's
transaction not a candidate) are omitted — the hypothesis covers only
the branches the lemma consumes, so it is weaker than the algorithm and
satisfied by it.
-/

namespace LeanDag

namespace RedSnapper

variable {Validator BlockId Tx Obj : Type*} [Fintype Validator] [DecidableEq Validator]
  [F : Faults Validator] [T : Transactions Tx Obj]

/-- **Two universes agree up to round `d`**: the same ids at rounds
`≤ d`, denoting the same blocks — what the coin-measurability claim
consumes. -/
structure AgreeUpto (U₁ U₂ : Universe Validator BlockId Tx Obj) (d : ℕ) : Prop where
  /-- The ids at rounds `≤ d` coincide. -/
  ids : ∀ i, (i ∈ U₁.ids ∧ (U₁.block i).round ≤ d) ↔
    (i ∈ U₂.ids ∧ (U₂.block i).round ≤ d)
  /-- And they denote the same blocks. -/
  block : ∀ i ∈ U₁.ids, (U₁.block i).round ≤ d → U₁.block i = U₂.block i

/-- Every correct block of round `ρ` reads a declared stance on `o` —
the paper's "every correct validator has a stance". -/
def StancedAt (U : Universe Validator BlockId Tx Obj) (o : Obj) (ρ : ℕ) : Prop :=
  ∀ b ∈ U.ids, (U.block b).author ∈ (Correct : Finset Validator) →
    (U.block b).round = ρ → ∃ s : Stance Tx, StanceIs U (U.block b).author o b (some s)

/-- The coin round for target `w` at attempt round `ρ + 1`: what a
correct validator does with its standing value on `o`. -/
structure CoinRule (U : Universe Validator BlockId Tx Obj) (w : Validator) (o : Obj)
    (ρ : ℕ) : Prop where
  /-- Without a refutation of the value read at the self-parent, the
  block stands at that value. -/
  keep : ∀ b ∈ U.ids, (U.block b).author ∈ (Correct : Finset Validator) →
    (U.block b).round = ρ + 1 →
    ∀ p ∈ (U.block b).parents, (U.block p).author = (U.block b).author →
    ∀ s : Stance Tx, StanceIs U (U.block b).author o p (some s) →
      ¬ IsRefutation U b o s →
      StanceIs U (U.block b).author o b (some s)
  /-- With a refutation, the block stands at the target's value, read at
  the target's referenced round-parent — the ACK branch, under the
  `Adopt` candidacy guard. The algorithm evaluates `Stance(w, o, b)`
  *before* writing `b`'s entry, i.e. over the referenced DAG; reading at
  `b` itself would make the clause circular — hence vacuous — on the
  target's own block, which reads its own declaration (D7). For a
  *Byzantine* target silent at its round-`ρ` block, the `q`-read can
  differ from the paper's full-history read (older declarations
  reachable outside `q`'s cone); the coin lemmas instantiate the rule
  only at correct targets, where the two coincide. -/
  adopt_ack : ∀ b ∈ U.ids, (U.block b).author ∈ (Correct : Finset Validator) →
    (U.block b).round = ρ + 1 →
    ∀ p ∈ (U.block b).parents, (U.block p).author = (U.block b).author →
    ∀ s : Stance Tx, StanceIs U (U.block b).author o p (some s) →
      IsRefutation U b o s →
      ∀ q ∈ (U.block b).parents, (U.block q).author = w →
      ∀ tx : Tx, StanceIs U w o q (some (Stance.ack tx)) → IsCandidate U b o tx →
        StanceIs U (U.block b).author o b (some (Stance.ack tx))
  /-- With a refutation, the `⊥` branch — bare, at the same read
  point. -/
  adopt_bot : ∀ b ∈ U.ids, (U.block b).author ∈ (Correct : Finset Validator) →
    (U.block b).round = ρ + 1 →
    ∀ p ∈ (U.block b).parents, (U.block p).author = (U.block b).author →
    ∀ s : Stance Tx, StanceIs U (U.block b).author o p (some s) →
      IsRefutation U b o s →
      ∀ q ∈ (U.block b).parents, (U.block q).author = w →
      StanceIs U w o q (some Stance.bot) →
      StanceIs U (U.block b).author o b (some Stance.bot)

end RedSnapper

end LeanDag
