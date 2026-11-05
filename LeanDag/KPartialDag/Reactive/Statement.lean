import LeanDag.KPartialDag.Model.Reactive
/-!
# Reactive nodes in time — statement

`docs/kpartial.md` §11. Under the reactive rules from round `R` to round
`N`, with message delay `δ` from time `G` and timeout `τ` (`ReactiveRules`):

* **every round is built** (`Built`): every correct validator builds at every
  round from `R` to `N`;
* **nodes behind catch up within `δ`** (`CatchesUp`): once `f + 1` correct
  validators have built at a round by a time `t ≥ G`, every correct
  validator has built at the round by `t + δ`;
* **a reactive run starts** (`Starts`): the round after the last round a
  correct node reached before `G + τ` starts a reactive run (`ReactiveRun`),
  built within `2δ + τ` of `G + τ`.

On a reactive run from round `R` to round `N`:

* **each round is built within `δ + τ`** (`Slow`) of the round below;
* **rounds led by correct validators are built within `δ`** (`Fast`): at
  `τ ≥ 2δ`, when the slots of a round and of the round below have correct
  leaders, no correct node waits for its timeout;
* **the run is responsive** (`Responsive`): at `τ ≥ 2δ`, the record is
  responsive among the correct validators from round `R + 1` to `N`, so
  `Live.Progress` applies;
* **a slot led by correct validators commits within `3δ`** (`Commits`): at
  `τ ≥ 2δ`, when the slots from one round below a slot to one round above
  it have correct leaders, every correct node commits the slot directly
  within `3δ` of the last correct block at the slot's round.

No bound depends on `K`: the downloads to depth `K` are inside `δ`.
Statements only; the proofs are `Proof.lean`.
-/

namespace LeanDag

namespace KPartialDag

namespace Reactive

/-- **Every round is built**: under the reactive rules from round `R` to
round `N`, every correct validator has a block at every round from `R` to
`N`. -/
def Built : Prop :=
  ∀ (Validator BlockId Payload : Type) [Fintype Validator] [DecidableEq Validator]
    [Faults Validator] [DecidableEq BlockId] [Slots Validator]
    (U : KRecord Validator BlockId Payload) (tl : Timeline Validator BlockId) (G δ τ R N : ℕ),
    ReactiveRules U tl G δ τ R N → ∀ s, R ≤ s → s ≤ N → ∃ t, BuiltBy U tl s t

/-- **Nodes behind catch up within `δ`**: under the reactive rules from round
`R` to round `N`, once a set `A` of `f + 1` correct validators have built at
round `s + 1`, from `R + 1` to `N`, by a time `t ≥ G`, every correct
validator has built at round `s + 1` by `t + δ`. -/
def CatchesUp : Prop :=
  ∀ (Validator BlockId Payload : Type) [Fintype Validator] [DecidableEq Validator]
    [F : Faults Validator] [DecidableEq BlockId] [Slots Validator]
    (U : KRecord Validator BlockId Payload) (tl : Timeline Validator BlockId) (G δ τ R N : ℕ),
    ReactiveRules U tl G δ τ R N → ∀ s t (A : Finset Validator), R ≤ s → s < N → G ≤ t →
      A ⊆ (Correct : Finset Validator) → F.f + 1 ≤ A.card →
      (∀ v ∈ A, ∃ b ∈ U.ids, (U.block b).creator = v ∧ (U.block b).round = s + 1 ∧
        tl.built b ≤ t) →
      BuiltBy U tl (s + 1) (t + δ)

/-- **A reactive run starts**: under the reactive rules from round `R` to
round `N`, there is a round `R' ≥ R`, either `R` or one above a round that a
correct block reached before `G + τ`, such that, if `R' ≤ N`, the timeline
is a reactive run from `R'` to `N`, and every correct validator has built at
`R'` within `2δ + τ` of `G + τ` and of the time all built at `R`. -/
def Starts : Prop :=
  ∀ (Validator BlockId Payload : Type) [Fintype Validator] [DecidableEq Validator]
    [Faults Validator] [DecidableEq BlockId] [Slots Validator]
    (U : KRecord Validator BlockId Payload) (tl : Timeline Validator BlockId) (G δ τ R N : ℕ),
    ReactiveRules U tl G δ τ R N → ∃ R', R ≤ R' ∧
      (R' = R ∨ ∃ x ∈ U.ids, (U.block x).creator ∈ (Correct : Finset Validator) ∧
        (U.block x).round + 1 = R' ∧ tl.built x < G + τ) ∧
      (R' ≤ N → ReactiveRun U tl G δ τ R' N ∧
        ∀ t₀, BuiltBy U tl R t₀ → BuiltBy U tl R' (max t₀ (G + τ) + 2 * δ + τ))

/-- **Each round within `δ + τ`**: once every correct validator has built at
round `s`, from `R` to below `N`, by `t`, every correct validator has built at round `s + 1` by
`t + δ + τ`. -/
def Slow : Prop :=
  ∀ (Validator BlockId Payload : Type) [Fintype Validator] [DecidableEq Validator]
    [Faults Validator] [DecidableEq BlockId] [Slots Validator]
    (U : KRecord Validator BlockId Payload) (tl : Timeline Validator BlockId) (G δ τ R N : ℕ),
    ReactiveRun U tl G δ τ R N → ∀ s t, R ≤ s → s < N → BuiltBy U tl s t →
      BuiltBy U tl (s + 1) (t + δ + τ)

/-- **Rounds led by correct validators within `δ`**: at `τ ≥ 2δ`, when the
slots at round `s`, from `R + 2` to below `N`, and one round below have
correct leaders, once
every correct validator has built at round `s` by `t`, every correct
validator has built at round `s + 1` by `t + δ`. -/
def Fast : Prop :=
  ∀ (Validator BlockId Payload : Type) [Fintype Validator] [DecidableEq Validator]
    [Faults Validator] [DecidableEq BlockId] [S : Slots Validator]
    (U : KRecord Validator BlockId Payload) (tl : Timeline Validator BlockId) (G δ τ R N : ℕ),
    ReactiveRun U tl G δ τ R N → 2 * δ ≤ τ → ∀ s t, R + 2 ≤ s → s < N →
      (∀ k, S.slotRound k = s ∨ S.slotRound k + 1 = s →
        S.leader k ∈ (Correct : Finset Validator)) →
      BuiltBy U tl s t → BuiltBy U tl (s + 1) (t + δ)

/-- **The run is responsive**: at `τ ≥ 2δ`, a reactive run from round `R` to
round `N` is responsive among the correct validators from round `R + 1` to
`N`. -/
def Responsive : Prop :=
  ∀ (Validator BlockId Payload : Type) [Fintype Validator] [DecidableEq Validator]
    [Faults Validator] [DecidableEq BlockId] [Slots Validator]
    (U : KRecord Validator BlockId Payload) (tl : Timeline Validator BlockId) (G δ τ R N : ℕ),
    ReactiveRun U tl G δ τ R N → 2 * δ ≤ τ →
      RespondsFrom U (Correct : Finset Validator) (R + 1) N

/-- **A slot led by correct validators commits within `3δ`**: at `τ ≥ 2δ`,
when every slot from one round below a slot at round `r`, from `R + 2` to
`N − 2`, to one round above it has a correct leader, and every correct validator has built at
round `r` by `t`, every correct node commits the slot directly on what it
holds at `t + 3δ`. -/
def Commits : Prop :=
  ∀ (Validator BlockId Payload : Type) [Fintype Validator] [DecidableEq Validator]
    [Faults Validator] [DecidableEq BlockId] [S : Slots Validator]
    (U : KRecord Validator BlockId Payload) (tl : Timeline Validator BlockId) (G δ τ R K N : ℕ),
    ReactiveRun U tl G δ τ R N → 2 * δ ≤ τ → ∀ k t, R + 2 ≤ S.slotRound k →
      S.slotRound k + 2 ≤ N →
      (∀ j, S.slotRound k ≤ S.slotRound j + 1 → S.slotRound j ≤ S.slotRound k + 1 →
        S.leader j ∈ (Correct : Finset Validator)) →
      BuiltBy U tl (S.slotRound k) t → ∀ v ∈ (Correct : Finset Validator),
        ∃ L, IsLeaderBlock U k L ∧ NodeDecided U K (tl.held v (t + 3 * δ)) k (some L)

/-- Reactive nodes in time. -/
def Statement : Prop := Built ∧ CatchesUp ∧ Starts ∧ Slow ∧ Fast ∧ Responsive ∧ Commits

end Reactive

end KPartialDag

end LeanDag
