import LeanDag.RedSnapper.Model.Five.Coin
import LeanDag.RedSnapper.Model.Liveness

/-!
# Coin success — statement

RS9a: the deterministic core of the paper's Lemma coin-success, in the
structural-liveness style of RS4: synchrony is `PopulatedOn` and
`SynchronisedOn` at `Correct` (Phase 6), the coin is the selected
target `w` (D8), and the probability bound is a cardinality.

The paper's claim — with probability at least `half / (5f + 1)` a full
certificate or a full unlock certificate is witnessed two rounds later
— splits into its two proof cases, each fully deterministic once `w` is
fixed, plus the count:

* **Concentrated** (no `Five`): if some stance `x` is held at `ρ` by
  `half` correct validators and the coin lands on one of them, every
  correct round-`(ρ + 2)` block carries a full certificate for `x`'s
  transaction, or a full unlock certificate when `x = ⊥`. Every correct
  validator not at `x` sees the holders among its synchronised parents
  — a refutation of its own value — and follows the coin to `x`; the
  holders keep or re-adopt.
* **Fragmented** (under `Five`): if no stance has `half` correct
  holders, every correct validator sees `(n − f) − 2f ≥ 2f + 1`
  differing stances and is movable, so *any* correct target unifies the
  committee on its own value — `n ≥ 5f + 1` is exactly what makes the
  whole committee movable at once.
* **The count**: there is a set of at least `half` targets, any of
  which unifies — the holder set, or all of `Correct` (of size at least
  `n − f ≥ half`). Under a uniformly drawn coin this *is* the paper's
  bound `half / n`; the arc states the numerator and leaves the
  division to the reader, probability theory staying out of the trusted
  core.
* **Measurability** (Mahi-Mahi's MM2′ pattern): the good-target set is
  built from the round-`ρ` holder sets, and two universes agreeing up
  to `ρ` have the same ones — so which targets are good is fixed by the
  history a coin revealed after round `ρ` cannot depend on, which is
  what makes the uniform reading of the count sound against an
  adversary that sees the draw.

The hypotheses are the attempt's conditioning: the freeze rule (for the
`Adopt` candidacy gate), the coin round itself, population at `ρ` and
`ρ + 1`, synchrony from `ρ` on, and every correct validator stanced at
`ρ` — the paper's premises, structurally. Of the freeze rule, only the
`ack_candidate` clause is consumed. No *population* is assumed past
`ρ + 1`: the conclusion quantifies over the round-`(ρ + 2)` blocks that
exist — vacuously, in a universe with none; a consumer wanting a
certificate in hand adds population at `ρ + 2`. (`SynchronisedOn` does
constrain every correct block above `ρ`, including at `ρ + 2` — its
referencing half is what the conclusion's counting reads.)
And `CoinSuccessCount`'s good set is existential: that the proofs
choose it from the transferred ingredients — the holder sets, or
`Correct` — is what ties it to `CoinMeasurable`, by inspection rather
than by statement.
-/

namespace LeanDag

namespace RedSnapper

namespace CoinSuccess

variable {Validator BlockId Tx Obj : Type*} [Fintype Validator] [DecidableEq Validator]
  [F : Faults Validator] [T : Transactions Tx Obj]

/-- `v` holds `x` on `o` at round `ρ`: every own block of that round
reads it. -/
def HoldsAt (U : Universe Validator BlockId Tx Obj) (v : Validator) (o : Obj) (ρ : ℕ)
    (x : Stance Tx) : Prop :=
  ∀ b ∈ U.ids, (U.block b).author = v →   -- at every own block ...
    (U.block b).round = ρ →               -- ... of the round (unique for correct authors),
    StanceIs U v o b (some x)             -- the stance read is x

/-- Round `r` certifies the value `x` on `o`: every correct block of
the round carries the matching certificate. -/
def CertifiedAt (U : Universe Validator BlockId Tx Obj) (o : Obj) (x : Stance Tx)
    (r : ℕ) : Prop :=
  ∀ C ∈ U.ids, (U.block C).author ∈ (Correct : Finset Validator) →
    (U.block C).round = r →               -- every correct block of the round carries
    (∃ tx, x = Stance.ack tx ∧ IsFullCert U C tx) ∨
                                          -- a full certificate for x's transaction, or
      (x = Stance.bot ∧ IsFullUnlockCert U C o)
                                          -- a full unlock certificate when x = ⊥

/-- **Concentrated**: the coin lands in a `half`-sized holder set. -/
def CoinConcentrated (U : Universe Validator BlockId Tx Obj) : Prop :=
  ∀ (w : Validator) (o : Obj) (ρ : ℕ) (x : Stance Tx) (H : Finset Validator),
    FreezeDiscipline U →                  -- the freeze rule: ACKs name candidates
    CoinRule U w o ρ →                    -- the attempt follows the coin, target w
    PopulatedOn U (Correct : Finset Validator) ρ →
    PopulatedOn U (Correct : Finset Validator) (ρ + 1) →
                                          -- every correct validator has a block at ρ, ρ+1
    SynchronisedOn U (Correct : Finset Validator) ρ →
                                          -- correct blocks above ρ reference all correct
                                          -- blocks of the round below
    StancedAt U o ρ →                     -- every correct validator has a stance at ρ
    H ⊆ (Correct : Finset Validator) → half Validator ≤ H.card →
                                          -- a set of 2f+1 correct validators ...
    (∀ v ∈ H, HoldsAt U v o ρ x) →        -- ... all holding the same value x at ρ
    w ∈ H →                               -- and the coin lands inside it: then
    CertifiedAt U o x (ρ + 2)             -- round ρ+2 certifies x

/-- **Fragmented**: no stance has `half` correct holders, and any
correct target unifies the committee on its own value. -/
def CoinFragmented (U : Universe Validator BlockId Tx Obj) : Prop :=
  ∀ (w : Validator) (o : Obj) (ρ : ℕ),
    FreezeDiscipline U →                  -- as above ...
    CoinRule U w o ρ →
    PopulatedOn U (Correct : Finset Validator) ρ →
    PopulatedOn U (Correct : Finset Validator) (ρ + 1) →
    SynchronisedOn U (Correct : Finset Validator) ρ →
    StancedAt U o ρ →
    (∀ x : Stance Tx, ¬ ∃ H : Finset Validator, H ⊆ (Correct : Finset Validator) ∧
      half Validator ≤ H.card ∧ ∀ v ∈ H, HoldsAt U v o ρ x) →
                                          -- ... but no value has 2f+1 correct holders
                                          -- (so everyone is movable, which needs 5f+1),
    w ∈ (Correct : Finset Validator) →    -- and the coin lands on any correct validator:
    ∃ x, HoldsAt U w o ρ x ∧ CertifiedAt U o x (ρ + 2)
                                          -- then ρ+2 certifies the target's own value

/-- **The count**: at least `half` targets succeed — the structural
numerator of the paper's `half / (5f + 1)`. -/
def CoinSuccessCount (U : Universe Validator BlockId Tx Obj) : Prop :=
  ∀ (o : Obj) (ρ : ℕ),
    FreezeDiscipline U →                  -- as above, with no coin fixed:
    PopulatedOn U (Correct : Finset Validator) ρ →
    PopulatedOn U (Correct : Finset Validator) (ρ + 1) →
    SynchronisedOn U (Correct : Finset Validator) ρ →
    StancedAt U o ρ →
    ∃ G : Finset Validator, half Validator ≤ G.card ∧
                                          -- at least 2f+1 good targets — the numerator
                                          -- of the paper's half/(5f+1) —
      ∀ w ∈ G, CoinRule U w o ρ → ∃ x, CertifiedAt U o x (ρ + 2)
                                          -- any of which, if followed, certifies ρ+2

variable (Validator BlockId Tx Obj) in
/-- **Measurability**: everything the good-target set is built from —
the holder sets and the stanced premise at round `ρ` — is determined by
the universe up to round `ρ`. -/
def CoinMeasurable : Prop :=
  ∀ (U₁ U₂ : Universe Validator BlockId Tx Obj) (ρ : ℕ) (o : Obj),
    AgreeUpto U₁ U₂ ρ →                   -- indistinguishable up to the attempt round:
    (∀ (v : Validator) (x : Stance Tx), HoldsAt U₁ v o ρ x ↔ HoldsAt U₂ v o ρ x) ∧
                                          -- the same holder sets — hence the same G —
      (StancedAt U₁ o ρ ↔ StancedAt U₂ o ρ)
                                          -- and the same stanced premise

/-- Coin success, over every fault configuration, transaction data and
universe the model admits: the concentrated case at any committee, the
fragmented case and the count at `n ≥ 5f + 1`, and the measurability of
the good-target set. -/
def Statement : Prop :=
  ∀ (Validator BlockId Tx Obj : Type) [Fintype Validator] [DecidableEq Validator]
    [Faults Validator] [Transactions Tx Obj],
    (∀ U : Universe Validator BlockId Tx Obj,
      CoinConcentrated U ∧ (Five Validator → CoinFragmented U ∧ CoinSuccessCount U)) ∧
    CoinMeasurable Validator BlockId Tx Obj

end CoinSuccess

end RedSnapper

end LeanDag
