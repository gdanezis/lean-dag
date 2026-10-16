import LeanDag.Scheme.Model.TryDecide
import LeanDag.Common.Anchored
/-!
# The commit loop — statement

`docs/scheme.md` §8. The scheme's `TryDecide`, run on a validator's view
from slot `lo` to slot `N`:

* **It outputs only what the relation derives**, at consecutive slots
  from `lo`, at every row and every vote-selection rule whose link and
  certificate thresholds are positive.
* **Two validators' outputs are prefix-comparable**, and **the loop
  decides every verdict the relation derives** once its scan reaches far
  enough, at every row the
  inequalities cover (`Scheme/Sufficiency/`): a two-round row meeting
  `TwoRound n f q` with a positive link, or a three-round row with a link
  of one certificate meeting `ThreeRound n f q`, on a record whose blocks
  reference `q` distinct authors and where validators outside `Hon`, at
  most `f`, never equivocate.

Statements only; the proofs are `Proof.lean`.
-/

namespace LeanDag

namespace Scheme

namespace Loop

/-- **`TryDecide` outputs only derivable verdicts.** -/
def Sound : Prop :=
  ∀ (Validator BlockId Payload : Type) [Fintype Validator] [DecidableEq Validator]
    [LinearOrder BlockId] (P : Validity Validator BlockId Payload) (honest : Finset Validator)
    (p : Params) (σ : VoteSel Validator BlockId Payload P honest) [S : Slots Validator]
    (U : BlockRecord Validator BlockId Payload P honest) (V : U.View) (lo N : ℕ),
    1 ≤ p.linkSize → (p.voteIsCert = false → 1 ≤ p.certThreshold) → lo ≤ N + 1 →
    (tryDecide p σ U V lo N).map Prod.fst = List.range' lo (tryDecide p σ U V lo N).length ∧
    ∀ e ∈ tryDecide p σ U V lo N, (schemeAnchored p σ).Decided U V e.1 e.2

/-- **Two validators' outputs are prefix-comparable**, at the rows the
inequalities cover. -/
def PrefixComparable : Prop :=
  ∀ (Validator BlockId Payload : Type) [Fintype Validator] [DecidableEq Validator]
    [LinearOrder BlockId] (P : Validity Validator BlockId Payload) [P.Mechanised]
    (q : ℕ) [P.Quorate q] (honest Hon : Finset Validator) (f : ℕ) (p : Params)
    (σ : VoteSel Validator BlockId Payload P honest) [S : Slots Validator]
    (U : BlockRecord Validator BlockId Payload P honest) (V₁ V₂ : U.View) (lo N₁ N₂ : ℕ),
    Honᶜ.card ≤ f → q ≤ Fintype.card Validator → U.NoEquivOn Hon →
    ((p.voteIsCert = true ∧ 2 ≤ p.waveLength ∧ 1 ≤ p.linkSize ∧
        p.TwoRound (Fintype.card Validator) f q) ∨
      (p.voteIsCert = false ∧ 3 ≤ p.waveLength ∧ p.linkSize = 1 ∧
        p.ThreeRound (Fintype.card Validator) f q)) →
    lo ≤ N₁ + 1 → lo ≤ N₂ + 1 →
    tryDecide p σ U V₁ lo N₁ <+: tryDecide p σ U V₂ lo N₂ ∨
      tryDecide p σ U V₂ lo N₂ <+: tryDecide p σ U V₁ lo N₁

/-- **The loop decides every derived verdict**, at the rows the
inequalities cover, once its scan reaches far enough. -/
def Complete : Prop :=
  ∀ (Validator BlockId Payload : Type) [Fintype Validator] [DecidableEq Validator]
    [LinearOrder BlockId] (P : Validity Validator BlockId Payload) [P.Mechanised]
    (q : ℕ) [P.Quorate q] (honest Hon : Finset Validator) (f : ℕ) (p : Params)
    (σ : VoteSel Validator BlockId Payload P honest) [S : Slots Validator]
    (U : BlockRecord Validator BlockId Payload P honest) (V : U.View) (k : ℕ)
    (v : Option BlockId),
    Honᶜ.card ≤ f → q ≤ Fintype.card Validator → U.NoEquivOn Hon →
    ((p.voteIsCert = true ∧ 2 ≤ p.waveLength ∧ 1 ≤ p.linkSize ∧
        p.TwoRound (Fintype.card Validator) f q) ∨
      (p.voteIsCert = false ∧ 3 ≤ p.waveLength ∧ p.linkSize = 1 ∧
        p.ThreeRound (Fintype.card Validator) f q)) →
    (schemeAnchored p σ).Decided U V k v →
    ∃ N₀, ∀ N, N₀ ≤ N → decisionAt p σ U V N k = some v

/-- **`TryDecide` outputs every derived verdict**, at the rows the
inequalities cover, once every slot from `lo` to `k` has one and the
scan reaches far enough. -/
def OutputComplete : Prop :=
  ∀ (Validator BlockId Payload : Type) [Fintype Validator] [DecidableEq Validator]
    [LinearOrder BlockId] (P : Validity Validator BlockId Payload) [P.Mechanised]
    (q : ℕ) [P.Quorate q] (honest Hon : Finset Validator) (f : ℕ) (p : Params)
    (σ : VoteSel Validator BlockId Payload P honest) [S : Slots Validator]
    (U : BlockRecord Validator BlockId Payload P honest) (V : U.View) (lo k : ℕ),
    Honᶜ.card ≤ f → q ≤ Fintype.card Validator → U.NoEquivOn Hon →
    ((p.voteIsCert = true ∧ 2 ≤ p.waveLength ∧ 1 ≤ p.linkSize ∧
        p.TwoRound (Fintype.card Validator) f q) ∨
      (p.voteIsCert = false ∧ 3 ≤ p.waveLength ∧ p.linkSize = 1 ∧
        p.ThreeRound (Fintype.card Validator) f q)) →
    lo ≤ k → (∀ m, lo ≤ m → m ≤ k → ∃ v, (schemeAnchored p σ).Decided U V m v) →
    ∃ N₀, ∀ N, N₀ ≤ N → ∀ v, (schemeAnchored p σ).Decided U V k v →
      (k, v) ∈ tryDecide p σ U V lo N

/-- The loop's claims. -/
def Statement : Prop := Sound ∧ PrefixComparable ∧ Complete ∧ OutputComplete

end Loop

end Scheme

end LeanDag
