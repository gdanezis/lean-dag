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
* **Restarting is idempotent**: a call from a slot inside an earlier
  output repeats its tail, and at the rows the inequalities cover, calls
  on growing views, each restarting after the last decision output,
  output together what one call on the last view outputs.

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

/-- **Restarting inside the output repeats its tail**: a call from any slot
`lo'` between `lo` and the end of the output from `lo` outputs that
output without its first `lo' − lo` entries. -/
def Restart : Prop :=
  ∀ (Validator BlockId Payload : Type) [Fintype Validator] [DecidableEq Validator]
    [LinearOrder BlockId] (P : Validity Validator BlockId Payload) (honest : Finset Validator)
    (p : Params) (σ : VoteSel Validator BlockId Payload P honest) [S : Slots Validator]
    (U : BlockRecord Validator BlockId Payload P honest) (V : U.View) (lo lo' N : ℕ),
    lo ≤ lo' → lo' ≤ lo + (tryDecide p σ U V lo N).length →
    tryDecide p σ U V lo' N = (tryDecide p σ U V lo N).drop (lo' - lo)

/-- **Resuming on a larger view**, at the rows the inequalities cover: the
output on a view, followed by the output on a larger view, scanned at
least as far, from the slot after it, is the output on the larger view. -/
def Resume : Prop :=
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
    V₁.ids ⊆ V₂.ids → N₁ ≤ N₂ →
    tryDecide p σ U V₁ lo N₁ ++
        tryDecide p σ U V₂ (lo + (tryDecide p σ U V₁ lo N₁).length) N₂ =
      tryDecide p σ U V₂ lo N₂

/-- **Successive calls output what one call outputs**, at the rows the
inequalities cover: on growing views scanned ever further, each call
restarting after the last decision output, the decisions output by
`t + 1` calls are the output of one call on the last view. -/
def Repeated : Prop :=
  ∀ (Validator BlockId Payload : Type) [Fintype Validator] [DecidableEq Validator]
    [LinearOrder BlockId] (P : Validity Validator BlockId Payload) [P.Mechanised]
    (q : ℕ) [P.Quorate q] (honest Hon : Finset Validator) (f : ℕ) (p : Params)
    (σ : VoteSel Validator BlockId Payload P honest) [S : Slots Validator]
    (U : BlockRecord Validator BlockId Payload P honest) (lo : ℕ) (W : ℕ → U.View)
    (N : ℕ → ℕ),
    Honᶜ.card ≤ f → q ≤ Fintype.card Validator → U.NoEquivOn Hon →
    ((p.voteIsCert = true ∧ 2 ≤ p.waveLength ∧ 1 ≤ p.linkSize ∧
        p.TwoRound (Fintype.card Validator) f q) ∨
      (p.voteIsCert = false ∧ 3 ≤ p.waveLength ∧ p.linkSize = 1 ∧
        p.ThreeRound (Fintype.card Validator) f q)) →
    (∀ t, (W t).ids ⊆ (W (t + 1)).ids) → (∀ t, N t ≤ N (t + 1)) →
    ∀ t, consumed p σ U lo W N (t + 1) = tryDecide p σ U (W t) lo (N t)

/-- The loop's claims. -/
def Statement : Prop :=
  Sound ∧ PrefixComparable ∧ Complete ∧ OutputComplete ∧ Restart ∧ Resume ∧ Repeated

end Loop

end Scheme

end LeanDag
