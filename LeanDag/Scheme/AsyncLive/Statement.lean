import LeanDag.Scheme.Model.AsyncLive
import LeanDag.Scheme.Model.Async
import LeanDag.Scheme.Model.AsyncRow
import LeanDag.Scheme.Model.Deliver
import LeanDag.Steelhead.Coin.Statement
import Mathlib.Probability.Distributions.Uniform
import Mathlib.Topology.Instances.ENNReal.Lemmas
/-!
# The asynchronous rows across waves — statement

`docs/scheme.md` §11.2. The record and its asynchronous pacing are fixed
before the coins are drawn: the adversary does not see the coin. Slot `s`
is led by a coin; the coins of `M` blocks of `d` consecutive slots from
slot `s₀` are uniform and independent (`Steelhead.coinOfBlocksFrom`), on a
schedule `S₀` with strictly increasing rounds, of which every `d`
consecutive slots span eligibility. At every row and vote:

* **the tail** (`Tail`): when every block slot's safe set holds at least
  `c` validators, some slot below `s₀` stays undecided on a reliable
  validator's own view with probability at most `badBlockBoundAt c d ^ M`,
  `((n^d − c^d)/n^d)^M`;
* **it vanishes** (`Vanishes`) at a positive floor;
* **at the rows ready for the count** (`Live`): the floor is `1` at one
  buffer round, `q − f` at two, and `⌈n/3⌉` at one buffer round where
  `n ≥ 5f + 3c + 1` and `q = n − f − c`.

* **Validity at every asynchronous row** (`RowsValidity`), at its own
  committee and parent quorum `n − f − c`, under the weak-reference rule: a
  block of a reliable validator held by every reliable validator by `t`
  fails to be delivered by every reliable validator with probability at
  most `badBlockBoundAt 1 d ^ M`, over `M` blocks of `d` coins from a slot at
  round `t + 2` or above;
* **with probability 1** (`RowsValidityOne`): for every `ε > 0` some `M₀`
  makes that probability at most `ε` for every `M ≥ M₀`.

Statements only; the proofs are `Proof.lean`.
-/

namespace LeanDag

namespace Scheme

namespace AsyncLive

open Filter Topology
open scoped ENNReal

/-- **The tail**: the slots below the blocks stay undecided with
probability at most `badBlockBoundAt c d ^ M`. -/
def Tail : Prop :=
  ∀ (Validator BlockId Payload : Type) [Fintype Validator] [DecidableEq Validator]
    [Nonempty Validator] [LinearOrder BlockId] (P : Validity Validator BlockId Payload)
    [P.Mechanised] (q : ℕ) [P.Quorate q] (honest : Finset Validator) (p : Params)
    (σ : VoteSel Validator BlockId Payload P honest)
    (U : BlockRecord Validator BlockId Payload P honest) (T : Finset Validator) (N qp : ℕ)
    (ap : AsyncPace qp U T N) (S₀ : Slots Validator) (hS : StrictMono S₀.slotRound)
    (dflt : Validator) (s₀ d M c : ℕ),
    p.CertFits q → p.commitThreshold ≤ T.card → qp ≤ T.card → 0 < d →
    (schemeAnchored p σ).SpansEligible (S := S₀) d →
    S₀.slotRound (s₀ + M * d) + (p.waveLength - 1) ≤ N →
    (∀ s, s₀ ≤ s → s < s₀ + M * d → c ≤ (safeAt p U (S₀.slotRound s)).card) →
    (PMF.uniformOfFintype (Fin M → Fin d → Validator)).toOuterMeasure
        (ap.UndecidedBelow p σ S₀ hS dflt s₀ M d) ≤
      Steelhead.Coin.badBlockBoundAt Validator c d ^ M

/-- **The tail vanishes** at a positive floor. -/
def Vanishes : Prop :=
  ∀ (Validator : Type) [Fintype Validator] [Nonempty Validator] (c d : ℕ), 0 < c →
    Tendsto (fun M : ℕ => Steelhead.Coin.badBlockBoundAt Validator c d ^ M) atTop (𝓝 0)

/-- **The rows ready for the count are live across waves**, under pacing
at `q` with the reliable set at least `q` strong: the tail at floor `1` at
one buffer round, `q − f` at two, and `⌈n/3⌉` at one buffer round where
`n ≥ 5f + 3c + 1`, `q = n − f − c` and the reliable validators are honest. -/
def Live : Prop :=
  ∀ (Validator BlockId Payload : Type) [Fintype Validator] [DecidableEq Validator]
    [Nonempty Validator] [LinearOrder BlockId] (P : Validity Validator BlockId Payload)
    [P.Mechanised] (q : ℕ) [P.Quorate q] (honest : Finset Validator) (f b : ℕ) (p : Params)
    (σ : VoteSel Validator BlockId Payload P honest)
    (U : BlockRecord Validator BlockId Payload P honest) (T : Finset Validator) (N : ℕ)
    (ap : AsyncPace q U T N) (S₀ : Slots Validator) (hS : StrictMono S₀.slotRound)
    (dflt : Validator) (s₀ d M : ℕ),
    honestᶜ.card ≤ f → p.AsyncReady (Fintype.card Validator) f q b → q ≤ T.card → 0 < d →
    (schemeAnchored p σ).SpansEligible (S := S₀) d →
    S₀.slotRound (s₀ + M * d) + (p.waveLength - 1) ≤ N →
    (1 ≤ b → (PMF.uniformOfFintype (Fin M → Fin d → Validator)).toOuterMeasure
        (ap.UndecidedBelow p σ S₀ hS dflt s₀ M d) ≤
      Steelhead.Coin.badBlockBoundAt Validator 1 d ^ M) ∧
    (2 ≤ b → (PMF.uniformOfFintype (Fin M → Fin d → Validator)).toOuterMeasure
        (ap.UndecidedBelow p σ S₀ hS dflt s₀ M d) ≤
      Steelhead.Coin.badBlockBoundAt Validator (q - f) d ^ M) ∧
    (1 ≤ b → T ⊆ honest → ∀ c, 5 * f + 3 * c + 1 ≤ Fintype.card Validator →
      q + f + c = Fintype.card Validator →
      (PMF.uniformOfFintype (Fin M → Fin d → Validator)).toOuterMeasure
          (ap.UndecidedBelow p σ S₀ hS dflt s₀ M d) ≤
        Steelhead.Coin.badBlockBoundAt Validator ((Fintype.card Validator + 2) / 3) d ^ M)

/-- **Validity at every asynchronous row**, at its own committee and parent
quorum `n − f − c`, under the weak-reference rule. -/
def RowsValidity : Prop :=
  ∀ (Validator BlockId Payload : Type) [Fintype Validator] [DecidableEq Validator]
    [Nonempty Validator] [LinearOrder BlockId] (P : Validity Validator BlockId Payload)
    [P.Mechanised] (honest : Finset Validator) (p : Params) (f c b : ℕ)
    [P.Quorate (Fintype.card Validator - f - c)],
    p.AsyncRow (Fintype.card Validator) f c b → honestᶜ.card ≤ f →
    ∀ (σ : VoteSel Validator BlockId Payload P honest) (wk : BlockId → Finset BlockId)
      (U : BlockRecord Validator BlockId Payload P honest) (T : Finset Validator) (N : ℕ)
      (ap : AsyncPace (Fintype.card Validator - f - c) U T N) (built : Validator → ℕ → ℕ)
      (S₀ : Slots Validator) (hS : StrictMono S₀.slotRound) (dflt : Validator) (s₀ d M : ℕ),
      T ⊆ honest → Fintype.card Validator - f - c ≤ T.card → 0 < d →
      (schemeAnchored p σ).SpansEligible (S := S₀) d →
      S₀.slotRound (s₀ + M * d) + (p.waveLength - 1) ≤ N →
      WeakRule U wk T ap.holds built →
      (∀ v ∈ T, ∀ b ∈ U.ids, (U.block b).creator = v →
        (U.block b).round ≤ built v (U.block b).round) →
      ∀ (P_k : Validator) (m : BlockId) (t : ℕ),
        P_k ∈ T → m ∈ U.ids → (U.block m).creator = P_k → (U.block m).round ≤ t →
        (∀ v ∈ T, m ∈ ap.holds v t) → t + 2 ≤ S₀.slotRound s₀ →
        (PMF.uniformOfFintype (Fin M → Fin d → Validator)).toOuterMeasure
            {g | ¬ ∀ (P_j : Validator) (hj : P_j ∈ T),
              ap.Delivers (S := coinSlots S₀ hS (Steelhead.coinOfBlocksFrom s₀ g dflt))
                p σ wk hj m} ≤
          Steelhead.Coin.badBlockBoundAt Validator 1 d ^ M

/-- **Validity at every asynchronous row, with probability 1**: for every
`ε > 0` some number of coin blocks `M₀` makes the failure probability at
most `ε` from `M₀` on. -/
def RowsValidityOne : Prop :=
  ∀ (Validator BlockId Payload : Type) [Fintype Validator] [DecidableEq Validator]
    [Nonempty Validator] [LinearOrder BlockId] (d : ℕ) (ε : ℝ≥0∞), 0 < ε →
    ∃ M₀ : ℕ, ∀ M, M₀ ≤ M →
    ∀ (P : Validity Validator BlockId Payload)
      [P.Mechanised] (honest : Finset Validator) (p : Params) (f c b : ℕ)
      [P.Quorate (Fintype.card Validator - f - c)],
      p.AsyncRow (Fintype.card Validator) f c b → honestᶜ.card ≤ f →
      ∀ (σ : VoteSel Validator BlockId Payload P honest) (wk : BlockId → Finset BlockId)
        (U : BlockRecord Validator BlockId Payload P honest) (T : Finset Validator) (N : ℕ)
        (ap : AsyncPace (Fintype.card Validator - f - c) U T N) (built : Validator → ℕ → ℕ)
        (S₀ : Slots Validator) (hS : StrictMono S₀.slotRound) (dflt : Validator) (s₀ : ℕ),
        T ⊆ honest → Fintype.card Validator - f - c ≤ T.card → 0 < d →
        (schemeAnchored p σ).SpansEligible (S := S₀) d →
        S₀.slotRound (s₀ + M * d) + (p.waveLength - 1) ≤ N →
        WeakRule U wk T ap.holds built →
        (∀ v ∈ T, ∀ b ∈ U.ids, (U.block b).creator = v →
          (U.block b).round ≤ built v (U.block b).round) →
        ∀ (P_k : Validator) (m : BlockId) (t : ℕ),
          P_k ∈ T → m ∈ U.ids → (U.block m).creator = P_k → (U.block m).round ≤ t →
          (∀ v ∈ T, m ∈ ap.holds v t) → t + 2 ≤ S₀.slotRound s₀ →
          (PMF.uniformOfFintype (Fin M → Fin d → Validator)).toOuterMeasure
              {g | ¬ ∀ (P_j : Validator) (hj : P_j ∈ T),
                ap.Delivers (S := coinSlots S₀ hS (Steelhead.coinOfBlocksFrom s₀ g dflt))
                  p σ wk hj m} ≤ ε

/-- The asynchronous rows across waves. -/
def Statement : Prop := Tail ∧ Vanishes ∧ Live ∧ RowsValidity ∧ RowsValidityOne

end AsyncLive

end Scheme

end LeanDag
