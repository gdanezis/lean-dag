import LeanDag.Scheme.Model.Rule
import LeanDag.Properties.Agree
import LeanDag.Common.Anchored.Band
/-!
# The table's inequalities suffice for agreement — statement

`docs/scheme.md` §7. A record is read with three numbers: `n` validators,
blocks that reference `q` distinct authors one round down, and a set
`Hon` of validators that never equivocate, with at most `f` outside it.
Crash faults enter only through `q`. At every vote-selection rule:

* a row whose vote is its certificate and whose wave is at least two,
  meeting `Params.TwoRound n f q`, decides alike from two views;
* a row that certifies votes one round later, with a wave of at least
  three and a link of one certificate, meeting `Params.ThreeRound n f q`,
  decides alike from two views.

The derived rows follow: Hybrid Mysticeti and Hybrid Mahi-Mahi at
`n = 3f + 2c + 1` and `q = 2f + c + 1`, and Orcaella and Async Orcaella
at every `n ≥ 5f + 3c + 1` and `q = n − f − c`.

Statements only; the proofs are `Proof.lean`.
-/

namespace LeanDag

namespace Scheme

namespace Sufficiency

open LeanDag.Properties

/-- **The two-round inequalities give agreement.** -/
def TwoRoundAgree : Prop :=
  ∀ (Validator BlockId Payload : Type) [Fintype Validator] [DecidableEq Validator]
    [LinearOrder BlockId] (P : Validity Validator BlockId Payload) [P.Mechanised]
    (q : ℕ) [P.Quorate q] (honest Hon : Finset Validator) (f : ℕ) (p : Params)
    (σ : VoteSel Validator BlockId Payload P honest),
    Honᶜ.card ≤ f → q ≤ Fintype.card Validator →
    p.voteIsCert = true → 2 ≤ p.waveLength → p.TwoRound (Fintype.card Validator) f q →
    Agree ((schemeAnchored p σ).toDagRuleOn (fun U => U.NoEquivOn Hon))

/-- **The three-round inequalities give agreement**, at a link of one
certificate. -/
def ThreeRoundAgree : Prop :=
  ∀ (Validator BlockId Payload : Type) [Fintype Validator] [DecidableEq Validator]
    [LinearOrder BlockId] (P : Validity Validator BlockId Payload) [P.Mechanised]
    (q : ℕ) [P.Quorate q] (honest Hon : Finset Validator) (f : ℕ) (p : Params)
    (σ : VoteSel Validator BlockId Payload P honest),
    Honᶜ.card ≤ f → q ≤ Fintype.card Validator →
    p.voteIsCert = false → 3 ≤ p.waveLength → p.linkSize = 1 →
    p.ThreeRound (Fintype.card Validator) f q →
    Agree ((schemeAnchored p σ).toDagRuleOn (fun U => U.NoEquivOn Hon))

/-- **The derived three-round rows agree**: Hybrid Mysticeti, and Hybrid
Mahi-Mahi at every wave `w ≥ 3`, at `n = 3f + 2c + 1` and
`q = 2f + c + 1`. -/
def HybridRowsAgree : Prop :=
  ∀ (Validator BlockId Payload : Type) [Fintype Validator] [DecidableEq Validator]
    [LinearOrder BlockId] (P : Validity Validator BlockId Payload) [P.Mechanised]
    (f c : ℕ) [P.Quorate (2 * f + c + 1)] (honest Hon : Finset Validator)
    (σ : VoteSel Validator BlockId Payload P honest),
    Honᶜ.card ≤ f → Fintype.card Validator = 3 * f + 2 * c + 1 →
    Agree ((schemeAnchored (Params.hybridMysticeti (Fintype.card Validator) f c) σ).toDagRuleOn
      (fun U => U.NoEquivOn Hon)) ∧
    ∀ w, 3 ≤ w →
      Agree ((schemeAnchored (Params.hybridMahiMahi w (Fintype.card Validator) f c) σ).toDagRuleOn
        (fun U => U.NoEquivOn Hon))

/-- **Orcaella and Async Orcaella agree** at every `n ≥ 5f + 3c + 1` and
`q = n − f − c`, above the bound included. -/
def OrcaellaRowsAgree : Prop :=
  ∀ (Validator BlockId Payload : Type) [Fintype Validator] [DecidableEq Validator]
    [LinearOrder BlockId] (P : Validity Validator BlockId Payload) [P.Mechanised]
    (f c : ℕ) [P.Quorate (Fintype.card Validator - f - c)] (honest Hon : Finset Validator)
    (σ : VoteSel Validator BlockId Payload P honest),
    Honᶜ.card ≤ f → 5 * f + 3 * c + 1 ≤ Fintype.card Validator →
    Agree ((schemeAnchored (Params.orcaella (Fintype.card Validator) f c) σ).toDagRuleOn
      (fun U => U.NoEquivOn Hon)) ∧
    Agree ((schemeAnchored (Params.asyncOrcaella (Fintype.card Validator) f c) σ).toDagRuleOn
      (fun U => U.NoEquivOn Hon))

/-- The two families, and the rows they give. -/
def Statement : Prop :=
  TwoRoundAgree ∧ ThreeRoundAgree ∧ HybridRowsAgree ∧ OrcaellaRowsAgree

end Sufficiency

end Scheme

end LeanDag
