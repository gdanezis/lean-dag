import LeanDag.KPartialDag.Model.Rule
import LeanDag.Scheme.Model.Rule
/-!
# Agreement of the commit rule — statement

`docs/kpartial.md` §4, Theorem 2. At a row of the scheme and its depth, the
commit rule (`kRule`) satisfies the laws of an anchored rule (`Laws`), so any
two views of one record decide each slot alike (`Agrees`). Its direct tests
are the scheme's at every vote-selection rule, and its link is a scheme
link (`Conforms`); Mysticeti, Cordial Miners and Blue Bottle are rows
without crashes, and Hybrid Mysticeti and Orcaella under a crash bound
(`Rows`).

Statements only; the proofs are `Proof.lean`.
-/

namespace LeanDag

namespace KPartialDag

namespace Agreement

open Scheme

/-- **The laws of an anchored rule** hold of the commit rule at a row of the
scheme and its depth. -/
def Laws : Prop :=
  ∀ (Validator BlockId Payload : Type) [Fintype Validator] [DecidableEq Validator]
    [Faults Validator] [Crashes Validator]
    [LinearOrder BlockId] (p : Params) (K : ℕ), Row Validator p → kDepth Validator p ≤ K →
    (kRule (Validator := Validator) (BlockId := BlockId) (Payload := Payload) p K).Laws

/-- **Two views decide each slot alike**: at a row of the scheme and its depth,
decisions of a slot by the commit rule on two views of one record are
equal. -/
def Agrees : Prop :=
  ∀ (Validator BlockId Payload : Type) [Fintype Validator] [DecidableEq Validator]
    [Faults Validator] [Crashes Validator] [LinearOrder BlockId] [S : Slots Validator] (p : Params)
    (U : KRecord Validator BlockId Payload) (K : ℕ) (V₁ V₂ : U.View) (k : ℕ)
    (v₁ v₂ : Option BlockId), Row Validator p → kDepth Validator p ≤ K →
    (kRule p K).Decided (S := S) U V₁ k v₁ →
    (kRule p K).Decided (S := S) U V₂ k v₂ → v₁ = v₂

/-- **The rule is the scheme's, linked through the sub-DAG**: at a row and
every vote-selection rule, the certificates of a block and the blames of a
slot are the scheme's, and a link through the sub-DAG below a block of the
record is a scheme link from it. -/
def Conforms : Prop :=
  ∀ (Validator BlockId Payload : Type) [Fintype Validator] [DecidableEq Validator]
    [Faults Validator] [Crashes Validator] [LinearOrder BlockId] [Slots Validator] (p : Params)
    (σ : VoteSel Validator BlockId Payload (KValid Validator BlockId Payload) Correct)
    (U : KRecord Validator BlockId Payload) (K : ℕ) (A L : BlockId) (k : ℕ), Row Validator p →
    certsAt p σ U L (U.block L).round = certsFor p U L (U.block L).round ∧
      blamersAt p σ U k = slotBlamers U k ∧
      (A ∈ U.ids → AvailLinked p U K A L (U.block L).round →
        p.linkSize ≤ (creatorsOf U.block (linkCerts p σ U A L (U.block L).round)).card)

/-- **Rows of the scheme**: with no crash bound, Mysticeti and Cordial
Miners are live rows of the substrate, and Blue Bottle is at `n ≥ 5f + 1`;
under any crash bound, Hybrid Mysticeti is, and Orcaella is at
`n ≥ 5f + 3c + 1`. -/
def Rows : Prop :=
  ∀ (Validator : Type) [Fintype Validator] [DecidableEq Validator] [F : Faults Validator]
    [Cr : Crashes Validator],
    (Cr.c = 0 → Row Validator (Params.mysticeti (Fintype.card Validator) F.f) ∧
      LiveRow Validator (Params.mysticeti (Fintype.card Validator) F.f)) ∧
    (Cr.c = 0 → Row Validator (Params.cordialMinersPS (Fintype.card Validator) F.f) ∧
      LiveRow Validator (Params.cordialMinersPS (Fintype.card Validator) F.f)) ∧
    (Cr.c = 0 → 5 * F.f + 1 ≤ Fintype.card Validator →
      Row Validator (Params.blueBottlePS (Fintype.card Validator) F.f) ∧
        LiveRow Validator (Params.blueBottlePS (Fintype.card Validator) F.f)) ∧
    (Row Validator (Params.hybridMysticeti (Fintype.card Validator) F.f Cr.c) ∧
      LiveRow Validator (Params.hybridMysticeti (Fintype.card Validator) F.f Cr.c)) ∧
    (5 * F.f + 3 * Cr.c + 1 ≤ Fintype.card Validator →
      Row Validator (Params.orcaella (Fintype.card Validator) F.f Cr.c) ∧
        LiveRow Validator (Params.orcaella (Fintype.card Validator) F.f Cr.c))

/-- Agreement of the commit rule. -/
def Statement : Prop := Laws ∧ Agrees ∧ Conforms ∧ Rows

end Agreement

end KPartialDag

end LeanDag
