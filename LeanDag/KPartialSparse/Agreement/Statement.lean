import LeanDag.KPartialSparse.Model.Rule
/-!
# Sparse K-partial DAG — agreement, statement

`docs/kpartial-sparse.md` §4, Theorem 2: at a three-round row with claims for
certificates, under the spreading condition and at `K ≥ 6`, the commit rule
meets the laws of an anchored rule on a disciplined schedule and record, so
two views decide each slot alike; Mysticeti, Cordial Miners and Hybrid
Mysticeti are such rows.

Statements only; the proofs are `Proof.lean`.
-/

namespace LeanDag

namespace KPartialSparse

namespace Agreement

open KPartialDag Scheme

/-- **The laws of an anchored rule** hold of the commit rule at a row, under
the spreading condition, at `K ≥ 6`, on a disciplined schedule and record. -/
def Laws : Prop :=
  ∀ (Validator BlockId Payload : Type) [Fintype Validator] [DecidableEq Validator]
    [Faults Validator] [Crashes Validator] [Leaders Validator]
    [LinearOrder BlockId] [ClaimFormat BlockId Payload] (p : Params) (K : ℕ),
    Row Validator p → Spread Validator → 6 ≤ K →
    (sRule (Validator := Validator) (BlockId := BlockId) (Payload := Payload) p K).Laws
      (Disciplined K p.certThreshold)

/-- **Two views decide each slot alike**: at a row, under the spreading
condition, at `K ≥ 6`, on a disciplined schedule and record, decisions of a
slot by the commit rule on two views of one record are equal. -/
def Agrees : Prop :=
  ∀ (Validator BlockId Payload : Type) [Fintype Validator] [DecidableEq Validator]
    [Faults Validator] [Crashes Validator] [Leaders Validator] [LinearOrder BlockId]
    [ClaimFormat BlockId Payload] [S : Slots Validator] (p : Params)
    (U : SRecord Validator BlockId Payload) (K : ℕ) (V₁ V₂ : U.View) (k : ℕ)
    (v₁ v₂ : Option BlockId), Row Validator p → Spread Validator → 6 ≤ K →
    Disciplined K p.certThreshold S U →
    (sRule p K).Decided (S := S) U V₁ k v₁ → (sRule p K).Decided (S := S) U V₂ k v₂ → v₁ = v₂

/-- **Rows of the scheme**: with no crash bound, Mysticeti and Cordial Miners
are rows and the spreading condition holds; under any crash bound, Hybrid
Mysticeti is a row. -/
def Rows : Prop :=
  ∀ (Validator : Type) [Fintype Validator] [DecidableEq Validator] [F : Faults Validator]
    [Cr : Crashes Validator],
    (Cr.c = 0 → Row Validator (Params.mysticeti (Fintype.card Validator) F.f) ∧
      Spread Validator) ∧
    (Cr.c = 0 → Row Validator (Params.cordialMinersPS (Fintype.card Validator) F.f)) ∧
    Row Validator (Params.hybridMysticeti (Fintype.card Validator) F.f Cr.c)

/-- Agreement of the commit rule. -/
def Statement : Prop := Laws ∧ Agrees ∧ Rows

end Agreement

end KPartialSparse

end LeanDag
