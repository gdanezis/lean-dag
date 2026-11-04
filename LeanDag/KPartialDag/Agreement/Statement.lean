import LeanDag.KPartialDag.Model.Rule
/-!
# Agreement of the commit rule — statement

`docs/kpartial.md` §4. On a K-partial DAG, at `K ≥ 3`, the commit rule
(`kRule`) satisfies the laws of an anchored rule (`Laws`), so any two views of
one record decide each slot alike (`Agrees`).

Statements only; the proofs are `Proof.lean`.
-/

namespace LeanDag

namespace KPartialDag

namespace Agreement

/-- **The laws of an anchored rule** hold of the commit rule at `K ≥ 3`. -/
def Laws : Prop :=
  ∀ (Validator BlockId Payload : Type) [Fintype Validator] [DecidableEq Validator]
    [Faults Validator] [DecidableEq BlockId] (K : ℕ), 3 ≤ K →
    (kRule (Validator := Validator) (BlockId := BlockId) (Payload := Payload) K).Laws

/-- **Two views decide each slot alike**: at `K ≥ 3`, decisions of a slot
by the commit rule on two views of one record are equal. -/
def Agrees : Prop :=
  ∀ (Validator BlockId Payload : Type) [Fintype Validator] [DecidableEq Validator]
    [Faults Validator] [DecidableEq BlockId] [S : Slots Validator] (K : ℕ)
    (U : KRecord Validator BlockId Payload) (V₁ V₂ : U.View) (k : ℕ) (v₁ v₂ : Option BlockId),
    3 ≤ K → (kRule K).Decided (S := S) U V₁ k v₁ → (kRule K).Decided (S := S) U V₂ k v₂ →
    v₁ = v₂

/-- Agreement of the commit rule. -/
def Statement : Prop := Laws ∧ Agrees

end Agreement

end KPartialDag

end LeanDag
