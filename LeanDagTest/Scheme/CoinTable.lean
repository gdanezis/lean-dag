import LeanDag.Scheme.Helpers.CoinHeads
/-!
# A reputation table, on data

Four validators, `f = 1`, quorum `q = 3`. A reputation table of six entries
that leaves validator `0` out and gives validators `1`, `2` and `3` two
entries each supports a quorum (`k = 3`) with weight `e = 2`. With two buffer
rounds the safe set holds at least `q − f = 2` validators, and every such set
meets the support: the table hits it in at least `2 · (3 + 2 − 4) = 2`
entries (`card_hits_ge`), so the coin names a safe leader with probability at
least `2/6`.
-/

namespace LeanDagTest

namespace CoinTable

open LeanDag LeanDag.Scheme

/-- Validators `1`, `2`, `3`, two entries each. -/
def tbl : Fin 6 → Fin 4 := fun j => ⟨j.val / 2 + 1, by omega⟩

theorem tbl_supports : Supports tbl 3 2 :=
  ⟨{1, 2, 3}, by decide, by decide⟩

/-- Every pair of validators is hit at least twice. -/
example (S : Finset (Fin 4)) (hS : 2 ≤ S.card) :
    2 ≤ (Finset.univ.filter fun j => tbl j ∈ S).card := by
  have := card_hits_ge (s := 2) tbl_supports hS
  simpa using this

/-- Even the pair avoiding most of the support, `{0, 1}`, is hit twice. -/
example : (Finset.univ.filter fun j => tbl j ∈ ({0, 1} : Finset (Fin 4))).card = 2 := by decide

end CoinTable

end LeanDagTest

#print axioms LeanDag.Scheme.card_hits_ge
