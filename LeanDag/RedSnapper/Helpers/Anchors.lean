import LeanDag.RedSnapper.Helpers.CausalHistory
import LeanDag.RedSnapper.Model.Anchors

/-!
# Anchor lemmas

Generated infrastructure over `Model/Anchors.lean`: membership and
chaining read off by index, and the full view. Nothing here is part of
the audit surface.
-/

namespace LeanDag

namespace RedSnapper

variable {Validator BlockId Tx Obj : Type*} [Fintype Validator] [DecidableEq Validator]
  [F : Faults Validator] {U : Universe Validator BlockId Tx Obj}

/-- The full view: the whole universe as one validator's local DAG. -/
def View.full (U : Universe Validator BlockId Tx Obj) : View U :=
  ⟨U.ids, Finset.Subset.refl _, U.complete⟩

/-- An indexed anchor is a block of the universe. -/
theorem anchor_mem_ids {A : Anchors U} {i : ℕ} {a : BlockId}
    (h : A.seq[i]? = some a) : a ∈ U.ids :=
  A.mem a (List.mem_of_getElem? h)

/-- A later anchor reaches an earlier one. -/
theorem anchor_reaches {A : Anchors U} {i j : ℕ} {a b : BlockId}
    (hij : i ≤ j) (hi : A.seq[i]? = some a) (hj : A.seq[j]? = some b) :
    Reaches U b a := by
  obtain ⟨hi', ha⟩ := List.getElem?_eq_some_iff.mp hi
  obtain ⟨hj', hb⟩ := List.getElem?_eq_some_iff.mp hj
  subst ha hb
  rcases Nat.lt_or_ge i j with hlt | hge
  · exact List.pairwise_iff_getElem.mp A.chained i j hi' hj' hlt
  · have : i = j := by omega
    subst this
    exact Reaches.refl

end RedSnapper

end LeanDag
