import LeanDag.RedSnapper.Model.Universe

/-!
# Block lemmas and decidability

Generated infrastructure over `Model/Block.lean` and
`Model/Universe.lean`. Nothing here is part of the audit surface.
-/

namespace LeanDag

namespace RedSnapper

variable {Validator BlockId Tx Obj : Type*} [Fintype Validator] [DecidableEq Validator]
  [F : Faults Validator]

/-- `ValidWrt` is decidable on concrete data: lets hand-built witness
DAGs be checked by `decide`. Not needed by any proof — a wrong instance
could not smuggle anything in anyway, since it still has to
kernel-check. -/
instance [DecidableEq BlockId] (blk : BlockId → Block Validator BlockId Tx Obj)
    (b : Block Validator BlockId Tx Obj) : Decidable (ValidWrt blk b) :=
  decidable_of_iff
    ((∀ i ∈ b.parents, (blk i).round + 1 = b.round) ∧
      (∀ i ∈ b.parents, ∀ j ∈ b.parents,
        (blk i).author = (blk j).author → i = j) ∧
      (0 < b.round → quorum Validator ≤ (authors blk b).card))
    ⟨fun h => ⟨h.1, h.2.1, h.2.2⟩,
      fun h => ⟨h.predecessor, h.distinct_authors, h.quorum⟩⟩

/-- `Conflict` and `Owned` are decidable on concrete data. -/
instance [DecidableEq Obj] [DecidableEq Tx] [T : Transactions Tx Obj] (tx tx' : Tx) :
    Decidable (Conflict tx tx') :=
  inferInstanceAs (Decidable (tx ≠ tx' ∧ T.input tx = T.input tx'))

instance [T : Transactions Tx Obj] (tx : Tx) : Decidable (Owned tx) :=
  inferInstanceAs (Decidable (¬ T.Mixed tx))

/-- Genesis blocks reference nothing: at round `0` the (additive)
predecessor condition is unsatisfiable — the derivation promised in the
`ValidWrt` docstring. -/
theorem ValidWrt.parents_empty_of_round_zero
    {blk : BlockId → Block Validator BlockId Tx Obj} {b : Block Validator BlockId Tx Obj}
    (hv : ValidWrt blk b) (h0 : b.round = 0) : b.parents = ∅ := by
  by_contra h
  obtain ⟨i, hi⟩ := Finset.nonempty_iff_ne_empty.mpr h
  have := hv.predecessor i hi
  omega

end RedSnapper

end LeanDag
