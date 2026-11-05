import LeanDag.KPartialDag.Model.Order
/-!
# K-partial DAG — bands of rounds

`docs/kpartial.md` §10. The band of rounds from `ρ` (`Band`), the blocks
between two rounds (`Between`), equivocation-free records (`EquivFree`), a
node's obligation when it builds (`Obliged`), and the layer bound
(`layerBound`).
-/

namespace LeanDag

namespace KPartialDag

variable {Validator : Type*} [Fintype Validator] [DecidableEq Validator] [F : Faults Validator]
variable {BlockId : Type*} [DecidableEq BlockId] {Payload : Type*}

/-- The blocks of `H` at round `ρ` or above. -/
def Band (U : KRecord Validator BlockId Payload) (H : Finset BlockId) (ρ : ℕ) : Finset BlockId :=
  H.filter fun b => ρ ≤ (U.block b).round

/-- The blocks of the record at rounds `lo` to `hi`. -/
def Between (U : KRecord Validator BlockId Payload) (lo hi : ℕ) : Finset BlockId :=
  U.ids.filter fun b => lo ≤ (U.block b).round ∧ (U.block b).round ≤ hi

/-- No author has two blocks at one round from `lo` to `hi`. -/
def EquivFree (U : KRecord Validator BlockId Payload) (lo hi : ℕ) : Prop :=
  ∀ i ∈ U.ids, ∀ j ∈ U.ids, lo ≤ (U.block i).round → (U.block i).round ≤ hi →
    (U.block j).round = (U.block i).round → (U.block i).creator = (U.block j).creator → i = j

/-- **The download obligation**: a node holding `H` holds the history to depth
`K` of each reference of `b`. -/
def Obliged (U : KRecord Validator BlockId Payload) (K : ℕ) (H : Finset BlockId)
    (b : Block Validator BlockId Payload) : Prop :=
  ∀ x ∈ b.refs, historyUpto U K x ⊆ H

/-- **The bound on one layer of a history**: `N_0 = 1` and
`N_{d+1} = c + f · N_d`, for `c` correct validators and `f` faults. -/
def layerBound (c f : ℕ) : ℕ → ℕ
  | 0 => 1
  | d + 1 => c + f * layerBound c f d

end KPartialDag

end LeanDag
