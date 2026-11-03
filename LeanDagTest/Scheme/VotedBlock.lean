import LeanDag.Scheme.Helpers.VotedBlock
import LeanDag.Scheme.Model.LeastSel
import LeanDagTest.MahiMahi.Model
/-!
# The scheme's vote and the least vote name different twins

On Mahi-Mahi's `twin4`, block `8` holds both round-`0` twins of validator
`0` in its history: twin `0` through block `5` and twin `4` through block
`6`. The least vote names twin `0`; the scheme's depth-first vote names
whichever twin its parent order reaches first.
-/

namespace LeanDagTest

namespace Scheme

open LeanDag LeanDag.Scheme

/-- Parents in ascending order. -/
def ascOrd : Fin 9 → Finset (Fin 9) → List (Fin 9) := fun _ s => (List.finRange 9).filter (· ∈ s)

/-- Parents in descending order. -/
def descOrd : Fin 9 → Finset (Fin 9) → List (Fin 9) := fun _ s =>
  (List.finRange 9).reverse.filter (· ∈ s)

-- The least vote names twin `0`.
example : (leastSel : VoteSel (Fin 4) (Fin 9) Unit ValidWrt Correct).sel twin4 8 0 0 = some 0 := by
  decide

-- The scheme's vote in ascending order agrees …
example : votedBlock ascOrd twin4 8 0 0 = some 0 := by decide

-- … and in descending order names twin `4`.
example : votedBlock descOrd twin4 8 0 0 = some 4 := by decide

-- Both orders list every parent, so both are vote-selection rules.
example : ∀ b s (x : Fin 9), x ∈ descOrd b s ↔ x ∈ s := fun _ _ x => by
  simp [descOrd, List.mem_finRange]

end Scheme

end LeanDagTest
