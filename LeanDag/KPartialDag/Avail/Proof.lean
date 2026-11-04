import LeanDag.KPartialDag.Avail.Statement
import LeanDag.KPartialDag.Helpers.Avail
/-!
# The available sub-DAG — proof

Each claim is a helper of `Helpers/Avail.lean`: `held`; `broad`, by a double
count over the references of a block two rounds up
(`exists_correct_referenced`); `linked`, from a block of round `r + 3` whose
references lie in the sub-DAG; and `not_directSkip`, by quorum intersection.
-/

namespace LeanDag

namespace KPartialDag

namespace Avail

theorem held : Held := by
  intro Validator BlockId Payload _ _ _ _ U K A z hz
  exact KPartialDag.held hz

theorem broad : Broad := by
  intro Validator BlockId Payload _ _ _ _ U K A ρ hK hA hρ
  obtain ⟨x, hx, hxr, hxc, hxa⟩ := KPartialDag.broad hK hA ((U.block A).round - (ρ + 2)) (by omega)
  exact ⟨x, hx, by omega, hxc, hxa⟩

theorem linked : Linked := by
  intro Validator BlockId Payload _ _ _ _ U K A L r hK hA hr hd
  exact KPartialDag.linked hK hA hr hd

theorem exclusive : Exclusive := by
  intro Validator BlockId Payload _ _ _ _ U K A L r hl
  obtain ⟨C, hC, -⟩ := hl
  exact not_directSkip hC

theorem holds : Statement := ⟨held, broad, linked, exclusive⟩

end Avail

end KPartialDag

end LeanDag
