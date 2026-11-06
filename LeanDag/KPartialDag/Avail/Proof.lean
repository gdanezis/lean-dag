import LeanDag.KPartialDag.Avail.Statement
import LeanDag.KPartialDag.Helpers.Avail
/-!
# The available sub-DAG — proof

Each result is a helper of `Helpers/Avail.lean`.
-/

namespace LeanDag

namespace KPartialDag

namespace Avail

theorem held : Held := by
  intro Validator BlockId Payload _ _ _ _ _ U K A hK hA hV z hz
  exact avail_correctHeld hK hA hV hz

theorem broad : Broad := by
  intro Validator BlockId Payload _ _ _ _ _ U K A ρ hsp hK hA hρ
  obtain ⟨x, hx, hxr, hxc, hxa⟩ :=
    KPartialDag.broad hsp hK hA ((U.block A).round - (ρ + 2)) (by omega)
  exact ⟨x, hx, by omega, hxc, hxa⟩

theorem core : Core := by
  intro Validator BlockId Payload _ _ _ _ _ U z hz hzr
  exact exists_core hz hzr

theorem linked : Linked := by
  intro Validator BlockId Payload _ _ _ _ _ p U K A L r hrow hK hA hr hd
  exact KPartialDag.linked hrow hK hA hr hd

theorem exclusive : Exclusive := by
  intro Validator BlockId Payload _ _ _ _ _ p U K A L r hrow hl
  exact not_directSkip hrow hl

theorem holds : Statement := ⟨held, broad, core, linked, exclusive⟩

end Avail

end KPartialDag

end LeanDag
