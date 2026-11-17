import LeanDag.KPartialSparse.Avail.Statement
import LeanDag.KPartialSparse.Helpers.Avail
/-!
# Sparse K-partial DAG — the available sub-DAG, proof

Each result is a helper of `Helpers/Avail.lean`.
-/

namespace LeanDag

namespace KPartialSparse

namespace Avail

theorem linked : Linked := by
  intro Validator BlockId Payload _ _ _ _ _ _ _ U K cm ρ A L hdeep hch hA hAl hAr hcm hcl
  exact KPartialSparse.linked hdeep hch hA hAl hAr hcm hcl

theorem backed : Backed := by
  intro Validator BlockId Payload _ _ _ _ _ _ _ U K t A hck hA X hX L hL
  exact KPartialSparse.backed hck hA hX hL

theorem held : Held := by
  intro Validator BlockId Payload _ _ _ _ _ _ U K A hA X hX
  exact avail_correctHeld hA hX

theorem holds : Statement := ⟨linked, backed, held⟩

end Avail

end KPartialSparse

end LeanDag
