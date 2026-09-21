import LeanDag.RedSnapper.Revocation.Statement
import LeanDag.RedSnapper.Helpers.Revocation

/-!
# The limits of vote revocation — proof

Generated proof layer; not part of the audit surface. The support bound
is a union-and-intersection count with the intersection inside the
Byzantine set; sufficiency and the committee corollaries are `omega`
over it and the committee bound; tightness and the reverse exposure
direction exhibit the profiles of `Helpers/Revocation.lean`; the
pigeonhole direction covers a collection of voters by its two sides.
-/

namespace LeanDag

namespace RedSnapper

namespace Revocation

theorem holds : Statement :=
  ⟨fun _ _ _ _ _ P x C => ⟨supportBound P x, sufficient P x C⟩,
    tight,
    exposureIff,
    strictThresholdIff,
    fun Validator _ _ _ =>
      ⟨thresholdAtQuorum Validator, strictAtQuorum Validator, exposureAtQuorum Validator⟩⟩

end Revocation

end RedSnapper

end LeanDag
