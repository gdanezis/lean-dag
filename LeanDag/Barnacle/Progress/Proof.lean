import LeanDag.Barnacle.Progress.Statement
import LeanDag.Barnacle.Helpers.Progress
/-!
# BN8 — proof

Generated proof layer; not part of the audit surface. BN8a is
`progress_exists` with the bound forgotten; BN8b is `everyHeight_bound`,
the induction on the height that carries `start K ≤ K · (maxInterval + 1 + c)`.
-/

namespace LeanDag

namespace Barnacle

namespace Progress

theorem holds : Statement := by
  intro Validator BlockId Payload _ _ _ R hR P upd hupd C₀ Q hupdh c
  refine ⟨?_, ?_⟩
  · intro U V Rnd N K hcov Rn hlive hgood hRnd hN
    exact progress hR hupd hcov Rn hlive hgood hRnd hN
  · intro hlive h₀ hQ₀ U V Rnd N hgood hcov hRnd K hK
    exact everyHeight hR hupd hupdh hlive h₀ hQ₀ hcov hgood hRnd K hK

end Progress

end Barnacle

end LeanDag
