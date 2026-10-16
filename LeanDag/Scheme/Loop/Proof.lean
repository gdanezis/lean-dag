import LeanDag.Scheme.Loop.Statement
import LeanDag.Scheme.Helpers.TryDecide
/-!
# The commit loop — proof

Soundness by induction down the scan (`Helpers/TryDecide.lean`); prefix
comparability from soundness and the laws of `Helpers/Sufficiency.lean`.
-/

namespace LeanDag

namespace Scheme

namespace Loop

theorem sound : Sound := by
  intro Validator BlockId Payload _ _ _ P honest p σ S U V lo N hl hc hlo
  exact tryDecide_sound hl hc hlo

theorem prefixComparable : PrefixComparable := by
  intro Validator BlockId Payload _ _ _ P _ q _ honest Hon f p σ S U V₁ V₂ lo N₁ N₂
    hHon hq hne hfam h₁ h₂
  rcases hfam with ⟨hv, -, hl, hineq⟩ | ⟨hv, hw, hl, hineq⟩
  · exact tryDecide_prefix hl (fun h => absurd (hv.symm.trans h) (by simp))
      (twoRoundLaws σ hv hHon hq hineq) hne h₁ h₂ V₁ V₂
  · exact tryDecide_prefix (by omega) (fun _ => by
        obtain ⟨ha, -, -⟩ := hineq; omega)
      (threeRoundLaws σ hv hw hHon hq hl hineq) hne h₁ h₂ V₁ V₂

theorem holds : Statement := ⟨sound, prefixComparable⟩

end Loop

end Scheme

end LeanDag
