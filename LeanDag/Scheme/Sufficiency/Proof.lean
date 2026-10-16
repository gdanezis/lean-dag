import LeanDag.Scheme.Sufficiency.Statement
import LeanDag.Scheme.Helpers.Sufficiency
import LeanDag.Scheme.Table.Proof
/-!
# The table's inequalities suffice for agreement — proof

Each family's laws (`Helpers/Sufficiency.lean`) give agreement under the
invariant; the derived rows meet their family's inequalities by
`Table.holds`.
-/

namespace LeanDag

namespace Scheme

namespace Sufficiency

theorem twoRoundAgree : TwoRoundAgree := by
  intro Validator BlockId Payload _ _ _ P _ q _ honest Hon f p σ hHon hq hv hw hineq
  exact AnchoredRule.agreeOn (twoRoundLaws σ hv hHon hq hineq) (fun _ _ h => h)

theorem threeRoundAgree : ThreeRoundAgree := by
  intro Validator BlockId Payload _ _ _ P _ q _ honest Hon f p σ hHon hq hv hw hl hineq
  exact AnchoredRule.agreeOn (threeRoundLaws σ hv hw hHon hq hl hineq) (fun _ _ h => h)

theorem hybridRowsAgree : HybridRowsAgree := by
  intro Validator BlockId Payload _ _ _ P _ f c _ honest Hon σ hHon hn
  obtain ⟨-, -, -, -, -, -, -, hm, hmm⟩ := Table.holds.1 f c
  rw [hn]
  refine ⟨threeRoundAgree Validator BlockId Payload P (2 * f + c + 1) honest Hon f _ σ hHon
    (by omega) rfl (show 3 ≤ 3 by omega) rfl (hn ▸ hm.1), fun w hw => ?_⟩
  exact threeRoundAgree Validator BlockId Payload P (2 * f + c + 1) honest Hon f _ σ hHon
    (by omega) rfl hw rfl (hn ▸ (hmm w).1)

theorem orcaellaRowsAgree : OrcaellaRowsAgree := by
  intro Validator BlockId Payload _ _ _ P _ f c _ honest Hon σ hHon hn
  obtain ⟨-, -, -, -, -, -, ho, -, -⟩ := Table.holds.1 f c
  obtain ⟨⟨h₁, -⟩, ⟨h₂, -⟩⟩ := ho _ hn
  exact ⟨twoRoundAgree Validator BlockId Payload P _ honest Hon f _ σ hHon (by omega) rfl
      (show 2 ≤ 2 by omega) h₁,
    twoRoundAgree Validator BlockId Payload P _ honest Hon f _ σ hHon (by omega) rfl
      (show 2 ≤ 3 by omega) h₂⟩

theorem twoRoundCrashAgree : TwoRoundCrashAgree := by
  intro Validator BlockId Payload _ _ _ P _ q _ honest Hon p σ hHon hq hv hw hineq
  exact AnchoredRule.agreeOn (twoRoundCrashLaws σ hv hHon hq hineq) (fun _ _ h => h)

theorem threeRoundCrashAgree : ThreeRoundCrashAgree := by
  intro Validator BlockId Payload _ _ _ P _ q _ honest Hon p σ hHon hq hv hw hl hineq
  exact AnchoredRule.agreeOn (threeRoundCrashLaws σ hv hw hHon hq hl hineq) (fun _ _ h => h)

theorem nemoRowsAgree : NemoRowsAgree := by
  intro Validator BlockId Payload _ _ _ P _ c _ honest Hon σ hHon hn
  obtain ⟨⟨h₁, -⟩, ⟨h₂, -⟩⟩ := Table.crashRows c
  rw [hn]
  exact ⟨twoRoundCrashAgree Validator BlockId Payload P (c + 1) honest Hon _ σ hHon (by omega)
      rfl (show 2 ≤ 2 by omega) (hn ▸ h₁),
    twoRoundCrashAgree Validator BlockId Payload P (c + 1) honest Hon _ σ hHon (by omega)
      rfl (show 2 ≤ 3 by omega) (hn ▸ h₂)⟩

theorem holds : Statement :=
  ⟨twoRoundAgree, threeRoundAgree, hybridRowsAgree, orcaellaRowsAgree, twoRoundCrashAgree,
    threeRoundCrashAgree, nemoRowsAgree⟩

end Sufficiency

end Scheme

end LeanDag
