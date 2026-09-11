import LeanDag.Adaptive.Score.Statement
/-!
# AL11 — proof

Generated proof layer; not part of the audit surface. Each clause is one
step: the view argument is ignored, `Score.Keeps` rewrites the two fields
`Config.InBounds` reads, the preservation clause passes through both
branches, and the constant score's two branches are the same pair.
-/

namespace LeanDag

namespace Adaptive

namespace Score

open Barnacle

variable {Validator : Type} [Fintype Validator] [DecidableEq Validator]
variable {BlockId : Type} [DecidableEq BlockId] {Payload : Type}
variable {R : BaseRule Validator BlockId Payload}

/-- **The rule is anchored**: it does not read the view, so two
validators holding the anchor take the same step. The clause AL13 asks
of an update rule. -/
theorem rule_anchored (score : Score R) : RuleAnchored R score :=
  fun _ _ _ _ _ _ _ => rfl

/-- **The rule keeps a configuration within the parameters**, from
`Score.Keeps` alone: `Config.InBounds` mentions the widths and the
interval, and the score moves neither. -/
theorem rule_bounded (P : Params) (score : Score R) : RuleBounded R P score := by
  intro hk C b U V v A h
  simp only [rule]
  split
  · obtain ⟨hs, hi⟩ := hk U _ v C
    exact ⟨fun r => hs ▸ h.1 r, hi ▸ h.2.1, hi ▸ h.2.2⟩
  · exact h

/-- **The rule keeps whatever the score keeps.** The clause AL16 asks of
an update rule is a clause on the score, and the fallback branch keeps
it because it changes nothing. -/
theorem rule_keeps (score : Score R) (Q : Config Validator → Prop) :
    RulePreserves R score Q := by
  intro hQ C b U V v A h
  simp only [rule]
  split
  · exact hQ _ _ _ _ h
  · exact h

/-- A permuting score keeps the shape, so AL11b applies to it. -/
@[simp] theorem permute_keeps (σ : Equiv.Perm Validator) :
    (Score.permute (R := R) σ).Keeps := fun _ _ _ _ => ⟨rfl, rfl⟩

@[simp] theorem const_keeps : (Score.const R).Keeps := fun _ _ _ _ => ⟨rfl, rfl⟩

/-- Under the constant score the rule is `constRule`, so AL15 is BN6's
statement at this arc's run. -/
theorem rule_const : ConstIsConst R := by
  funext C b U V v A
  simp only [rule, Score.const, constRule]
  split <;> rfl


theorem holds : Statement := fun _ _ _ _ _ _ R P score Q =>
  ⟨rule_anchored score, rule_bounded P score, rule_keeps score Q, rule_const⟩

end Score

end Adaptive

end LeanDag
