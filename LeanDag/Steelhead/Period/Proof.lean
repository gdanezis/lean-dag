import LeanDag.Steelhead.Period.Statement
import LeanDag.Steelhead.Helpers.Period
/-!
# The period sequence — proof

Generated proof layer; not part of the audit surface. Each conjunct is
the helper of the same name in `Helpers/Period.lean`.
-/

namespace LeanDag

namespace Steelhead

namespace Period

theorem holds : Statement := by
  intro Validator BlockId Payload _ _ _ _ S U ws wa I K
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro coin upd k₀ V₁ V₂ w j st₁ st₂ hwa h₁ h₂
    exact periodAt_unique hwa h₁ h₂
  · intro coin known upd k₀ N V₁ V₂ per₁ per₂ k v₁ v₂ hws hwa hN hk h₁ h₂ d₁ d₂
    exact ⟨adaptive_periods_agree hws hwa h₁ h₂, adaptive_decided_unique hws hwa hN hk h₁ h₂ d₁ d₂⟩
  · intro coin upd k₀ V w j st hw hp hall
    exact exists_periodAt_succ hw hp hall
  · intro coin upd k₀ V w c N hwa hI hw hrun hV j hN
    exact periodAt_of_clause hwa hI hw hrun hV j hN
  · intro coin upd k₀ V w j r next' last' st A hA hp ha hadv h
    exact periodAt_one_of_anchor hp ha hadv h
  · intro j k hk hI
    exact two_async_rounds hk hI
  · intro coin upd k₀ V w j st h₀ hK hupd hp
    exact periodAt_mem_range h₀ hK hupd hp
  · intro coin upd k₀ V w j st hw hp
    exact decided_of_lt_next hw hp
  · intro coin upd k₀ V w j s st hw hid hp h₁ hund
    exact stalled_below_undecided hw hid hp h₁ hund
  · intro k top hk hK hwa hI htop
    exact window_resolves hk hK hwa hI htop
  · intro coin upd k₀ V per s j₁ r₁ b A hws hle hwa hid hI hper hlead h₁ hs hA hb hgood hV
    exact output_liveness hws hle hwa hid hI hper hlead h₁ hs hA hb hgood hV
  · intro coin upd k₀ V per c N hws hle hwa hid hI hlead hwaK hcK hrun hV hper s h₁ hN
    exact all_decided hws hle hwa hid hI hlead hwaK hcK hrun hV hper s h₁ hN
  · intro coin upd k₀ V per s j b hws hle hwa hid hI hlead hper h₁ hs hgood hb hgoodb hV
    exact output_liveness_of_runs hws hle hwa hid hI hlead hper h₁ hs hgood hb hgoodb hV

end Period

end Steelhead

end LeanDag
