import LeanDag.KPartialDag.Bounds.Statement
import LeanDag.KPartialDag.Helpers.Bounds
/-!
# Bounds for deciding and restarting — proof

Each result is a helper of `Helpers/Bounds.lean`.
-/

namespace LeanDag

namespace KPartialDag

namespace Bounds

theorem decides : Decides := by
  intro Validator BlockId Payload _ _ _ _ S U K H ρ i v hH h1 h2
  exact nodeDecided_band_iff hH h1 h2

theorem progress : Progress := by
  intro Validator BlockId Payload _ _ _ _ S K T c hc hspan fair R k
  obtain ⟨b, hkb, hRb, hrun⟩ := Slots.exists_run_past fair k R
  exact ⟨b, hkb, hRb, fun U h H ρ hH hW hav =>
    nodeDecided_of_run_band h.1 hH hc hspan (responds_of_run hc hRb hrun h) hW hav⟩

theorem builds : Builds := by
  intro Validator BlockId Payload _ _ _ _ U K H Q r b hQ hd hq hwin hbr hbQ
  exact ⟨validAt_of_quorum (fun x hx => (hQ x hx).2) hd hq hbr hbQ, obliged_band hQ hbQ hwin⟩

theorem resumes : Resumes := by
  intro Validator BlockId Payload _ _ _ _ S U K D H₁ H₂ g₁ g₂ s m hK hH₁ hH₂ hg₁ hg₂ hdec hf₁ hf₂
    b k hsk hkm
  have hagree : ∀ j, j < m → S.slotRound s ≤ S.slotRound j + D → g₁ j = g₂ j :=
    fun j hj hr => (hdec j hj hr).1.agree hK hH₁ hH₂ (hdec j hj hr).2
  exact ⟨entersIn_resume hH₁ hH₂ hg₁ hg₂ hagree hf₁ hf₂ hsk hkm,
    entersIn_resume hH₂ hH₁ hg₂ hg₁ (fun j hj hr => (hagree j hj hr).symm) hf₂ hf₁ hsk hkm⟩

theorem counts : Counts := by
  intro Validator BlockId Payload _ _ _ _ U lo hi hE
  exact card_between_le hE

theorem window : Window := by
  intro Validator BlockId Payload _ _ _ _ U K x hx
  exact ⟨historyUpto_subset_between hx, card_historyUpto_le K hx⟩

theorem availRound : AvailRound := by
  intro Validator BlockId Payload _ _ _ _ U K A ρ hA
  refine ⟨fun X hX => ?_, fun Z hZ => card_avail_round_le hA hZ⟩
  have := card_anchored_le hA (B := Finset.univ) fun x hx =>
    ⟨(hX x hx).1, (hX x hx).2.1, (hX x hx).2.2, Finset.mem_univ _⟩
  rwa [Finset.card_univ] at this

theorem holds : Statement := ⟨decides, progress, builds, resumes, counts, window, availRound⟩

end Bounds

end KPartialDag

end LeanDag
