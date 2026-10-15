import LeanDag.Scheme.Table.Statement
/-!
# The scheme's table — proof

Every claim is linear arithmetic over the row definitions.
-/

namespace LeanDag

namespace Scheme

namespace Table

open Params

theorem rowsHold : RowsHold := by
  intro f c
  simp only [ThreeRound, Live, TwoRound, mysticeti, mahiMahi, cordialMinersPS,
    cordialMinersAsync, blueBottlePS, blueBottleAsync, orcaella, asyncOrcaella,
    hybridMysticeti, hybridMahiMahi]
  refine ⟨⟨⟨?_, ?_, ?_⟩, ?_, ?_, ?_⟩, fun w => ⟨⟨?_, ?_, ?_⟩, ?_, ?_, ?_⟩,
    ⟨⟨?_, ?_, ?_⟩, ?_, ?_⟩, ⟨?_, ?_, ?_⟩, ⟨⟨?_, ?_, ?_⟩, ?_, ?_, ?_⟩,
    ⟨⟨?_, ?_, ?_⟩, ?_, ?_, ?_⟩, fun n hn => ⟨⟨⟨?_, ?_, ?_⟩, ?_, ?_, ?_⟩,
      ⟨⟨?_, ?_, ?_⟩, ?_, ?_, ?_⟩⟩, ⟨⟨?_, ?_, ?_⟩, ?_, ?_, ?_⟩,
    fun w => ⟨⟨?_, ?_, ?_⟩, ?_, ?_, ?_⟩⟩ <;> omega

theorem twoRoundBound : TwoRoundBound := by
  intro p n f c h hl
  simp only [TwoRound, Live, orcaella] at *
  obtain ⟨h1, h2, h3⟩ := h
  obtain ⟨l1, l2, -⟩ := hl
  refine ⟨by omega, fun hn => ⟨by omega, by omega, by omega⟩⟩

theorem threeRoundBound : ThreeRoundBound := by
  intro p n f c h hl
  simp only [ThreeRound, Live, hybridMysticeti, mysticeti] at *
  obtain ⟨h1, h2, h3⟩ := h
  obtain ⟨l1, l2, l3⟩ := hl
  refine ⟨by omega, fun hn => ⟨by omega, by omega, by omega, fun hc => ⟨by omega, by omega,
    by omega⟩⟩⟩

theorem nemoNotTwoRound : NemoNotTwoRound := by
  intro c hc
  simp only [TwoRound, nemoNemo]
  refine ⟨fun ⟨_, h2, _⟩ => by omega, by omega, by omega⟩

theorem holds : Statement := ⟨rowsHold, twoRoundBound, threeRoundBound, nemoNotTwoRound⟩

end Table

end Scheme

end LeanDag
