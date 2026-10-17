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

theorem crashWeaker : CrashWeaker := by
  intro p n q
  simp only [TwoRound, ThreeRound, TwoRoundCrash, ThreeRoundCrash]
  refine ⟨fun h => ?_, fun h => ?_⟩ <;> obtain ⟨h1, h2, h3⟩ := h <;> exact ⟨by omega, by omega⟩

theorem crashRows : CrashRows := by
  intro c
  simp only [TwoRoundCrash, nemoNemo, asyncNemoNemo]
  refine ⟨⟨⟨?_, ?_⟩, ?_, ?_⟩, ⟨?_, ?_⟩, ?_, ?_⟩ <;> omega

theorem crashBound : CrashBound := by
  refine ⟨fun p n c h hl hcm => ?_, fun p n c h hcm => ?_⟩
  · simp only [TwoRoundCrash, Live, orcaella] at *
    obtain ⟨h1, h2⟩ := h
    refine ⟨by omega, fun hl => ?_⟩
    obtain ⟨l1, l2, l3⟩ := hl
    exact ⟨by omega, fun hn => ⟨by omega, by omega, by omega⟩⟩
  · simp only [ThreeRoundCrash, Live, hybridMysticeti] at *
    obtain ⟨h1, h2⟩ := h
    refine ⟨by omega, fun hl hn => ?_⟩
    obtain ⟨l1, l2, l3⟩ := hl
    exact ⟨by omega, by omega, by omega⟩

theorem hybridAnyCommittee : HybridAnyCommittee := by
  intro n f c hn
  simp only [ThreeRound, Live, hybridMysticeti]
  refine ⟨⟨?_, ?_, ?_⟩, ?_, ?_, ?_⟩ <;> omega

theorem rowsCovered : RowsCovered := by
  intro n f c
  refine ⟨fun hn => ⟨Or.inr (Or.inl ⟨rfl, le_rfl, rfl, ?_⟩),
      fun w hw => Or.inr (Or.inl ⟨rfl, hw, rfl, ?_⟩), Or.inr (Or.inl ⟨rfl, le_rfl, rfl, ?_⟩),
      Or.inr (Or.inl ⟨rfl, by simp [cordialMinersAsync], rfl, ?_⟩)⟩,
    fun hn => ⟨Or.inl ⟨rfl, le_rfl, ?_, ?_⟩, Or.inl ⟨rfl, by simp [blueBottleAsync], ?_, ?_⟩⟩,
    fun hn => ⟨Or.inl ⟨rfl, le_rfl, ?_, ?_⟩, Or.inl ⟨rfl, by simp [asyncOrcaella], ?_, ?_⟩⟩,
    fun hn => ⟨Or.inr (Or.inl ⟨rfl, le_rfl, rfl, ?_⟩),
      fun w hw => Or.inr (Or.inl ⟨rfl, hw, rfl, ?_⟩)⟩,
    fun hn => ⟨Or.inr (Or.inr (Or.inl ⟨rfl, le_rfl, le_rfl, rfl, ?_⟩)),
      Or.inr (Or.inr (Or.inl ⟨rfl, by simp [asyncNemoNemo], le_rfl, rfl, ?_⟩))⟩⟩ <;>
  simp only [TwoRound, ThreeRound, TwoRoundCrash, mysticeti, mahiMahi, cordialMinersPS,
    cordialMinersAsync, blueBottlePS, blueBottleAsync, orcaella, asyncOrcaella, hybridMysticeti,
    hybridMahiMahi, nemoNemo, asyncNemoNemo] <;> omega

theorem holds : Statement :=
  ⟨rowsHold, twoRoundBound, threeRoundBound, nemoNotTwoRound, crashWeaker, crashRows, crashBound,
    hybridAnyCommittee, rowsCovered⟩

end Table

end Scheme

end LeanDag
