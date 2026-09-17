import LeanDagTest.Common.VaryingWave
/-!
# A rule with the band laws whose wave varies is not banded

`AnchoredRule.banded` takes two hypotheses: `hb : R.BandLaws` and `hw`, that the wave be the same
at every round. `VaryingWave.altRule` is not banded, but it has no band laws either: its direct
commit reads a block at `r + altWave r`, which a shift of the rounds moves, so `commit_band` fails
on the very frames that refute it. That removes both hypotheses at once.

This file removes only `hw`. `floorRule` reads its wave through eligibility alone: the direct commit
looks at the slot's own round (a candidate by validator `2` that the view holds commits outright),
there is no direct skip, and the single rung links a candidate its anchor references from strictly
above the slot's round. Each survives a shift of the band, `floorRule_bandLaws`. The wave still
alternates, so the anchor floor sits two rounds above an even slot and one round above an odd one,
and the same DAG a round up hands slot `0` a different nearest anchor: in the upper frame the
committed slot `1` links its candidate, in the lower frame every eligible anchor sits at round `2`
or above, where no block references it. The indirect commit of the upper frame has no counterpart
in the lower one, `floorRule_not_banded`, so `hb` alone does not yield `Banded`
(`bandLaws_not_banded`).

The ladders `av3` and `av4`, the schedules and the wave are those of `VaryingWave`; only the rule
and the direction of the band change.
-/

namespace LeanDagTest

namespace VaryingWaveBand

open LeanDag LeanDag.Properties VaryingWave

set_option maxRecDepth 4096

/-! ## The rule -/

/-- **A rule whose wave enters through eligibility only.** The direct commit reads the slot's own
round, the rung reads the anchor's references, and neither mentions `altWave`. -/
def floorRule : AnchoredRule (Fin 4) (Fin 20) Unit ValidWrt (Correct : Finset (Fin 4)) where
  waveAt := altWave
  Commit := fun U V L _ => L ∈ V.ids ∧ (U.block L).creator = 2
  decCommit := fun _ _ _ _ => inferInstance
  Skip := fun _ _ _ _ => False
  rungs := 1
  Link := fun _ U A L S k => S.slotRound k < (U.block A).round ∧ L ∈ (U.block A).refs
  tie := fun _ _ _ => False

example : floorRule.waveAt 0 = 1 := rfl
example : floorRule.waveAt 1 = 0 := rfl
example : ¬ ∀ r r', floorRule.waveAt r = floorRule.waveAt r' := fun h => by
  have := h 0 1
  simp [floorRule, altWave] at this

/-! ## The band laws hold at the varying wave -/

/-- **The rule has the band laws.** A commit reads one block at the slot's round, which the band
carries with its author; a link reads the anchor's references strictly above the floor, which the
band carries too; a candidate the band did not carry is referenced by no old anchor. -/
theorem floorRule_bandLaws : floorRule.BandLaws where
  commit_band := fun {S S' U U' lo hi g g' V V' k k' L} hab _ _ hlo hhi hV hL hc => by
    obtain ⟨hLV, hcr⟩ := hc
    have hround : (U.block L).round = S.slotRound k := hL.2.1
    obtain ⟨-, hcreator⟩ := AnchoredRule.band_block hab hL.1 (by omega) (by omega)
    exact ⟨hV L hLV (by omega) (by omega), by rw [hcreator]; exact hcr⟩
  skip_band := fun _ _ _ _ _ _ hs => hs.elim
  link_band := fun {S S' U U' lo hi g g' A L k k' i} hab hA hAlo hAhi hsch _ hklo _ _ _ => by
    obtain ⟨hr, -⟩ := AnchoredRule.band_block hab hA hAlo hAhi
    show (S'.slotRound k' < (U'.block A).round ∧ L ∈ (U'.block A).refs) ↔
      (S.slotRound k < (U.block A).round ∧ L ∈ (U.block A).refs)
    by_cases hlt : S.slotRound k < (U.block A).round
    · rw [AnchoredRule.band_refs hab hA (by omega) hAhi]
      exact ⟨fun h => ⟨hlt, h.2⟩, fun h => ⟨by omega, h.2⟩⟩
    · exact ⟨fun h => absurd (by omega : S.slotRound k < (U.block A).round) hlt,
        fun h => absurd h.1 hlt⟩
  link_novel := fun {S S' U U' lo hi g g' A L k k' i} hab hA hAlo hAhi hsch _ hklo _ _ _ hLo => by
    obtain ⟨hr, -⟩ := AnchoredRule.band_block hab hA hAlo hAhi
    rintro ⟨hlt, hmem⟩
    have hlt' : S.slotRound k < (U.block A).round := by omega
    rw [AnchoredRule.band_refs hab hA (by omega) hAhi] at hmem
    exact hLo (U.complete A hA L hmem)

/-- **Persistence**, through the extension laws the band laws contain. -/
theorem floorRule_persist : Persist floorRule.toDagRule :=
  AnchoredRule.persist floorRule_bandLaws.toExtendLaws

/-! ## The verdict, and its absence a round down -/

/-- **Slot `0` commits indirectly in the upper frame.** At round `1` its wave is `0`, so the
committed slot `1` at round `2` is its nearest eligible anchor, and block `6` references
block `1`. -/
theorem floor_decided_upper :
    floorRule.Decided (S := altSlots') av4 (View.full av4) 0 (some 1) :=
  AnchoredRule.Decided.indirectCommit_single (S := altSlots') (k := 0) (j := 1) (A := 6) (L := 1)
    rfl (fun _ _ h => h) (by omega) ((floorRule.eligible_iff (S := altSlots')).mpr (by decide))
    (AnchoredRule.Decided.directCommit (S := altSlots') (k := 1) (L := 6) (by decide) (by decide))
    (fun _ hm hm' _ => absurd hm' (by omega)) (by decide)
    (show altSlots'.slotRound 0 < (av4.block 6).round ∧ (1 : Fin 20) ∈ (av4.block 6).refs from
      ⟨by decide, by decide⟩)

/-- No block of the lower frame at round `2` or above references block `1`: the ladder
references the round below only. -/
theorem av3_no_ref_one :
    ∀ A : Fin 20, 2 ≤ (av3.block A).round → (1 : Fin 20) ∉ (av3.block A).refs := by decide

/-- **And has no such verdict in the lower frame.** At round `0` the wave is `1`, so every
eligible anchor sits at round `2` or above, where no block references block `1`; the direct rule
does not commit it either, block `1` being validator `1`'s. -/
theorem floor_not_decided_lower :
    ¬ floorRule.Decided (S := altSlots) av3 (View.full av3) 0 (some 1) := by
  intro h
  cases h with
  | directCommit _ hc => exact absurd hc.2 (by decide)
  | indirectCommit _ helig hj _ _ _ _ hlink _ =>
    have hA := AnchoredRule.isLeaderBlock_of_decided (S := altSlots) hj
    have helig' := (floorRule.eligible_iff (S := altSlots)).mp helig
    have hs0 : altSlots.slotRound 0 = 0 := rfl
    have hw0 : floorRule.waveAt (altSlots.slotRound 0) = 1 := rfl
    refine av3_no_ref_one _ ?_ hlink.2
    rw [hA.2.1]
    omega

/-! ## The band, read from the upper frame down -/

theorem av4_mem_of_round : ∀ b : Fin 20, 1 ≤ (av4.block b).round + 0 → b ∈ av3.ids := by decide

theorem av4_lt_of_round : ∀ b : Fin 20, 1 ≤ (av4.block b).round + 0 → (b : ℕ) < 16 := by decide

theorem av3_lt : ∀ b : Fin 20, b ∈ av3.ids → (b : ℕ) < 16 := by decide

theorem av_block_shift_down : ∀ b : Fin 20, (b : ℕ) < 16 →
    (av3.block b).round + 1 = (av4.block b).round + 0 ∧
      (av3.block b).creator = (av4.block b).creator := by decide

theorem av_refs_shift_down : ∀ b : Fin 20, 1 < (av4.block b).round + 0 →
    (av3.block b).refs = (av4.block b).refs := by decide

/-- **The two frames agree on every band from round `1` of the upper frame up.** The fresh
genesis layer of the upper frame sits below the floor, and the old bottom layer sits at it, where
the references clause does not reach. -/
theorem floor_agreeBand (top : ℕ) : AgreeBand floorRule.toDagRule av4 av3 1 top 0 1 where
  mem := fun b _ hlo _ => av4_mem_of_round b hlo
  block := fun b _ hor => by
    have hb : (b : ℕ) < 16 := by
      rcases hor with ⟨h1, _⟩ | ⟨h1, _, _⟩
      · exact av4_lt_of_round b h1
      · exact av3_lt b h1
    exact av_block_shift_down b hb
  refs := fun b _ hlo _ => av_refs_shift_down b hlo

/-! ## The refutation -/

/-- **A rule with the band laws whose wave varies is not banded**: the upper frame's verdict does
not carry to the lower frame, though the two agree on every band above the slot. -/
theorem floorRule_not_banded : ¬ Banded floorRule.toDagRule := by
  intro hb
  obtain ⟨top, ht⟩ := hb altSlots' av4 (View.full av4) 0 (some 1) floor_decided_upper
  refine floor_not_decided_lower (ht 0 1 0 0 altSlots av3 (View.full av3) 0 rfl ?_ ?_
    (floor_agreeBand top) ?_)
  · intro m m' hm _
    have : m = m' := by omega
    subst this
    rfl
  · intro m m' hm _
    have : m = m' := by omega
    subst this
    rfl
  · intro b _ hlo _
    exact av4_mem_of_round b hlo

/-- **`banded`'s constancy hypothesis is not implied by its band laws**: a rule with the band laws
that is not banded. -/
theorem bandLaws_not_banded :
    ∃ R : AnchoredRule (Fin 4) (Fin 20) Unit ValidWrt (Correct : Finset (Fin 4)),
      R.BandLaws ∧ ¬ Banded R.toDagRule :=
  ⟨floorRule, floorRule_bandLaws, floorRule_not_banded⟩

/-! ## Axioms

Nothing here should ever acquire an axiom beyond the standard three. -/

#print axioms floorRule_bandLaws
#print axioms floorRule_not_banded
#print axioms bandLaws_not_banded

end VaryingWaveBand

end LeanDagTest
