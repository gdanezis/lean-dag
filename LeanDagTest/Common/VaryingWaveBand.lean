import LeanDagTest.Common.VaryingWave
import LeanDag.Properties.Compose
/-!
# A rule with the band laws whose wave varies is banded, its wave read from the kind

`AnchoredRule.banded` asks one hypothesis, `hb : R.BandLaws`. The wave a rule reads at a slot is
`waveAt (S.kind k)`, the wave of the kind the schedule assigns the slot, and the band's schedule
agreement carries a slot's kind with its leader, so a wave that varies is no obstacle to the band.
`VaryingWave.altRule` is not banded because its direct commit reads the wave of the slot's *round*
inside `Commit`, which a shift moves; it has no band laws for the same reason.

`floorRule` reads its wave through eligibility alone, hence from the kind: the direct commit looks
at the slot's own round (a candidate by validator `2` that the view holds commits outright), there
is no direct skip, and the single rung links a candidate its anchor references from strictly above
the slot's round. Each survives a shift of the band, `floorRule_bandLaws`, and so the rule is
banded, `floorRule_banded`.

The two frames that refuted `Banded` when the wave was read from the round are here with the
parity of their own rounds as their kinds, `altSlotsK` and `altSlotsK'`: slot `0` has kind `0` in
the lower frame and kind `1` in the upper, so the upper frame decides it through an anchor at
round `2` (`floor_decided_upper`) and the lower frame does not (`floor_not_decided_lower`). That
is no longer a counterexample: the upper frame changed slot `0`'s kind, so it is not a rebase of
the lower one (`altSlotsK'_not_rebases`), and the band's premise excludes it. The frame that
carries the kinds, `altSlotsC'`, is a rebase, and there the verdicts of the two frames are the
same (`floor_frames_agree`).

The ladders `av3` and `av4`, the schedules and the wave are those of `VaryingWave`; only the rule
and the direction of the band change. `floorRule` commits any leader block its view holds whose
author is validator `2`, reading no vote at all, so a protocol's rule is not meant here either,
only a rule the structure admits.
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
  Commit := fun U V L _ _ => L ∈ V.ids ∧ (U.block L).creator = 2
  decCommit := fun _ _ _ _ _ => inferInstance
  Skip := fun _ _ _ _ => False
  rungs := 1
  Link := fun _ U A L S k => S.slotRound k < (U.block A).round ∧ L ∈ (U.block A).refs
  tie := fun _ _ _ => False

example : floorRule.waveAt 0 = 1 := rfl
example : floorRule.waveAt 1 = 0 := rfl
example : ¬ ∀ r r', floorRule.waveAt r = floorRule.waveAt r' := fun h => by
  have := h 0 1
  simp [floorRule, altWave] at this

/-- **The wave repeats every two rounds**, `altWave`'s own period. -/
theorem floorRule_waveAt_periodic (r : ℕ) : floorRule.waveAt (r + 2) = floorRule.waveAt r :=
  altWave_periodic r

/-! ## The two frames, with the parity of their rounds as kinds -/

/-- The lower frame: slot `k` at round `k`, of kind the round's parity. -/
@[reducible]
def altSlotsK : Slots (Fin 4) := { altSlots with kind := fun k => k % 2 }

/-- **The upper frame reading its own rounds' parity**: slot `k` at round `k + 1`, of kind
`(k + 1) % 2`. This is the frame that refuted the band when the wave was read from the round;
it recomputes each slot's kind rather than carrying it. -/
@[reducible]
def altSlotsK' : Slots (Fin 4) := { altSlots' with kind := fun k => (k + 1) % 2 }

/-- **The upper frame with the kinds carried**: slot `k` at round `k + 1`, of the kind it has in
the lower frame. This is what a rebase produces. -/
@[reducible]
def altSlotsC' : Slots (Fin 4) := { altSlots' with kind := fun k => k % 2 }

/-! ## The band laws hold at the varying wave -/

/-- **The rule has the band laws.** A commit reads one block at the slot's round, which the band
carries with its author; a link reads the anchor's references strictly above the floor, which the
band carries too; a candidate the band did not carry is referenced by no old anchor. -/
theorem floorRule_bandLaws : floorRule.BandLaws where
  commit_band := fun {S S' U U' lo hi g g' V V' k k' L} hab _ _ _ hlo hhi hV hL hc => by
    obtain ⟨hLV, hcr⟩ := hc
    have hround : (U.block L).round = S.slotRound k := hL.2.1
    obtain ⟨-, hcreator⟩ := AnchoredRule.band_block hab hL.1 (by omega) (by omega)
    exact ⟨hV L hLV (by omega) (by omega), by rw [hcreator]; exact hcr⟩
  skip_band := fun _ _ _ _ _ _ _ hs => hs.elim
  link_band := fun {S S' U U' lo hi g g' A L k k' i} hab hA hAlo hAhi hsch _ _ hklo _ _ _ => by
    obtain ⟨hr, -⟩ := AnchoredRule.band_block hab hA hAlo hAhi
    change (S'.slotRound k' < (U'.block A).round ∧ L ∈ (U'.block A).refs) ↔
      (S.slotRound k < (U.block A).round ∧ L ∈ (U.block A).refs)
    by_cases hlt : S.slotRound k < (U.block A).round
    · rw [AnchoredRule.band_refs hab hA (by omega) hAhi]
      exact ⟨fun h => ⟨hlt, h.2⟩, fun h => ⟨by omega, h.2⟩⟩
    · exact ⟨fun h => absurd (by omega : S.slotRound k < (U.block A).round) hlt,
        fun h => absurd h.1 hlt⟩
  link_novel := fun {S S' U U' lo hi g g' A L k k' i} hab hA _ hAlo hAhi hsch _ _ hklo _ _ _
      hLo => by
    obtain ⟨hr, -⟩ := AnchoredRule.band_block hab hA hAlo hAhi
    rintro ⟨hlt, hmem⟩
    have hlt' : S.slotRound k < (U.block A).round := by omega
    rw [AnchoredRule.band_refs hab hA (by omega) hAhi] at hmem
    exact hLo (U.complete A hA L hmem)

/-- **Persistence**, through the extension laws the band laws contain. -/
theorem floorRule_persist : Persist floorRule.toDagRule :=
  AnchoredRule.persist floorRule_bandLaws.toExtendLaws fun _ _ => trivial

/-! ## The verdict, and its absence a round down -/

/-- **Slot `0` commits indirectly in the upper frame reading its own parity.** Its kind there is
`1`, whose wave is `0`, so the committed slot `1` at round `2` is its nearest eligible anchor, and
block `6` references block `1`. -/
theorem floor_decided_upper :
    floorRule.Decided (S := altSlotsK') av4 (View.full av4) 0 (some 1) :=
  AnchoredRule.Decided.indirectCommit_single (S := altSlotsK') (k := 0) (j := 1) (A := 6) (L := 1)
    rfl (fun _ _ h => h) (by omega) ((floorRule.eligible_iff (S := altSlotsK')).mpr (by decide))
    (AnchoredRule.Decided.directCommit (S := altSlotsK') (k := 1) (L := 6) (by decide) (by decide))
    (fun _ hm hm' _ => absurd hm' (by omega)) (by decide)
    (show altSlotsK'.slotRound 0 < (av4.block 6).round ∧ (1 : Fin 20) ∈ (av4.block 6).refs from
      ⟨by decide, by decide⟩)

/-- No block of the lower frame at round `2` or above references block `1`: the ladder
references the round below only. -/
theorem av3_no_ref_one :
    ∀ A : Fin 20, 2 ≤ (av3.block A).round → (1 : Fin 20) ∉ (av3.block A).refs := by decide

/-- **And has no such verdict in the lower frame.** Slot `0`'s kind there is `0`, whose wave is
`1`, so every eligible anchor sits at round `2` or above, where no block references block `1`;
the direct rule does not commit it either, block `1` being validator `1`'s. -/
theorem floor_not_decided_lower :
    ¬ floorRule.Decided (S := altSlotsK) av3 (View.full av3) 0 (some 1) := by
  intro h
  cases h with
  | directCommit _ hc => exact absurd hc.2 (by decide)
  | indirectCommit _ helig hj _ _ _ _ hlink _ =>
    have hA := AnchoredRule.isLeaderBlock_of_decided (S := altSlotsK) hj
    have helig' := (floorRule.eligible_iff (S := altSlotsK)).mp helig
    have hs0 : altSlotsK.slotRound 0 = 0 := rfl
    have hw0 : floorRule.waveAt (altSlotsK.kind 0) = 1 := rfl
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

/-! ## The band, and what the two frames are to each other -/

/-- **The rule is banded**: the band laws are all `banded` asks, the wave being read from the
kind. -/
theorem floorRule_banded : Banded floorRule.toDagRule :=
  AnchoredRule.banded floorRule_bandLaws fun _ _ => trivial

/-! ## A rule whose direct commit reads the wave of the kind

Steelhead's shape (`steelheadAnchored`): the direct predicates and the eligibility all read the
wave of the slot, `Commit` from the kind it is handed and `Skip`, `Link` from `S.kind k`. Here the
direct commit looks for a block of the view at `r + kindWave κ` referencing the candidate, at a wave
of at least one round, so the block sits strictly above the band's floor and the band carries its
references. -/

/-- One round above a slot of kind `0`, two above any other. Never zero. -/
def kindWave : ℕ → ℕ := fun κ => if κ = 0 then 1 else 2

theorem kindWave_pos (κ : ℕ) : 0 < kindWave κ := by unfold kindWave; split <;> omega

/-- **A rule reading one reference at the decision round of the slot's kind.** -/
def kindRule : AnchoredRule (Fin 4) (Fin 20) Unit ValidWrt (Correct : Finset (Fin 4)) where
  waveAt := kindWave
  Commit := fun U V L r κ =>
    ∃ c ∈ V.ids, (U.block c).round = r + kindWave κ ∧ L ∈ (U.block c).refs
  decCommit := fun _ _ _ _ _ => inferInstance
  Skip := fun _ _ _ _ => False
  rungs := 0
  Link := fun _ _ _ _ _ _ => False
  tie := fun _ _ _ => False

/-- **The rule has the band laws.** The referencing block sits `kindWave κ ≥ 1` rounds above the
slot, so strictly above the band's floor, where the band carries its round, its author and its
references; the two frames agree on the slot's kind, so on the wave it reads. -/
theorem kindRule_bandLaws : kindRule.BandLaws where
  commit_band := fun {S S' U U' lo hi g g' V V' k k' L} hab hkk _ hkind hlo hhi hV _ hc => by
    obtain ⟨c, hcV, hcr, hcL⟩ := hc
    have hpos := kindWave_pos (S.kind k)
    have hhi' : S.slotRound k + kindWave (S.kind k) + g ≤ hi := hhi
    obtain ⟨hr, -⟩ := AnchoredRule.band_block hab (V.subset_ids hcV) (by omega) (by omega)
    refine ⟨c, hV c hcV (by omega) (by omega), ?_, ?_⟩
    · rw [← hkind]; omega
    · rw [AnchoredRule.band_refs hab (V.subset_ids hcV) (by omega) (by omega)]; exact hcL
  skip_band := fun _ _ _ _ _ _ _ hs => hs.elim
  link_band := fun _ _ _ _ _ _ _ _ _ hi _ => absurd hi (Nat.not_lt_zero _)
  link_novel := fun _ _ _ _ _ _ _ _ _ _ hi _ _ => absurd hi (Nat.not_lt_zero _)

/-- **And is banded**, its wave varying with the kind and read inside its direct commit. -/
theorem kindRule_banded : Banded kindRule.toDagRule :=
  AnchoredRule.banded kindRule_bandLaws fun _ _ => trivial

/-- **The frame that recomputes its kinds is not a rebase of the lower frame**: it changes slot
`0`'s kind, which a rebase carries. The two verdicts above disagree, and the band's schedule
premise is what excludes the pair. -/
theorem altSlotsK'_not_rebases : ¬ Rebases altSlotsC' altSlotsK' 0 0 :=
  fun h => absurd (h.kind 0) (by decide)

/-- The upper frame with the kinds carried is a rebase of the lower one, by one round. -/
theorem altSlotsC'_rebases : Rebases altSlotsC' altSlotsK 1 0 where
  slotRound := fun k => by rw [Nat.zero_add]; rfl
  leader := fun k => by rw [Nat.zero_add]; rfl
  kind := fun k => by rw [Nat.zero_add]; rfl
  base := le_refl _

/-- The upper ladder pruned below round `1` and moved down a round is the lower ladder. -/
theorem av_rebasedAbove : RebasedAbove floorRule.toDagRule av4 av3 1 1 where
  mem := by decide
  round := by decide
  creator := by decide
  refs := by decide

/-- **With the kinds carried, the two frames decide slot `0` alike**: `decided_of_rebased` at
`floorRule_banded`, for every verdict. -/
theorem floor_frames_agree (v : Option (Fin 20)) :
    floorRule.Decided (S := altSlotsC') av4 (View.full av4) 0 v ↔
      floorRule.Decided (S := altSlotsK) av3 (View.full av3) 0 v :=
  decided_of_rebased floorRule_banded (V := View.full av4) (V' := View.full av3)
    { av_rebasedAbove, altSlotsC'_rebases with }
    (fun b _ hr => by
      change b ∈ (View.full av4).ids ↔ b ∈ (View.full av3).ids
      simp only [View.full_ids]
      exact ⟨fun _ => av4_mem_of_round b (by simpa using hr), fun _ => Finset.mem_univ b⟩)
    0 (by decide) v

/-! ## Axioms

Nothing here should ever acquire an axiom beyond the standard three. -/

#print axioms floorRule_bandLaws
#print axioms floorRule_persist
#print axioms floorRule_banded
#print axioms floor_frames_agree
#print axioms kindRule_bandLaws
#print axioms kindRule_banded

end VaryingWaveBand

end LeanDagTest
