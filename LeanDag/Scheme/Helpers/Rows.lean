import LeanDag.Scheme.Helpers.Transfer
import LeanDag.Scheme.Helpers.Votes
import LeanDag.Mysticeti.Rule
import LeanDag.Odontoceti.Decision
import LeanDag.Hybrid.Decision
/-!
# The rows whose vote round is the round above

Mysticeti, Blue Bottle PS and Orcaella vote one round above the
candidate, so the scheme's votes are references (`Helpers/Votes.lean`)
and each row reads what the rule of this development reads: Mysticeti's
`coreAnchored`, Odontoceti's `odontocetiAnchored` and Hybrid's
`hybridAnchored` at Orcaella's committee. The one difference is the
tie-break, which Mysticeti does without: there a linked candidate is
unique by the core's laws, so the scheme's least choice is that candidate.
-/

namespace LeanDag

namespace Scheme

variable {Validator : Type} [Fintype Validator] [DecidableEq Validator]
variable {BlockId : Type} [LinearOrder BlockId] {Payload : Type}
variable [S : Slots Validator]

section Core

variable [F : Faults Validator]

omit S in
/-- The core's universe: references name distinct authors. -/
theorem distinctRefs_core {U : BlockUniverse Validator BlockId Payload} :
    ∀ b ∈ U.ids, DistinctRefs U b :=
  fun b hb => (U.valid b hb).distinct_creators

omit S F in
/-- A count of one author is a block in the anchor's history. -/
theorem one_le_card_iff_linkedVia {P : Validity Validator BlockId Payload}
    [P.Mechanised] {honest : Finset Validator}
    {U : BlockRecord Validator BlockId Payload P honest} {A : BlockId} (hA : A ∈ U.ids)
    (s : Finset BlockId) :
    1 ≤ (creatorsOf U.block (s.filter (fun C => C ∈ history U A))).card ↔ LinkedVia U A s := by
  rw [linkedVia_iff_history hA, Finset.filter_mem_eq_inter, Nat.one_le_iff_ne_zero,
    Ne, Finset.card_eq_zero, ← Ne, ← Finset.nonempty_iff_ne_empty, creatorsOf,
    Finset.image_nonempty]

/-- **The Mysticeti row reads as `coreAnchored`.** -/
theorem readAlike_mysticeti (σ : VoteSel Validator BlockId Payload ValidWrt Correct)
    (U : BlockUniverse Validator BlockId Payload) :
    ReadAlike (schemeAnchored (Params.mysticeti (Fintype.card Validator) F.f) σ)
      (coreAnchored Validator BlockId Payload) U where
  waveAt := fun _ => rfl
  rungs := rfl
  commit := fun V k L hL => by
    show HoldsAtLeast U V _ (certsAt _ σ U L _) ↔ HoldsAtLeast U V _ _
    rw [certsAt_eq_certificatesAt σ _ rfl rfl distinctRefs_core hL.2.1]
    rfl
  skip := fun V k => by
    show HoldsAtLeast U V _ (blamersAt _ σ U k) ↔ HoldsAtLeast U V _ _
    rw [blamersAt_eq σ _ rfl k]
    rfl
  link := fun {i k j A L} _ hL hA _ => by
    show _ ≤ (creatorsOf U.block ((certsAt _ σ U L _).filter _)).card ↔ LinkedVia U A _
    rw [certsAt_eq_certificatesAt σ _ rfl rfl distinctRefs_core hL.2.1]
    exact one_le_card_iff_linkedVia hA.1 _
  least := fun {i k j A L} hi hL hA he hl => by
    have hi0 : i = 0 := by simp only [schemeAnchored] at hi; omega
    subst hi0
    have hlink : ∀ {L'}, IsLeaderBlock U k L' →
        ((schemeAnchored (Params.mysticeti (Fintype.card Validator) F.f) σ).Link 0 U A L' S k ↔
          (coreAnchored Validator BlockId Payload).Link 0 U A L' S k) := fun hL' => by
      show _ ≤ (creatorsOf U.block ((certsAt _ σ U _ _).filter _)).card ↔ LinkedVia U A _
      rw [certsAt_eq_certificatesAt σ _ rfl rfl distinctRefs_core hL'.2.1]
      exact one_le_card_iff_linkedVia hA.1 _
    constructor
    · exact fun _ _ _ _ h => h
    · intro _ L' hL' hl' hlt
      have heq := (coreLaws (Validator := Validator) (BlockId := BlockId)
        (Payload := Payload)).link_unique (S := S) (U := U) (i := 0) trivial hL hL' hA trivial he
        Nat.one_pos (fun _ h => absurd h (Nat.not_lt_zero _)) ((hlink hL).mp hl)
        ((hlink hL').mp hl') (fun _ _ _ h => h) (fun _ _ _ h => h)
      exact lt_irrefl L (heq ▸ hlt)

end Core

section Odontoceti

variable [F : Faults5 Validator]

/-- The Blue Bottle PS row's link is Odontoceti's thick link. -/
theorem link_blueBottlePS (σ : VoteSel Validator BlockId Payload ValidWrt Correct)
    (U : BlockUniverse Validator BlockId Payload) {i k : ℕ} {A L : BlockId}
    (hL : IsLeaderBlock U k L) :
    (schemeAnchored (Params.blueBottlePS (Fintype.card Validator) F.f) σ).Link i U A L S k ↔
      (Odontoceti.odontocetiAnchored Validator BlockId Payload).Link i U A L S k := by
  show _ ≤ (creatorsOf U.block ((certsAt _ σ U L _).filter _)).card ↔ _
  rw [certsAt_eq_votesFor σ _ rfl rfl distinctRefs_core hL.2.1]
  rfl

/-- **The Blue Bottle PS row reads as `odontocetiAnchored`.** -/
theorem readAlike_blueBottlePS (σ : VoteSel Validator BlockId Payload ValidWrt Correct)
    (U : BlockUniverse Validator BlockId Payload) :
    ReadAlike (schemeAnchored (Params.blueBottlePS (Fintype.card Validator) F.f) σ)
      (Odontoceti.odontocetiAnchored Validator BlockId Payload) U where
  waveAt := fun _ => rfl
  rungs := rfl
  commit := fun V k L hL => by
    show HoldsAtLeast U V _ (certsAt _ σ U L _) ↔ HoldsAtLeast U V _ _
    rw [certsAt_eq_votesFor σ _ rfl rfl distinctRefs_core hL.2.1]
    rfl
  skip := fun V k => by
    show HoldsAtLeast U V _ (blamersAt _ σ U k) ↔ HoldsAtLeast U V _ _
    rw [blamersAt_eq σ _ rfl k]
    rfl
  link := fun _ hL _ _ => link_blueBottlePS σ U hL
  least := fun {i k j A L} _ _ _ _ _ =>
    ⟨fun h L' hL' hl' => h L' hL' ((link_blueBottlePS σ U (i := i) hL').mpr hl'),
      fun h L' hL' hl' => h L' hL' ((link_blueBottlePS σ U (i := i) hL').mp hl')⟩

end Odontoceti

section Hybrid

variable [H : HybridFaults Validator]

/-- The Orcaella row's link is Hybrid's thick link at `k = n − 3f − 2c`. -/
theorem link_orcaella (σ : VoteSel Validator BlockId Payload ValidWrt Correct)
    (U : BlockUniverse Validator BlockId Payload) {i k : ℕ} {A L : BlockId}
    (hL : IsLeaderBlock U k L) :
    (schemeAnchored (Params.orcaella (Fintype.card Validator) H.fb H.fc) σ).Link i U A L S k ↔
      (Hybrid.hybridAnchored Validator BlockId Payload
        (Fintype.card Validator - 3 * H.fb - 2 * H.fc)).Link i U A L S k := by
  show _ ≤ (creatorsOf U.block ((certsAt _ σ U L _).filter _)).card ↔ _
  rw [certsAt_eq_votesFor σ _ rfl rfl distinctRefs_core hL.2.1]
  rfl

/-- **The Orcaella row reads as `hybridAnchored`** at the committee
`n = 5f + 3c + 1` and the link threshold `k = n − 3f − 2c`, where the
row's skip threshold `4f + 2c + 1` is `n − f − c`. -/
theorem readAlike_orcaella (σ : VoteSel Validator BlockId Payload ValidWrt Correct)
    (U : BlockUniverse Validator BlockId Payload)
    (hn : Fintype.card Validator = 5 * H.fb + 3 * H.fc + 1) :
    ReadAlike (schemeAnchored (Params.orcaella (Fintype.card Validator) H.fb H.fc) σ)
      (Hybrid.hybridAnchored Validator BlockId Payload
        (Fintype.card Validator - 3 * H.fb - 2 * H.fc)) U where
  waveAt := fun _ => rfl
  rungs := rfl
  commit := fun V k L hL => by
    show HoldsAtLeast U V _ (certsAt _ σ U L _) ↔ HoldsAtLeast U V _ _
    rw [certsAt_eq_votesFor σ _ rfl rfl distinctRefs_core hL.2.1]
    show HoldsAtLeast U V (Fintype.card Validator - H.fb - H.fc) _ ↔
      HoldsAtLeast U V (Fintype.card Validator - (H.fb + H.fc)) _
    rw [Nat.sub_sub]
  skip := fun V k => by
    show HoldsAtLeast U V _ (blamersAt _ σ U k) ↔ HoldsAtLeast U V _ _
    rw [blamersAt_eq σ _ rfl k]
    show HoldsAtLeast U V (4 * H.fb + 2 * H.fc + 1) _ ↔
      HoldsAtLeast U V (Fintype.card Validator - (H.fb + H.fc)) _
    rw [show 4 * H.fb + 2 * H.fc + 1 = Fintype.card Validator - (H.fb + H.fc) by omega]
  link := fun _ hL _ _ => link_orcaella σ U hL
  least := fun {i k j A L} _ _ _ _ _ =>
    ⟨fun h L' hL' hl' => h L' hL' ((link_orcaella σ U (i := i) hL').mpr hl'),
      fun h L' hL' hl' => h L' hL' ((link_orcaella σ U (i := i) hL').mp hl')⟩

end Hybrid

end Scheme

end LeanDag
