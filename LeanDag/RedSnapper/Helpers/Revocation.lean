import Mathlib.Data.Fintype.Fin
import Mathlib.Data.Finset.Powerset
import LeanDag.RedSnapper.Revocation.Statement

/-!
# Vote profiles — lemmas and constructions

Generated infrastructure for `Revocation/Proof.lean`; not part of the
audit surface. The support bound and its consequence; the pigeonhole
direction of exposure; and the two witness families over `Fin n` — the
tightness profile and the even split — with their counts.
-/

namespace LeanDag

namespace RedSnapper

namespace Revocation

section Profiles

variable {Validator Value : Type*} [Fintype Validator] [DecidableEq Validator]
  [DecidableEq Value] (P : Profile Validator Value) (x : Value)

/-- A validator both supporting and opposing `x` voted twice, so it is
Byzantine. -/
theorem inter_subset_byzantine : supporters P x ∩ opposers P x ⊆ P.byzantine := by
  intro v hv
  simp only [supporters, opposers, Finset.mem_inter, Finset.mem_filter, Finset.mem_univ,
    true_and] at hv
  obtain ⟨hx, y, hy, hne⟩ := hv
  by_contra hb
  have h1 := P.honest_single v hb
  have h2 : 1 < (P.votes v).card :=
    Finset.one_lt_card.2 ⟨x, hx, y, hy, fun h => hne h.symm⟩
  omega

theorem supportBound : SupportBound P x := by
  unfold SupportBound
  have h1 := Finset.card_union_add_card_inter (supporters P x) (opposers P x)
  have h2 : (supporters P x ∪ opposers P x).card ≤ Fintype.card Validator := by
    have := Finset.card_le_card (Finset.subset_univ (supporters P x ∪ opposers P x))
    rwa [Finset.card_univ] at this
  have h3 := Finset.card_le_card (inter_subset_byzantine P x)
  have h4 := P.card_byzantine
  omega

theorem sufficient (C : ℕ) : Sufficient P x C := by
  unfold Sufficient
  have := supportBound P x
  unfold SupportBound at this
  omega

/-- A voter supports `x` or opposes it. -/
theorem mem_supporters_or_opposers {v : Validator} (hv : v ∈ voters P) :
    v ∈ supporters P x ∨ v ∈ opposers P x := by
  simp only [voters, supporters, opposers, Finset.mem_filter, Finset.mem_univ, true_and] at hv ⊢
  obtain ⟨y, hy⟩ := hv
  by_cases h : y = x
  · exact Or.inl (h ▸ hy)
  · exact Or.inr ⟨y, hy, h⟩

/-- The pigeonhole direction of exposure. -/
theorem exposes_of_le {Q R : ℕ} (hR : R ≤ (Q + 1) / 2) : Exposes P x Q R := by
  intro S hS hQ
  have hsub : S ⊆ (S ∩ supporters P x) ∪ (S ∩ opposers P x) := by
    intro v hv
    rcases mem_supporters_or_opposers P x (hS hv) with h | h
    · exact Finset.mem_union_left _ (Finset.mem_inter.2 ⟨hv, h⟩)
    · exact Finset.mem_union_right _ (Finset.mem_inter.2 ⟨hv, h⟩)
  have := (Finset.card_le_card hsub).trans (Finset.card_union_le _ _)
  omega

end Profiles

section Fin

/-- The validators of `Fin n` with index below `m ≤ n` number `m`. -/
theorem card_filter_lt (n m : ℕ) (h : m ≤ n) :
    (Finset.univ.filter fun v : Fin n => (v : ℕ) < m).card = m := by
  rw [Fin.card_filter_val_lt, min_eq_right h]

/-- The validators of `Fin n` with index at or above `m ≤ n` number
`n − m`. -/
theorem card_filter_not_lt (n m : ℕ) (h : m ≤ n) :
    (Finset.univ.filter fun v : Fin n => ¬ (v : ℕ) < m).card + m = n := by
  have := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset (Fin n)))
    (fun v : Fin n => (v : ℕ) < m)
  rw [card_filter_lt n m h, Finset.card_univ, Fintype.card_fin] at this
  omega

/-- The tightness profile on `n` validators: the first `f` Byzantine and
voting both ways, the next `R − f` voting `false`, the rest `true`. -/
def tightProfile (n f R : ℕ) (hf : f ≤ R) (hR : R ≤ n) : Profile (Fin n) Bool where
  f := f
  byzantine := Finset.univ.filter fun v => (v : ℕ) < f
  card_byzantine := by rw [card_filter_lt n f (hf.trans hR)]
  votes := fun v =>
    if (v : ℕ) < f then {true, false} else if (v : ℕ) < R then {false} else {true}
  honest_single := by
    intro v hv
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hv
    simp [hv]
    split_ifs <;> simp

theorem opposers_tightProfile (n f R : ℕ) (hf : f ≤ R) (hR : R ≤ n) :
    opposers (tightProfile n f R hf hR) true =
      Finset.univ.filter fun v : Fin n => (v : ℕ) < R := by
  ext v
  simp only [opposers, tightProfile, Finset.mem_filter, Finset.mem_univ, true_and]
  split_ifs with h1 h2 <;> simp <;> omega

theorem supporters_tightProfile (n f R : ℕ) (hf : f ≤ R) (hR : R ≤ n) :
    supporters (tightProfile n f R hf hR) true =
      Finset.univ.filter fun v : Fin n => ¬ (f ≤ (v : ℕ) ∧ (v : ℕ) < R) := by
  ext v
  simp only [supporters, tightProfile, Finset.mem_filter, Finset.mem_univ, true_and]
  split_ifs with h1 h2 <;> simp <;> omega

/-- The validators with index in `[f, R)` number `R − f`. -/
theorem card_filter_Ico (n f R : ℕ) (hf : f ≤ R) (hR : R ≤ n) :
    (Finset.univ.filter fun v : Fin n => f ≤ (v : ℕ) ∧ (v : ℕ) < R).card + f = R := by
  have h := Finset.card_filter_add_card_filter_not
    (s := Finset.univ.filter fun v : Fin n => (v : ℕ) < R) (fun v : Fin n => (v : ℕ) < f)
  rw [Finset.filter_filter, Finset.filter_filter, card_filter_lt n R hR] at h
  have h1 : (Finset.univ.filter fun v : Fin n => (v : ℕ) < R ∧ (v : ℕ) < f) =
      Finset.univ.filter fun v : Fin n => (v : ℕ) < f := by
    apply Finset.filter_congr
    intro v _
    constructor
    · exact fun h => h.2
    · exact fun h => ⟨by omega, h⟩
  have h2 : (Finset.univ.filter fun v : Fin n => (v : ℕ) < R ∧ ¬ (v : ℕ) < f) =
      Finset.univ.filter fun v : Fin n => f ≤ (v : ℕ) ∧ (v : ℕ) < R := by
    apply Finset.filter_congr
    intro v _
    omega
  rw [h1, h2, card_filter_lt n f (hf.trans hR)] at h
  omega

theorem tight (n f C : ℕ) (hf : f ≤ C) (hC : C ≤ n) : Tight n f C := by
  have hfR : f ≤ n + f - C := by omega
  have hRn : n + f - C ≤ n := by omega
  refine ⟨tightProfile n f (n + f - C) hfR hRn, rfl, ?_, ?_⟩
  · rw [opposers_tightProfile, card_filter_lt n _ hRn]
    omega
  · rw [supporters_tightProfile]
    have h := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset (Fin n)))
      (fun v : Fin n => f ≤ (v : ℕ) ∧ (v : ℕ) < n + f - C)
    rw [Finset.card_univ, Fintype.card_fin] at h
    have h2 := card_filter_Ico n f (n + f - C) hfR hRn
    omega

/-- The even split on `Q` correct validators: the first `⌈Q/2⌉` vote
`true`, the rest `false`. -/
def evenProfile (Q : ℕ) : Profile (Fin Q) Bool where
  f := 0
  byzantine := ∅
  card_byzantine := by simp
  votes := fun v => if (v : ℕ) < (Q + 1) / 2 then {true} else {false}
  honest_single := by
    intro v _
    split_ifs <;> simp

theorem supporters_evenProfile (Q : ℕ) :
    supporters (evenProfile Q) true =
      Finset.univ.filter fun v : Fin Q => (v : ℕ) < (Q + 1) / 2 := by
  ext v
  simp only [supporters, evenProfile, Finset.mem_filter, Finset.mem_univ, true_and]
  split_ifs <;> simp_all

theorem opposers_evenProfile (Q : ℕ) :
    opposers (evenProfile Q) true =
      Finset.univ.filter fun v : Fin Q => ¬ (v : ℕ) < (Q + 1) / 2 := by
  ext v
  simp only [opposers, evenProfile, Finset.mem_filter, Finset.mem_univ, true_and]
  split_ifs <;> simp_all

theorem univ_subset_voters_evenProfile (Q : ℕ) :
    (Finset.univ : Finset (Fin Q)) ⊆ voters (evenProfile Q) := by
  intro v _
  simp only [voters, evenProfile, Finset.mem_filter, Finset.mem_univ, true_and]
  split_ifs <;> simp

/-- The even split refutes exposure above `⌈Q/2⌉`. -/
theorem not_exposes_evenProfile {Q R : ℕ} (hR : (Q + 1) / 2 < R) :
    ¬ Exposes (evenProfile Q) true Q R := by
  intro h
  have := h Finset.univ (univ_subset_voters_evenProfile Q) (by simp)
  rw [Finset.univ_inter, Finset.univ_inter, supporters_evenProfile, opposers_evenProfile,
    card_filter_lt Q _ (by omega)] at this
  have h2 := card_filter_not_lt Q ((Q + 1) / 2) (by omega)
  omega

end Fin

theorem exposureIff (Q R : ℕ) : ExposureIff Q R := by
  unfold ExposureIff
  constructor
  · intro h
    by_contra hlt
    exact not_exposes_evenProfile (by omega) (h (Fin Q) Bool (evenProfile Q) true)
  · intro hR Validator Value _ _ _ P x
    exact exposes_of_le P x hR

theorem strictThresholdIff (n f C : ℕ) : StrictThresholdIff n f C := by
  unfold StrictThresholdIff
  constructor
  · rintro ⟨R, h1, h2⟩
    omega
  · intro h
    exact ⟨n + f + 1 - C, by omega, by omega⟩

section Committee

variable (Validator : Type*) [Fintype Validator] [DecidableEq Validator] [F : Faults Validator]

theorem thresholdAtQuorum : ThresholdAtQuorum Validator := by
  unfold ThresholdAtQuorum quorum half
  have := F.card_validators
  intro R
  omega

theorem strictAtQuorum : StrictAtQuorum Validator := by
  unfold StrictAtQuorum quorum half
  have := F.card_validators
  omega

theorem exposureAtQuorum : ExposureAtQuorum Validator := by
  unfold ExposureAtQuorum quorum half
  have := F.card_validators
  omega

end Committee

end Revocation

end RedSnapper

end LeanDag
