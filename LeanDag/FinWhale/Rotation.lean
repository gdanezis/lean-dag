import LeanDag.FinWhale.Liveness
import LeanDag.FinWhale.Model.Schedule
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.Ring

/-!
# FinWhale — the round-robin schedule supplies three correct leaders

Lemma 22: in any window of `3f + 3` rounds, round robin names three
consecutive correct-led rounds, which Lemma 23 needs for its committed
anchor. The paper's single cyclic argument only reaches `p = 1`; for
`p ≥ 2` the window is shorter than a cycle, so `three_correct_window`
supplies a pigeonhole argument instead, and `lemma22` picks whichever
of the two applies.
-/


namespace LeanDag

namespace FinWhale

variable {Validator : Type*} [Fintype Validator] [DecidableEq Validator]
variable [F : Faults Validator]

/-- The committee is nonempty, which is what `ZMod n` needs to be the
cyclic group of order `n`. -/
theorem neZero_card : NeZero (Fintype.card Validator) :=
  ⟨by have := F.card_validators; omega⟩

/-- **Lemma 22, the cyclic half**: some triple of consecutive correct
leaders lies within `n + 2` rounds, since otherwise every cyclic
position would carry a Byzantine leader within two of it, and each
Byzantine validator covers at most three positions, giving `n ≤ 3f`
against the fault model. -/
theorem three_correct_of_roundRobin {leader : ℕ → Validator} (h : RoundRobin leader) (r₀ : ℕ) :
    ∃ r, r₀ ≤ r ∧ r < r₀ + Fintype.card Validator ∧
      leader r ∈ (Correct : Finset Validator) ∧
      leader (r + 1) ∈ (Correct : Finset Validator) ∧
      leader (r + 2) ∈ (Correct : Finset Validator) := by
  classical
  obtain ⟨e, he⟩ := h
  haveI := neZero_card (Validator := Validator)
  by_contra hcon
  have hcon' : ∀ r, r₀ ≤ r → r < r₀ + Fintype.card Validator →
      ¬ (leader r ∈ (Correct : Finset Validator) ∧
        leader (r + 1) ∈ (Correct : Finset Validator) ∧
        leader (r + 2) ∈ (Correct : Finset Validator)) :=
    fun r h1 h2 h3 => hcon ⟨r, h1, h2, h3⟩
  -- every cyclic position carries a Byzantine leader within two of it
  have key : ∀ x : ZMod (Fintype.card Validator),
      ∃ y : ZMod (Fintype.card Validator),
        (y = x ∨ y = x + 1 ∨ y = x + 2) ∧ e y ∈ F.byzantine := by
    intro x
    obtain ⟨d, hd, hdx⟩ : ∃ d : ℕ, d < Fintype.card Validator ∧
        ((r₀ + d : ℕ) : ZMod (Fintype.card Validator)) = x := by
      refine ⟨(x - (r₀ : ZMod (Fintype.card Validator))).val, ZMod.val_lt _, ?_⟩
      push_cast [ZMod.natCast_val, ZMod.cast_id]
      ring
    have h0 : leader (r₀ + d) = e x := by rw [he, hdx]
    have h1 : leader (r₀ + d + 1) = e (x + 1) := by
      rw [he]; congr 1; push_cast [← hdx]; ring
    have h2 : leader (r₀ + d + 2) = e (x + 2) := by
      rw [he]; congr 1; push_cast [← hdx]; ring
    have hlo : r₀ ≤ r₀ + d := by omega
    have hhi : r₀ + d < r₀ + Fintype.card Validator := by omega
    by_cases hc0 : leader (r₀ + d) ∈ (Correct : Finset Validator)
    · by_cases hc1 : leader (r₀ + d + 1) ∈ (Correct : Finset Validator)
      · refine ⟨x + 2, Or.inr (Or.inr rfl), ?_⟩
        have hc2 : leader (r₀ + d + 2) ∉ (Correct : Finset Validator) :=
          fun hc2 => hcon' _ hlo hhi ⟨hc0, hc1, hc2⟩
        rw [← h2]; exact not_not.1 (mem_correct.not.1 hc2)
      · exact ⟨x + 1, Or.inr (Or.inl rfl), by rw [← h1]; exact not_not.1 (mem_correct.not.1 hc1)⟩
    · exact ⟨x, Or.inl rfl, by rw [← h0]; exact not_not.1 (mem_correct.not.1 hc0)⟩
  choose y hy hyb using key
  -- the Byzantine validator answering for each cyclic position
  have himg : (Finset.univ.image fun x => e (y x)) ⊆ F.byzantine := by
    intro b hb
    obtain ⟨x, -, rfl⟩ := Finset.mem_image.1 hb
    exact hyb x
  -- each Byzantine validator answers for at most three positions
  have hfib : ∀ b ∈ Finset.univ.image (fun x => e (y x)),
      (Finset.univ.filter fun x => e (y x) = b).card ≤ 3 := by
    intro b _
    have hsub : (Finset.univ.filter fun x => e (y x) = b) ⊆
        ({e.symm b, e.symm b - 1, e.symm b - 2} : Finset (ZMod (Fintype.card Validator))) := by
      intro x hx
      simp only [Finset.mem_filter] at hx
      have hyx : y x = e.symm b := by rw [← hx.2]; simp
      simp only [Finset.mem_insert, Finset.mem_singleton]
      rcases hy x with h | h | h
      · exact Or.inl (by rw [← h, hyx])
      · exact Or.inr (Or.inl (eq_sub_of_add_eq (by rw [← h, hyx])))
      · exact Or.inr (Or.inr (eq_sub_of_add_eq (by rw [← h, hyx])))
    refine le_trans (Finset.card_le_card hsub) ?_
    have hc1 := Finset.card_insert_le (e.symm b)
      ({e.symm b - 1, e.symm b - 2} : Finset (ZMod (Fintype.card Validator)))
    have hc2 := Finset.card_insert_le (e.symm b - 1)
      ({e.symm b - 2} : Finset (ZMod (Fintype.card Validator)))
    simp only [Finset.card_singleton] at hc1 hc2
    omega
  have hcount := Finset.card_le_mul_card_image (Finset.univ : Finset (ZMod _)) 3 hfib
  have hcard : (Finset.univ : Finset (ZMod (Fintype.card Validator))).card =
      Fintype.card Validator := by
    simp [Finset.card_univ, ZMod.card]
  have himgcard := Finset.card_le_card himg
  have := F.card_validators
  have := F.card_byzantine
  omega

/-- **Round robin names every validator once a cycle**, within any
starting round. -/
theorem exists_round_led_by {leader : ℕ → Validator} (h : RoundRobin leader)
    (v : Validator) (r₀ : ℕ) :
    ∃ s, r₀ ≤ s ∧ s < r₀ + Fintype.card Validator ∧ leader s = v := by
  obtain ⟨e, he⟩ := h
  haveI := neZero_card (Validator := Validator)
  refine ⟨r₀ + (e.symm v - (r₀ : ZMod (Fintype.card Validator))).val, by omega,
    by have := ZMod.val_lt (e.symm v - (r₀ : ZMod (Fintype.card Validator))); omega, ?_⟩
  rw [he]
  have hcast : ((r₀ + (e.symm v - (r₀ : ZMod (Fintype.card Validator))).val : ℕ) :
      ZMod (Fintype.card Validator)) = e.symm v := by
    push_cast [ZMod.natCast_val, ZMod.cast_id]
    ring
  rw [hcast, Equiv.apply_symm_apply]

omit [DecidableEq Validator] F in
/-- **Round robin is injective within a cycle**: two rounds of one
cycle with the same leader are the same round. -/
theorem leader_injOn {leader : ℕ → Validator} (h : RoundRobin leader) (a i i' : ℕ)
    (hi : i < Fintype.card Validator) (hi' : i' < Fintype.card Validator)
    (heq : leader (a + i) = leader (a + i')) : i = i' := by
  obtain ⟨e, he⟩ := h
  rw [he, he] at heq
  have hmod : (a + i) % Fintype.card Validator = (a + i') % Fintype.card Validator :=
    (ZMod.natCast_eq_natCast_iff' _ _ _).1 (e.injective heq)
  have hcancel : i % Fintype.card Validator = i' % Fintype.card Validator :=
    Nat.ModEq.add_left_cancel' a hmod
  rwa [Nat.mod_eq_of_lt hi, Nat.mod_eq_of_lt hi'] at hcancel

/-- **Lemma 22, the pigeonhole half**, where the window fits inside a
cycle: `f + 1` disjoint triples would need `f + 1` distinct Byzantine
leaders. -/
theorem three_correct_window {leader : ℕ → Validator} (h : RoundRobin leader)
    (hwide : 3 * F.f + 3 ≤ Fintype.card Validator) (r₀ : ℕ) :
    ∃ r, r₀ ≤ r ∧ r + 2 < r₀ + (3 * F.f + 3) ∧
      leader r ∈ (Correct : Finset Validator) ∧
      leader (r + 1) ∈ (Correct : Finset Validator) ∧
      leader (r + 2) ∈ (Correct : Finset Validator) := by
  classical
  by_contra hcon
  have hbad : ∀ i : Fin (F.f + 1), ∃ c : ℕ, c ≤ 2 ∧
      leader (r₀ + (3 * i.val + c)) ∈ F.byzantine := by
    intro i
    have hi : i.val ≤ F.f := by omega
    by_cases h0 : leader (r₀ + 3 * i.val) ∈ (Correct : Finset Validator)
    · by_cases h1 : leader (r₀ + 3 * i.val + 1) ∈ (Correct : Finset Validator)
      · refine ⟨2, by omega, ?_⟩
        have h2 : leader (r₀ + 3 * i.val + 2) ∉ (Correct : Finset Validator) :=
          fun h2 => hcon ⟨r₀ + 3 * i.val, by omega, by omega, h0, h1, h2⟩
        rw [show r₀ + (3 * i.val + 2) = r₀ + 3 * i.val + 2 by omega]
        exact not_not.1 (mem_correct.not.1 h2)
      · refine ⟨1, by omega, ?_⟩
        rw [show r₀ + (3 * i.val + 1) = r₀ + 3 * i.val + 1 by omega]
        exact not_not.1 (mem_correct.not.1 h1)
    · refine ⟨0, by omega, ?_⟩
      rw [show r₀ + (3 * i.val + 0) = r₀ + 3 * i.val by omega]
      exact not_not.1 (mem_correct.not.1 h0)
  choose c hc hcb using hbad
  have hinj : Set.InjOn (fun i : Fin (F.f + 1) => leader (r₀ + (3 * i.val + c i)))
      (Finset.univ : Finset (Fin (F.f + 1))) := by
    intro i _ i' _ heq
    have h1 : 3 * i.val + c i < Fintype.card Validator := by have := hc i; omega
    have h2 : 3 * i'.val + c i' < Fintype.card Validator := by have := hc i'; omega
    have := leader_injOn h r₀ _ _ h1 h2 heq
    have := hc i
    have := hc i'
    exact Fin.ext (by omega)
  have hcard := Finset.card_le_card_of_injOn _ (fun i _ => hcb i) hinj
  simp only [Finset.card_univ, Fintype.card_fin] at hcard
  have := F.card_byzantine
  omega

/-- **Lemma 22.** In any window of `3f + 3` rounds, round robin names
three consecutive correct-led rounds — the pigeonhole where the window
fits inside a cycle, the cyclic count at `p = 1` otherwise, though the
paper gives only the latter. -/
theorem lemma22 [P : Params Validator] {leader : ℕ → Validator} (h : RoundRobin leader)
    (r₀ : ℕ) :
    ∃ r, r₀ ≤ r ∧ r + 2 < r₀ + (3 * F.f + 3) ∧
      leader r ∈ (Correct : Finset Validator) ∧
      leader (r + 1) ∈ (Correct : Finset Validator) ∧
      leader (r + 2) ∈ (Correct : Finset Validator) := by
  rcases Nat.lt_or_ge (Fintype.card Validator) (3 * F.f + 3) with hw | hw
  · obtain ⟨r, hlo, hhi, htriple⟩ := three_correct_of_roundRobin h r₀
    have := params_arith (Validator := Validator)
    exact ⟨r, hlo, by omega, htriple⟩
  · exact three_correct_window h hw r₀

end FinWhale

end LeanDag
