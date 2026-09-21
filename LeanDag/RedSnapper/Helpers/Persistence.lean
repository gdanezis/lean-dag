import LeanDag.RedSnapper.Model.Five.Moves
import LeanDag.RedSnapper.Helpers.Chain
import LeanDag.RedSnapper.Helpers.Counting
import LeanDag.RedSnapper.Helpers.Stance
import LeanDag.RedSnapper.Helpers.Exclusion

/-!
# Stance persistence under the move rule

Generated: the proof core of RS6. A silent correct block inherits its
self-parent's stance (its author's declaring blocks below the two are
the same); a correct set standing at one value, large enough that the
rest of the committee cannot fill a refutation (`n < |S| + half`),
therefore stands at that value at every own block from its base round
on — a declared change would need `half` anti-voting authors at the
round below, of whom those in `S` contradict the induction hypothesis
by the functionality of the stance read. `correct_core_of_atLeast`
extracts such a set from any parent threshold. None of this consumes
the `Five` bound. Nothing here is part of the audit surface.
-/

namespace LeanDag

namespace RedSnapper

variable {Validator BlockId Tx Obj : Type*} [Fintype Validator] [DecidableEq Validator]
  [F : Faults Validator] [T : Transactions Tx Obj] {U : Universe Validator BlockId Tx Obj}

omit T in
/-- A threshold whose predicate avoids the authors of `S` fails when the
rest of the committee is too small to fill it. -/
theorem not_atLeast_of_disjoint {k : ℕ} {s : Finset BlockId} {P : BlockId → Prop}
    {S : Finset Validator} (hcount : Fintype.card Validator < S.card + k)
    (havoid : ∀ b ∈ s, P b → (U.block b).author ∉ S) : ¬ AtLeast U k s P := by
  rintro ⟨t, hts, hP, hk⟩
  have hsub : authorsOf U.block t ⊆ Sᶜ := by
    intro v hv
    obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp hv
    exact Finset.mem_compl.mpr (havoid b (hts hb) (hP b hb))
  have hle := Finset.card_le_card hsub
  rw [Finset.card_compl] at hle
  have hSn : S.card ≤ Fintype.card Validator := by
    simpa using Finset.card_le_card (Finset.subset_univ S)
  omega

omit T in
/-- Below a silent correct block, the author's declaring blocks on an
object are exactly those below its self-parent. -/
theorem declaring_congr_of_silent {b p : BlockId} {o : Obj} (hb : b ∈ U.ids)
    (hc : (U.block b).author ∈ (Correct : Finset Validator))
    (hp : p ∈ (U.block b).parents) (hap : (U.block p).author = (U.block b).author)
    (hd : (U.block b).declares o = none) (b' : BlockId) :
    Declaring U (U.block b).author o b b' ↔ Declaring U (U.block b).author o p b' := by
  have hpid : p ∈ U.ids := U.complete b hb p hp
  have hpr : (U.block p).round + 1 = (U.block b).round := round_of_mem_parents hb hp
  constructor
  · rintro ⟨hb'id, hab', hreach, hdec⟩
    have hne : b' ≠ b := fun h => hdec (h ▸ hd)
    have hlt := round_lt_of_reaches_ne hb hreach hne
    exact ⟨hb'id, hab', reaches_own_of_round_le hpid hb'id (hap.symm ▸ hc)
      (hab'.trans hap.symm) (by omega), hdec⟩
  · rintro ⟨hb'id, hab', hreach, hdec⟩
    exact ⟨hb'id, hab', Reaches.of_mem_parents hp hreach, hdec⟩

omit T in
/-- Two read points with the same declaring blocks read the same
stance. -/
theorem stanceIs_congr_of_declaring {id : Validator} {o : Obj} {b₁ b₂ : BlockId}
    (h : ∀ b', Declaring U id o b₁ b' ↔ Declaring U id o b₂ b') (s : Option (Stance Tx)) :
    StanceIs U id o b₁ s ↔ StanceIs U id o b₂ s := by
  have hL : ∀ b', Latest U id o b₁ b' ↔ Latest U id o b₂ b' := by
    intro b'
    constructor
    · rintro ⟨hd, hmax⟩
      exact ⟨(h b').mp hd, fun b'' hb'' => hmax b'' ((h b'').mpr hb'')⟩
    · rintro ⟨hd, hmax⟩
      exact ⟨(h b').mpr hd, fun b'' hb'' => hmax b'' ((h b'').mp hb'')⟩
  cases s with
  | some v =>
      constructor <;> rintro ⟨b', hLb, hd, hu⟩
      · exact ⟨b', (hL b').mp hLb, hd, fun b'' hb'' => hu b'' ((hL b'').mpr hb'')⟩
      · exact ⟨b', (hL b').mpr hLb, hd, fun b'' hb'' => hu b'' ((hL b'').mp hb'')⟩
  | none =>
      constructor <;> rintro (hno | ⟨c₁, c₂, hc₁, hc₂, hne⟩)
      · exact Or.inl fun ⟨b', hb'⟩ => hno ⟨b', (h b').mpr hb'⟩
      · exact Or.inr ⟨c₁, c₂, (hL c₁).mp hc₁, (hL c₂).mp hc₂, hne⟩
      · exact Or.inl fun ⟨b', hb'⟩ => hno ⟨b', (h b').mp hb'⟩
      · exact Or.inr ⟨c₁, c₂, (hL c₁).mpr hc₁, (hL c₂).mpr hc₂, hne⟩

omit T in
/-- Stance persistence: a correct set standing at `s₀` at round `ρ₀`,
large enough that the rest of the committee cannot fill a refutation,
stands at `s₀` at every own block from `ρ₀` on. -/
theorem stance_persists (hmove : MoveDiscipline U) {o : Obj} {s₀ : Stance Tx} {ρ₀ : ℕ}
    {S : Finset Validator} (hS : S ⊆ (Correct : Finset Validator))
    (hcount : Fintype.card Validator < S.card + half Validator)
    (hbase : ∀ v ∈ S, ∀ b ∈ U.ids, (U.block b).author = v →
      (U.block b).round = ρ₀ → StanceIs U v o b (some s₀))
    {v : Validator} {b : BlockId} (hv : v ∈ S) (hb : b ∈ U.ids)
    (hab : (U.block b).author = v) (hρ : ρ₀ ≤ (U.block b).round) :
    StanceIs U v o b (some s₀) := by
  suffices h : ∀ n : ℕ, ∀ b ∈ U.ids, (U.block b).author ∈ S →
      ρ₀ ≤ (U.block b).round → (U.block b).round = n →
      StanceIs U (U.block b).author o b (some s₀) by
    subst hab
    exact h _ b hb hv hρ rfl
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
      intro b hb hv hρ hn
      subst hn
      rcases Nat.eq_or_lt_of_le hρ with heq | hlt
      · exact hbase _ hv b hb rfl heq.symm
      · have hc : (U.block b).author ∈ (Correct : Finset Validator) := hS hv
        obtain ⟨p, hpmem, hap⟩ := U.self_parent b hb hc (by omega)
        have hpid : p ∈ U.ids := U.complete b hb p hpmem
        have hpr : (U.block p).round + 1 = (U.block b).round :=
          round_of_mem_parents hb hpmem
        have hps : StanceIs U (U.block b).author o p (some s₀) := by
          have := ih (U.block p).round (by omega) p hpid
            (by rw [hap]; exact hv) (by omega) rfl
          rwa [hap] at this
        cases hd : (U.block b).declares o with
        | none =>
            exact (stanceIs_congr_of_declaring
              (declaring_congr_of_silent hb hc hpmem hap hd) (some s₀)).mpr hps
        | some s' =>
            by_cases hss : s' = s₀
            · subst hss
              exact stanceIs_self_of_declares hb hd
            · exfalso
              have href := hmove.move_on_refutation b hb hc p hpmem hap o s₀ s' hps hd hss
              refine not_atLeast_of_disjoint hcount ?_ href
              rintro q hq ⟨s'', hst, hne⟩ hqS
              have hqid : q ∈ U.ids := U.complete b hb q hq
              have hqr : (U.block q).round + 1 = (U.block b).round :=
                round_of_mem_parents hb hq
              have hind := ih (U.block q).round (by omega) q hqid hqS (by omega) rfl
              exact hne (Option.some.inj (stanceIs_unique hst hind))

omit T in
/-- The correct core of a parent threshold: at least `k − f` correct
authors whose blocks at the parents' round satisfy the predicate. -/
theorem correct_core_of_atLeast {C : BlockId} {k : ℕ} {P : BlockId → Prop}
    (hC : C ∈ U.ids) (h : AtLeast U k (U.block C).parents P) :
    ∃ S : Finset Validator, S ⊆ (Correct : Finset Validator) ∧ k ≤ S.card + F.f ∧
      ∀ v ∈ S, ∀ b ∈ U.ids, (U.block b).author = v →
        (U.block b).round + 1 = (U.block C).round → P b := by
  obtain ⟨t, hts, hP, hk⟩ := h
  refine ⟨authorsOf U.block t ∩ Correct, Finset.inter_subset_right, ?_, ?_⟩
  · have h1 : authorsOf U.block t ⊆ (authorsOf U.block t ∩ Correct) ∪ F.byzantine := by
      intro v hv
      by_cases hcv : v ∈ (Correct : Finset Validator)
      · exact Finset.mem_union_left _ (Finset.mem_inter.mpr ⟨hv, hcv⟩)
      · exact Finset.mem_union_right _ (by simpa [Correct] using hcv)
    have h2 := Finset.card_le_card h1
    have h3 := Finset.card_union_le (authorsOf U.block t ∩ Correct) F.byzantine
    have h4 := F.card_byzantine
    omega
  · rintro v hv b hb hab hr
    obtain ⟨hva, hvc⟩ := Finset.mem_inter.mp hv
    obtain ⟨q, hq, haq⟩ := Finset.mem_image.mp hva
    have hqid : q ∈ U.ids := U.complete C hC q (hts hq)
    have hqr : (U.block q).round + 1 = (U.block C).round :=
      round_of_mem_parents hC (hts hq)
    have hbq : b = q :=
      U.no_equivocation b hb q hqid (hab.symm ▸ hvc) (by rw [hab, haq]) (by omega)
    exact hbq ▸ hP q hq

omit T in
/-- A positive parent threshold forces a positive round. -/
theorem round_pos_of_atLeast {C : BlockId} {k : ℕ} {P : BlockId → Prop}
    (hC : C ∈ U.ids) (hk : 0 < k) (h : AtLeast U k (U.block C).parents P) :
    0 < (U.block C).round := by
  obtain ⟨t, hts, -, hcard⟩ := h
  have hne : t.Nonempty := by
    by_contra hno
    rw [Finset.not_nonempty_iff_eq_empty] at hno
    subst hno
    simp only [authorsOf, Finset.image_empty, Finset.card_empty] at hcard
    omega
  obtain ⟨q, hq⟩ := hne
  have := round_of_mem_parents hC (hts hq)
  omega

end RedSnapper

end LeanDag
