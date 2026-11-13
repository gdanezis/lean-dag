import LeanDag.Barnacle.Model.Chains
import Mathlib.Data.Fintype.CardEmbedding
import Mathlib.Logic.Equiv.Fintype
/-!
# A random ordering opens with `w` validators of `T`

The first `w` positions of an ordering form an embedding `Fin w ↪ V`
(`prefixEmb`). Every such embedding is the prefix of the same number of
orderings (`card_fiber_eq`: a permutation of the validators carries one
fiber onto another), so the orderings whose prefix lies in `T` are the
fraction `|T|^(w) / n^(w)` of all orderings, falling factorials
(`card_prefixIn_mul`).
-/

namespace LeanDag

namespace Barnacle

variable {V : Type} [Fintype V] [DecidableEq V]

/-- The first `w` positions of an ordering. -/
def prefixEmb {w : ℕ} (hw : w ≤ Fintype.card V) (e : Fin (Fintype.card V) ≃ V) : Fin w ↪ V :=
  (Fin.castLEEmb hw).trans e.toEmbedding

theorem prefixEmb_apply {w : ℕ} (hw : w ≤ Fintype.card V) (e : Fin (Fintype.card V) ≃ V)
    (j : Fin w) : prefixEmb hw e j = e (Fin.castLE hw j) := rfl

/-- **Every prefix has as many orderings as every other.** -/
theorem card_fiber_eq {w : ℕ} (hw : w ≤ Fintype.card V) (φ ψ : Fin w ↪ V) :
    Fintype.card {e // prefixEmb hw e = φ} = Fintype.card {e // prefixEmb hw e = ψ} := by
  classical
  let r : Set.range φ ≃ Set.range ψ :=
    (Equiv.ofInjective φ φ.injective).symm.trans (Equiv.ofInjective ψ ψ.injective)
  let σ : Equiv.Perm V := Equiv.extendSubtype (p := fun x => x ∈ Set.range φ)
    (q := fun x => x ∈ Set.range ψ) r
  have hσ : ∀ j, σ (φ j) = ψ j := fun j => by
    have := Equiv.extendSubtype_apply_of_mem (p := fun x => x ∈ Set.range φ)
      (q := fun x => x ∈ Set.range ψ) r (φ j) ⟨j, rfl⟩
    rw [this]
    simp only [r, Equiv.trans_apply]
    rw [show (Equiv.ofInjective φ φ.injective).symm ⟨φ j, ⟨j, rfl⟩⟩ = j from
      (Equiv.ofInjective φ φ.injective).symm_apply_eq.mpr rfl]
    rfl
  refine Fintype.card_congr
    { toFun := fun e => ⟨e.1.trans σ, ?_⟩
      invFun := fun e => ⟨e.1.trans σ.symm, ?_⟩
      left_inv := fun e => Subtype.ext (Equiv.ext fun x => by simp)
      right_inv := fun e => Subtype.ext (Equiv.ext fun x => by simp) }
  · ext j
    rw [prefixEmb_apply, Equiv.trans_apply, ← prefixEmb_apply hw e.1 j, e.2, hσ]
  · ext j
    rw [prefixEmb_apply, Equiv.trans_apply, ← prefixEmb_apply hw e.1 j, e.2, ← hσ,
      Equiv.symm_apply_apply]

/-- **The orderings whose prefix lies in `T`**, counted against all of them:
`#{e | prefix in T} · n^(w) = |T|^(w) · n!`. -/
theorem card_prefixIn_mul {w : ℕ} (hw : w ≤ Fintype.card V) (T : Finset V) :
    (Finset.univ.filter fun e : Fin (Fintype.card V) ≃ V =>
        ∀ i : Fin (Fintype.card V), (i : ℕ) < w → e i ∈ T).card *
      (Fintype.card V).descFactorial w =
    T.card.descFactorial w * Fintype.card (Fin (Fintype.card V) ≃ V) := by
  classical
  obtain ⟨φ₀⟩ : Nonempty (Fin w ↪ V) := by
    rw [← Fintype.card_pos_iff, Fintype.card_embedding_eq, Fintype.card_fin]
    exact Nat.descFactorial_pos.mpr hw
  set F := Fintype.card {e // prefixEmb hw e = φ₀}
  -- the orderings with prefix in a set `S` of embeddings number `|S| · F`
  have hcount : ∀ S : Finset (Fin w ↪ V),
      (Finset.univ.filter fun e => prefixEmb hw e ∈ S).card = S.card * F := by
    intro S
    have hf := Finset.card_eq_sum_card_fiberwise
      (s := Finset.univ.filter fun e => prefixEmb hw e ∈ S) (t := S) (f := prefixEmb hw)
      (fun e he => (Finset.mem_filter.mp he).2)
    rw [hf, Finset.sum_const_nat (m := F) fun φ hφ => ?_]
    show _ = Fintype.card {e // prefixEmb hw e = φ₀}
    rw [card_fiber_eq hw φ₀ φ, Fintype.card_subtype]
    congr 1
    ext e
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, and_iff_right_iff_imp]
    rintro rfl; exact hφ
  -- the embeddings into `T`
  let S : Finset (Fin w ↪ V) := Finset.univ.filter fun φ => ∀ j, φ j ∈ T
  have hS : S.card = T.card.descFactorial w := by
    have : S.card = Fintype.card (Fin w ↪ T) := by
      rw [← Fintype.card_coe]
      refine Fintype.card_congr
        { toFun := fun φ => ⟨fun j => ⟨φ.1 j, (Finset.mem_filter.mp φ.2).2 j⟩,
            fun a b h => φ.1.injective (congrArg Subtype.val h)⟩
          invFun := fun ψ => ⟨ψ.trans (Function.Embedding.subtype _),
            Finset.mem_filter.mpr ⟨Finset.mem_univ _, fun j => (ψ j).2⟩⟩
          left_inv := fun φ => by ext; rfl
          right_inv := fun ψ => by ext; rfl }
    rw [this, Fintype.card_embedding_eq, Fintype.card_fin, Fintype.card_coe]
  have hpre : (Finset.univ.filter fun e : Fin (Fintype.card V) ≃ V =>
      ∀ i : Fin (Fintype.card V), (i : ℕ) < w → e i ∈ T) =
      Finset.univ.filter fun e => prefixEmb hw e ∈ S := by
    ext e
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, S, prefixEmb_apply]
    constructor
    · intro h j; exact h _ (by simp)
    · intro h i hi
      simpa using h ⟨i, hi⟩
  have hall : Fintype.card (Fin (Fintype.card V) ≃ V) = (Fintype.card V).descFactorial w * F := by
    have := hcount Finset.univ
    rw [Finset.card_univ, Fintype.card_embedding_eq, Fintype.card_fin] at this
    rw [← this]
    simp
  rw [hpre, hcount S, hS, hall]
  ring

end Barnacle

end LeanDag
