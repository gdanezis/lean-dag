import LeanDag.Common.Dedup
import Mathlib.Data.List.Nodup
/-!
# First-occurrence deduplication — lemmas

Generated proof layer; not part of the audit surface. What
`Common/Dedup.lean`'s filter guarantees: it is stable under extending
the list, emits no key twice, emits only what it was given, and loses no
key.
-/

namespace LeanDag

variable {α κ : Type*} [DecidableEq κ]

/-- Extending the input only extends the output. -/
theorem dedupFrom_prefix_append (key : α → κ) : ∀ (l₁ l₂ : List α) (seen : Finset κ),
    dedupFrom key l₁ seen <+: dedupFrom key (l₁ ++ l₂) seen := by
  intro l₁
  induction l₁ with
  | nil => intro l₂ seen; simp [dedupFrom]
  | cons a as ih =>
      intro l₂ seen
      by_cases h : key a ∈ seen
      · simp only [List.cons_append, dedupFrom, if_pos h]
        exact ih l₂ seen
      · simp only [List.cons_append, dedupFrom, if_neg h]
        exact (List.prefix_cons_inj a).mpr (ih l₂ _)

/-- An emitted element's key was not already seen. -/
theorem dedupFrom_key_notMem (key : α → κ) : ∀ (l : List α) (seen : Finset κ),
    ∀ b ∈ dedupFrom key l seen, key b ∉ seen := by
  intro l
  induction l with
  | nil => intro seen b hb; simp [dedupFrom] at hb
  | cons c cs ih =>
      intro seen b hb
      by_cases hc : key c ∈ seen
      · rw [dedupFrom, if_pos hc] at hb
        exact ih seen b hb
      · rw [dedupFrom, if_neg hc] at hb
        rcases List.mem_cons.mp hb with rfl | hb'
        · exact hc
        · exact fun hmem => ih _ b hb' (Finset.mem_insert_of_mem hmem)

/-- No key is emitted twice. -/
theorem dedupFrom_nodup_key (key : α → κ) : ∀ (l : List α) (seen : Finset κ),
    ((dedupFrom key l seen).map key).Nodup := by
  intro l
  induction l with
  | nil => intro seen; simp [dedupFrom]
  | cons c cs ih =>
      intro seen
      by_cases hc : key c ∈ seen
      · rw [dedupFrom, if_pos hc]; exact ih seen
      · rw [dedupFrom, if_neg hc, List.map_cons, List.nodup_cons]
        refine ⟨fun hmem => ?_, ih _⟩
        obtain ⟨b, hb, hkb⟩ := List.mem_map.mp hmem
        exact dedupFrom_key_notMem key cs _ b hb (hkb ▸ Finset.mem_insert_self (key c) seen)

/-- What is emitted is a subsequence of the input. -/
theorem dedupFrom_sublist (key : α → κ) : ∀ (l : List α) (seen : Finset κ),
    (dedupFrom key l seen).Sublist l := by
  intro l
  induction l with
  | nil => intro seen; simp [dedupFrom]
  | cons c cs ih =>
      intro seen
      by_cases hc : key c ∈ seen
      · rw [dedupFrom, if_pos hc]; exact (ih seen).cons c
      · rw [dedupFrom, if_neg hc]; exact (ih _).cons_cons c

/-- Every key of the input was seen already or is emitted. -/
theorem dedupFrom_key_mem (key : α → κ) : ∀ (l : List α) (seen : Finset κ),
    ∀ b ∈ l, key b ∈ seen ∨ ∃ c ∈ dedupFrom key l seen, key c = key b := by
  intro l
  induction l with
  | nil => intro seen b hb; simp at hb
  | cons c cs ih =>
      intro seen b hb
      by_cases hc : key c ∈ seen
      · rw [dedupFrom, if_pos hc]
        rcases List.mem_cons.mp hb with rfl | hb'
        · exact Or.inl hc
        · exact ih seen b hb'
      · rw [dedupFrom, if_neg hc]
        rcases List.mem_cons.mp hb with rfl | hb'
        · exact Or.inr ⟨b, List.mem_cons_self, rfl⟩
        · rcases ih (insert (key c) seen) b hb' with hin | ⟨d, hd, hdk⟩
          · rcases Finset.mem_insert.mp hin with heq | hin'
            · exact Or.inr ⟨c, List.mem_cons_self, heq.symm⟩
            · exact Or.inl hin'
          · exact Or.inr ⟨d, List.mem_cons_of_mem c hd, hdk⟩

/-! ## From the empty set -/

/-- **Prefixes survive deduplication.** -/
theorem dedupBy_prefix (key : α → κ) {l₁ l₂ : List α} (h : l₁ <+: l₂) :
    dedupBy key l₁ <+: dedupBy key l₂ := by
  obtain ⟨t, rfl⟩ := h
  exact dedupFrom_prefix_append key l₁ t ∅

/-- **No key appears twice.** -/
theorem dedupBy_nodup_key (key : α → κ) (l : List α) : ((dedupBy key l).map key).Nodup :=
  dedupFrom_nodup_key key l ∅

/-- Hence no element does. -/
theorem dedupBy_nodup (key : α → κ) (l : List α) : (dedupBy key l).Nodup :=
  List.Nodup.of_map key (dedupBy_nodup_key key l)

theorem dedupBy_sublist (key : α → κ) (l : List α) : (dedupBy key l).Sublist l :=
  dedupFrom_sublist key l ∅

/-- **No key is lost.** -/
theorem dedupBy_key_mem (key : α → κ) {l : List α} {b : α} (hb : b ∈ l) :
    ∃ c ∈ dedupBy key l, key c = key b := by
  rcases dedupFrom_key_mem key l ∅ b hb with hin | h
  · simp at hin
  · exact h

end LeanDag
