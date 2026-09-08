import LeanDag.FinWhale.Consistency
import LeanDag.FinWhale.Model.Order
/-!
# FinWhale — commit sequences and the delivered order

Lemma 12 settles one slot at a time; this file carries the argument to
the whole sequence. `commitSeq` is a validator's committed leader
sequence; Lemma 13 makes any two prefix-comparable. `linearise` is the
delivery order built by walking the leader sequence and appending each
leader's undelivered causal history; Theorem 14 (total order) and
Theorem 15 (integrity) follow since it only ever appends.
-/


namespace LeanDag

namespace FinWhale

variable {BlockId : Type*} [DecidableEq BlockId]

omit [DecidableEq BlockId] in
/-- Verdicts agreeing below `k` give the same sequence. -/
theorem commitSeq_congr {dec dec' : ℕ → Verdict BlockId} :
    ∀ k, (∀ s, s < k → dec s = dec' s) → commitSeq dec k = commitSeq dec' k := by
  intro k
  induction k with
  | zero => intro _; rfl
  | succ k ih =>
    intro h
    simp only [commitSeq, ih fun s hs => h s (by omega), h k (by omega)]

omit [DecidableEq BlockId] in
/-- Scanning further extends the sequence. -/
theorem commitSeq_prefix (dec : ℕ → Verdict BlockId) {k k' : ℕ} (h : k ≤ k') :
    commitSeq dec k <+: commitSeq dec k' := by
  induction k' with
  | zero =>
    have hk : k = 0 := by omega
    subst hk; exact List.prefix_rfl
  | succ k' ih =>
    rcases Nat.lt_or_ge k (k' + 1) with hlt | hge
    · exact (ih (by omega)).trans (by simp only [commitSeq]; exact List.prefix_append _ _)
    · have hk : k = k' + 1 := by omega
      subst hk; exact List.prefix_rfl

omit [DecidableEq BlockId] in
/-- **Lemma 13.** Two validators' committed leader sequences are
prefix-comparable. Each validator commits up to its first undecided slot,
Lemma 12 makes the two agree wherever both have decided, and the shorter
decided prefix is a prefix of the longer. -/
theorem lemma13 {dec dec' : ℕ → Verdict BlockId} {k k' : ℕ}
    (hagree : ∀ s, dec s ≠ Verdict.undecided → dec' s ≠ Verdict.undecided → dec s = dec' s)
    (hk : ∀ s, s < k → dec s ≠ Verdict.undecided)
    (hk' : ∀ s, s < k' → dec' s ≠ Verdict.undecided) :
    commitSeq dec k <+: commitSeq dec' k' ∨ commitSeq dec' k' <+: commitSeq dec k := by
  rcases le_total k k' with hle | hle
  · refine Or.inl ?_
    rw [commitSeq_congr k fun s hs => hagree s (hk s hs) (hk' s (by omega))]
    exact commitSeq_prefix dec' hle
  · refine Or.inr ?_
    rw [← commitSeq_congr k' fun s hs => hagree s (hk s (by omega)) (hk' s hs)]
    exact commitSeq_prefix dec hle

/-- The accumulator only grows at its end. -/
theorem linearise_foldl_append (hist : BlockId → List BlockId) :
    ∀ (ls : List BlockId) (acc : List BlockId),
      ∃ t, ls.foldl (fun acc l => acc ++ (hist l).filter (fun b => b ∉ acc)) acc = acc ++ t := by
  intro ls
  induction ls with
  | nil => intro acc; exact ⟨[], by simp⟩
  | cons l ls ih =>
    intro acc
    obtain ⟨t, ht⟩ := ih (acc ++ (hist l).filter (fun b => b ∉ acc))
    exact ⟨(hist l).filter (fun b => b ∉ acc) ++ t,
      by simp only [List.foldl_cons, ht, List.append_assoc]⟩

/-- **Theorem 14 (Total Order).** A longer committed leader sequence
delivers an extension of what a shorter one delivers, so two validators
never disagree on the order of what both have delivered. With Lemma 13
this is the total order property: the two leader sequences are
prefix-comparable, hence so are the two delivery orders. -/
theorem theorem14 (hist : BlockId → List BlockId) {ls ls' : List BlockId}
    (h : ls <+: ls') : linearise hist ls <+: linearise hist ls' := by
  obtain ⟨t, rfl⟩ := h
  obtain ⟨u, hu⟩ := linearise_foldl_append hist t (linearise hist ls)
  refine ⟨u, ?_⟩
  simpa [linearise, List.foldl_append] using hu.symm

/-- **Theorem 15 (Integrity).** No block is delivered twice: each leader
appends only what the accumulator does not already hold, and a causal
history lists each block once. -/
theorem theorem15 (hist : BlockId → List BlockId) (hnd : ∀ l, (hist l).Nodup)
    (ls : List BlockId) : (linearise hist ls).Nodup := by
  have key : ∀ (ls : List BlockId) (acc : List BlockId), acc.Nodup →
      (ls.foldl (fun acc l => acc ++ (hist l).filter (fun b => b ∉ acc)) acc).Nodup := by
    intro ls
    induction ls with
    | nil => intro acc h; exact h
    | cons l ls ih =>
      intro acc h
      refine ih _ ?_
      rw [List.nodup_append]
      refine ⟨h, (hnd l).filter _, ?_⟩
      intro a ha b hb hab
      have hnot := List.of_mem_filter hb
      simp only [decide_eq_true_eq] at hnot
      exact hnot (hab ▸ ha)
  exact key ls [] List.nodup_nil

end FinWhale

end LeanDag
