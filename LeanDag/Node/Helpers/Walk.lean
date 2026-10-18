import LeanDag.Node.Model.Step
/-!
# The walk reaches every missing block down a chain of pending blocks

`walkLevel` iterated from a front: if a chain of pending blocks leads
from a block of the front, each a reference of the one before, down to a
block that is neither pending nor accepted, the walk finds that block
within as many levels as the chain is long (`walk_reaches`). A block met
at a level is either expanded there, if pending, or kept as missing; a
block met again was met at an earlier level, so its expansion is
already in hand.
-/

namespace LeanDag

namespace Node

variable {Validator BlockId Payload : Type} [Fintype Validator] [DecidableEq Validator]
variable [LinearOrder BlockId]
variable (s : State Validator BlockId Payload)

/-- The blocks a level of the walk meets: its front, at or above the
horizon, neither accepted nor met already. -/
def walkFront (w : List (BlockId × ℕ) × List BlockId × List (BlockId × ℕ)) :
    List (BlockId × ℕ) :=
  (w.1.filter fun x =>
    decide (s.store.base ≤ x.2) && decide (x.1 ∉ s.store.ids) && decide (x.1 ∉ w.2.1)).dedup

variable {s}

omit [Fintype Validator] [DecidableEq Validator] in
theorem walkLevel_eq (w : List (BlockId × ℕ) × List BlockId × List (BlockId × ℕ)) :
    walkLevel s w =
      (((walkFront s w).filter fun x => decide (x.1 ∈ s.pending.map Prod.fst)).flatMap
          (fun x => expand s x.1),
        w.2.1 ++ (walkFront s w).map Prod.fst,
        w.2.2 ++ (walkFront s w).filter fun x => !decide (x.1 ∈ s.pending.map Prod.fst)) := by
  simp only [walkLevel, walkFront, List.partition_eq_filter_filter]
  rfl

omit [Fintype Validator] [DecidableEq Validator] in
theorem mem_walkFront {w : List (BlockId × ℕ) × List BlockId × List (BlockId × ℕ)}
    {x : BlockId × ℕ} :
    x ∈ walkFront s w ↔ x ∈ w.1 ∧ s.store.base ≤ x.2 ∧ x.1 ∉ s.store.ids ∧ x.1 ∉ w.2.1 := by
  simp only [walkFront, List.mem_dedup, List.mem_filter, Bool.and_eq_true, decide_eq_true_eq]
  tauto

variable (s) in
/-- The walk's state after `ℓ` levels from the front `init`. -/
abbrev walkAt (init : List (BlockId × ℕ)) (ℓ : ℕ) :
    List (BlockId × ℕ) × List BlockId × List (BlockId × ℕ) :=
  (walkLevel s)^[ℓ] (init, [], [])

omit [Fintype Validator] [DecidableEq Validator] in
theorem walkAt_succ (init : List (BlockId × ℕ)) (ℓ : ℕ) :
    walkAt s init (ℓ + 1) = walkLevel s (walkAt s init ℓ) :=
  Function.iterate_succ_apply' _ _ _

omit [Fintype Validator] [DecidableEq Validator] in
/-- **What a level keeps as missing stays so.** -/
theorem acc_mono (init : List (BlockId × ℕ)) {ℓ : ℕ} {y : BlockId × ℕ}
    (hy : y ∈ (walkAt s init ℓ).2.2) : ∀ k, y ∈ (walkAt s init (ℓ + k)).2.2
  | 0 => hy
  | k + 1 => by
    rw [← Nat.add_assoc, walkAt_succ, walkLevel_eq]
    exact List.mem_append_left _ (acc_mono init hy k)

omit [Fintype Validator] [DecidableEq Validator] in
/-- **An identifier met already was met at an earlier level.** -/
theorem seen_earlier (init : List (BlockId × ℕ)) :
    ∀ ℓ, ∀ j ∈ (walkAt s init ℓ).2.1, ∃ ℓ' < ℓ, ∃ x ∈ walkFront s (walkAt s init ℓ'), x.1 = j
  | 0, j, hj => by simp [walkAt] at hj
  | ℓ + 1, j, hj => by
    rw [walkAt_succ, walkLevel_eq] at hj
    rcases List.mem_append.mp hj with hj | hj
    · obtain ⟨ℓ', hℓ', x, hx, hxj⟩ := seen_earlier init ℓ j hj
      exact ⟨ℓ', by omega, x, hx, hxj⟩
    · obtain ⟨x, hx, hxj⟩ := List.mem_map.mp hj
      exact ⟨ℓ, by omega, x, hx, hxj⟩

omit [Fintype Validator] [DecidableEq Validator] in
/-- **The walk reaches every missing block down a chain of pending
blocks.** -/
theorem walk_reaches (init : List (BlockId × ℕ)) {n : ℕ} (x : ℕ → BlockId × ℕ)
    (h0 : x 0 ∈ init)
    (hok : ∀ i ≤ n, s.store.base ≤ (x i).2 ∧ (x i).1 ∉ s.store.ids)
    (hpend : ∀ i < n, (x i).1 ∈ s.pending.map Prod.fst)
    (hstep : ∀ i < n, x (i + 1) ∈ expand s (x i).1)
    (hz : (x n).1 ∉ s.pending.map Prod.fst) {fuel : ℕ} (hfuel : n + 1 ≤ fuel) :
    ∃ y ∈ (walkAt s init fuel).2.2, y.1 = (x n).1 := by
  -- each block of the chain is met at a level no later than its place
  have hmet : ∀ i ≤ n, ∃ ℓ ≤ i, ∃ y ∈ walkFront s (walkAt s init ℓ), y.1 = (x i).1 := by
    intro i
    induction i with
    | zero =>
      intro _
      refine ⟨0, le_rfl, x 0, mem_walkFront.mpr ⟨h0, (hok 0 (Nat.zero_le _)).1,
        (hok 0 (Nat.zero_le _)).2, by simp [walkAt]⟩, rfl⟩
    | succ i ih =>
      intro hi
      obtain ⟨ℓ, hℓ, y, hy, hyx⟩ := ih (by omega)
      have hyp : y.1 ∈ s.pending.map Prod.fst := hyx ▸ hpend i (by omega)
      have hfr : x (i + 1) ∈ (walkAt s init (ℓ + 1)).1 := by
        rw [walkAt_succ, walkLevel_eq]
        refine List.mem_flatMap.mpr ⟨y, List.mem_filter.mpr ⟨hy, by simpa using hyp⟩, ?_⟩
        rw [hyx]
        exact hstep i (by omega)
      by_cases hs : (x (i + 1)).1 ∈ (walkAt s init (ℓ + 1)).2.1
      · obtain ⟨ℓ', hℓ', y', hy', hy'x⟩ := seen_earlier init (ℓ + 1) _ hs
        exact ⟨ℓ', by omega, y', hy', hy'x⟩
      · exact ⟨ℓ + 1, by omega, x (i + 1), mem_walkFront.mpr ⟨hfr, (hok _ hi).1, (hok _ hi).2, hs⟩,
          rfl⟩
  obtain ⟨ℓ, hℓ, y, hy, hyx⟩ := hmet n le_rfl
  have hacc : y ∈ (walkAt s init (ℓ + 1)).2.2 := by
    rw [walkAt_succ, walkLevel_eq]
    exact List.mem_append_right _ (List.mem_filter.mpr ⟨hy, by simpa [hyx] using hz⟩)
  have := acc_mono init hacc (fuel - (ℓ + 1))
  rw [show ℓ + 1 + (fuel - (ℓ + 1)) = fuel by omega] at this
  exact ⟨y, this, hyx⟩

end Node

end LeanDag
