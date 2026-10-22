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

/-- The blocks a level of the walk meets: its front, neither accepted nor
met already. -/
def walkFront (w : List BlockId × List BlockId × List BlockId) : List BlockId :=
  (w.1.filter fun x => decide (x ∉ s.store.ids) && decide (x ∉ w.2.1)).dedup

variable {s}

omit [Fintype Validator] [DecidableEq Validator] in
theorem walkLevel_eq (w : List BlockId × List BlockId × List BlockId) :
    walkLevel s w =
      (((walkFront s w).filter fun x => decide (x ∈ s.pending.map Prod.fst)).flatMap
          (fun x => expand s x),
        w.2.1 ++ walkFront s w,
        w.2.2 ++ (walkFront s w).filter fun x => !decide (x ∈ s.pending.map Prod.fst)) := by
  simp only [walkLevel, walkFront, List.partition_eq_filter_filter]
  rfl

omit [Fintype Validator] [DecidableEq Validator] in
theorem mem_walkFront {w : List BlockId × List BlockId × List BlockId} {x : BlockId} :
    x ∈ walkFront s w ↔ x ∈ w.1 ∧ x ∉ s.store.ids ∧ x ∉ w.2.1 := by
  simp only [walkFront, List.mem_dedup, List.mem_filter, Bool.and_eq_true, decide_eq_true_eq]

variable (s) in
/-- The walk's state after `ℓ` levels from the front `init`. -/
abbrev walkAt (init : List BlockId) (ℓ : ℕ) : List BlockId × List BlockId × List BlockId :=
  (walkLevel s)^[ℓ] (init, [], [])

omit [Fintype Validator] [DecidableEq Validator] in
theorem walkAt_succ (init : List BlockId) (ℓ : ℕ) :
    walkAt s init (ℓ + 1) = walkLevel s (walkAt s init ℓ) :=
  Function.iterate_succ_apply' _ _ _

omit [Fintype Validator] [DecidableEq Validator] in
/-- **What a level keeps as missing stays so.** -/
theorem acc_mono (init : List BlockId) {ℓ : ℕ} {y : BlockId}
    (hy : y ∈ (walkAt s init ℓ).2.2) : ∀ k, y ∈ (walkAt s init (ℓ + k)).2.2
  | 0 => hy
  | k + 1 => by
    rw [← Nat.add_assoc, walkAt_succ, walkLevel_eq]
    exact List.mem_append_left _ (acc_mono init hy k)

omit [Fintype Validator] [DecidableEq Validator] in
/-- **An identifier met already was met at an earlier level.** -/
theorem seen_earlier (init : List BlockId) :
    ∀ ℓ, ∀ j ∈ (walkAt s init ℓ).2.1, ∃ ℓ' < ℓ, j ∈ walkFront s (walkAt s init ℓ')
  | 0, j, hj => by simp [walkAt] at hj
  | ℓ + 1, j, hj => by
    rw [walkAt_succ, walkLevel_eq] at hj
    rcases List.mem_append.mp hj with hj | hj
    · obtain ⟨ℓ', hℓ', hx⟩ := seen_earlier init ℓ j hj
      exact ⟨ℓ', by omega, hx⟩
    · exact ⟨ℓ, by omega, hj⟩

omit [Fintype Validator] [DecidableEq Validator] in
/-- **The walk reaches every missing block down a chain of pending
blocks.** -/
theorem walk_reaches (init : List BlockId) {n : ℕ} (x : ℕ → BlockId)
    (h0 : x 0 ∈ init)
    (hok : ∀ i ≤ n, x i ∉ s.store.ids)
    (hpend : ∀ i < n, x i ∈ s.pending.map Prod.fst)
    (hstep : ∀ i < n, x (i + 1) ∈ expand s (x i))
    (hz : x n ∉ s.pending.map Prod.fst) {fuel : ℕ} (hfuel : n + 1 ≤ fuel) :
    x n ∈ (walkAt s init fuel).2.2 := by
  -- each block of the chain is met at a level no later than its place
  have hmet : ∀ i ≤ n, ∃ ℓ ≤ i, x i ∈ walkFront s (walkAt s init ℓ) := by
    intro i
    induction i with
    | zero =>
      intro _
      exact ⟨0, le_rfl, mem_walkFront.mpr ⟨h0, hok 0 (Nat.zero_le _), by simp [walkAt]⟩⟩
    | succ i ih =>
      intro hi
      obtain ⟨ℓ, hℓ, hy⟩ := ih (by omega)
      have hfr : x (i + 1) ∈ (walkAt s init (ℓ + 1)).1 := by
        rw [walkAt_succ, walkLevel_eq]
        exact List.mem_flatMap.mpr
          ⟨x i, List.mem_filter.mpr ⟨hy, by simpa using hpend i (by omega)⟩, hstep i (by omega)⟩
      by_cases hs : x (i + 1) ∈ (walkAt s init (ℓ + 1)).2.1
      · obtain ⟨ℓ', hℓ', hy'⟩ := seen_earlier init (ℓ + 1) _ hs
        exact ⟨ℓ', by omega, hy'⟩
      · exact ⟨ℓ + 1, by omega, mem_walkFront.mpr ⟨hfr, hok _ hi, hs⟩⟩
  obtain ⟨ℓ, hℓ, hy⟩ := hmet n le_rfl
  have hacc : x n ∈ (walkAt s init (ℓ + 1)).2.2 := by
    rw [walkAt_succ, walkLevel_eq]
    exact List.mem_append_right _ (List.mem_filter.mpr ⟨hy, by simpa using hz⟩)
  have := acc_mono init hacc (fuel - (ℓ + 1))
  rwa [show ℓ + 1 + (fuel - (ℓ + 1)) = fuel by omega] at this

end Node

end LeanDag
