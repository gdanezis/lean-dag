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

The core sweep records for a block only authors of round-`(r − 1)` blocks
that reach it (`mem_coreSets`): its first level gives each such block its
author, and each later level passes a block's authors to its references.
Down a chain of references whose blocks below the first all fall short of
the threshold, the pruned store still reaches the chain's last block from
its first (`pruned_chain`).
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

/-! ## The core sweep -/

section Core

variable (cfg : Config Validator BlockId Payload) (st : Store Validator BlockId Payload)
variable {R : BlockId → Validator → Prop}

omit [Fintype Validator] [DecidableEq Validator] in
/-- Inserting a set the predicate holds of keeps it on every set of a map. -/
theorem core_insert {m : Std.TreeMap BlockId (Finset Validator) compare}
    (hm : ∀ j, ∀ a ∈ m.getD j ∅, R j a) {k : BlockId} {v : Finset Validator}
    (hv : ∀ a ∈ v, R k a) : ∀ j, ∀ a ∈ (m.insert k v).getD j ∅, R j a := by
  intro j a ha
  rw [Std.TreeMap.getD_insert] at ha
  split at ha
  · rename_i h
    rw [compare_eq_iff_eq] at h
    exact h ▸ hv a ha
  · exact hm j a ha

omit [Fintype Validator] [DecidableEq Validator] in
/-- A map's entries are its sets. -/
theorem core_toList {m : Std.TreeMap BlockId (Finset Validator) compare}
    (hm : ∀ j, ∀ a ∈ m.getD j ∅, R j a) : ∀ e ∈ m.toList, ∀ a ∈ e.2, R e.1 a := by
  intro e he a ha
  have h := Std.TreeMap.mem_toList_iff_getElem?_eq_some.mp he
  refine hm e.1 a ?_
  rw [Std.TreeMap.getD_eq_getD_getElem?, h]
  exact ha

omit [Fintype Validator] in
/-- **One level of the sweep passes a block's authors to its references**,
for a predicate that does the same. -/
theorem coreLevel_sound (hR : ∀ i a, R i a → ∀ j ∈ (st.blk i).refs, R j a)
    {lvl : List (BlockId × Finset Validator)} (hl : ∀ e ∈ lvl, ∀ a ∈ e.2, R e.1 a) :
    ∀ e ∈ coreLevel st lvl, ∀ a ∈ e.2, R e.1 a := by
  have inner : ∀ (s : Finset Validator) (l : List BlockId)
      (m : Std.TreeMap BlockId (Finset Validator) compare),
      (∀ j, ∀ a ∈ m.getD j ∅, R j a) → (∀ j ∈ l, ∀ a ∈ s, R j a) →
      ∀ j, ∀ a ∈ (l.foldl (fun m j => m.insert j (m.getD j ∅ ∪ s)) m).getD j ∅, R j a := by
    intro s l
    induction l with
    | nil => intro m hm _; exact hm
    | cons j l ih =>
      intro m hm hs
      refine ih _ (core_insert hm fun a ha => ?_) fun j' hj' => hs j' (List.mem_cons_of_mem _ hj')
      rcases Finset.mem_union.mp ha with ha | ha
      · exact hm j a ha
      · exact hs j List.mem_cons_self a ha
  have outer : ∀ (l : List (BlockId × Finset Validator))
      (m : Std.TreeMap BlockId (Finset Validator) compare),
      (∀ j, ∀ a ∈ m.getD j ∅, R j a) → (∀ e ∈ l, ∀ a ∈ e.2, R e.1 a) →
      ∀ j, ∀ a ∈ (l.foldl (fun (m : Std.TreeMap BlockId (Finset Validator) compare) e =>
        ((st.blk e.1).refs.sort (· ≤ ·)).foldl
          (fun m j => m.insert j (m.getD j ∅ ∪ e.2)) m) m).getD j ∅, R j a := by
    intro l
    induction l with
    | nil => intro m hm _; exact hm
    | cons e l ih =>
      intro m hm hl
      refine ih _ (inner _ _ _ hm fun j hj a ha => ?_)
        fun e' he' => hl e' (List.mem_cons_of_mem _ he')
      exact hR e.1 a (hl e List.mem_cons_self a ha) j ((Finset.mem_sort _).mp hj)
  exact core_toList (outer lvl ∅ (fun j a ha => by simp at ha) hl)

/-- **The sweep keeps the predicate** on the sets it records. -/
theorem coreFrom_sound (hR : ∀ i a, R i a → ∀ j ∈ (st.blk i).refs, R j a) :
    ∀ (fuel : ℕ) (lvl : List (BlockId × Finset Validator))
      (acc : Std.TreeMap BlockId (Finset Validator) compare),
      (∀ e ∈ lvl, ∀ a ∈ e.2, R e.1 a) → (∀ j, ∀ a ∈ acc.getD j ∅, R j a) →
      ∀ j, ∀ a ∈ (coreFrom cfg st fuel lvl acc).getD j ∅, R j a := by
  intro fuel
  induction fuel with
  | zero => intro lvl acc _ hacc; exact hacc
  | succ fuel ih =>
    intro lvl acc hl hacc
    have hins : ∀ (l : List (BlockId × Finset Validator))
        (m : Std.TreeMap BlockId (Finset Validator) compare),
        (∀ j, ∀ a ∈ m.getD j ∅, R j a) → (∀ e ∈ l, ∀ a ∈ e.2, R e.1 a) →
        ∀ j, ∀ a ∈ (l.foldl (fun m e => m.insert e.1 e.2) m).getD j ∅, R j a := by
      intro l
      induction l with
      | nil => intro m hm _; exact hm
      | cons e l ih' =>
        intro m hm hl'
        exact ih' _ (core_insert hm (hl' e List.mem_cons_self))
          fun e' he' => hl' e' (List.mem_cons_of_mem _ he')
    unfold coreFrom
    dsimp only
    split
    · exact hins lvl acc hacc hl
    · exact ih _ _ (coreLevel_sound st hR hl) (hins lvl acc hacc hl)

/-- **The sweep records only reaching authors**: an author it records for a
block has a round-`(r − 1)` block in the store that reaches it. -/
theorem mem_coreSets {r : ℕ} {j : BlockId} {a : Validator}
    (ha : a ∈ (coreSets cfg st r).getD j ∅) :
    ∃ y ∈ st.ids, (st.blk y).round = r - 1 ∧ (st.blk y).creator = a ∧ ReachesFrom st.blk y j := by
  unfold coreSets at ha
  split at ha
  · simp at ha
  · refine coreFrom_sound cfg st
      (R := fun j a => ∃ y ∈ st.ids, (st.blk y).round = r - 1 ∧ (st.blk y).creator = a ∧
        ReachesFrom st.blk y j)
      (fun i a ⟨y, hy, hyr, hyc, hyi⟩ j hj => ⟨y, hy, hyr, hyc, hyi.trans (ReachesFrom.single hj)⟩)
      r _ ∅ (fun e he a ha => ?_) (fun j a ha => by simp at ha) j a ha
    obtain ⟨c, hc, rfl⟩ := List.mem_map.mp he
    have hc' := mem_blocksAt.mp (st.atRound_eq (r - 1) ▸ (Finset.mem_sort _).mp hc)
    exact ⟨c, hc'.1, hc'.2, (Finset.mem_singleton.mp ha).symm, ReachesFrom.refl⟩

/-- **The pruned store reaches down a chain of non-core blocks**: if each
block of a chain of references below its first falls short of the
threshold, the chain's last block is in the pruned history of its first. -/
theorem pruned_chain {r K len : ℕ} {x : ℕ → BlockId}
    (hx : ∀ k, K ≤ k → k < len → x (k + 1) ∈ (st.blk (x k)).refs)
    (hnc : ∀ k, K < k → k ≤ len → ¬ coreThreshold cfg ≤ ((coreSets cfg st r).getD (x k) ∅).card) :
    ∀ d, K + d ≤ len → x len ∈ historyUptoFrom (pruned cfg st r) d (x (len - d)) := by
  intro d
  induction d with
  | zero => intro _; exact mem_historyUptoFrom_self
  | succ d ih =>
    intro hd
    refine mem_historyUptoFrom_succ.mpr (Or.inr ⟨x (len - d), ?_, ih (by omega)⟩)
    have hk := hx (len - (d + 1)) (by omega) (by omega)
    rw [show len - (d + 1) + 1 = len - d by omega] at hk
    change x (len - d) ∈ (st.blk (x (len - (d + 1)))).refs.filter _
    exact Finset.mem_filter.mpr ⟨hk, hnc (len - d) (by omega) (by omega)⟩

end Core

end Node

end LeanDag
