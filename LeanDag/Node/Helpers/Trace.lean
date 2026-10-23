import LeanDag.Node.Model.Trace
import LeanDag.Node.Helpers.Steps
/-!
# A node's states along a trace

Event `i` moves only its own node: node `v`'s state before event `i + 1`
is its step at event `i` if that event is `v`'s, and its state before
event `i` otherwise (`stateBefore_succ`). So a node's disk grows from
event to event (`grows_before`), and what its run up to an event
persisted or was delivered is what the trace's earlier events at it
persisted or delivered (`mem_persists_before`, `mem_delivered_before`).
-/

namespace LeanDag

namespace Node

variable {Validator BlockId Payload : Type} [Fintype Validator] [DecidableEq Validator]
variable [LinearOrder BlockId]
variable {cfg : Config Validator BlockId Payload} {tr : Trace Validator BlockId Payload}

omit [Fintype Validator] [LinearOrder BlockId] in
theorem inputsBefore_succ {i : ℕ} {w : Validator} {inp : Input Validator BlockId Payload}
    (h : tr[i]? = some (w, inp)) (v : Validator) :
    inputsBefore tr (i + 1) v = inputsBefore tr i v ++ if w = v then [inp] else [] := by
  unfold inputsBefore
  rw [List.take_add_one, h]
  simp only [Option.toList_some, List.filterMap_append, List.filterMap_cons, List.filterMap_nil]
  split <;> simp_all

omit [Fintype Validator] [LinearOrder BlockId] in
theorem inputsBefore_of_le {i : ℕ} (h : tr.length ≤ i) (v : Validator) :
    inputsBefore tr i v = inputsBefore tr tr.length v := by
  unfold inputsBefore
  rw [List.take_of_length_le h, List.take_length]

theorem run_append (c : Config Validator BlockId Payload) :
    ∀ (s : State Validator BlockId Payload) (l₁ l₂ : List (Input Validator BlockId Payload)),
    run c s (l₁ ++ l₂) =
      ((run c (run c s l₁).1 l₂).1, (run c s l₁).2 ++ (run c (run c s l₁).1 l₂).2)
  | s, [], l₂ => by simp [run]
  | s, i :: l₁, l₂ => by
    simp only [List.cons_append, run]
    rw [run_append c _ l₁ l₂, List.append_assoc]

theorem run_append_single (c : Config Validator BlockId Payload) :
    ∀ (s : State Validator BlockId Payload) (l : List (Input Validator BlockId Payload))
      (x : Input Validator BlockId Payload),
      run c s (l ++ [x]) =
        ((step c (run c s l).1 x).1, (run c s l).2 ++ (step c (run c s l).1 x).2)
  | s, [], x => by simp [run]
  | s, i :: l, x => by
    simp only [List.cons_append, run]
    rw [run_append_single c (step c s i).1 l x, List.append_assoc]

/-- **Event `i` moves only its own node.** -/
theorem stateBefore_succ {i : ℕ} {w : Validator} {inp : Input Validator BlockId Payload}
    (h : tr[i]? = some (w, inp)) (v : Validator) :
    stateBefore cfg tr (i + 1) v =
      if w = v then (step (cfg.at v) (stateBefore cfg tr i v) inp).1
      else stateBefore cfg tr i v := by
  unfold stateBefore
  rw [inputsBefore_succ h]
  split
  · rename_i hw
    rw [run_append_single]
  · rw [List.append_nil]

theorem outputsAt_eq {i : ℕ} {w : Validator} {inp : Input Validator BlockId Payload}
    (h : tr[i]? = some (w, inp)) :
    outputsAt cfg tr i = (step (cfg.at w) (stateBefore cfg tr i w) inp).2 := by
  unfold outputsAt; rw [h]

/-- **A node's disk grows from event to event.** -/
theorem grows_before (v : Validator) : ∀ {i j : ℕ}, i ≤ j →
    Grows (stateBefore cfg tr i v).disk (stateBefore cfg tr j v).disk := by
  intro i j hij
  induction j, hij using Nat.le_induction with
  | base => exact Grows.refl _
  | succ j _ ih =>
    refine ih.trans ?_
    rcases hj : tr[j]? with _ | ⟨w, inp⟩
    · have : tr.length ≤ j := List.getElem?_eq_none_iff.mp hj
      unfold stateBefore
      rw [inputsBefore_of_le this, inputsBefore_of_le (by omega : tr.length ≤ j + 1)]
      exact Grows.refl _
    · rw [stateBefore_succ hj]
      split
      · rename_i hw; subst hw; exact Grows.step _ _
      · exact Grows.refl _

/-- **What a node's run up to event `i` persisted**, its events before `i`
persisted. -/
theorem mem_persists_before (v : Validator) :
    ∀ (i : ℕ) {x : BlockId × Block Validator BlockId Payload},
      x ∈ persists (run (cfg.at v) (State.init (cfg.at v)) (inputsBefore tr i v)).2 →
      ∃ j < i, (tr[j]?.map Prod.fst) = some v ∧ x ∈ persists (outputsAt cfg tr j)
  | 0, x, hx => by simp [inputsBefore, run, persists] at hx
  | i + 1, x, hx => by
    rcases hi : tr[i]? with _ | ⟨w, inp⟩
    · have : tr.length ≤ i := List.getElem?_eq_none_iff.mp hi
      have he : inputsBefore tr (i + 1) v = inputsBefore tr i v := by
        rw [inputsBefore_of_le this, inputsBefore_of_le (by omega : tr.length ≤ i + 1)]
      rw [he] at hx
      obtain ⟨j, hj, hjv, hx⟩ := mem_persists_before v i hx
      exact ⟨j, by omega, hjv, hx⟩
    · rw [inputsBefore_succ hi] at hx
      split at hx
      · rename_i hw; subst hw
        rw [run_append_single, persists_append] at hx
        rcases List.mem_append.mp hx with hx | hx
        · obtain ⟨j, hj, hjv, hx⟩ := mem_persists_before w i hx
          exact ⟨j, by omega, hjv, hx⟩
        · exact ⟨i, by omega, by rw [hi]; rfl, by rw [outputsAt_eq hi]; exact hx⟩
      · rw [List.append_nil] at hx
        obtain ⟨j, hj, hjv, hx⟩ := mem_persists_before v i hx
        exact ⟨j, by omega, hjv, hx⟩

/-- **What an event at a node persists, the node's run past it
persisted.** -/
theorem persists_of_event {j : ℕ} {w : Validator} {inp : Input Validator BlockId Payload}
    (h : tr[j]? = some (w, inp)) {x : BlockId × Block Validator BlockId Payload}
    (hx : x ∈ persists (outputsAt cfg tr j)) :
    x ∈ persists (run (cfg.at w) (State.init (cfg.at w)) (inputsBefore tr (j + 1) w)).2 := by
  rw [inputsBefore_succ h, if_pos rfl, run_append_single, persists_append]
  rw [outputsAt_eq h] at hx
  exact List.mem_append_right _ hx

omit [Fintype Validator] in
/-- **What was delivered to a node before event `i`**, its earlier events
delivered. -/
theorem mem_delivered_before (c : Config Validator BlockId Payload) (v : Validator) :
    ∀ (i : ℕ) {x : BlockId × Block Validator BlockId Payload},
      x ∈ delivered c (inputsBefore tr i v) →
      ∃ j < i, ∃ inp, tr[j]? = some (v, inp) ∧ x ∈ delivered c [inp]
  | 0, x, hx => by simp [inputsBefore, delivered] at hx
  | i + 1, x, hx => by
    rcases hi : tr[i]? with _ | ⟨w, inp⟩
    · have : tr.length ≤ i := List.getElem?_eq_none_iff.mp hi
      have he : inputsBefore tr (i + 1) v = inputsBefore tr i v := by
        rw [inputsBefore_of_le this, inputsBefore_of_le (by omega : tr.length ≤ i + 1)]
      rw [he] at hx
      obtain ⟨j, hj, inp, hjv, hx⟩ := mem_delivered_before c v i hx
      exact ⟨j, by omega, inp, hjv, hx⟩
    · rw [inputsBefore_succ hi] at hx
      unfold delivered at hx
      rw [List.flatMap_append] at hx
      rcases List.mem_append.mp hx with hx | hx
      · obtain ⟨j, hj, inp', hjv, hx⟩ := mem_delivered_before c v i hx
        exact ⟨j, by omega, inp', hjv, hx⟩
      · by_cases hw : w = v
        · subst hw
          rw [if_pos rfl] at hx
          exact ⟨i, by omega, inp, hi, hx⟩
        · rw [if_neg hw] at hx
          exact absurd hx (by simp)

end Node

end LeanDag
