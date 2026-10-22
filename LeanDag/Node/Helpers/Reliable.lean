import LeanDag.Node.Helpers.Quiet
import LeanDag.Node.Helpers.Live
/-!
# A node along a trace

A step of a node leaves its state alone or settles (`step_settles`), so
along a trace the node is settled after each of its events from its start
on (`settled_step`, `settled_before`). Its top and its next undecided slot
only rise (`Rises`, `rises_before`).
-/

namespace LeanDag

namespace Node

variable {Validator BlockId Payload : Type} [Fintype Validator] [DecidableEq Validator]
variable [LinearOrder BlockId]
variable {cfg : Config Validator BlockId Payload}

/-- **A step of a node** leaves its state alone or settles. -/
theorem step_settles {s : State Validator BlockId Payload} {inp : Input Validator BlockId Payload} :
    (Node.step cfg s inp).1 = s ∨ ∃ x, (Node.step cfg s inp).1 = (Node.settle cfg x).1 := by
  cases inp with
  | start =>
    simp only [Node.step]
    split
    · split
      · exact Or.inr ⟨_, rfl⟩
      · exact Or.inl rfl
    · exact Or.inl rfl
  | deliver id b =>
    by_cases hA : Admits cfg s id b
    · rw [step_deliver hA]; exact Or.inr ⟨_, rfl⟩
    · rw [step_deliver_not hA]; exact Or.inl rfl
  | timer r => exact Or.inr ⟨_, rfl⟩
  | fetchRequest p ids => exact Or.inl rfl

/-! ## What only rises -/

/-- **Rising from `s` to `s'`**: the top, once there, and the next
undecided slot, none lower. -/
def Rises (s s' : State Validator BlockId Payload) : Prop :=
  s.top.getD 0 ≤ s'.top.getD 0 ∧ (s.top.isSome → s'.top.isSome) ∧ s.lo ≤ s'.lo

theorem Rises.refl (s : State Validator BlockId Payload) : Rises s s :=
  ⟨le_rfl, id, le_rfl⟩

theorem Rises.trans {a b c : State Validator BlockId Payload} (h₁ : Rises a b) (h₂ : Rises b c) :
    Rises a c :=
  ⟨h₁.1.trans h₂.1, h₂.2.1 ∘ h₁.2.1, h₁.2.2.trans h₂.2.2⟩

theorem rises_progress : ∀ (fuel : ℕ) (s : State Validator BlockId Payload),
    Rises s (Node.progress cfg fuel s).1
  | 0, s => Rises.refl s
  | fuel + 1, s => by
    simp only [Node.progress]
    split
    · rename_i s₁ out hb
      obtain ⟨r, -, -, -, -, -, hr, -, -, -, -, -, ht₁, -, hlo, -⟩ := tryBuild_some hb
      refine Rises.trans ⟨?_, ?_, ?_⟩ (rises_progress fuel s₁)
      · rw [hr, ht₁]; simp
      · rw [ht₁]; exact fun _ => rfl
      · rw [hlo]
    · exact Rises.refl s

theorem rises_advance (s : State Validator BlockId Payload) : Rises s (Node.advance cfg s).1 := by
  have h₁ := rises_progress (cfg := cfg) (s.store.topRound + 2) s
  obtain ⟨-, -, hdtop, hdlo, -⟩ := decideStep_bound (cfg := cfg)
    (Node.progress cfg (s.store.topRound + 2) s).1
  refine h₁.trans ⟨?_, ?_, ?_⟩
  · simp only [Node.advance]; rw [hdtop]
  · simp only [Node.advance]; rw [hdtop]; exact id
  · simp only [Node.advance]; exact hdlo

theorem rises_quiesce (n : ℕ) (s : State Validator BlockId Payload) :
    Rises s (quiesce cfg n s).1 :=
  (quiesce_rel (P := fun _ => True) (R := fun a _ b => Rises a b) Rises.refl
    (fun _ _ _ _ _ h₁ h₂ => h₁.trans h₂) (fun s _ => ⟨rises_advance s, trivial⟩) n s trivial).1

theorem rises_settle (s : State Validator BlockId Payload) : Rises s (Node.settle cfg s).1 :=
  rises_quiesce _ s

/-- **A step of a node** raises its top and its next undecided slot, or
keeps them. -/
theorem rises_step {s : State Validator BlockId Payload} {inp : Input Validator BlockId Payload} :
    Rises s (Node.step cfg s inp).1 := by
  -- settling a state that already rose from `s`
  have hset : ∀ x : State Validator BlockId Payload, Rises s x →
      (Node.step cfg s inp).1 = (Node.settle cfg x).1 → Rises s (Node.step cfg s inp).1 :=
    fun x hx he => by rw [he]; exact hx.trans (rises_settle x)
  cases inp with
  | start =>
    by_cases h₁ : s.top = none ∧ cfg.Admissible
    · by_cases h₂ : cfg.idOf cfg.genesis ∉ s.store.ids ∧
          rowValid cfg.q (Function.update s.store.blk (cfg.idOf cfg.genesis) cfg.genesis)
            cfg.genesis
      · let st := s.store.insert (cfg.idOf cfg.genesis) cfg.genesis h₂.1
          (fun _ hj => absurd hj (Finset.notMem_empty _))
          (fun j hj => absurd hj (Finset.notMem_empty j))
        let gid := cfg.idOf cfg.genesis
        let s₀ : State Validator BlockId Payload :=
          { s with store := st, top := some 0, own := some gid }
        refine hset s₀ ⟨by rw [h₁.1]; simp [s₀], fun _ => rfl, le_rfl⟩
          (by simp only [Node.step, dif_pos h₂, if_pos h₁]; rfl)
      · rw [show (Node.step cfg s .start).1 = s by simp only [Node.step, dif_neg h₂, if_pos h₁]]
        exact Rises.refl s
    · rw [show (Node.step cfg s .start).1 = s by simp only [Node.step, if_neg h₁]]
      exact Rises.refl s
  | deliver id b =>
    by_cases hA : Admits cfg s id b
    · refine hset _ ?_ (by rw [step_deliver hA])
      exact ⟨le_rfl, fun h => h, le_rfl⟩
    · rw [step_deliver_not hA]; exact Rises.refl s
  | timer r => exact hset { s with fired := insert r s.fired } ⟨le_rfl, id, le_rfl⟩ rfl
  | fetchRequest p ids => exact Rises.refl s

/-! ## Along a trace -/

variable {tr : Trace Validator BlockId Payload}

/-- **An invariant of a node's states** that each of its steps keeps
holds before every event. -/
theorem inv_before (v : Validator)
    (P : State Validator BlockId Payload → Prop) (h₀ : P (stateBefore cfg tr 0 v))
    (hs : ∀ s inp, P s → P (Node.step (cfg.at v) s inp).1) :
    ∀ i, P (stateBefore cfg tr i v)
  | 0 => h₀
  | i + 1 => by
    have ih := inv_before v P h₀ hs i
    rcases he : tr[i]? with _ | ⟨w, inp⟩
    · have hlen : tr.length ≤ i := List.getElem?_eq_none_iff.mp he
      have heq : stateBefore cfg tr (i + 1) v = stateBefore cfg tr i v := by
        unfold stateBefore
        rw [inputsBefore_of_le hlen, inputsBefore_of_le (by omega : tr.length ≤ i + 1)]
      rw [heq]; exact ih
    · rw [stateBefore_succ he]
      split
      · exact hs _ inp ih
      · exact ih

/-- **A node is settled before every event** once it has started, for a
quorum of two or more. -/
theorem settled_before (hq : 2 ≤ cfg.q) (v : Validator) (i : ℕ) :
    (stateBefore cfg tr i v).top = none ∨ Settled (cfg.at v) (stateBefore cfg tr i v) := by
  refine inv_before (cfg := cfg) v (fun s => s.top = none ∨ Settled (cfg.at v) s)
    (Or.inl rfl) (fun s inp h => ?_) i
  rcases step_settles (cfg := cfg.at v) (s := s) (inp := inp) with he | ⟨x, he⟩ <;> rw [he]
  · exact h
  · exact Or.inr (settle_settled (cfg := cfg.at v) hq x)

/-- **Along a trace**, the top and the next undecided slot of `v` only
rise. -/
theorem rises_before (v : Validator) :
    ∀ {i j : ℕ}, i ≤ j → Rises (stateBefore cfg tr i v) (stateBefore cfg tr j v) := by
  intro i j hij
  induction j, hij using Nat.le_induction with
  | base => exact Rises.refl _
  | succ j hij ih =>
    refine ih.trans ?_
    rcases he : tr[j]? with _ | ⟨w, inp⟩
    · have hlen : tr.length ≤ j := List.getElem?_eq_none_iff.mp he
      have heq : stateBefore cfg tr (j + 1) v = stateBefore cfg tr j v := by
        unfold stateBefore
        rw [inputsBefore_of_le hlen, inputsBefore_of_le (by omega : tr.length ≤ j + 1)]
      rw [heq]; exact Rises.refl _
    · rw [stateBefore_succ he]
      split
      · exact rises_step
      · exact Rises.refl _

/-! ## Times -/

omit [Fintype Validator] [DecidableEq Validator] [LinearOrder BlockId] in
/-- **The events by `t` are the first `eventsBy t`**, under nondecreasing
times. -/
theorem lt_eventsBy {time : ℕ → ℕ} (hmono : Live.TimeMono tr time) {i t : ℕ}
    (hi : i < tr.length) : i < eventsBy tr time t ↔ time i ≤ t := by
  unfold eventsBy
  have hnd : ((List.range tr.length).filter fun j => time j ≤ t).Nodup :=
    (List.nodup_range).filter _
  rw [← List.toFinset_card_of_nodup hnd]
  constructor
  · intro h
    by_contra hti
    have hsub : ((List.range tr.length).filter fun j => time j ≤ t).toFinset ⊆
        Finset.range i := by
      intro j hj
      simp only [List.mem_toFinset, List.mem_filter, List.mem_range, decide_eq_true_eq] at hj
      simp only [Finset.mem_range]
      by_contra hji
      have := hmono i j (by omega) hj.1
      omega
    have := Finset.card_le_card hsub
    rw [Finset.card_range] at this
    omega
  · intro hti
    have hsub : Finset.range (i + 1) ⊆
        ((List.range tr.length).filter fun j => time j ≤ t).toFinset := by
      intro j hj
      simp only [Finset.mem_range] at hj
      simp only [List.mem_toFinset, List.mem_filter, List.mem_range, decide_eq_true_eq]
      exact ⟨by omega, (hmono j i (by omega) hi).trans hti⟩
    have := Finset.card_le_card hsub
    rw [Finset.card_range] at this
    omega

omit [Fintype Validator] [DecidableEq Validator] [LinearOrder BlockId] in
theorem eventsBy_le_length {time : ℕ → ℕ} (t : ℕ) : eventsBy tr time t ≤ tr.length := by
  unfold eventsBy
  exact (List.length_filter_le _ _).trans (by simp)

omit [Fintype Validator] [DecidableEq Validator] [LinearOrder BlockId] in
theorem eventsBy_mono {time : ℕ → ℕ} {t t' : ℕ} (h : t ≤ t') :
    eventsBy tr time t ≤ eventsBy tr time t' := by
  unfold eventsBy
  exact (List.monotone_filter_right _ fun j hj => by
    simp only [decide_eq_true_eq] at hj ⊢; omega).length_le

end Node

end LeanDag
