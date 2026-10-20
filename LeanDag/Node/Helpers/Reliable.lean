import LeanDag.Node.Helpers.Quiet
import LeanDag.Node.Helpers.Live
/-!
# A reliable node along a trace

`docs/validator.md` §13.2. A step of a node not recovering, other than a
restart, leaves its state alone or settles (`step_settles`), so along a
trace without restarts the node is settled after each of its events from
its first settle on (`settled_step`).
-/

namespace LeanDag

namespace Node

variable {Validator BlockId Payload : Type} [Fintype Validator] [DecidableEq Validator]
variable [LinearOrder BlockId]
variable {cfg : Config Validator BlockId Payload}

/-- **A step of a node not recovering**, other than a restart, leaves its
state alone or settles. -/
theorem step_settles {s : State Validator BlockId Payload} {inp : Input Validator BlockId Payload}
    (hs : s.recovering = false) (hr : inp ≠ .restart) :
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
    · have h' : ¬ (id = cfg.idOf b ∧ b.creator ≠ cfg.me ∧ s.store.base ≤ b.round ∧
          id ∉ s.store.ids ∧ id ∉ s.pending.map Prod.fst ∧ kept cfg s id b) := hA
      simp only [Node.step, if_neg h']; exact Or.inl trivial
  | timer r => exact Or.inr ⟨_, rfl⟩
  | restart => exact absurd rfl hr
  | baseOffer p G bs =>
    simp only [Node.step, hs, Bool.false_eq_true, false_and, if_false]; exact Or.inl trivial
  | baseRequest p => exact Or.inl rfl
  | fetchRequest p G ids => exact Or.inl rfl
  | certOffer p c ds =>
    rcases certOffer_cases (cfg := cfg) s p c ds with ⟨h₁, -, -⟩ | ⟨-, ds', -, -, -, he⟩ |
      ⟨-, -, -, he⟩ | ⟨-, he⟩
    · rw [hs] at h₁; cases h₁
    · rw [he, adopt_eq]; exact Or.inr ⟨_, rfl⟩
    · rw [he]; exact Or.inr ⟨_, rfl⟩
    · rw [he]; exact Or.inl rfl
  | announced p c =>
    rcases announced_cases (cfg := cfg) s p c with ⟨-, -, he⟩ | he | he <;> rw [he]
    · exact Or.inr ⟨_, rfl⟩
    · exact Or.inl rfl
    · exact Or.inl rfl
  | decisionRequest p lo => exact Or.inl rfl
  | proposal p k kh =>
    rw [step_proposal]
    split
    · exact Or.inr ⟨_, rfl⟩
    · exact Or.inl rfl

/-- **A step keeps a node settled**, not recovering and other than a
restart, for a quorum of two or more. -/
theorem settled_step (hq : 2 ≤ cfg.q) {s : State Validator BlockId Payload}
    {inp : Input Validator BlockId Payload} (h : Settled cfg s) (hs : s.recovering = false)
    (hr : inp ≠ .restart) : Settled cfg (Node.step cfg s inp).1 := by
  rcases step_settles (cfg := cfg) hs hr with he | ⟨x, he⟩ <;> rw [he]
  · exact h
  · exact settle_settled hq x

/-! ## Along a trace -/

variable {tr : Trace Validator BlockId Payload}

/-- **An invariant of a node's states** that each of its steps keeps, not
recovering and other than a restart, holds before every event, along a
trace without restarts at the node. -/
theorem inv_before {v : Validator} (hnr : ∀ i : ℕ, tr[i]? ≠ some (v, Input.restart))
    (P : State Validator BlockId Payload → Prop) (h₀ : P (stateBefore cfg tr 0 v))
    (hs : ∀ s inp, P s → s.recovering = false → inp ≠ .restart → P (Node.step (cfg.at v) s inp).1) :
    ∀ i, P (stateBefore cfg tr i v)
  | 0 => h₀
  | i + 1 => by
    have ih := inv_before hnr P h₀ hs i
    rcases he : tr[i]? with _ | ⟨w, inp⟩
    · have hlen : tr.length ≤ i := List.getElem?_eq_none_iff.mp he
      have heq : stateBefore cfg tr (i + 1) v = stateBefore cfg tr i v := by
        unfold stateBefore
        rw [inputsBefore_of_le hlen, inputsBefore_of_le (by omega : tr.length ≤ i + 1)]
      rw [heq]; exact ih
    · rw [stateBefore_succ he]
      split
      · rename_i hw
        subst hw
        exact hs _ inp ih (fired_before (cfg := cfg) hnr i).1 fun h => hnr i (by rw [he, h])
      · exact ih

/-- **A node that never restarts is settled before every event**, once it
has started or settled, for a quorum of two or more. -/
theorem settled_before (hq : 2 ≤ cfg.q) {v : Validator}
    (hnr : ∀ i : ℕ, tr[i]? ≠ some (v, Input.restart)) (i : ℕ) :
    (stateBefore cfg tr i v).top = none ∨ Settled (cfg.at v) (stateBefore cfg tr i v) := by
  refine inv_before (cfg := cfg) hnr (fun s => s.top = none ∨ Settled (cfg.at v) s)
    (Or.inl rfl) (fun s inp h hs hr => ?_) i
  rcases step_settles (cfg := cfg.at v) hs hr with he | ⟨x, he⟩ <;> rw [he]
  · exact h
  · exact Or.inr (settle_settled (cfg := cfg.at v) hq x)

end Node

end LeanDag
