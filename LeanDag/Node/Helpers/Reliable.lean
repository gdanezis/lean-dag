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
    · rw [step_deliver_not_of hA hs]; exact Or.inl rfl
  | timer r => exact Or.inr ⟨_, rfl⟩
  | restart => exact absurd rfl hr
  | baseOffer p G bs =>
    simp only [Node.step, hs, Bool.false_eq_true, false_and, if_false]; exact Or.inl trivial
  | baseRequest p => exact Or.inl rfl
  | fetchRequest p G ids => exact Or.inl rfl
  | certOffer p c ds =>
    rcases certOffer_cases (cfg := cfg) s p c ds with ⟨h₁, -, -⟩ | ⟨l, hcl, ds', -, -, -, he⟩ |
      ⟨l, hcl, -, -, he⟩ | ⟨l, hcl, he⟩
    all_goals try obtain rfl := certs_of_not hcl hs
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

/-! ## What only rises -/

/-- **Rising from `s` to `s'`**: the top, once there, the next undecided
slot and the certificate's height, none lower. -/
def Rises (s s' : State Validator BlockId Payload) : Prop :=
  s.top.getD 0 ≤ s'.top.getD 0 ∧ (s.top.isSome → s'.top.isSome) ∧ s.lo ≤ s'.lo ∧
    s.certHeight ≤ s'.certHeight

theorem Rises.refl (s : State Validator BlockId Payload) : Rises s s :=
  ⟨le_rfl, id, le_rfl, le_rfl⟩

theorem Rises.trans {a b c : State Validator BlockId Payload} (h₁ : Rises a b) (h₂ : Rises b c) :
    Rises a c :=
  ⟨h₁.1.trans h₂.1, h₂.2.1 ∘ h₁.2.1, h₁.2.2.1.trans h₂.2.2.1, h₁.2.2.2.trans h₂.2.2.2⟩

omit [Fintype Validator] in
theorem rises_progress (fuel : ℕ) (s : State Validator BlockId Payload) :
    Rises s (Node.progress cfg fuel s).1 := by
  obtain ⟨-, -, hlo, -, -, -⟩ := progress_frame (cfg := cfg) fuel s
  have hc : (Node.progress cfg fuel s).1.certHeight = s.certHeight := by
    simp [State.certHeight, (progress_frame (cfg := cfg) fuel s).2.1]
  unfold Rises
  rcases ht : s.top with _ | t
  · exact ⟨by simp, by simp, hlo.ge, hc.ge⟩
  · obtain ⟨t', htt, ht'⟩ := progress_top (cfg := cfg) fuel ht
    exact ⟨by rw [ht']; simpa using htt, fun _ => by rw [ht']; rfl, hlo.ge, hc.ge⟩

theorem rises_advance (s : State Validator BlockId Payload) : Rises s (Node.advance cfg s).1 := by
  have h₁ := rises_progress (cfg := cfg) (s.store.topRound + 2) s
  obtain ⟨-, -, hdtop, hdlo, -, hdc, -⟩ := decideStep_bound (cfg := cfg)
    (Node.progress cfg (s.store.topRound + 2) s).1
  obtain ⟨hglo, hgc, hgtop, -, -, -⟩ := collect_bound (cfg := cfg)
    (Node.decideStep cfg (Node.progress cfg (s.store.topRound + 2) s).1).1
  refine h₁.trans ⟨?_, ?_, ?_, ?_⟩
  · simp only [Node.advance]; rw [hgtop, hdtop]
  · simp only [Node.advance]; rw [hgtop, hdtop]; exact id
  · simp only [Node.advance]; rw [hglo]; exact hdlo
  · simp only [Node.advance, State.certHeight]; rw [hgc]; exact hdc

theorem rises_quiesce (n : ℕ) (s : State Validator BlockId Payload) :
    Rises s (quiesce cfg n s).1 :=
  (quiesce_rel (P := fun _ => True) (R := fun a _ b => Rises a b) Rises.refl
    (fun _ _ _ _ _ h₁ h₂ => h₁.trans h₂) (fun s _ => ⟨rises_advance s, trivial⟩) n s trivial).1

theorem rises_settle {s : State Validator BlockId Payload} (hs : s.recovering = false) :
    Rises s (Node.settle cfg s).1 := by
  rw [settle_of_idle hs]; exact rises_quiesce _ s

/-- **A step of a node not recovering**, other than a restart, raises
its top, its next undecided slot and its certificate's height, or keeps
them. -/
theorem rises_step {s : State Validator BlockId Payload} {inp : Input Validator BlockId Payload}
    (hs : s.recovering = false) (hr : inp ≠ .restart) : Rises s (Node.step cfg s inp).1 := by
  -- settling a state that already rose from `s`, not recovering
  have hset : ∀ x : State Validator BlockId Payload, Rises s x → x.recovering = false →
      (Node.step cfg s inp).1 = (Node.settle cfg x).1 → Rises s (Node.step cfg s inp).1 :=
    fun x hx hxr he => by rw [he]; exact hx.trans (rises_settle hxr)
  cases inp with
  | start =>
    by_cases h₁ : s.top = none ∧ cfg.Admissible
    · by_cases h₂ : cfg.idOf cfg.genesis ∉ s.store.ids ∧ s.store.base ≤ cfg.genesis.round ∧
          rowValid cfg.q (Function.update s.store.blk (cfg.idOf cfg.genesis) cfg.genesis)
            cfg.genesis
      · let st := s.store.insert _ _ h₂.1 h₂.2.1 (fun _ => Finset.empty_subset _)
          (fun _ j hj => absurd hj (Finset.notMem_empty j))
        let gid := cfg.idOf cfg.genesis
        let s₀ : State Validator BlockId Payload :=
          { { s with store := st, top := some 0, own := some gid } with
            owner := slotted cfg [(gid, cfg.genesis)] ++ s.owner, recovering := false }
        refine hset s₀ ⟨by rw [h₁.1]; simp [s₀], fun _ => rfl, le_rfl, le_rfl⟩ rfl
          (by simp only [Node.step, dif_pos h₂, if_pos h₁]; rfl)
      · rw [show (Node.step cfg s .start).1 = s by simp only [Node.step, dif_neg h₂, if_pos h₁]]
        exact Rises.refl s
    · rw [show (Node.step cfg s .start).1 = s by simp only [Node.step, if_neg h₁]]
      exact Rises.refl s
  | deliver id b =>
    by_cases hA : Admits cfg s id b
    · refine hset _ ?_ ?_ (by rw [step_deliver hA])
      · exact ⟨le_rfl, fun h => h, le_rfl, le_rfl⟩
      · exact hs
    · rw [step_deliver_not_of hA hs]; exact Rises.refl s
  | timer r => exact hset { s with fired := insert r s.fired } (Rises.refl s) hs rfl
  | restart => exact absurd rfl hr
  | baseOffer p G bs =>
    simp only [Node.step, hs, Bool.false_eq_true, false_and, if_false]; exact Rises.refl s
  | baseRequest p => exact Rises.refl s
  | fetchRequest p G ids => exact Rises.refl s
  | decisionRequest p lo => exact Rises.refl s
  | certOffer p c ds =>
    rcases certOffer_cases (cfg := cfg) s p c ds with ⟨h₁, -, -⟩ | ⟨l, hcl, ds', -, -, ha, he⟩ |
      ⟨l, hcl, -, hcf, he⟩ | ⟨l, hcl, he⟩
    all_goals try obtain rfl := certs_of_not hcl hs
    · rw [hs] at h₁; cases h₁
    · rw [adopt_eq] at he
      refine hset (adopted s c ds') ⟨le_rfl, id, (adoptable_lo ha).le, ?_⟩ hs (by rw [he])
      unfold adopted State.certHeight; dsimp only
      split
      · rename_i h; simp only [Option.map_some, Option.getD_some]; exact h.le
      · exact le_rfl
    · refine hset { s with cert := some c, props := above (some c) s.props }
        ⟨le_rfl, id, le_rfl, ?_⟩ hs (by rw [he]; rfl)
      unfold confirms at hcf
      simp only [Bool.and_eq_true, decide_eq_true_eq] at hcf
      exact hcf.1.1.2.le
    · rw [he]; exact Rises.refl s
  | announced p c =>
    rcases announced_cases (cfg := cfg) s p c with ⟨-, hcf, he⟩ | he | he
    · refine hset { s with cert := some c, props := above (some c) s.props }
        ⟨le_rfl, id, le_rfl, ?_⟩ hs (by rw [he]; rfl)
      unfold confirms at hcf
      simp only [Bool.and_eq_true, decide_eq_true_eq] at hcf
      exact hcf.1.1.2.le
    · rw [he]; exact Rises.refl s
    · rw [he]; exact Rises.refl s
  | proposal p k kh =>
    by_cases hpm : p ≠ cfg.me
    · obtain ⟨n, hn⟩ := seek_eq (cfg := cfg) (record cfg s p k kh) k kh
      refine hset (seek cfg (record cfg s p k kh) k kh).1
        ⟨by rw [hn]; exact le_rfl, by rw [hn]; exact id, by rw [hn]; exact le_rfl,
          by rw [hn]; exact record_certHeight s p k kh⟩ (by rw [hn]; exact hs)
        (by rw [step_proposal, if_pos hpm])
    · rw [step_proposal, if_neg hpm]; exact Rises.refl s

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

/-- **Along a trace without restarts at `v`**, its top, next undecided
slot and certificate's height only rise. -/
theorem rises_before {v : Validator} (hnr : ∀ i : ℕ, tr[i]? ≠ some (v, Input.restart)) :
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
      · rename_i hw
        subst hw
        exact rises_step (cfg := cfg.at w) (fired_before (cfg := cfg) hnr j).1
          fun h => hnr j (by rw [he, h])
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
