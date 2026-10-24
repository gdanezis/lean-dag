import LeanDag.Node.Helpers.Arrive
/-!
# The wait timer along a trace

`docs/validator.md` §5.2. A node with a quorum of its top round has armed
that round's timer (`Armed`). The node set the timer at its last event
that set it; from that event on it is at that round with the timer armed
(`armed_last`). Past the last restart the timer fires within its timeout
(`TopTimerBy`). A node sets each timer at or below its top, and one of its
top round only with a quorum of it (`timersSet_before`). So a timer that
fires at the node's top round was set a timeout before, with a quorum of
the round (`timer_set`).
-/

namespace LeanDag

namespace Node

variable {Validator BlockId Payload : Type} [Fintype Validator] [DecidableEq Validator]
variable [LinearOrder BlockId]
variable {cfg : Config Validator BlockId Payload}

/-! ## Through one step -/

section Step

variable (cfg) in
/-- **Arming from `s` to `s'` sets the timer**: a round armed in `s'` and
not in `s` had its timer set in `out`. -/
def ArmsBy (s : State Validator BlockId Payload) (out : List (Output Validator BlockId Payload))
    (s' : State Validator BlockId Payload) : Prop :=
  ∀ n, s'.armed = some n → s.armed ≠ some n → Output.setTimer n (cfg.timeout n) ∈ out

omit [Fintype Validator] in
theorem ArmsBy.refl (s : State Validator BlockId Payload) : ArmsBy cfg s [] s :=
  fun _ h h' => absurd h h'

omit [Fintype Validator] in
theorem ArmsBy.trans {a b c : State Validator BlockId Payload}
    {o₁ o₂ : List (Output Validator BlockId Payload)} (h₁ : ArmsBy cfg a o₁ b)
    (h₂ : ArmsBy cfg b o₂ c) : ArmsBy cfg a (o₁ ++ o₂) c := by
  intro n hc ha
  by_cases hb : b.armed = some n
  · exact List.mem_append_left _ (h₁ n hb ha)
  · exact List.mem_append_right _ (h₂ n hc hb)

omit [Fintype Validator] in
theorem ArmsBy.of_armed {s s' : State Validator BlockId Payload}
    {out : List (Output Validator BlockId Payload)} (h : s'.armed = s.armed) :
    ArmsBy cfg s out s' :=
  fun _ h₁ h₂ => absurd (h ▸ h₁) h₂

omit [Fintype Validator] in
theorem ArmsBy.congr {s x s' : State Validator BlockId Payload}
    {out out' : List (Output Validator BlockId Payload)} (hx : x.armed = s.armed)
    (h : ArmsBy cfg x out s') (hsub : out ⊆ out') : ArmsBy cfg s out' s' :=
  fun n h₁ h₂ => hsub (h n h₁ (hx ▸ h₂))

omit [Fintype Validator] in
theorem pass_armed (s : State Validator BlockId Payload) : (Node.pass cfg s).1.armed = s.armed := by
  simp only [Node.pass, flushSyncs_armed]
  rw [decideStep_armed, progress_armed]

omit [Fintype Validator] in
theorem armsBy_arm (s : State Validator BlockId Payload) :
    ArmsBy cfg s (Node.arm cfg s).2 (Node.arm cfg s).1 := by
  intro n h₁ h₂
  unfold Node.arm at h₁ ⊢
  rcases ht : s.top with _ | r
  · simp only [ht] at h₁; exact absurd h₁ h₂
  · simp only [ht] at h₁ ⊢
    by_cases hc : s.armed ≠ some r ∧ cfg.q ≤ (s.memory.authorsAt r).card
    · rw [if_pos hc] at h₁ ⊢
      obtain rfl : r = n := Option.some.inj h₁
      exact List.mem_singleton_self _
    · rw [if_neg hc] at h₁
      exact absurd h₁ h₂

omit [Fintype Validator] in
theorem armsBy_advance (s : State Validator BlockId Payload) :
    ArmsBy cfg s (Node.advance cfg s).2 (Node.advance cfg s).1 :=
  (ArmsBy.of_armed (pass_armed s) (out := (Node.pass cfg s).2)).trans (armsBy_arm _)

omit [Fintype Validator] in
theorem armsBy_quiesce (n : ℕ) (s : State Validator BlockId Payload) :
    ArmsBy cfg s (Node.quiesce cfg n s).2 (Node.quiesce cfg n s).1 :=
  (quiesce_rel (P := fun _ => True) (R := ArmsBy cfg) ArmsBy.refl
    (fun _ _ _ _ _ h₁ h₂ => h₁.trans h₂) (fun s _ => ⟨armsBy_advance s, trivial⟩) n s trivial).1

/-- **A step that arms a round sets its timer.** -/
theorem armsBy_step (s : State Validator BlockId Payload) (inp : Input Validator BlockId Payload) :
    ArmsBy cfg s (Node.step cfg s inp).2 (Node.step cfg s inp).1 := by
  cases inp with
  | start =>
    simp only [Node.step]
    split
    · split
      · exact ArmsBy.congr rfl (armsBy_quiesce _ _) (List.subset_append_right _ _)
      · exact ArmsBy.refl _
    · exact ArmsBy.refl _
  | deliver u id b =>
    rcases step_receipt (cfg := cfg) (s := s) (Or.inl ⟨u, id, b, rfl⟩) with
      he | ⟨s₁, pre, hr, -, he⟩
    · rw [he]; exact ArmsBy.refl _
    · rw [he]; exact ArmsBy.congr hr.armed (armsBy_quiesce _ _) (List.subset_append_right _ _)
  | stream u L =>
    rcases step_receipt (cfg := cfg) (s := s) (Or.inr ⟨u, L, rfl⟩) with he | ⟨s₁, pre, hr, -, he⟩
    · rw [he]; exact ArmsBy.refl _
    · rw [he]; exact ArmsBy.congr hr.armed (armsBy_quiesce _ _) (List.subset_append_right _ _)
  | timer r =>
    rw [step_timer_fst]
    rcases step_timer_snd (cfg := cfg) s r with h | h <;> rw [h]
    · exact ArmsBy.congr rfl (armsBy_quiesce _ _) (List.Subset.refl _)
    · exact ArmsBy.congr rfl (armsBy_quiesce _ _) (List.subset_append_left _ _)
  | syncRequest p t fr ids => exact ArmsBy.of_armed rfl
  | restart =>
    exact ArmsBy.congr (x := { s with recovering := true }) rfl (armsBy_quiesce _ _)
      (List.subset_append_right _ _)

variable (cfg) in
/-- **The top round is armed once the memory holds a quorum of it.** -/
def Armed (s : State Validator BlockId Payload) : Prop :=
  ∀ r, s.top = some r → cfg.q ≤ (s.memory.authorsAt r).card → s.armed = some r

omit [Fintype Validator] in
theorem armed_arm (s : State Validator BlockId Payload) : Armed cfg (Node.arm cfg s).1 := by
  intro r ht hq
  rw [arm_top] at ht
  rw [arm_memory] at hq
  unfold Node.arm
  simp only [ht]
  by_cases h : s.armed = some r
  · rw [if_neg (fun hc => hc.1 h)]; exact h
  · rw [if_pos ⟨h, hq⟩]

omit [Fintype Validator] in
theorem armed_quiesce : ∀ (n : ℕ) (s : State Validator BlockId Payload),
    Armed cfg (Node.quiesce cfg (n + 1) s).1
  | 0, s => by
    rcases quiesce_succ_cases (cfg := cfg) 0 s with h | h <;> rw [h]
    · exact armed_arm _
    · exact armed_arm _
  | n + 1, s => by
    rcases quiesce_succ_cases (cfg := cfg) (n + 1) s with h | h <;> rw [h]
    · exact armed_arm _
    · exact armed_quiesce n _

omit [Fintype Validator] in
theorem armed_settle (x : State Validator BlockId Payload) : Armed cfg (Node.settle cfg x).1 := by
  obtain ⟨n, hn⟩ := passes_succ (cfg := cfg) x
  unfold Node.settle
  rw [hn]
  exact armed_quiesce n x

theorem Armed.step {s : State Validator BlockId Payload} (h : Armed cfg s)
    (inp : Input Validator BlockId Payload) : Armed cfg (Node.step cfg s inp).1 := by
  rcases step_settles (cfg := cfg) (s := s) (inp := inp) with he | ⟨x, he⟩ <;> rw [he]
  · exact h
  · exact armed_settle x

end Step

/-! ## Along a trace -/

section Trace

variable {tr : Trace Validator BlockId Payload} {v : Validator}

/-- **A node with a quorum of its top round has armed it**, before every
event. -/
theorem armed_before (v : Validator) (i : ℕ) : Armed (cfg.at v) (stateBefore cfg tr i v) :=
  inv_before (cfg := cfg) v (fun s => Armed (cfg.at v) s)
    (fun _ h => by simp [stateBefore, inputsBefore, run, State.init] at h)
    (fun _ inp h => h.step inp) i

/-- **An armed round has a quorum**, before every event. -/
theorem armedQuorum_before (v : Validator) (i : ℕ) :
    ArmedQuorum (cfg.at v) (stateBefore cfg tr i v) :=
  inv_before (cfg := cfg) v (fun s => ArmedQuorum (cfg.at v) s)
    (fun _ h => by simp [stateBefore, inputsBefore, run, State.init] at h)
    (fun _ inp h => (timersSet_step h inp).2) i

/-- **The timers a node sets at an event**, read on its state after it:
each at or below the top, one of the top round above `0` only with a
quorum of it. -/
theorem timersSet_before {i : ℕ} {inp : Input Validator BlockId Payload}
    (hi : tr[i]? = some (v, inp)) :
    TimersSet (cfg.at v) (stateBefore cfg tr (i + 1) v) (outputsAt cfg tr i) := by
  rw [outputsAt_eq hi, stateBefore_succ hi, if_pos rfl]
  exact (timersSet_step (armedQuorum_before v i) inp).1

/-- **A round armed later was armed earlier, or had its timer set in
between.** -/
theorem armed_from {E n : ℕ} (ha : (stateBefore cfg tr E v).armed = some n) {k : ℕ} (hk : k ≤ E) :
    (stateBefore cfg tr k v).armed = some n ∨ ∃ k', k ≤ k' ∧ k' < E ∧
      (tr[k']?.map Prod.fst) = some v ∧
        Output.setTimer n (cfg.timeout n) ∈ outputsAt cfg tr k' := by
  induction E, hk using Nat.le_induction with
  | base => exact Or.inl ha
  | succ E hkE ih =>
    rcases before_succ_cases (cfg := cfg) (tr := tr) v E with heq | ⟨inp, he, heq⟩
    · rcases ih (heq ▸ ha) with h | ⟨k', h₁, h₂, h₃⟩
      · exact Or.inl h
      · exact Or.inr ⟨k', h₁, by omega, h₃⟩
    · by_cases hE : (stateBefore cfg tr E v).armed = some n
      · rcases ih hE with h | ⟨k', h₁, h₂, h₃⟩
        · exact Or.inl h
        · exact Or.inr ⟨k', h₁, by omega, h₃⟩
      · refine Or.inr ⟨E, hkE, by omega, by rw [he]; rfl, ?_⟩
        rw [outputsAt_eq he]
        exact armsBy_step (cfg := cfg.at v) _ inp n (heq ▸ ha) hE

/-- **The top between two events**: a node at round `n` at a later event
was at round `n` at every event in between at which it was at `n` or
above. -/
theorem top_between {p q : ℕ} (hpq : p ≤ q) {n : ℕ}
    (hp : (stateBefore cfg tr p v).top.isSome) (hpn : n ≤ (stateBefore cfg tr p v).top.getD 0)
    (hq : (stateBefore cfg tr q v).top = some n) : (stateBefore cfg tr p v).top = some n := by
  have h := rises_before (cfg := cfg) (tr := tr) v hpq
  obtain ⟨t, ht⟩ := Option.isSome_iff_exists.mp hp
  have h₁ := h.1
  rw [ht, hq] at h₁
  rw [ht] at hpn
  simp only [Option.getD_some] at h₁ hpn
  rw [ht, show t = n by omega]

open Classical in
/-- **The last event that set an armed top round's timer**: a node at
round `n` with `n` armed before event `E` set round `n`'s timer at a last
event before `E`, and from it to `E` it is at round `n` with `n` armed. -/
theorem armed_last {E n : ℕ} (ha : (stateBefore cfg tr E v).armed = some n)
    (ht : (stateBefore cfg tr E v).top = some n) :
    ∃ a < E, (tr[a]?.map Prod.fst) = some v ∧
      Output.setTimer n (cfg.timeout n) ∈ outputsAt cfg tr a ∧
      (∀ a', a < a' → a' < E → (tr[a']?.map Prod.fst) = some v →
        Output.setTimer n (cfg.timeout n) ∉ outputsAt cfg tr a') ∧
      ∀ k, a < k → k ≤ E →
        (stateBefore cfg tr k v).top = some n ∧ (stateBefore cfg tr k v).armed = some n := by
  let P : ℕ → Prop := fun a =>
    (tr[a]?.map Prod.fst) = some v ∧ Output.setTimer n (cfg.timeout n) ∈ outputsAt cfg tr a
  obtain ⟨b, hbE, hPb⟩ : ∃ b, b < E ∧ P b := by
    rcases armed_from ha (Nat.zero_le E) with h | ⟨k', -, h₁, h₂⟩
    · simp [stateBefore, inputsBefore, run, State.init] at h
    · exact ⟨k', h₁, h₂⟩
  set a := Nat.findGreatest P (E - 1) with hadef
  have hPa : P a := Nat.findGreatest_spec (P := P) (m := b) (by omega) hPb
  have haE : a < E := lt_of_le_of_lt (Nat.findGreatest_le (E - 1)) (by omega)
  have hmax : ∀ a', a < a' → a' < E → ¬ P a' := fun a' h₁ h₂ =>
    Nat.findGreatest_is_greatest h₁ (by omega)
  refine ⟨a, haE, hPa.1, hPa.2, fun a' h₁ h₂ h₃ h₄ => hmax a' h₁ h₂ ⟨h₃, h₄⟩, fun k hak hkE => ?_⟩
  obtain ⟨inpa, hai⟩ := Converge.event_of_map hPa.1
  obtain ⟨t, hta, hnt, -⟩ := timersSet_before hai n _ hPa.2
  obtain ⟨hr₁, hr₂, -⟩ := rises_before (cfg := cfg) (tr := tr) v (show a + 1 ≤ k by omega)
  rw [hta] at hr₁ hr₂
  simp only [Option.getD_some] at hr₁
  refine ⟨top_between hkE (hr₂ rfl) (by omega) ht, ?_⟩
  rcases armed_from ha hkE with h | ⟨k', hkk', hk'E, hk'v, hk'set⟩
  · exact h
  · exact absurd ⟨hk'v, hk'set⟩ (hmax k' (by omega) hk'E)

variable {T : Finset Validator} {time : ℕ → ℕ} {t_r t₁ : ℕ}

variable (cfg) in
/-- **The top round's timer fires within its timeout past `G`**: a
reliable node at round `n` with `n` armed at a time `s ≥ G` is given
round `n`'s timer by `s + timeout n`. -/
def TopTimerBy (T : Finset Validator) (tr : Trace Validator BlockId Payload)
    (time : ℕ → ℕ) (G t₁ : ℕ) : Prop :=
  ∀ v ∈ T, ∀ s n, G ≤ s → s + cfg.timeout n ≤ t₁ → (stateAt cfg tr time v s).top = some n →
    (stateAt cfg tr time v s).armed = some n →
      ∃ f, tr[f]? = some (v, .timer n) ∧ time f ≤ s + cfg.timeout n

/-- **The armed top round's timer fires**, a timeout after it was last
set, when timers fire. -/
theorem TopTimerBy.of_fire {G : ℕ} (hmono : Live.TimeMono tr time)
    (h : Live.TimersFire cfg T tr time t₁) : TopTimerBy cfg T tr time G t₁ := by
  intro v hv s n _ hst₁ hts has
  obtain ⟨a, haE, hav, hset, -, -⟩ := armed_last (E := eventsBy tr time s) has hts
  obtain ⟨inp, hai⟩ := Converge.event_of_map hav
  have hal : a < tr.length := (List.getElem?_eq_some_iff.mp hai).1
  have hta : time a ≤ s := (lt_eventsBy hmono hal).mp haE
  obtain ⟨f, -, hfe, htf⟩ := h a v inp hai hv n (cfg.timeout n) hset (by omega)
  exact ⟨f, hfe, by omega⟩

/-- **Past the last restart, the armed top round's timer fires within its
timeout**: a restart after its last setting, while armed, would have set
it again. -/
theorem topTimerBy_of_up (hmono : Live.TimeMono tr time) (hup : Live.UpFrom T tr time t_r t₁)
    (hfire : Live.TimersFireUp cfg T tr time t₁) {G : ℕ} (hG : t_r ≤ G) :
    TopTimerBy cfg T tr time G t₁ := by
  intro v hv s n hgs hst₁ hts has
  obtain ⟨a, haE, hav, hset, hmax, hat⟩ := armed_last (E := eventsBy tr time s) has hts
  obtain ⟨inp, hai⟩ := Converge.event_of_map hav
  have hal : a < tr.length := (List.getElem?_eq_some_iff.mp hai).1
  have hta : time a ≤ s := (lt_eventsBy hmono hal).mp haE
  have hnr : ∀ k, a < k → time k ≤ time a + cfg.timeout n → tr[k]? ≠ some (v, .restart) := by
    intro k hak hkt hk
    have hkl : k < tr.length := (List.getElem?_eq_some_iff.mp hk).1
    by_cases hkE : k < eventsBy tr time s
    · obtain ⟨htk, hak'⟩ := hat k hak hkE.le
      refine hmax k hak hkE (by rw [hk]; rfl) ?_
      rw [outputsAt_eq hk]
      change _ ∈ Node.resend (cfg.at v) _ ++ Node.rearm (cfg.at v) _ ++ _
      refine List.mem_append_left _ (List.mem_append_right _ ?_)
      simp [Node.rearm, htk, hak', Config.at]
    · have := hup k v hk hv (by omega)
      have := (lt_eventsBy hmono hkl).not.mp hkE
      omega
  obtain ⟨f, -, hfe, htf⟩ := hfire a v inp hai hv n (cfg.timeout n) hset (by omega) hnr
  exact ⟨f, hfe, by omega⟩

/-- **A timer that fires was set before**: at an event after which the
node was at its round or above, and if at its round, above `0`, a
timeout before, with a quorum of it. -/
theorem timer_set (hwait : Live.TimersAfterSet cfg T tr time) (hv : v ∈ T) {j n : ℕ}
    (hj : tr[j]? = some (v, .timer n)) :
    ∃ i < j, (tr[i]?.map Prod.fst) = some v ∧
      ∃ t, (stateBefore cfg tr (i + 1) v).top = some t ∧ n ≤ t ∧
        (n = t → 1 ≤ n → time i + cfg.timeout n ≤ time j ∧
          cfg.q ≤ ((stateBefore cfg tr (i + 1) v).disk.authorsAt n).card) := by
  obtain ⟨i, hij, a, hiv, hset, hta⟩ := hwait j v n hj hv
  obtain ⟨inp, hi⟩ := Converge.event_of_map hiv
  obtain ⟨t, ht, hnt, hq⟩ := timersSet_before hi n a hset
  refine ⟨i, hij, hiv, t, ht, hnt, fun h₁ h₂ => ?_⟩
  obtain ⟨ha, hq'⟩ := hq h₁ h₂
  exact ⟨ha ▸ hta, hq'⟩

end Trace

end Node

end LeanDag
