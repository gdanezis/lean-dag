import LeanDag.Node.Helpers.Reach
import LeanDag.Node.Helpers.Prefix
/-!
# No reliable node stalls twice past GST

`docs/validator.md` §13.12. Only a timer that finds a node stalled notes
the round (`step_stalled`), so a node noted stalled at `r` was found so at
an earlier firing of `r`'s timer (`stalled_noted`). Past GST that firing
lies a timeout before the next, and a reliable node is above `r` within
`3Δ + Δₛ` of it (`stall_builds`), so the next finds it elsewhere
(`no_stall`). The argument reads the trace's events before the firing
only, so it runs on that prefix, where the reliable nodes are steady by
induction.
-/

namespace LeanDag

namespace Node

variable {Validator BlockId Payload : Type} [Fintype Validator] [DecidableEq Validator]
variable [LinearOrder BlockId]
variable {cfg : Config Validator BlockId Payload}

/-! ## What a step does to the stalled round -/

omit [Fintype Validator] in
theorem tryBuild_stalled {s s' : State Validator BlockId Payload}
    {out : List (Output Validator BlockId Payload)} (h : tryBuild cfg s = some (s', out)) :
    s'.stalled = s.stalled := by
  unfold tryBuild at h
  split at h
  · dsimp only at h
    split at h
    · split at h
      · rw [Option.some.injEq, Prod.mk.injEq] at h
        rw [← h.1]
      · cases h
    · cases h
  · cases h

omit [Fintype Validator] in
theorem progress_stalled : ∀ (fuel : ℕ) (s : State Validator BlockId Payload),
    (progress cfg fuel s).1.stalled = s.stalled
  | 0, _ => rfl
  | fuel + 1, s => by
    unfold Node.progress
    split
    · rename_i s₁ out h
      rw [progress_stalled fuel s₁, tryBuild_stalled h]
    · rfl

omit [Fintype Validator] in
theorem decideStep_stalled (s : State Validator BlockId Payload) :
    (decideStep cfg s).1.stalled = s.stalled := by
  unfold Node.decideStep
  dsimp only
  split
  · obtain ⟨ps, c, lp, ch, he, -⟩ := proposeAt_eq (cfg := cfg)
      { s with lo := s.lo + _, decided := _ }
    rw [he]
  · obtain ⟨ps, c, lp, ch, he, -⟩ := proposeAt_eq (cfg := cfg) s
    rw [he]

omit [Fintype Validator] in
theorem collect_stalled (s : State Validator BlockId Payload) :
    (collect cfg s).1.stalled = s.stalled := by
  unfold Node.collect
  split
  · dsimp only
    split <;> rfl
  · rfl

omit [Fintype Validator] in
theorem advance_stalled (s : State Validator BlockId Payload) :
    (advance cfg s).1.stalled = s.stalled := by
  simp only [Node.advance]
  rw [collect_stalled, decideStep_stalled, progress_stalled]

omit [Fintype Validator] in
theorem settle_stalled (s : State Validator BlockId Payload) :
    (settle cfg s).1.stalled = s.stalled := by
  have hq : ∀ (n : ℕ) (x : State Validator BlockId Payload),
      (quiesce cfg n x).1.stalled = x.stalled := fun n x =>
    (quiesce_rel (P := fun _ => True) (R := fun a _ b => b.stalled = a.stalled)
      (fun _ => rfl) (fun _ _ _ _ _ h₁ h₂ => h₂.trans h₁)
      (fun y _ => ⟨advance_stalled y, trivial⟩) n x trivial).1
  rcases settle_cases (cfg := cfg) s with he | ⟨s₁, hj, he⟩ <;> rw [he]
  · exact hq _ s
  · obtain ⟨R, rc, rfl⟩ := tryResume_eq hj
    exact hq _ _

/-- **A step notes a stalled round only at that round's timer**, finding
the node stalled there; a restart clears it. -/
theorem step_stalled (s : State Validator BlockId Payload) (inp : Input Validator BlockId Payload) :
    (Node.step cfg s inp).1.stalled = s.stalled ∨ (Node.step cfg s inp).1.stalled = none ∨
      ∃ r, inp = .timer r ∧ stalledAt cfg s r = true ∧
        (Node.step cfg s inp).1.stalled = some r := by
  have hsame : ∀ x : State Validator BlockId Payload, x.stalled = s.stalled →
      (settle cfg x).1.stalled = s.stalled := fun x hx => (settle_stalled x).trans hx
  cases inp with
  | start =>
    simp only [Node.step]
    split
    · split
      · exact Or.inl (hsame _ rfl)
      · exact Or.inl rfl
    · exact Or.inl rfl
  | deliver id b =>
    simp only [Node.step]
    split
    · exact Or.inl (hsame _ rfl)
    · split <;> exact Or.inl rfl
  | timer r =>
    rw [step_timer_eq]
    simp only [settle_stalled]
    unfold timerState
    by_cases h : stalledAt cfg s r = true
    · exact Or.inr (Or.inr ⟨r, rfl, h, by simp [h]⟩)
    · exact Or.inl (by simp [h])
  | restart =>
    simp only [Node.step]
    exact Or.inr (Or.inl (by rw [settle_stalled]; rfl))
  | baseOffer p G =>
    rw [step_offer]
    split
    · exact Or.inl (hsame _ rfl)
    · exact Or.inl rfl
  | certOffer p c ds =>
    rcases certOffer_cases (cfg := cfg) s p c ds with ⟨ds', -, -, -, he⟩ | ⟨-, -, he⟩ | he <;>
      rw [he]
    · rw [adopt_eq]; exact Or.inl (hsame _ rfl)
    · exact Or.inl (hsame _ rfl)
    · exact Or.inl rfl
  | announced p c =>
    rcases announced_cases (cfg := cfg) s p c with ⟨-, -, he⟩ | he | he <;> rw [he]
    · exact Or.inl (hsame _ rfl)
    · exact Or.inl rfl
    · exact Or.inl rfl
  | proposal p k kh =>
    rw [step_proposal]
    split
    · exact Or.inl (hsame _ rfl)
    · exact Or.inl rfl
  | _ => exact Or.inl rfl

variable {tr : Trace Validator BlockId Payload}

/-- **A node noted stalled at `r` was found so at an earlier firing of
`r`'s timer.** -/
theorem stalled_noted (v : Validator) :
    ∀ (j : ℕ) {r : ℕ}, (stateBefore cfg tr j v).stalled = some r →
      ∃ j' < j, tr[j']? = some (v, .timer r) ∧
        stalledAt (cfg.at v) (stateBefore cfg tr j' v) r = true
  | 0, r, h => by simp [stateBefore, inputsBefore, run, State.init] at h
  | j + 1, r, h => by
    rcases before_succ_cases (cfg := cfg) (tr := tr) v j with heq | ⟨inp, he, heq⟩
    · rw [heq] at h
      obtain ⟨j', hj', rest⟩ := stalled_noted v j h
      exact ⟨j', by omega, rest⟩
    · rw [heq] at h
      rcases step_stalled (cfg := cfg.at v) (stateBefore cfg tr j v) inp with
        h₁ | h₁ | ⟨r', rfl, hst, h₁⟩
      · rw [h₁] at h
        obtain ⟨j', hj', rest⟩ := stalled_noted v j h
        exact ⟨j', by omega, rest⟩
      · rw [h₁] at h; cases h
      · rw [h₁, Option.some.injEq] at h
        subst h
        exact ⟨j, by omega, he, hst⟩

/-! ## No stall past GST -/

section NoStall

variable {H T : Finset Validator} {time : ℕ → ℕ} {gst Δ Δₛ t₁ : ℕ}

/-- Under an admissible row the horizon's lag, at least the vote offset, is
positive. -/
theorem one_le_lag (hadm : cfg.Admissible) (hvo : cfg.p.voteOffset ≤ cfg.lag) : 1 ≤ cfg.lag := by
  have hw : 2 ≤ cfg.p.waveLength := by
    rcases hadm.1 with ⟨-, hw, -⟩ | ⟨-, hw, -⟩ | ⟨-, hw, -⟩ | ⟨-, hw, -⟩ <;> omega
  exact (Scheme.Params.one_le_voteOffset hw).trans hvo

/-- **No reliable node stalls twice by `t₁`**, if none does by
`gst + 3Δ + Δₛ`: a quorum holds a reliable node, the timeouts exceed
`2(3Δ + Δₛ)`, and the reliable nodes never restart. -/
theorem no_stall (hq : 2 ≤ cfg.q) (hσ : cfg.σ = boundedSel)
    (hadm : cfg.Admissible) (hf : Hᶜ.card ≤ cfg.f) (hid : Function.Injective cfg.idOf)
    (hvo : cfg.p.voteOffset ≤ cfg.lag) (hto : ∀ r, 2 * (3 * Δ + Δₛ) < cfg.timeout r)
    (htime : Converge.TimelyAuthentic cfg H tr)
    (hcert : Boot.TimelyCerts cfg H tr) (hinj : Converge.HashInjective cfg H tr)
    (hchain : Boot.ChainInjective cfg H tr) (hTH : T ⊆ H)
    (hqT : Fintype.card Validator < cfg.q + T.card) (hnr : Converge.NoRestart T tr)
    (hns : Live.NoStallBy cfg T tr time (gst + (3 * Δ + Δₛ))) (hmono : Live.TimeMono tr time)
    (hdel : Live.DeliveredWithin cfg T tr time gst Δ t₁)
    (htimer : Live.TimersOnTime cfg T tr time t₁)
    (hsync : Live.SyncedWithin cfg H T tr time gst Δₛ t₁) :
    ∀ j v r, v ∈ T → tr[j]? = some (v, .timer r) → time j ≤ t₁ →
      stallsTwice (cfg.at v) (stateBefore cfg tr j v) r = false := by
  intro j
  induction j using Nat.strong_induction_on with
  | _ j ih =>
  intro v r hv hj htj
  by_cases hg : time j ≤ gst + (3 * Δ + Δₛ)
  · exact hns j v r hv hj hg
  rw [← Bool.not_eq_true]
  intro hst
  unfold stallsTwice at hst
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hst
  obtain ⟨hstj, hnoted⟩ := hst
  have hjl : j < tr.length := (List.getElem?_eq_some_iff.mp hj).1
  -- the firing that noted the stall, a timeout before
  obtain ⟨j', hj'j, hj', hst'⟩ := stalled_noted (cfg := cfg) (tr := tr) v j hnoted
  obtain ⟨i, hij, a, hiv, hset, hta, hno⟩ := htimer.2 j v r hj hv
  have hj'i : j' ≤ i := by
    by_contra h
    exact hno j' (by omega) hj'j hj'
  -- the prefix before `j`, on which the reliable nodes are steady
  have hN : ∀ k < tr.length, time k ≤ time j - 1 → k < j := by
    intro k hk htk
    by_contra h
    have := hmono j k (by omega) hk
    omega
  have hsteady : ∀ u ∈ T, Steady cfg (tr.take j) u := fun u hu =>
    steady_take fun k hk inp hku => ⟨fun h => hnr k u hu (by rw [hku, h]),
      fun r' hr' => ih k hk u r' hu (by rw [hku, hr']) ((hmono k j hk.le hjl).trans htj)⟩
  have hnv := hsteady v hv
  -- the timer was set for `timeout r`
  obtain ⟨inpi, hi⟩ := Converge.event_of_map hiv
  have hi' : (tr.take j)[i]? = some (v, inpi) := by rw [take_getElem? hij]; exact hi
  have ha : a = cfg.timeout r := by
    rw [← outputsAt_take hij, outputsAt_eq hi'] at hset
    exact (timersBuilt_step (cfg := cfg.at v) (fired_before (cfg := cfg) hnv i).1
      (hnv i _ hi').1 r a hset).1
  have htj' : time j' ≤ time i := hmono j' i hj'i (by omega)
  have hτ := hto r
  have ht₁' : time j - 1 ≤ t₁ := by omega
  -- the stalled node is above `r` by `max (time j') gst + 3Δ + Δₛ`, before `j`
  have hb := stall_builds (tr := tr.take j) (time := time) hq hσ hadm hf hid
    (timelyAuthentic_take htime j) (timelyCerts_take hcert j) (hashInjective_take hinj j)
    (chainInjective_take hchain j) hTH hsteady hqT (one_le_lag hadm hvo) (timeMono_take hmono j)
    (deliveredWithin_take hdel ht₁' hN) (syncedWithin_take hsync hinj ht₁' hN) hv
    (by rw [take_getElem? hj'j]; exact hj') (by rw [stateBefore_take hj'j.le]; exact hst')
    (τ := max (time j') gst + 3 * Δ + Δₛ) le_rfl (by omega)
  -- but it is still at `r` at `j`
  have hE : eventsBy (tr.take j) time (max (time j') gst + 3 * Δ + Δₛ) ≤ j :=
    (eventsBy_le_length _).trans (by simp)
  have hr := (rises_before (cfg := cfg) hnv hE).1
  rw [stateBefore_take le_rfl] at hr
  unfold stalledAt at hstj
  simp only [Bool.and_eq_true, Bool.not_eq_true', decide_eq_true_eq] at hstj
  rw [hstj.2.1] at hr
  change _ ≤ topAt cfg (tr.take j) time v _ at hb
  unfold topAt stateAt at hb
  simp only [Option.getD_some] at hr
  omega

end NoStall

end Node

end LeanDag
