import LeanDag.Node.Helpers.Verdict
import LeanDag.Node.Helpers.Converge
import LeanDag.Node.Helpers.Decided
/-!
# Honest disks are cuts of the run's record

Over a trace, what each honest node knew is what the trace delivered
it and what it made (`knownOf_sub`). Timely authentication and
the hash over the trace give authentication and the hash at its end
(`authentic_of_timely`, `hashInjective_of_trace`), so the honest nodes'
knowledge forms the run's record. By induction over the trace, every
honest disk is a cut of that record and every decision a verdict on a
view of it (`cut_before`).
-/

namespace LeanDag

namespace Node

variable {Validator BlockId Payload : Type} [Fintype Validator] [DecidableEq Validator]
variable [LinearOrder BlockId]

variable {cfg : Config Validator BlockId Payload} {tr : Trace Validator BlockId Payload}

omit [Fintype Validator] [LinearOrder BlockId] in
/-- A node's inputs before an event extend its inputs before any earlier
one, and are extended by its inputs over the whole trace. -/
theorem inputsBefore_prefix (v : Validator) {i j : ℕ} (hij : i ≤ j) :
    ∃ l, inputsBefore tr j v = inputsBefore tr i v ++ l := by
  induction j, hij using Nat.le_induction with
  | base => exact ⟨[], by simp⟩
  | succ j _ ih =>
    obtain ⟨l, hl⟩ := ih
    rcases hj : tr[j]? with _ | ⟨w, inp⟩
    · have hL : tr.length ≤ j := List.getElem?_eq_none_iff.mp hj
      refine ⟨l, ?_⟩
      rw [inputsBefore_of_le (by omega), ← inputsBefore_of_le hL, hl]
    · exact ⟨l ++ if w = v then [inp] else [], by rw [inputsBefore_succ hj, hl, List.append_assoc]⟩

omit [Fintype Validator] [LinearOrder BlockId] in
theorem inputsBefore_prefix_length (v : Validator) (t : ℕ) :
    ∃ l, inputsBefore tr tr.length v = inputsBefore tr t v ++ l := by
  by_cases h : t ≤ tr.length
  · exact inputsBefore_prefix v h
  · exact ⟨[], by rw [inputsBefore_of_le (by omega : tr.length ≤ t)]; simp⟩

/-- **What a node's run output before an event, its whole run output.** -/
theorem mem_outputs_full {v : Validator} {t : ℕ} {o : Output Validator BlockId Payload}
    (h : o ∈ (run (cfg.at v) (State.init (cfg.at v)) (inputsBefore tr t v)).2) :
    o ∈ (run (cfg.at v) (State.init (cfg.at v)) (inputsBefore tr tr.length v)).2 := by
  obtain ⟨l, hl⟩ := inputsBefore_prefix_length (tr := tr) v t
  rw [hl, run_append]
  exact List.mem_append_left _ h

/-- **What an event at a node outputs, its whole run output.** -/
theorem mem_outputs_of_event {i : ℕ} {w : Validator} {inp : Input Validator BlockId Payload}
    (h : tr[i]? = some (w, inp)) {o : Output Validator BlockId Payload}
    (ho : o ∈ outputsAt cfg tr i) :
    o ∈ (run (cfg.at w) (State.init (cfg.at w)) (inputsBefore tr tr.length w)).2 := by
  refine mem_outputs_full (t := i + 1) ?_
  rw [inputsBefore_succ h, if_pos rfl, run_append_single]
  rw [outputsAt_eq h] at ho
  exact List.mem_append_right _ ho

/-- **What a node knew before an event, it knew over the trace.** -/
theorem knownBefore_knownOf {t : ℕ} {v : Validator} {x : BlockId × Block Validator BlockId Payload}
    (hx : x ∈ Converge.knownBefore cfg tr t v) : x ∈ knownOf cfg tr v := by
  obtain ⟨l, hl⟩ := inputsBefore_prefix_length (tr := tr) v t
  simp only [Converge.knownBefore, Set.mem_setOf_eq, List.mem_append] at hx
  simp only [knownOf, runOf, List.mem_append, hl, delivered, List.flatMap_append,
    run_append, persists_append]
  rcases hx with hx | hx
  · exact Or.inl (Or.inl hx)
  · exact Or.inr (Or.inl hx)

/-- **What an event gives a node, it knew over the trace.** -/
theorem event_knownOf {t : ℕ} {w : Validator} {inp : Input Validator BlockId Payload}
    (h : tr[t]? = some (w, inp)) :
    (∀ x ∈ delivered (cfg.at w) [inp], x ∈ knownOf cfg tr w) ∧
    ∀ x ∈ persists (step (cfg.at w) (stateBefore cfg tr t w) inp).2,
      x ∈ knownOf cfg tr w := by
  have ht : t + 1 ≤ tr.length := (List.getElem?_eq_some_iff.mp h).1
  obtain ⟨l, hl⟩ := inputsBefore_prefix (tr := tr) w ht
  rw [inputsBefore_succ h, if_pos rfl] at hl
  refine ⟨fun x hx => ?_, fun x hx => ?_⟩
  · simp only [knownOf, runOf, List.mem_append, hl, delivered, List.flatMap_append]
    exact Or.inl (Or.inl (Or.inr (by simpa [delivered] using hx)))
  · simp only [knownOf, runOf, List.mem_append, hl, run_append, persists_append]
    refine Or.inr (Or.inl (Or.inr ?_))
    simpa [run, stateBefore] using hx

variable {H : Finset Validator}

/-- **What an honest node knew over the trace, the trace's honest nodes
knew.** -/
theorem knownOf_sub {v : Validator} (hv : v ∈ H) {x : BlockId × Block Validator BlockId Payload}
    (hx : x ∈ knownOf cfg tr v) : x ∈ Converge.knownIn cfg H tr := by
  simp only [knownOf, List.mem_append] at hx
  rcases hx with hx | hx
  · obtain ⟨j, -, inp, hj, hd⟩ := mem_delivered_before (cfg.at v) v tr.length hx
    exact Or.inl ⟨j, v, inp, hj, hv, hd⟩
  · obtain ⟨j, -, hjv, hx⟩ := mem_persists_before (cfg := cfg) v tr.length hx
    exact Or.inr ⟨j, v, hjv, hv, hx⟩

/-! ## The record's assumptions -/

omit [Fintype Validator] [DecidableEq Validator] [LinearOrder BlockId] in
/-- A block is among an output list's broadcasts iff the list broadcasts it. -/
theorem mem_broadcasts {out : List (Output Validator BlockId Payload)}
    {x : BlockId × Block Validator BlockId Payload} :
    x ∈ broadcasts out ↔ Output.broadcast x.1 x.2 ∈ out := by
  unfold broadcasts
  rw [List.mem_filterMap]
  constructor
  · rintro ⟨o, ho, hox⟩
    cases o <;> simp at hox
    subst hox
    exact ho
  · intro h
    exact ⟨_, h, rfl⟩

/-- **The hash over the trace is injective on what the honest nodes knew
at its end.** -/
theorem hashInjective_of_trace (hinj : Converge.HashInjective cfg H tr) :
    HashInjective cfg H tr := fun _ hv _ hw x hx y hy h =>
  hinj x (knownOf_sub hv hx) y (knownOf_sub hw hy) h

/-- **Timely authentication gives authentication at the end of the
trace.** -/
theorem authentic_of_timely (htime : Converge.TimelyAuthentic cfg H tr) :
    Authentic cfg H tr := by
  intro v hv x hx hc
  obtain ⟨j, -, inp, hj, hd⟩ := mem_delivered_before (cfg.at v) v tr.length hx
  obtain ⟨i, -, hiv, hxp⟩ := htime j v inp hj hv x hd hc
  obtain ⟨inp', hi⟩ := Converge.event_of_map hiv
  exact mem_broadcasts.mpr (mem_outputs_of_event hi (mem_broadcasts.mp hxp))

/-! ## The run's record -/

/-- **Every honest disk is a cut of the run's record, and every decision
a verdict on a view of it**, before every event of the trace. -/
theorem cut_before (hσ : cfg.σ = boundedSel) (hadm : cfg.Admissible) (hf : Hᶜ.card ≤ cfg.f)
    (htime : Converge.TimelyAuthentic cfg H tr) (hinj : Converge.HashInjective cfg H tr)
    (t : ℕ) :
    ∀ v ∈ H,
      IsCut (globalRecord (hashInjective_of_trace hinj) (authentic_of_timely htime))
        (stateBefore cfg tr t v).disk ∧
      ∀ e ∈ commitsOf (run (cfg.at v) (State.init (cfg.at v)) (inputsBefore tr t v)).2,
        Verdict (cfg.at v) (globalRecord (hashInjective_of_trace hinj)
          (authentic_of_timely htime)) e := by
  -- authentication and the hash at the end of the trace
  have hinjR := hashInjective_of_trace hinj
  have hauthR := authentic_of_timely htime
  haveI : Validity.Quorate (ValidAt (Validator := Validator) (BlockId := BlockId)
      (Payload := Payload) cfg.q Clause.none) cfg.q :=
    Validity.Quorate.of_validAt hadm.2.2.2.1 fun _ _ => Iff.rfl
  let U := globalRecord hinjR hauthR
  have ht : cfg.p.Tolerates H cfg.f cfg.q := ⟨hf, hadm.2.2.2.2, hadm.1⟩
  have hg := ground hinjR hauthR
  have hK : ∀ v ∈ H, ∀ x ∈ knownOf cfg tr v, x ∈ knownAll cfg H tr :=
    fun v hv x hx => ⟨v, hv, hx⟩
  -- every honest disk is a cut, and every decision a verdict
  have key : ∀ t, ∀ v ∈ H, IsCut U (stateBefore cfg tr t v).disk ∧
      ∀ e ∈ commitsOf (run (cfg.at v) (State.init (cfg.at v)) (inputsBefore tr t v)).2,
        Verdict (cfg.at v) U e := by
    intro t
    induction t using Nat.strong_induction_on with
    | _ t ih =>
    intro v hv
    rcases t with _ | t
    · refine ⟨isCut_init hinjR hauthR (cfg.at v), fun e he => ?_⟩
      simp [inputsBefore, run, commitsOf] at he
    · rcases hj : tr[t]? with _ | ⟨w, inp⟩
      · have hL : tr.length ≤ t := List.getElem?_eq_none_iff.mp hj
        have h₁ : inputsBefore tr (t + 1) v = inputsBefore tr t v := by
          rw [inputsBefore_of_le (by omega), inputsBefore_of_le hL]
        have := ih t (by omega) v hv
        unfold stateBefore at this ⊢
        rw [h₁]
        exact this
      · by_cases hw : w = v
        · subst hw
          obtain ⟨hc, hv₀⟩ := ih t (by omega) w hv
          have hi := Converge.inv_before (cfg := cfg) (tr := tr) t w
          obtain ⟨hd, hb⟩ := event_knownOf (cfg := cfg) hj
          obtain ⟨hc', hv'⟩ := IsCut.step (cfg := cfg.at w) hg hσ ht inp hc
            (fun e he => hK w hv _ (knownBefore_knownOf (hi.pend e he)))
            (fun e he => hK w hv e (hd e he))
            (fun e he => hK w hv e (hb e he))
          refine ⟨by rw [stateBefore_succ hj, if_pos rfl]; exact hc', fun e he => ?_⟩
          rw [inputsBefore_succ hj, if_pos rfl, run_append_single, commitsOf_append] at he
          rcases List.mem_append.mp he with he | he
          · exact hv₀ e he
          · exact hv' e he
        · have h₁ : inputsBefore tr (t + 1) v = inputsBefore tr t v := by
            rw [inputsBefore_succ hj, if_neg hw, List.append_nil]
          have := ih t (by omega) v hv
          unfold stateBefore at this ⊢
          rw [h₁]
          exact this
  exact key t

end Node

end LeanDag
