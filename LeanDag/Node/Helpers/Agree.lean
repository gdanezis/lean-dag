import LeanDag.Node.Boot.Statement
import LeanDag.Node.Helpers.Boot
import LeanDag.Node.Helpers.Converge
/-!
# Bootstrapping nodes agree slot by slot

Over a trace, what each honest node knew is what the trace delivered and
offered it, and what it made (`knownOf_sub`). Timely authentication and
the hash over the trace give authentication and the hash at its end
(`authentic_of_timely`, `hashInjective_of_trace`), so the honest nodes'
knowledge forms the run's record. Then, by induction over the
trace, every honest store is a cut of that record and every decision a
verdict on a view of it (`cut_before`): a node bootstraps only at a round
some honest peer offered from its store, which the record reaches, since
that peer's store was a cut of it earlier. Two verdicts on one slot agree.
-/

namespace LeanDag

namespace Node

variable {Validator BlockId Payload : Type} [Fintype Validator] [DecidableEq Validator]
variable [LinearOrder BlockId]

section Lists

theorem run_append (c : Config Validator BlockId Payload) :
    ∀ (s : State Validator BlockId Payload) (l₁ l₂ : List (Input Validator BlockId Payload)),
    run c s (l₁ ++ l₂) =
      ((run c (run c s l₁).1 l₂).1, (run c s l₁).2 ++ (run c (run c s l₁).1 l₂).2)
  | s, [], l₂ => by simp [run]
  | s, i :: l₁, l₂ => by
    simp only [List.cons_append, run]
    rw [run_append c _ l₁ l₂, List.append_assoc]

end Lists

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

/-! ## The served base -/

omit [Fintype Validator] in
theorem serveBase_not_mem_advance (s : State Validator BlockId Payload) {p : Validator} {G : ℕ}
    {bs : List (BlockId × Block Validator BlockId Payload)} :
    Output.serveBase p G bs ∉ (advance cfg s).2 := by
  obtain ⟨b, hb⟩ := progress_built (cfg := cfg) (s.store.topRound + 2) s
  simp only [Node.advance]
  generalize hr : progress cfg (s.store.topRound + 2) s = r at hb
  intro h
  simp only [List.mem_append] at h
  rcases h with (h | h) | h
  · rw [hb] at h
    simp [built] at h
  · unfold Node.decideStep at h
    dsimp only at h
    split at h <;> simp at h
  · unfold Node.collect at h
    split at h
    · dsimp only at h; split at h <;> simp at h
    · simp at h

omit [Fintype Validator] in
theorem serveBase_not_mem_settle (s : State Validator BlockId Payload) {p : Validator} {G : ℕ}
    {bs : List (BlockId × Block Validator BlockId Payload)} :
    Output.serveBase p G bs ∉ (Node.settle cfg s).2 := by
  rcases settle_cases (cfg := cfg) s with h | ⟨s₁, -, h⟩ <;> rw [h]
  · exact serveBase_not_mem_advance s
  · exact serveBase_not_mem_advance s₁

/-- **A served base is the server's store** at the step that served it. -/
theorem serveBase_mem {s : State Validator BlockId Payload} {inp : Input Validator BlockId Payload}
    {p : Validator} {G : ℕ} {bs : List (BlockId × Block Validator BlockId Payload)}
    (h : Output.serveBase p G bs ∈ (step cfg s inp).2) : bs = s.store.window := by
  cases inp with
  | baseRequest peer =>
    change Output.serveBase p G bs ∈ [Output.serveBase peer s.store.base s.store.window] at h
    simp at h; exact h.2.2
  | start =>
    simp only [Node.step] at h
    split at h
    · split at h
      · simp only [List.mem_append] at h
        rcases h with h | h
        · simp [built] at h
        · exact absurd h (serveBase_not_mem_settle _)
      · simp at h
    · simp at h
  | deliver id b =>
    simp only [Node.step] at h
    split at h
    · simp only [List.mem_append] at h
      rcases h with h | h
      · split at h <;> simp at h
      · exact absurd h (serveBase_not_mem_settle _)
    · simp at h
  | timer r => exact absurd h (serveBase_not_mem_settle _)
  | fetchRequest peer ids =>
    change Output.serveBase p G bs ∈ answer s peer ids at h
    unfold answer at h; simp at h
  | restart =>
    simp only [Node.step, List.mem_cons] at h
    rcases h with h | h
    · cases h
    · exact absurd h (serveBase_not_mem_settle _)
  | baseOffer q G' bs' =>
    rw [step_offer] at h
    split at h
    · split at h
      · exact absurd h (serveBase_not_mem_advance _)
      · simp at h
    · simp at h

/-- **The offers a node holds were given to it before.** -/
theorem offers_before (v : Validator) : ∀ (t : ℕ), ∀ o ∈ (stateBefore cfg tr t v).offers,
    ∃ j < t, tr[j]? = some (v, .baseOffer o.1 o.2.1 o.2.2)
  | 0, o, ho => by simp [stateBefore, inputsBefore, run, State.init] at ho
  | t + 1, o, ho => by
    rcases hj : tr[t]? with _ | ⟨w, inp⟩
    · have hL : tr.length ≤ t := List.getElem?_eq_none_iff.mp hj
      rw [Converge.stateBefore_of_le (by omega), ← Converge.stateBefore_of_le hL] at ho
      obtain ⟨j, hj', h⟩ := offers_before v t o ho
      exact ⟨j, by omega, h⟩
    · rw [stateBefore_succ hj] at ho
      split at ho
      · rename_i hw
        subst hw
        rcases step_offers _ inp o ho with ho | rfl
        · obtain ⟨j, hj', h⟩ := offers_before w t o ho
          exact ⟨j, by omega, h⟩
        · exact ⟨t, by omega, hj⟩
      · obtain ⟨j, hj', h⟩ := offers_before v t o ho
        exact ⟨j, by omega, h⟩

omit [LinearOrder BlockId] in
/-- **`f + 1` distinct validators include an honest one**, with at most `f`
outside `H`. -/
theorem exists_mem_of_length {f : ℕ} (hf : Hᶜ.card ≤ f) {l : List Validator} (hl : l.Nodup)
    (hlen : f + 1 ≤ l.length) : ∃ p ∈ l, p ∈ H := by
  obtain ⟨p, hp, hpH⟩ := exists_mem_of_card hf (S := l.toFinset)
    (by rw [List.toFinset_card_of_nodup hl]; exact hlen)
  exact ⟨p, List.mem_toFinset.mp hp, hpH⟩

/-! ## The record's assumptions -/

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

end Node

end LeanDag
