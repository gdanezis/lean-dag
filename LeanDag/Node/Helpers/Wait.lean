import LeanDag.Node.Helpers.Trace
import LeanDag.Node.Helpers.Commits
import LeanDag.Node.Helpers.SyncSteps
/-!
# The build rule's three exits

`docs/validator.md` §5.3. A block the node builds above
round `r` passes the reach and certificate tests on the memory, or was
built after the round's timer fired or on being behind, on `refsFor`'s
references (`tryBuild_exit`). Those reference every block of the round below that is
the only one of its author the memory holds, and the node's own block
(`mem_refsFor`).

Along a trace, each round whose timer node `v` counts as fired had its
timer input at an earlier event (`fired_before`), and `v`'s own block at
its top is on its disk (`ownTop_before`). Each block a step persists is the
genesis block or comes from one build, at a state whose disk is a cut of
the record (`BuildState`, `step_witness`). Each timer a step sets is at
or below the node's top, and one of its top round above `0` is set for
its timeout once the disk holds a quorum of the round (`TimersSet`,
`timersSet_step`).
On a cut, the reach test reads as reaching the record's leader blocks
(`reaches_of_reachReady`), the certificate test as certifying them
(`isCert_of_certReady`), and `refsFor` references each honest block
of the store at its round (`mem_refsFor_of_cut`).
-/

namespace LeanDag

namespace Node

variable {Validator BlockId Payload : Type} [Fintype Validator] [DecidableEq Validator]
variable [LinearOrder BlockId]
variable {cfg : Config Validator BlockId Payload}

omit [Fintype Validator] in
/-- `refsAt`'s references pass the tests, or are `refsFor`'s, or `refsFor`'s
cannot be built on. -/
theorem refsAt_cases (st : Store Validator BlockId Payload) (r : ℕ) (o : Option BlockId)
    (E : Finset (Validator × BlockId × BlockId)) :
    (reachReady cfg st (refsAt cfg st r o E) r
      (excluded cfg st r E) && certReady cfg st (refsAt cfg st r o E) r (excluded cfg st r E)) =
        true ∨
      refsAt cfg st r o E = refsFor cfg st r o E ∨
      buildable cfg st r (refsFor cfg st r o E) E = false := by
  unfold refsAt
  dsimp only
  split
  · rename_i h
    simp only [Bool.and_eq_true] at h
    exact Or.inl (by simp [h.1.1, h.1.2])
  · split
    · rename_i R hR
      have := List.find?_some hR
      simp only [Bool.and_eq_true] at this
      exact Or.inl (by simp [this.1.1, this.1.2])
    · split
      · exact Or.inr (Or.inl rfl)
      · rename_i h
        exact Or.inr (Or.inr (by simpa using h))

omit [Fintype Validator] in
/-- **The build rule's three exits**: a block built above round `r` passes
the reach and certificate tests in memory, or the round's timer fired, or
the node is behind round `r + 1`, and then its references are `refsFor`'s
or `refsFor`'s cannot be built on. -/
theorem tryBuild_exit {s s' : State Validator BlockId Payload}
    {out : List (Output Validator BlockId Payload)} (h : tryBuild cfg s = some (s', out)) :
    ∃ r o, s.top.isSome ∧ s.top.getD 0 ≤ r ∧
      ((s.top = some r ∧ o = s.own) ∨ (s.recovering = true ∧ o = none ∧
        reachReady cfg s.memory (refsAt cfg s.memory r o s.evidence) r
          (excluded cfg s.memory r s.evidence) = true ∧
        certReady cfg s.memory (refsAt cfg s.memory r o s.evidence) r
          (excluded cfg s.memory r s.evidence) = true)) ∧
      cfg.q ≤ (authorsIn s.disk.toRecord s.disk.ids r).card ∧
      ((reachReady cfg s.memory (refsAt cfg s.memory r o s.evidence) r
        (excluded cfg s.memory r s.evidence) = true ∧
          certReady cfg s.memory (refsAt cfg s.memory r o s.evidence) r
            (excluded cfg s.memory r s.evidence) = true) ∨
        ((s.top = some r ∧ r ∈ s.fired ∨ behind cfg s.memory r) ∧
          (refsAt cfg s.memory r o s.evidence = refsFor cfg s.memory r o s.evidence ∨
            buildable cfg s.memory r (refsFor cfg s.memory r o s.evidence) s.evidence = false))) ∧
      out = built cfg [(cfg.idOf (blockOn cfg s.memory r (refsAt cfg s.memory r o s.evidence)
          s.evidence), blockOn cfg s.memory r (refsAt cfg s.memory r o s.evidence) s.evidence)] :=
              by
  obtain ⟨t, r, o, ht, hb, hro⟩ := tryBuild_cases h
  have hshape : s.top.isSome ∧ s.top.getD 0 ≤ r ∧
      ((s.top = some r ∧ o = s.own) ∨ (s.recovering = true ∧ o = none ∧
        reachReady cfg s.memory (refsAt cfg s.memory r o s.evidence) r
          (excluded cfg s.memory r s.evidence) = true ∧
        certReady cfg s.memory (refsAt cfg s.memory r o s.evidence) r
          (excluded cfg s.memory r s.evidence) = true)) := by
    rw [ht]
    rcases hro with ⟨rfl, rfl⟩ | ⟨hrec, hlt, rfl, -, -, ht₁, ht₂⟩
    · exact ⟨rfl, le_rfl, Or.inl ⟨rfl, rfl⟩⟩
    · exact ⟨rfl, hlt.le, Or.inr ⟨hrec, rfl, ht₁, ht₂⟩⟩
  unfold buildAbove at hb
  dsimp only at hb
  split at hb
  · rename_i hc
    split at hb
    · rw [Option.some.injEq, Prod.mk.injEq] at hb
      refine ⟨r, o, hshape.1, hshape.2.1, hshape.2.2, by
        rw [← Store.authorsAt_eq]
        exact hc.1.trans (Finset.card_le_card (s.mirrors.authorsAt_sub r)), ?_,
        by rw [← hb.2]; simp [built, blockOn]⟩
      have hcases := refsAt_cases (cfg := cfg) s.memory r o s.evidence
      rcases hc.2 with hf | hbeh | hready
      · rcases hcases with h' | h'
        · simp only [Bool.and_eq_true] at h'
          exact Or.inl h'
        · rcases hro with ⟨rfl, -⟩ | ⟨-, -, rfl, -, -, ht₁, ht₂⟩
          · exact Or.inr ⟨Or.inl ⟨ht, hf⟩, h'⟩
          · exact Or.inl ⟨ht₁, ht₂⟩
      · rcases hcases with h' | h'
        · simp only [Bool.and_eq_true] at h'
          exact Or.inl h'
        · exact Or.inr ⟨Or.inr hbeh, h'⟩
      · exact Or.inl hready
    · exact absurd hb (by simp)
  · exact absurd hb (by simp)

omit [Fintype Validator] in
/-- **What `refsFor` references**: a round-`r` block the store holds that
is its author's only one there, if the author is neither left out nor
the node, or the node's own block `o` there, if the node is not left out. -/
theorem mem_refsFor {st : Store Validator BlockId Payload} {r : ℕ} {o : Option BlockId}
    {E : Finset (Validator × BlockId × BlockId)}
    {j : BlockId} (hj : j ∈ st.ids) (hr : (st.blk j).round = r)
    (huniq : ∀ i ∈ st.ids, (st.blk i).round = r → (st.blk i).creator = (st.blk j).creator →
      i = j)
    (hown : (st.blk j).creator = cfg.me → o = some j)
    (hex : (st.blk j).creator ∉ excluded cfg st r E) :
    j ∈ refsFor cfg st r o E := by
  unfold refsFor
  dsimp only
  rw [Store.atRound_eq]
  have hjR : j ∈ blocksAt st.toRecord r := Finset.mem_filter.mpr ⟨hj, hr⟩
  refine Finset.mem_biUnion.mpr ⟨(st.blk j).creator,
    Finset.mem_sdiff.mpr ⟨Finset.mem_image_of_mem _ hjR, hex⟩, ?_⟩
  split
  · rename_i h
    rw [hown h.1]
    exact Option.mem_toFinset.mpr rfl
  · have hset : ((blocksAt st.toRecord r).filter
        fun i => (st.blk i).creator = (st.blk j).creator) = {j} := by
      ext i
      simp only [Finset.mem_filter, Finset.mem_singleton]
      constructor
      · rintro ⟨hi, hc⟩
        exact huniq i (Finset.mem_filter.mp hi).1 (Finset.mem_filter.mp hi).2 hc
      · rintro rfl
        exact ⟨hjR, rfl⟩
    rw [hset]
    simp [Scheme.leastOf]

/-- **A change that fires no timer.** -/
def Calm (s s' : State Validator BlockId Payload) : Prop :=
  s'.fired ⊆ s.fired

omit [Fintype Validator] [DecidableEq Validator] in
theorem Calm.refl (s : State Validator BlockId Payload) : Calm s s := subset_rfl

omit [Fintype Validator] [DecidableEq Validator] in
theorem Calm.trans {a b c : State Validator BlockId Payload} (h₁ : Calm a b) (h₂ : Calm b c) :
    Calm a c := Finset.Subset.trans h₂ h₁

omit [Fintype Validator] in
theorem calm_tryBuild {s s' : State Validator BlockId Payload}
    {out : List (Output Validator BlockId Payload)} (h : tryBuild cfg s = some (s', out)) :
    Calm s s' := by
  obtain ⟨_, _, _, -, h, -⟩ := tryBuild_cases h
  unfold buildAbove at h
  dsimp only at h
  split at h
  · split at h
    · rw [Option.some.injEq, Prod.mk.injEq] at h
      rw [← h.1]; intro r hr; rwa [release_fired] at hr
    · exact absurd h (by simp)
  · exact absurd h (by simp)

omit [Fintype Validator] in
theorem calm_progress : ∀ (fuel : ℕ) (s : State Validator BlockId Payload),
    Calm s (Node.progress cfg fuel s).1
  | 0, s => Calm.refl s
  | fuel + 1, s => by
    unfold Node.progress
    split
    · rename_i s₁ out h
      exact Calm.trans (calm_tryBuild h) (calm_progress fuel s₁)
    · exact Calm.refl s

omit [Fintype Validator] in
theorem calm_decideStep (s : State Validator BlockId Payload) :
    Calm s (Node.decideStep cfg s).1 := by
  unfold Node.decideStep
  dsimp only
  split
  · intro r hr; rwa [release_fired] at hr
  · exact Calm.refl _

omit [Fintype Validator] in
theorem calm_advance (s : State Validator BlockId Payload) :
    Calm s (Node.advance cfg s).1 := by
  intro r h
  rw [advance_fired] at h
  simp only [Node.pass, flushSyncs_fired] at h
  exact Calm.trans (calm_progress _ s) (calm_decideStep _) h

omit [Fintype Validator] in
theorem calm_quiesce (n : ℕ) (s : State Validator BlockId Payload) :
    Calm s (quiesce cfg n s).1 :=
  (quiesce_rel (P := fun _ => True) (R := fun a _ b => Calm a b) Calm.refl
    (fun _ _ _ _ _ h₁ h₂ => h₁.trans h₂) (fun s _ => ⟨calm_advance s, trivial⟩) n s trivial).1

/-- **A step fires a round's timer only on that timer's input.** -/
theorem step_calm (s : State Validator BlockId Payload) (inp : Input Validator BlockId Payload) :
    ∀ r ∈ (Node.step cfg s inp).1.fired, r ∈ s.fired ∨ inp = .timer r := by
  cases inp with
  | start =>
    simp only [Node.step]
    split
    · split
      · intro r h
        have := calm_quiesce (cfg := cfg) _ _ h
        exact Or.inl this
      · exact fun r h => Or.inl h
    · exact fun r h => Or.inl h
  | deliver u id b =>
    rcases step_receipt (cfg := cfg) (s := s) (Or.inl ⟨u, id, b, rfl⟩) with
      he | ⟨s₁, pre, hr, -, he⟩
    · rw [he]; exact fun r h => Or.inl h
    · rw [he]; intro r h
      have := calm_quiesce (cfg := cfg) _ _ h
      rw [hr.fired] at this
      exact Or.inl this
  | stream u L =>
    rcases step_receipt (cfg := cfg) (s := s) (Or.inr ⟨u, L, rfl⟩) with he | ⟨s₁, pre, hr, -, he⟩
    · rw [he]; exact fun r h => Or.inl h
    · rw [he]; intro r h
      have := calm_quiesce (cfg := cfg) _ _ h
      rw [hr.fired] at this
      exact Or.inl this
  | timer t =>
    intro r h
    rw [step_timer_fst] at h
    rcases Finset.mem_insert.mp (calm_quiesce (cfg := cfg) _ _ h) with rfl | h
    · exact Or.inr rfl
    · exact Or.inl (Finset.mem_filter.mp h).1
  | syncRequest peer t fr ids => exact fun r h => Or.inl h
  | ask peer r => exact fun r h => Or.inl h
  | restart =>
    intro r h
    rw [step_restart_fst] at h
    exact Or.inl (calm_quiesce (cfg := cfg) _ { s with recovering := true } h)

/-- **Each round whose timer node `v` counts as fired before event `i`**
had its timer input at an earlier event. -/
theorem fired_before {tr : Trace Validator BlockId Payload} {v : Validator} :
    ∀ i, ∀ r ∈ (stateBefore cfg tr i v).fired, ∃ j < i, tr[j]? = some (v, Input.timer r)
  | 0 => fun r hr => by
    simp [stateBefore, inputsBefore, run, State.init] at hr
  | i + 1 => by
    have ih : ∀ r ∈ (stateBefore cfg tr i v).fired, ∃ j < i, tr[j]? = some (v, Input.timer r) :=
      fired_before i
    rcases he : tr[i]? with _ | ⟨w, inp⟩
    · have hlen : tr.length ≤ i := List.getElem?_eq_none_iff.mp he
      have heq : stateBefore cfg tr (i + 1) v = stateBefore cfg tr i v := by
        unfold stateBefore
        rw [inputsBefore_of_le hlen, inputsBefore_of_le (by omega : tr.length ≤ i + 1)]
      rw [heq]
      exact fun r hr => (ih r hr).imp fun j ⟨hj, h⟩ => ⟨by omega, h⟩
    · rw [stateBefore_succ he]
      split
      · rename_i hw
        subst hw
        intro r hr'
        rcases step_calm (cfg := cfg.at w) _ _ r hr' with h | rfl
        · exact (ih r h).imp fun j ⟨hj, h⟩ => ⟨by omega, h⟩
        · exact ⟨i, by omega, he⟩
      · exact fun r hr => (ih r hr).imp fun j ⟨hj, h⟩ => ⟨by omega, h⟩

omit [Fintype Validator] in
/-- **Each block the build loop persists comes from one build**, at a state
that every property kept by the loop's builds holds of. -/
theorem progress_witness (Q : State Validator BlockId Payload → Prop)
    (K : Set (BlockId × Block Validator BlockId Payload))
    (hQ : ∀ x y o, Q x → tryBuild cfg x = some (y, o) → (∀ e ∈ persists o, e ∈ K) → Q y) :
    ∀ (fuel : ℕ) (s : State Validator BlockId Payload), Q s →
      (∀ e ∈ persists (Node.progress cfg fuel s).2, e ∈ K) →
      ∀ e ∈ persists (Node.progress cfg fuel s).2, ∃ x y o, Q x ∧
        tryBuild cfg x = some (y, o) ∧ e ∈ persists o ∧
        Grows x.disk (Node.progress cfg fuel s).1.disk
  | 0, s, _, _, e, he => by simp [Node.progress, persists] at he
  | fuel + 1, s, hs, hK, e, he => by
    rcases hb : tryBuild cfg s with _ | ⟨s₁, out⟩
    · simp [Node.progress, hb, persists] at he
    · simp only [Node.progress, hb] at he hK ⊢
      rw [persists_append] at he hK
      have hK₁ : ∀ e ∈ persists out, e ∈ K := fun e he => hK e (List.mem_append_left _ he)
      rcases List.mem_append.mp he with he | he
      · obtain ⟨r, id, b, hnew, hrefs, hpred, -, -, -, -, -, hst, -⟩ := tryBuild_some hb
        have hg₁ : Grows s.disk s₁.disk := by rw [hst]; exact Grows.insert s.disk
        exact ⟨s, s₁, out, hs, hb, he, hg₁.trans (Grows.progress (cfg := cfg) fuel s₁).1⟩
      · exact progress_witness Q K hQ fuel s₁ (hQ s s₁ out hs hb hK₁)
          (fun e he => hK e (List.mem_append_right _ he)) e he

variable (cfg) in
/-- **The node's own block at its top is on its disk**, as `own`. -/
def OwnTop (s : State Validator BlockId Payload) : Prop :=
  ∀ r, s.top = some r → ∃ j, s.own = some j ∧ j ∈ s.disk.ids ∧ (s.disk.blk j).round = r ∧
    (s.disk.blk j).creator = cfg.me

omit [Fintype Validator] in
theorem OwnTop.grow {s s' : State Validator BlockId Payload} (h : OwnTop cfg s)
    (hg : Grows s.disk s'.disk) (ht : s'.top = s.top) (ho : s'.own = s.own) :
    OwnTop cfg s' := by
  intro r hr
  obtain ⟨j, hj, hji, hjr, hjc⟩ := h r (ht ▸ hr)
  exact ⟨j, ho ▸ hj, hg.1 hji, by rw [hg.blk hji, hjr], by rw [hg.blk hji, hjc]⟩

omit [Fintype Validator] in
theorem OwnTop.tryBuild {s s' : State Validator BlockId Payload}
    {out : List (Output Validator BlockId Payload)} (h : tryBuild cfg s = some (s', out)) :
    OwnTop cfg s' := by
  obtain ⟨_, _, _, -, h, -⟩ := tryBuild_cases h
  unfold buildAbove at h
  dsimp only at h
  split at h
  · split at h
    · rw [Option.some.injEq, Prod.mk.injEq] at h
      rw [← h.1]
      intro r hr
      simp only [release_top, release_own, release_disk] at hr ⊢
      simp only [Option.some.injEq] at hr
      subst hr
      refine ⟨_, rfl, (by simp [Store.insert_ids]), ?_, ?_⟩ <;>
        simp [Store.blk, Store.insert, Std.TreeMap.getD_insert_self, blockOn]
    · exact absurd h (by simp)
  · exact absurd h (by simp)

omit [Fintype Validator] in
theorem OwnTop.progress : ∀ (fuel : ℕ) {s : State Validator BlockId Payload}, OwnTop cfg s →
    OwnTop cfg (Node.progress cfg fuel s).1
  | 0, _, h => h
  | fuel + 1, s, h => by
    unfold Node.progress
    split
    · rename_i s₁ out hb
      exact OwnTop.progress fuel (OwnTop.tryBuild hb)
    · exact h

omit [Fintype Validator] in
theorem OwnTop.advance {s : State Validator BlockId Payload} (h : OwnTop cfg s) :
    OwnTop cfg (Node.advance cfg s).1 := by
  have hp : OwnTop cfg (Node.pass cfg s).1 := by
    simp only [Node.pass]
    have h₁ := OwnTop.progress (s.disk.topRound + 2) h
    generalize Node.progress cfg (s.disk.topRound + 2) s = r at h₁
    have h₂ : OwnTop cfg (Node.decideStep cfg r.1).1 := by
      have hown : (Node.decideStep cfg r.1).1.own = r.1.own := by
        unfold Node.decideStep; dsimp only; split <;> simp only [release_own]
      exact h₁.grow (by rw [decideStep_disk]; exact Grows.refl _) (decideStep_top _) hown
    exact h₂.grow (by exact Grows.flushSyncs _ _) (flushSyncs_top _ _) (flushSyncs_own _ _)
  exact hp.grow (by rw [advance_disk]; exact Grows.refl _) (advance_top s) (advance_own s)

omit [Fintype Validator] in
theorem OwnTop.settle {s : State Validator BlockId Payload} (h : OwnTop cfg s) :
    OwnTop cfg (Node.settle cfg s).1 :=
  quiesce_ind (fun _ h => h.advance) _ _ h

/-- **A step keeps the node's own block at its top on its disk.** -/
theorem OwnTop.step {s : State Validator BlockId Payload} (h : OwnTop cfg s)
    (inp : Input Validator BlockId Payload) : OwnTop cfg (Node.step cfg s inp).1 := by
  cases inp with
  | start =>
    simp only [Node.step]
    split
    · split
      · refine OwnTop.settle (fun r hr => ?_)
        change some 0 = some r at hr
        rw [Option.some.injEq] at hr
        subst hr
        refine ⟨_, rfl, (by simp [Store.insert_ids]), ?_, ?_⟩ <;>
          simp [Store.blk, Store.insert, Std.TreeMap.getD_insert_self, Config.genesis]
      · exact h
    · exact h
  | deliver u id b =>
    rcases step_receipt (cfg := cfg) (s := s) (Or.inl ⟨u, id, b, rfl⟩) with
      he | ⟨s₁, pre, hr, -, he⟩
    · rw [he]; exact h
    · rw [he]; exact OwnTop.settle (h.grow hr.grows hr.top hr.own)
  | stream u L =>
    rcases step_receipt (cfg := cfg) (s := s) (Or.inr ⟨u, L, rfl⟩) with he | ⟨s₁, pre, hr, -, he⟩
    · rw [he]; exact h
    · rw [he]; exact OwnTop.settle (h.grow hr.grows hr.top hr.own)
  | timer t => rw [step_timer_fst]; exact OwnTop.settle (h.grow (Grows.refl _) rfl rfl)
  | syncRequest peer t fr ids => exact h
  | ask peer r => exact h
  | restart =>
    rw [step_restart_fst]
    exact OwnTop.settle (h.grow (s' := { s with recovering := true }) (Grows.refl _) rfl rfl)

/-- **Node `v`'s own block at its top is on its disk before every event.** -/
theorem ownTop_before {tr : Trace Validator BlockId Payload} {v : Validator} :
    ∀ i, OwnTop (cfg.at v) (stateBefore cfg tr i v)
  | 0 => fun r hr => by simp [stateBefore, inputsBefore, run, State.init] at hr
  | i + 1 => by
    have ih : OwnTop (cfg.at v) (stateBefore cfg tr i v) := ownTop_before i
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
        exact ih.step inp
      · exact ih

variable {P : Validity Validator BlockId Payload} {H : Finset Validator}

variable (cfg) in
/-- **A state the node builds from during a step at `s` on `inp`**: its
disk a cut of `U` grown from `s`'s, its top held and its own block at
its top on the disk, each round it counts as fired fired before or by `inp`,
and its blocks known in `K` and valid. -/
structure BuildState (U : BlockRecord Validator BlockId Payload P H)
    (K : Set (BlockId × Block Validator BlockId Payload))
    (s : State Validator BlockId Payload) (inp : Input Validator BlockId Payload)
    (x : State Validator BlockId Payload) : Prop where
  cut : IsCut U x.disk
  held : Held cfg x
  own : OwnTop cfg x
  grows : Grows s.disk x.disk
  fired : ∀ r ∈ x.fired, r ∈ s.fired ∨ inp = .timer r
  inv : ∃ B, Inv cfg x K B
  ev : EvidenceOn cfg x
  det : s.detected ⊆ x.detected

omit [Fintype Validator] in
theorem BuildState.tryBuild {U : BlockRecord Validator BlockId Payload P H}
    {K : Set (BlockId × Block Validator BlockId Payload)} (hg : Ground U K cfg.q)
    {s x y : State Validator BlockId Payload} {inp : Input Validator BlockId Payload}
    {o : List (Output Validator BlockId Payload)} (h : BuildState cfg U K s inp x)
    (hb : Node.tryBuild cfg x = some (y, o)) (hK : ∀ e ∈ persists o, e ∈ K) :
    BuildState cfg U K s inp y := by
  obtain ⟨_, _, _, _, _, _, -, -, -, -, -, hst, -⟩ := tryBuild_some hb
  refine ⟨h.cut.tryBuild hg hb hK, h.held.tryBuild hb, OwnTop.tryBuild hb,
    h.grows.trans (hst ▸ Grows.insert x.disk),
    fun r hr => h.fired r (calm_tryBuild hb hr), ?_,
    h.ev.grow (hst ▸ Grows.insert x.disk) (tryBuild_detected hb).1 (tryBuild_detected hb).2,
    h.det.trans (tryBuild_detected hb).1.symm.subset⟩
  obtain ⟨B, hi⟩ := h.inv
  obtain ⟨e, he, hi'⟩ := hi.tryBuild hb
  refine ⟨_, hi'.mono fun z hz => ?_⟩
  rcases hz with hz | hz
  · exact hz
  · rw [Set.mem_singleton_iff] at hz
    exact hK z (by rw [he, persists_built, hz]; exact List.mem_singleton_self _)

omit [Fintype Validator] in
/-- **A state the node builds from leaves out no honest author**, when the
evidence it knew names none. -/
theorem BuildState.not_excluded {U : BlockRecord Validator BlockId Payload P H}
    {K : Set (BlockId × Block Validator BlockId Payload)}
    {s x : State Validator BlockId Payload} {inp : Input Validator BlockId Payload}
    (h : BuildState cfg U K s inp x)
    (hK : ∀ y ∈ K, ∀ e ∈ cfg.xp.ev y.2.payload, e.2.1 ≠ e.2.2 → e.1 ∉ H)
    {a : Validator} (ha : a ∈ H) (r : ℕ) : a ∉ excluded cfg x.disk r x.evidence := by
  obtain ⟨B, hi⟩ := h.inv
  intro hm
  rcases Finset.mem_union.mp hm with hm | hm
  · obtain ⟨e, he, rfl⟩ := Finset.mem_image.mp hm
    obtain ⟨he, hne⟩ := Finset.mem_filter.mp he
    rcases (h.ev.2 e he).2 with ⟨h₁, h₂, h₃, h₄, h₅⟩ | ⟨i, hi', hie⟩
    · exact hne (U.no_equivocation _ (h.cut _ h₁).1 _ (h.cut _ h₂).1
        (by rw [h.cut.creator h₁, h₃]; exact ha)
        (by rw [h.cut.creator h₁, h.cut.creator h₂, h₃, h₄])
        (by rw [h.cut.round h₁, h.cut.round h₂, h₅]))
    · exact hK _ (hi.known i hi') e hie hne ha
  · obtain ⟨i, hiR, ham⟩ := Finset.mem_biUnion.mp hm
    exact ex_not_named hi.valid (fun j hj e he hne => hK _ (hi.known j hj) e he hne) i
      (Store.mem_atRound.mp hiR).1 _ ham ha

/-- **A state the node builds from leaves out only authors of `D`**, when
`D` holds every author that evidence in a known block names and every
author with two known blocks of a round. -/
theorem BuildState.excluded_sub {U : BlockRecord Validator BlockId Payload P H}
    {K : Set (BlockId × Block Validator BlockId Payload)}
    {s x : State Validator BlockId Payload} {inp : Input Validator BlockId Payload}
    (h : BuildState cfg U K s inp x) {D : Finset Validator}
    (hev : ∀ y ∈ K, ∀ e ∈ cfg.xp.ev y.2.payload, e.2.1 ≠ e.2.2 → e.1 ∈ D)
    (htw : ∀ y ∈ K, ∀ z ∈ K, y.1 ≠ z.1 → y.2.creator = z.2.creator →
      y.2.round = z.2.round → y.2.creator ∈ D)
    (r : ℕ) : excluded cfg x.disk r x.evidence ⊆ D := by
  obtain ⟨B, hi⟩ := h.inv
  intro a hm
  rcases Finset.mem_union.mp hm with hm | hm
  · obtain ⟨e, he, rfl⟩ := Finset.mem_image.mp hm
    obtain ⟨he, hne⟩ := Finset.mem_filter.mp he
    rcases (h.ev.2 e he).2 with ⟨h₁, h₂, h₃, h₄, h₅⟩ | ⟨i, hi', hie⟩
    · have := htw _ (hi.known _ h₁) _ (hi.known _ h₂) hne (by simp only; rw [h₃, h₄]) h₅
      simp only at this
      rwa [h₃] at this
    · exact hev _ (hi.known i hi') e hie hne
  · obtain ⟨i, hiR, ham⟩ := Finset.mem_biUnion.mp hm
    by_contra hD
    exact ex_not_named (A := Dᶜ) hi.valid
      (fun j hj e he hne hc => Finset.mem_compl.mp hc (hev _ (hi.known j hj) e he hne)) i
      (Store.mem_atRound.mp hiR).1 _ ham (Finset.mem_compl.mpr hD)

omit [Fintype Validator] in
/-- **A pass keeps a state the node builds from.** -/
theorem BuildState.advance {U : BlockRecord Validator BlockId Payload P H}
    {K : Set (BlockId × Block Validator BlockId Payload)} (hg : Ground U K cfg.q)
    {s x : State Validator BlockId Payload} {inp : Input Validator BlockId Payload}
    (h : BuildState cfg U K s inp x) (hp : ∀ e ∈ x.syncs, e.2.1 ∈ K)
    (hK : ∀ e ∈ persists (Node.advance cfg x).2, e ∈ K) :
    BuildState cfg U K s inp (Node.advance cfg x).1 := by
  refine ⟨h.cut.advanceStore hg hp hK, h.held.advance, h.own.advance,
    h.grows.trans (Grows.advance x), fun r hr => h.fired r (calm_advance x hr), ?_,
    (Thins.advance x).twins h.ev, h.det.trans (Thins.advance x).det⟩
  obtain ⟨B, hi⟩ := h.inv
  obtain ⟨bs, ho, hi'⟩ := hi.advance
  exact ⟨_, hi'.mono fun z hz => hz.elim id fun hz => hK z (by rw [ho.1]; exact hz)⟩

omit [Fintype Validator] in
/-- **Each block a pass persists comes from one build**, at a state the
node builds from. -/
theorem advance_witness {U : BlockRecord Validator BlockId Payload P H}
    {K : Set (BlockId × Block Validator BlockId Payload)} (hg : Ground U K cfg.q)
    {s s₀ : State Validator BlockId Payload} {inp : Input Validator BlockId Payload}
    (h₀ : BuildState cfg U K s inp s₀) (hK : ∀ e ∈ persists (Node.advance cfg s₀).2, e ∈ K) :
    ∀ e ∈ persists (Node.advance cfg s₀).2, ∃ x y o, BuildState cfg U K s inp x ∧
      Node.tryBuild cfg x = some (y, o) ∧ e ∈ persists o ∧
      Grows x.disk (Node.advance cfg s₀).1.disk := by
  have hpe : persists (Node.advance cfg s₀).2 =
      persists (Node.progress cfg (s₀.disk.topRound + 2) s₀).2 := by
    rw [advance_snd, persists_append, persists_arm, List.append_nil]
    simp only [Node.pass]
    rw [persists_append, decideStep_persist, List.append_nil]
  have hga : Grows (Node.progress cfg (s₀.disk.topRound + 2) s₀).1.disk
      (Node.advance cfg s₀).1.disk := by
    rw [advance_disk]
    simp only [Node.pass]
    rw [← decideStep_disk (cfg := cfg) (Node.progress cfg (s₀.disk.topRound + 2) s₀).1]
    exact Grows.flushSyncs _ _
  rw [hpe] at hK
  intro e he
  rw [hpe] at he
  obtain ⟨x, y, o, hx, hb, heo, hg'⟩ := progress_witness (BuildState cfg U K s inp) K
    (fun _ _ _ hx hb hK => hx.tryBuild hg hb hK) _ s₀ h₀ hK e he
  exact ⟨x, y, o, hx, hb, heo, hg'.trans hga⟩

omit [Fintype Validator] in
theorem quiesce_witness {U : BlockRecord Validator BlockId Payload P H}
    {K : Set (BlockId × Block Validator BlockId Payload)} (hg : Ground U K cfg.q)
    {s : State Validator BlockId Payload} {inp : Input Validator BlockId Payload} :
    ∀ (n : ℕ) (s₀ : State Validator BlockId Payload), BuildState cfg U K s inp s₀ →
    (∀ e ∈ s₀.syncs, e.2.1 ∈ K) → (∀ e ∈ persists (quiesce cfg n s₀).2, e ∈ K) →
    ∀ e ∈ persists (quiesce cfg n s₀).2, ∃ x y o, BuildState cfg U K s inp x ∧
      Node.tryBuild cfg x = some (y, o) ∧ e ∈ persists o ∧
      Grows x.disk (quiesce cfg n s₀).1.disk
  | 0, s₀, _, _, _ => by intro e he; simp [Node.quiesce, persists] at he
  | n + 1, s₀, h₀, hp, hK => by
    rcases quiesce_succ_cases (cfg := cfg) n s₀ with he | he <;> rw [he] at hK ⊢
    · exact advance_witness hg h₀ hK
    · rw [persists_append] at hK
      intro e he'
      rw [persists_append] at he'
      rcases List.mem_append.mp he' with he' | he'
      · obtain ⟨x, y, o, hx, hb, heo, hg'⟩ :=
          advance_witness hg h₀ (fun e he => hK e (List.mem_append_left _ he)) e he'
        exact ⟨x, y, o, hx, hb, heo, hg'.trans (Grows.quiesce (cfg := cfg) n _)⟩
      · exact quiesce_witness hg n _
          (h₀.advance hg hp (fun e he => hK e (List.mem_append_left _ he)))
          (fun e he => hp e (advance_sub (cfg := cfg) s₀ e he))
          (fun e he => hK e (List.mem_append_right _ he)) e he'

omit [Fintype Validator] in
/-- **Each block a settle persists comes from one build**, at a state the
node builds from. -/
theorem settle_witness {U : BlockRecord Validator BlockId Payload P H}
    {K : Set (BlockId × Block Validator BlockId Payload)} (hg : Ground U K cfg.q)
    {s s₀ : State Validator BlockId Payload} {inp : Input Validator BlockId Payload}
    (h₀ : BuildState cfg U K s inp s₀) (hp : ∀ e ∈ s₀.syncs, e.2.1 ∈ K)
    (hK : ∀ e ∈ persists (Node.settle cfg s₀).2, e ∈ K) :
    ∀ e ∈ persists (Node.settle cfg s₀).2, ∃ x y o, BuildState cfg U K s inp x ∧
      Node.tryBuild cfg x = some (y, o) ∧ e ∈ persists o ∧
      Grows x.disk (Node.settle cfg s₀).1.disk :=
  quiesce_witness hg _ s₀ h₀ hp hK

/-- **Each block a step persists is the genesis block or comes from one
build**, at a state the node builds from. -/
theorem step_witness {U : BlockRecord Validator BlockId Payload P H}
    {K : Set (BlockId × Block Validator BlockId Payload)} (hg : Ground U K cfg.q)
    {s : State Validator BlockId Payload} {inp : Input Validator BlockId Payload}
    {B₀ : List (BlockId × Block Validator BlockId Payload)} (hi : Inv cfg s K B₀)
    (hc : IsCut U s.disk) (hh : Held cfg s) (hown : OwnTop cfg s) (hev : EvidenceOn cfg s)
    (hp : ∀ e ∈ s.syncs, e.2.1 ∈ K) (hd : ∀ e ∈ delivered cfg [inp], e ∈ K)
    (hb : ∀ e ∈ persists (Node.step cfg s inp).2, e ∈ K) :
    ∀ e ∈ persists (Node.step cfg s inp).2, e.2.round = 0 ∨ ∃ x y o,
      BuildState cfg U K s inp x ∧ Node.tryBuild cfg x = some (y, o) ∧ e ∈ persists o ∧
      Grows x.disk (Node.step cfg s inp).1.disk := by
  -- a step that settles `s₀` after outputs persisting only round-`0` blocks
  have hset : ∀ (s₀ : State Validator BlockId Payload)
      (pre : List (Output Validator BlockId Payload)),
      BuildState cfg U K s inp s₀ → (∀ e ∈ s₀.syncs, e.2.1 ∈ K) →
      (∀ e ∈ persists pre, e.2.round = 0) →
      Node.step cfg s inp = ((Node.settle cfg s₀).1, pre ++ (Node.settle cfg s₀).2) →
      ∀ e ∈ persists (Node.step cfg s inp).2, e.2.round = 0 ∨ ∃ x y o,
        BuildState cfg U K s inp x ∧ Node.tryBuild cfg x = some (y, o) ∧ e ∈ persists o ∧
        Grows x.disk (Node.step cfg s inp).1.disk := by
    intro s₀ pre h₀ hp₀ hpre he e hev
    rw [he] at hb hev ⊢
    rw [persists_append] at hb hev
    rcases List.mem_append.mp hev with hev | hev
    · exact Or.inl (hpre e hev)
    · exact Or.inr (settle_witness hg h₀ hp₀ (fun e he => hb e (List.mem_append_right _ he))
        e hev)
  have hsame : Node.step cfg s inp = (s, []) →
      ∀ e ∈ persists (Node.step cfg s inp).2, e.2.round = 0 ∨ ∃ x y o,
        BuildState cfg U K s inp x ∧ Node.tryBuild cfg x = some (y, o) ∧ e ∈ persists o ∧
        Grows x.disk (Node.step cfg s inp).1.disk := by
    intro he e hev; rw [he] at hev; simp [persists] at hev
  cases inp with
  | start =>
    by_cases h₁ : s.top = none ∧ cfg.Admissible
    · by_cases h₂ : cfg.idOf cfg.genesis ∉ s.disk.ids ∧
          rowValid cfg.q cfg.xp (Function.update s.disk.blk (cfg.idOf cfg.genesis) cfg.genesis)
            cfg.genesis
      · let st := s.disk.insert (cfg.idOf cfg.genesis) cfg.genesis h₂.1
          (fun _ hj => absurd hj (Finset.notMem_empty _))
          (fun j hj => absurd hj (Finset.notMem_empty j))
        have hx : (cfg.idOf cfg.genesis, cfg.genesis) ∈ K :=
          hb _ (by simp only [Node.step, dif_pos h₂, if_pos h₁]; simp [persists])
        have hrefs : cfg.genesis.refs ⊆ s.disk.ids := fun _ hj => absurd hj (Finset.notMem_empty _)
        have hcst : IsCut U st := hc.insert (hg.real _ hx
          (fun _ hj => absurd hj (Finset.notMem_empty _))
          (validAt_of_cut hc h₂.1 hrefs h₂.2))
        let gid := cfg.idOf cfg.genesis
        let s₀ : State Validator BlockId Payload :=
          { keep s (cfg.idOf cfg.genesis) cfg.genesis h₂.1
              (fun _ hj => absurd hj (Finset.notMem_empty _))
              (fun j hj => absurd hj (Finset.notMem_empty j)) with
              top := some 0, own := some gid, recovering := false }
        have hh₀ : Held cfg s₀ :=
          ⟨fun t ht => ⟨gid, (by simp [s₀, st, gid, Store.insert_ids]), by
            change some 0 = some t at ht
            simp only [Option.some.injEq] at ht
            omega⟩, hh.junk⟩
        have ho₀ : OwnTop cfg s₀ := by
          intro r hr
          change some 0 = some r at hr
          rw [Option.some.injEq] at hr
          subst hr
          refine ⟨gid, rfl, (by simp [s₀, st, gid, Store.insert_ids]), ?_, ?_⟩
          · change (st.blk gid).round = 0
            simp [st, gid, Store.blk, Store.insert, Std.TreeMap.getD_insert_self,
              Config.genesis]
          · change (st.blk gid).creator = cfg.me
            simp [st, gid, Store.blk, Store.insert, Std.TreeMap.getD_insert_self,
              Config.genesis]
        have hi₀ : Inv cfg s₀ K [(gid, cfg.genesis)] :=
          ⟨known_insert (hnew := h₂.1) (hrefs := fun _ hj => absurd hj (Finset.notMem_empty _))
              (hpred := fun j hj => absurd hj (Finset.notMem_empty j))
              (fun j hj => hi.known j hj) hx,
            fun x hx => hi.pend x hx,
            Or.inr ⟨0, rfl, ⟨by simp, fun x hx => by
              rw [List.mem_singleton] at hx; subst hx; rfl⟩⟩,
            fun x hx => by
              rw [List.mem_singleton] at hx; subst hx
              refine ⟨rfl, rfl, fun j hj => absurd hj (Finset.notMem_empty j), fun blk _ => ?_⟩
              exact rowValid_congr (fun j hj => absurd hj (Finset.notMem_empty j)) h₂.2,
            fun x hx => by rw [List.mem_singleton] at hx; subst hx; exact hx,
            hi.valid.insert (hnew := h₂.1) (hrefs := fun _ hj => absurd hj (Finset.notMem_empty _))
              (hpred := fun j hj => absurd hj (Finset.notMem_empty j)) h₂.2,
            fun j hj => by
              change some gid = some j at hj
              rw [Option.some.injEq] at hj
              subst hj
              refine ⟨by simp [s₀, st, gid, Store.insert_ids], ?_⟩
              simp [s₀, keep, gid, Store.insert_blk],
            by
              have := hi.floor
              simp only [floorOf, h₁.1, Option.getD_none] at this
              simpa [floorOf, s₀, keep] using this⟩
        refine hset s₀ (built cfg [(cfg.idOf cfg.genesis, cfg.genesis)])
          ⟨hcst, hh₀, ho₀, (Grows.insert s.disk : Grows s.disk st), fun r hr => Or.inl hr,
            ⟨_, hi₀⟩, hev.grow (Grows.insert s.disk : Grows s.disk st) rfl rfl, subset_rfl⟩ hp ?_
          (by simp only [Node.step, dif_pos h₂, if_pos h₁]; rfl)
        intro e he
        simp only [built, persists, List.flatMap_cons, List.flatMap_nil, List.append_nil,
          List.filterMap_cons, List.filterMap_nil, List.mem_singleton] at he
        subst he
        rfl
      · exact hsame (by simp only [Node.step, dif_neg h₂, if_pos h₁])
    · exact hsame (by simp only [Node.step, if_neg h₁])
  | deliver u id b =>
    rcases step_receipt (cfg := cfg) (s := s) (Or.inl ⟨u, id, b, rfl⟩) with
      he | ⟨s₁, pre, hr, hpre, he⟩
    · exact hsame he
    · obtain ⟨hc₁, hp₁⟩ := hr.cut hg hc hp hd
      refine hset s₁ pre
        ⟨hc₁, hh.grow hr.grows hr.top, hown.grow hr.grows hr.top hr.own, hr.grows,
          fun r hr' => Or.inl (by rwa [hr.fired] at hr'), ⟨B₀, hr.inv hi hd⟩, hr.ev hev,
          hr.det⟩ hp₁ ?_ he
      intro e he
      obtain ⟨o, ho, he⟩ := List.mem_filterMap.mp he
      obtain ⟨_, _, _, _, rfl⟩ := hpre o ho; cases he
  | stream u L =>
    rcases step_receipt (cfg := cfg) (s := s) (Or.inr ⟨u, L, rfl⟩) with he | ⟨s₁, pre, hr, hpre, he⟩
    · exact hsame he
    · obtain ⟨hc₁, hp₁⟩ := hr.cut hg hc hp hd
      refine hset s₁ pre
        ⟨hc₁, hh.grow hr.grows hr.top, hown.grow hr.grows hr.top hr.own, hr.grows,
          fun r hr' => Or.inl (by rwa [hr.fired] at hr'), ⟨B₀, hr.inv hi hd⟩, hr.ev hev,
          hr.det⟩ hp₁ ?_ he
      intro e he
      obtain ⟨o, ho, he⟩ := List.mem_filterMap.mp he
      obtain ⟨_, _, _, _, rfl⟩ := hpre o ho; cases he
  | timer r =>
    intro e hev'
    rw [persists_step_timer] at hb hev'
    rw [step_timer_fst]
    refine Or.inr (settle_witness hg (s := s) (inp := .timer r)
      (s₀ := { s with fired := fire s r, recovering := false })
      ⟨hc, hh.grow (Grows.refl _) rfl, hown.grow (Grows.refl _) rfl rfl, Grows.refl _,
        fun t ht => ?_, ⟨B₀, hi.of_eq rfl rfl rfl rfl rfl le_rfl⟩,
        hev.grow (Grows.refl _) rfl rfl, subset_rfl⟩ hp hb e hev')
    rcases Finset.mem_insert.mp ht with rfl | ht
    · exact Or.inr rfl
    · exact Or.inl (Finset.mem_filter.mp ht).1
  | syncRequest peer t fr ids =>
    intro e he
    simp only [Node.step] at he
    split at he <;> simp [persists] at he
  | ask peer r =>
    intro e he
    simp only [Node.step] at he
    split at he <;> (try split at he) <;> simp [persists] at he
  | restart =>
    intro e hev'
    rw [persists_step_restart] at hb hev'
    rw [step_restart_fst]
    exact Or.inr (settle_witness hg (s := s) (inp := .restart)
      (s₀ := { s with recovering := true })
      ⟨hc, hh.grow (Grows.refl _) rfl, hown.grow (Grows.refl _) rfl rfl, Grows.refl _,
        fun t ht => Or.inl ht, ⟨B₀, hi.of_eq rfl rfl rfl rfl rfl le_rfl⟩,
        hev.grow (Grows.refl _) rfl rfl, subset_rfl⟩ hp hb e hev')

omit [Fintype Validator] in
theorem decideStep_armed (s : State Validator BlockId Payload) :
    (Node.decideStep cfg s).1.armed = s.armed := by
  unfold Node.decideStep; dsimp only; split <;> simp only [release_own, release_fired,
        release_armed, release_top]

omit [Fintype Validator] in
theorem progress_armed : ∀ (fuel : ℕ) (s : State Validator BlockId Payload),
    (Node.progress cfg fuel s).1.armed = s.armed
  | 0, _ => rfl
  | fuel + 1, s => by
    unfold Node.progress
    split
    · rename_i s₁ out hb
      rw [progress_armed fuel s₁]
      obtain ⟨_, _, _, -, hb, -⟩ := tryBuild_cases hb
      unfold buildAbove at hb
      dsimp only at hb
      split at hb
      · split at hb
        · rw [Option.some.injEq, Prod.mk.injEq] at hb
          rw [← hb.1, release_armed]; rfl
        · exact absurd hb (by simp)
      · exact absurd hb (by simp)
    · rfl

/-- A top that only rises: from `s` to `s'`, a top `t` becomes a top at
or above `t`. -/
def TopRises (s s' : State Validator BlockId Payload) : Prop :=
  ∀ t, s.top = some t → ∃ t', s'.top = some t' ∧ t ≤ t'

omit [Fintype Validator] in
theorem TopRises.refl (s : State Validator BlockId Payload) : TopRises s s :=
  fun t ht => ⟨t, ht, le_rfl⟩

omit [Fintype Validator] in
theorem TopRises.trans {a b c : State Validator BlockId Payload} (h₁ : TopRises a b)
    (h₂ : TopRises b c) : TopRises a c := fun t ht => by
  obtain ⟨t₁, h₁', h₁''⟩ := h₁ t ht
  obtain ⟨t₂, h₂', h₂''⟩ := h₂ t₁ h₁'
  exact ⟨t₂, h₂', by omega⟩

omit [Fintype Validator] in
theorem TopRises.of_eq {s s' : State Validator BlockId Payload} (h : s'.top = s.top) :
    TopRises s s' := fun t ht => ⟨t, h ▸ ht, le_rfl⟩

variable (cfg) in
/-- **The timers a node sets, read on the state after**: each at a round
at or below the top, and one of the top round above `0` for its timeout,
only once the disk holds a quorum of it. -/
def TimersSet (s : State Validator BlockId Payload)
    (out : List (Output Validator BlockId Payload)) : Prop :=
  ∀ r a, Output.setTimer r a ∈ out → ∃ t, s.top = some t ∧ r ≤ t ∧
    (r = t → 1 ≤ r → a = cfg.timeout r ∧ cfg.q ≤ (s.disk.authorsAt r).card)

variable (cfg) in
/-- **An armed round has a quorum** on the disk. -/
def ArmedQuorum (s : State Validator BlockId Payload) : Prop :=
  ∀ r, s.armed = some r → cfg.q ≤ (s.disk.authorsAt r).card

omit [Fintype Validator] in
/-- A grown store has the authors of each round it had. -/
theorem Grows.authorsAt {st st' : Store Validator BlockId Payload} (hg : Grows st st') (r : ℕ) :
    st.authorsAt r ⊆ st'.authorsAt r := by
  rw [Store.authorsAt_eq, Store.authorsAt_eq]
  exact hg.authorsIn r

omit [Fintype Validator] in
theorem TimersSet.mono {s s' : State Validator BlockId Payload}
    {out : List (Output Validator BlockId Payload)} (h : TimersSet cfg s out)
    (hg : Grows s.disk s'.disk) (ht : TopRises s s') : TimersSet cfg s' out := by
  intro r a hm
  obtain ⟨t, hst, hrt, hq⟩ := h r a hm
  obtain ⟨t', hst', htt'⟩ := ht t hst
  refine ⟨t', hst', by omega, fun hr h1 => ?_⟩
  have hrt' : r = t := by omega
  exact ⟨(hq hrt' h1).1, (hq hrt' h1).2.trans (Finset.card_le_card (hg.authorsAt r))⟩

omit [Fintype Validator] in
theorem TimersSet.append {s : State Validator BlockId Payload}
    {x y : List (Output Validator BlockId Payload)} (hx : TimersSet cfg s x)
    (hy : TimersSet cfg s y) : TimersSet cfg s (x ++ y) := fun r a hm => by
  rcases List.mem_append.mp hm with hm | hm
  · exact hx r a hm
  · exact hy r a hm

omit [Fintype Validator] in
/-- Timers set on a state stay set as its top rises and its disk grows. -/
theorem TimersSet.rise {s s' : State Validator BlockId Payload}
    {out : List (Output Validator BlockId Payload)} (h : TimersSet cfg s out)
    (ht : TopRises s s') (hg : Grows s.disk s'.disk) : TimersSet cfg s' out := fun r a hm => by
  obtain ⟨t, hts, hrt, hq⟩ := h r a hm
  obtain ⟨t', ht', htt'⟩ := ht t hts
  refine ⟨t', ht', hrt.trans htt', fun hr h1 => ?_⟩
  obtain ⟨ha, hq'⟩ := hq (by omega) h1
  exact ⟨ha, hq'.trans (Finset.card_le_card (hg.authorsAt r))⟩

omit [Fintype Validator] in
theorem TimersSet.of_none {s : State Validator BlockId Payload}
    {x : List (Output Validator BlockId Payload)} (h : ∀ r a, Output.setTimer r a ∉ x) :
    TimersSet cfg s x := fun r a hm => absurd hm (h r a)

omit [Fintype Validator] in
/-- **Building sets the timer of the round below** the new top. -/
theorem timersSet_progress : ∀ (fuel : ℕ) (s : State Validator BlockId Payload),
    TimersSet cfg (Node.progress cfg fuel s).1 (Node.progress cfg fuel s).2 ∧
      Grows s.disk (Node.progress cfg fuel s).1.disk ∧ TopRises s (Node.progress cfg fuel s).1
  | 0, s => ⟨TimersSet.of_none fun _ _ h => by simp [Node.progress] at h, Grows.refl _,
      TopRises.refl _⟩
  | fuel + 1, s => by
    unfold Node.progress
    split
    · rename_i s₁ out hb
      obtain ⟨r, id, b, hnew, hrefs, hpred, hr, hbr, -, -, -, hst, htop, -, -, hout⟩ :=
        tryBuild_some hb
      obtain ⟨h₁, h₂, h₃⟩ := timersSet_progress fuel s₁
      have hg : Grows s.disk s₁.disk := by rw [hst]; exact Grows.insert s.disk
      have ht : TopRises s s₁ := fun t ht => ⟨r + 1, htop, by
        have := hr.2.1; rw [ht] at this; simp only [Option.getD_some] at this; omega⟩
      refine ⟨TimersSet.append ?_ h₁, hg.trans h₂, ht.trans h₃⟩
      intro r' a hm
      rw [hout] at hm
      simp only [built, List.flatMap_cons, List.flatMap_nil, List.append_nil, List.mem_cons,
        reduceCtorEq, Output.setTimer.injEq, List.not_mem_nil, or_false, false_or] at hm
      obtain ⟨rfl, rfl⟩ := hm
      obtain ⟨t', ht', htt'⟩ := h₃ (r + 1) htop
      exact ⟨t', ht', by rw [hbr]; omega, fun h _ => by rw [hbr] at h; omega⟩
    · exact ⟨TimersSet.of_none fun _ _ h => by simp at h, Grows.refl _, TopRises.refl _⟩

omit [Fintype Validator] in
/-- **Arming sets the top round's timer** once the disk holds a quorum of
it. -/
theorem timersSet_arm (s : State Validator BlockId Payload) :
    TimersSet cfg (Node.arm cfg s).1 (Node.arm cfg s).2 := by
  intro r a hm
  obtain ⟨t, ht, hq, -, ho⟩ := mem_arm hm
  rw [Output.setTimer.injEq] at ho
  obtain ⟨rfl, rfl⟩ := ho
  exact ⟨r, by rw [arm_top]; exact ht, le_rfl, fun _ _ => ⟨rfl, by rw [arm_disk]; exact hq⟩⟩

omit [Fintype Validator] in
theorem ArmedQuorum.arm {s : State Validator BlockId Payload} (h : ArmedQuorum cfg s) :
    ArmedQuorum cfg (Node.arm cfg s).1 := by
  intro r hr
  rw [arm_disk]
  unfold Node.arm at hr
  split at hr
  · rename_i t ht
    split at hr
    · rename_i hc
      cases hr
      exact hc.2.trans (Finset.card_le_card (s.mirrors.authorsAt_sub _))
    · exact h r hr
  · exact h r hr

omit [Fintype Validator] in
theorem ArmedQuorum.grow {s s' : State Validator BlockId Payload} (h : ArmedQuorum cfg s)
    (hg : Grows s.disk s'.disk) (ha : s'.armed = s.armed) : ArmedQuorum cfg s' := fun r hr =>
  (h r (ha ▸ hr)).trans (Finset.card_le_card (hg.authorsAt r))

omit [Fintype Validator] in
theorem timersSet_advance (s : State Validator BlockId Payload) :
    TimersSet cfg (Node.advance cfg s).1 (Node.advance cfg s).2 ∧
      Grows s.disk (Node.advance cfg s).1.disk ∧ TopRises s (Node.advance cfg s).1 := by
  obtain ⟨h₁, h₂, h₃⟩ := timersSet_progress (cfg := cfg) (s.disk.topRound + 2) s
  have hgp : Grows (Node.progress cfg (s.disk.topRound + 2) s).1.disk
      (Node.pass cfg s).1.disk := by
    simp only [Node.pass]
    rw [← decideStep_disk (cfg := cfg) (Node.progress cfg (s.disk.topRound + 2) s).1]
    exact Grows.flushSyncs _ _
  have htp : TopRises (Node.progress cfg (s.disk.topRound + 2) s).1 (Node.pass cfg s).1 :=
    TopRises.of_eq (by simp only [Node.pass, flushSyncs_top]; exact decideStep_top _)
  have hga : Grows (Node.pass cfg s).1.disk (Node.advance cfg s).1.disk := by
    rw [advance_disk]; exact Grows.refl _
  have hta : TopRises (Node.pass cfg s).1 (Node.advance cfg s).1 :=
    TopRises.of_eq (advance_top s)
  refine ⟨?_, h₂.trans (hgp.trans hga), h₃.trans (htp.trans hta)⟩
  rw [advance_snd]
  refine TimersSet.append ?_ ((timersSet_arm _).mono (by
    simp only [Node.advance, release_disk]; exact Grows.refl _)
    (TopRises.of_eq (by simp only [Node.advance, release_top])))
  simp only [Node.pass]
  refine TimersSet.append ((h₁.mono hgp htp).mono hga hta) (TimersSet.of_none fun r a h => ?_)
  unfold Node.decideStep at h
  dsimp only at h
  split at h
  · obtain ⟨_, _, h⟩ := List.mem_map.mp h
    cases h
  · simp at h

omit [Fintype Validator] in
theorem ArmedQuorum.advance {s : State Validator BlockId Payload} (h : ArmedQuorum cfg s) :
    ArmedQuorum cfg (Node.advance cfg s).1 := by
  have hp : ArmedQuorum cfg (Node.pass cfg s).1 :=
    h.grow (by rw [← advance_disk]; exact (timersSet_advance (cfg := cfg) s).2.1)
      (by simp only [Node.pass, flushSyncs_armed]; rw [decideStep_armed, progress_armed])
  exact hp.arm.grow (by simp only [Node.advance, release_disk]; exact Grows.refl _)
    (by simp only [Node.advance, release_armed])

omit [Fintype Validator] in
theorem timersSet_quiesce (n : ℕ) (s : State Validator BlockId Payload) :
    TimersSet cfg (Node.quiesce cfg n s).1 (Node.quiesce cfg n s).2 ∧
      Grows s.disk (Node.quiesce cfg n s).1.disk ∧ TopRises s (Node.quiesce cfg n s).1 :=
  (quiesce_rel (P := fun _ => True)
    (R := fun a o b => TimersSet cfg b o ∧ Grows a.disk b.disk ∧ TopRises a b)
    (fun s => ⟨TimersSet.of_none fun _ _ h => absurd h List.not_mem_nil, Grows.refl _,
      TopRises.refl _⟩)
    (fun _ _ _ _ _ h₁ h₂ => ⟨TimersSet.append (h₁.1.mono h₂.2.1 h₂.2.2) h₂.1,
      h₁.2.1.trans h₂.2.1, h₁.2.2.trans h₂.2.2⟩)
    (fun s _ => ⟨timersSet_advance s, trivial⟩) n s trivial).1

omit [Fintype Validator] in
theorem ArmedQuorum.settle {s : State Validator BlockId Payload} (h : ArmedQuorum cfg s) :
    ArmedQuorum cfg (Node.settle cfg s).1 :=
  quiesce_ind (fun _ h => h.advance) _ _ h

omit [Fintype Validator] in
/-- **Resending sets the timer of the round below the top.** -/
theorem timersSet_resend (s : State Validator BlockId Payload) :
    TimersSet cfg s (Node.resend cfg s) := by
  intro r a hm
  obtain ⟨t, ht, hrt, -⟩ := mem_resend_setTimer hm
  exact ⟨t, ht, by omega, fun h h1 => by omega⟩

omit [Fintype Validator] in
theorem timersSet_rearm {s : State Validator BlockId Payload} (h : ArmedQuorum cfg s) :
    TimersSet cfg s (Node.rearm cfg s) := by
  intro r a hm
  obtain ⟨t, ht, ha, ho⟩ := mem_rearm hm
  rw [Output.setTimer.injEq] at ho
  obtain ⟨rfl, rfl⟩ := ho
  exact ⟨r, ht, le_rfl, fun _ _ => ⟨rfl, h r ha⟩⟩

/-- **A step sets timers at or below the top**, and one of the top round
above `0` only with a quorum of it. -/
theorem timersSet_step {s : State Validator BlockId Payload} (hA : ArmedQuorum cfg s)
    (inp : Input Validator BlockId Payload) :
    TimersSet cfg (Node.step cfg s inp).1 (Node.step cfg s inp).2 ∧
      ArmedQuorum cfg (Node.step cfg s inp).1 := by
  cases inp with
  | start =>
    simp only [Node.step]
    split
    · split
      · rename_i h₁ h₂
        set g := cfg.idOf cfg.genesis
        set s₀ : State Validator BlockId Payload :=
          { keep s g cfg.genesis h₂.1 (fun _ hj => absurd hj (Finset.notMem_empty _))
              (fun j hj => absurd hj (Finset.notMem_empty j)) with
            top := some 0
            own := some g
            recovering := false }
        have hA₀ : ArmedQuorum cfg s₀ := hA.grow (Grows.insert s.disk (hnew := h₂.1)
          (hrefs := fun _ hj => absurd hj (Finset.notMem_empty _))
          (hpred := fun j hj => absurd hj (Finset.notMem_empty j))) rfl
        obtain ⟨h₁', h₂', h₃'⟩ := timersSet_quiesce (cfg := cfg) (passes cfg s₀) s₀
        refine ⟨TimersSet.append ?_ h₁', hA₀.settle⟩
        intro r a hm
        simp only [List.mem_cons, reduceCtorEq, Output.setTimer.injEq, List.not_mem_nil,
          or_false, false_or] at hm
        obtain ⟨rfl, rfl⟩ := hm
        obtain ⟨t, ht, -⟩ := h₃' 0 rfl
        exact ⟨t, ht, Nat.zero_le _, fun _ h => absurd h (by omega)⟩
      · exact ⟨TimersSet.of_none fun _ _ h => absurd h List.not_mem_nil, hA⟩
    · exact ⟨TimersSet.of_none fun _ _ h => absurd h List.not_mem_nil, hA⟩
  | deliver u id b =>
    rcases step_receipt (cfg := cfg) (s := s) (Or.inl ⟨u, id, b, rfl⟩) with
      he | ⟨s₁, pre, hr, hpre, he⟩
    · rw [he]; exact ⟨TimersSet.of_none fun _ _ h => absurd h List.not_mem_nil, hA⟩
    · rw [he]
      refine ⟨TimersSet.append (TimersSet.of_none fun r a h => ?_) (timersSet_quiesce _ _).1,
        ArmedQuorum.settle (hA.grow hr.grows hr.armed)⟩
      obtain ⟨_, _, _, _, h⟩ := hpre _ h; cases h
  | stream u L =>
    rcases step_receipt (cfg := cfg) (s := s) (Or.inr ⟨u, L, rfl⟩) with he | ⟨s₁, pre, hr, hpre, he⟩
    · rw [he]; exact ⟨TimersSet.of_none fun _ _ h => absurd h List.not_mem_nil, hA⟩
    · rw [he]
      refine ⟨TimersSet.append (TimersSet.of_none fun r a h => ?_) (timersSet_quiesce _ _).1,
        ArmedQuorum.settle (hA.grow hr.grows hr.armed)⟩
      obtain ⟨_, _, _, _, h⟩ := hpre _ h; cases h
  | timer r =>
    have hAs :
        ArmedQuorum cfg (Node.settle cfg { s with fired := fire s r, recovering := false }).1 :=
      ArmedQuorum.settle (s := { s with fired := fire s r, recovering := false }) hA
    have hts := (timersSet_quiesce (cfg := cfg)
      (passes cfg { s with fired := fire s r, recovering := false })
      { s with fired := fire s r, recovering := false }).1
    simp only [Node.step]
    split
    · exact ⟨TimersSet.append hts (timersSet_resend _), hAs⟩
    · exact ⟨hts, hAs⟩
  | syncRequest peer t fr ids =>
    refine ⟨TimersSet.of_none fun r a h => ?_, hA⟩
    simp only [Node.step] at h
    split at h <;> simp at h
  | ask peer r =>
    refine ⟨TimersSet.of_none fun r a h => ?_, hA⟩
    simp only [Node.step] at h
    split at h <;> (try split at h) <;> simp at h
  | restart =>
    have hAs : ArmedQuorum cfg (Node.settle cfg { s with recovering := true }).1 :=
      ArmedQuorum.settle (s := { s with recovering := true }) hA
    obtain ⟨hts, hg, hr⟩ :=
      timersSet_quiesce (cfg := cfg) (passes cfg { s with recovering := true })
        { s with recovering := true }
    refine ⟨TimersSet.append (TimersSet.append ((timersSet_resend s).rise hr hg)
      ((timersSet_rearm hA).rise hr hg)) hts, hAs⟩

omit [Fintype Validator] [DecidableEq Validator] in
/-- **A cut's paths are the record's**: what a block of the store reaches in
the store it reaches in the record. -/
theorem IsCut.reachesFrom {U : BlockRecord Validator BlockId Payload P H}
    {st : Store Validator BlockId Payload} (hc : IsCut U st) {i : BlockId} :
    ∀ {j : BlockId}, j ∈ st.ids → ReachesFrom st.blk j i → ReachesFrom U.block j i := by
  intro j hj h
  induction h using Relation.ReflTransGen.head_induction_on with
  | refl => exact ReachesFrom.refl
  | @head a c hstep hrest ih =>
    have hstep : c ∈ (st.blk a).refs := hstep
    have hcs : c ∈ st.ids := st.complete a hj c hstep
    have hU : c ∈ (U.block a).refs := by rw [hc.eq hj]; exact hstep
    exact Relation.ReflTransGen.head hU (ih hcs)

omit [Fintype Validator] in
/-- Slot `k` is proposed at its slot round. -/
theorem mem_slotsAt (k : ℕ) : k ∈ cfg.slotsAt (cfg.slots.slotRound k) := by
  unfold Config.slotsAt
  change k ∈ if cfg.per * (k / cfg.m) % cfg.per = 0 then
    (List.range cfg.m).map (fun i => cfg.m * (cfg.per * (k / cfg.m) / cfg.per) + i) else []
  rw [if_pos (Nat.mul_mod_right _ _), Nat.mul_div_cancel_left _ cfg.per_pos]
  exact List.mem_map.mpr ⟨k % cfg.m, List.mem_range.mpr (Nat.mod_lt _ cfg.m_pos),
    Nat.div_add_mod k cfg.m⟩

omit [Fintype Validator] in
/-- **The reach test, read on the record**: a block of round `r + 1` whose
references pass the reach test on a cut reaches, in the record, the
block of each honest leader of a slot `m` rounds below `r`, for `m` below
the vote offset. -/
theorem reaches_of_reachReady {U : BlockRecord Validator BlockId Payload P H}
    {st : Store Validator BlockId Payload} (hc : IsCut U st) {refs : Finset BlockId} {r : ℕ}
    {X : Finset Validator} (hready : reachReady cfg st refs r X = true) (hrefs : refs ⊆ st.ids)
    {k m : ℕ} (hm : m < cfg.p.voteOffset) (hk : cfg.slots.slotRound k + m = r)
    (hlead : cfg.slots.leader k ∈ H) (hlX : cfg.slots.leader k ∉ X) {L : BlockId}
    (hL : IsLeaderBlock (S := cfg.slots) U k L)
    {c : BlockId} (hcrefs : (U.block c).refs = refs) : Reaches U c L := by
  unfold reachReady at hready
  have h₁ := List.all_eq_true.mp hready m (List.mem_range.mpr hm)
  rw [if_pos (by omega)] at h₁
  have h₂ := List.all_eq_true.mp h₁ k (by rw [← hk, Nat.add_sub_cancel]; exact mem_slotsAt k)
  obtain ⟨L', hL', c', hc', hhist⟩ := (of_decide_eq_true h₂).resolve_left hlX
  rw [Store.leaderBlocks_eq] at hL'
  obtain ⟨hL's, hL'c, hL'r⟩ := Finset.mem_filter.mp hL'
  have hreach : ReachesFrom U.block c' L' :=
    hc.reachesFrom (hrefs hc') (reaches_of_mem_historyUptoFrom hhist)
  have hlead' : IsLeaderBlock (S := cfg.slots) U k L' :=
    ⟨(hc L' hL's).1, by rw [hc.round hL's]; exact hL'r, by rw [hc.creator hL's]; exact hL'c⟩
  rw [isLeaderBlock_unique_of_honest (S := cfg.slots) hlead hL hlead']
  exact Relation.ReflTransGen.head (show c' ∈ (U.block c).refs by rw [hcrefs]; exact hc') hreach

omit [Fintype Validator] in
/-- **`refsFor` on a cut references each block of the store by an honest author
at its round**, given the node's own block there as `o` if the author is
the node. -/
theorem mem_refsFor_of_cut {U : BlockRecord Validator BlockId Payload P H}
    {st : Store Validator BlockId Payload} (hc : IsCut U st) {r : ℕ} {o : Option BlockId}
    {E : Finset (Validator × BlockId × BlockId)}
    {b : BlockId} (hb : b ∈ st.ids) (hbr : (st.blk b).round = r)
    (hhon : (st.blk b).creator ∈ H)
    (ho : (st.blk b).creator = cfg.me → ∃ j, o = some j ∧ j ∈ st.ids ∧
      (st.blk j).round = r ∧ (st.blk j).creator = cfg.me)
    (hex : (st.blk b).creator ∉ excluded cfg st r E) :
    b ∈ refsFor cfg st r o E := by
  have huniq : ∀ i ∈ st.ids, (st.blk i).round = r → (st.blk i).creator = (st.blk b).creator →
      i = b := fun i hi hir hic =>
    U.no_equivocation i (hc i hi).1 b (hc b hb).1 (by rw [hc.creator hi, hic]; exact hhon)
      (by rw [hc.creator hi, hc.creator hb, hic]) (by rw [hc.round hi, hc.round hb, hir, hbr])
  refine mem_refsFor hb hbr huniq (fun hme => ?_) hex
  obtain ⟨j, hoj, hj, hjr, hjc⟩ := ho hme
  rw [hoj, huniq j hj hjr (by rw [hjc, hme])]

omit [Fintype Validator] in
/-- **The certificate test, read on the record**: where votes are
certified a round later, a block of round `r + 1` whose references pass
the certificate test on a cut certifies, in the record, the block of each
honest leader of a slot whose vote round is `r`. -/
theorem isCert_of_certReady [P.Mechanised] (hσ : cfg.σ = boundedSel)
    {U : BlockRecord Validator BlockId Payload P H} {st : Store Validator BlockId Payload}
    (hc : IsCut U st) {refs : Finset BlockId} {r : ℕ} {X : Finset Validator}
    (hready : certReady cfg st refs r X = true)
    (hrefs : refs ⊆ st.ids) (hvc : cfg.p.voteIsCert = false) {k : ℕ}
    (hk : cfg.slots.slotRound k + cfg.p.voteOffset = r) (hlead : cfg.slots.leader k ∈ H)
    (hlX : cfg.slots.leader k ∉ X)
    {L : BlockId} (hL : IsLeaderBlock (S := cfg.slots) U k L) {c : BlockId}
    (hcrefs : (U.block c).refs = refs) : Scheme.IsCert cfg.p boundedSel U c L := by
  unfold certReady at hready
  rw [hvc, if_neg (by simp), if_pos (by omega)] at hready
  have h₂ := List.all_eq_true.mp hready k
    (by rw [← hk, Nat.add_sub_cancel]; exact mem_slotsAt k)
  obtain ⟨L', hL', hcount⟩ := (of_decide_eq_true h₂).resolve_left hlX
  rw [Store.leaderBlocks_eq] at hL'
  obtain ⟨hL's, hL'c, hL'r⟩ := Finset.mem_filter.mp hL'
  have hlead' : IsLeaderBlock (S := cfg.slots) U k L' :=
    ⟨(hc L' hL's).1, by rw [hc.round hL's]; exact hL'r, by rw [hc.creator hL's]; exact hL'c⟩
  rw [isLeaderBlock_unique_of_honest (S := cfg.slots) hlead hL hlead']
  obtain ⟨V, -, hV⟩ := hc.extend ⟨∅, Finset.empty_subset _, fun i hi => absurd hi
    (Finset.notMem_empty _)⟩ (fun i hi => absurd hi (Finset.notMem_empty _))
  have hva := ViewsAbove.of_store (st := st) (V := V) hV (fun i hi => (hc i hi).2)
  have hf : refs.filter (fun b => cfg.σ.Votes st.toRecord b L') =
      (U.block c).refs.filter (fun b =>
        (boundedSel : Scheme.VoteSel Validator BlockId Payload P H).Votes U b L') := by
    rw [hcrefs, hσ]
    exact Finset.filter_congr fun b hb =>
      hva.votes_iff (hrefs hb) (Nat.zero_le _) hL's (Nat.zero_le _)
  unfold Scheme.IsCert
  rw [if_neg (by simp [hvc])]
  unfold CarriesVotes carriedVotes
  rw [← hf]
  have hcr : creatorsOf U.block (refs.filter fun b => cfg.σ.Votes st.toRecord b L') =
      creatorsOf st.blk (refs.filter fun b => cfg.σ.Votes st.toRecord b L') :=
    Finset.image_congr fun b hb => hc.creator (hrefs (Finset.mem_filter.mp hb).1)
  rw [hcr]
  exact hcount

end Node

end LeanDag
