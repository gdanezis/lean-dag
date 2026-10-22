import LeanDag.Node.Helpers.Trace
import LeanDag.Node.Helpers.Commits
/-!
# The build rule's two exits

`docs/validator.md` §13.2, step 11.1b. A block the node builds above
round `r` either passes the reach and certificate tests on the store, or
was built after the round's timer fired, on `refsFor`'s references
(`tryBuild_exit`). Those reference every block of the round below that is
the only one of its author the store holds, and the node's own block
(`mem_refsFor`).

Along a trace, each round whose timer node `v` counts as fired had its
timer input at an earlier event (`fired_before`), and `v`'s own block at
its top is stored (`ownTop_before`). Each block a step persists is the
genesis block or comes from one build, at a state whose store is a cut of
the record (`BuildState`, `step_witness`). Each timer a step sets is set
for its round's timeout, beside a block of that round (`timersBuilt_step`).
On a cut, the reach test reads as reaching the record's leader blocks
(`reaches_of_reachReady`), the certificate test as certifying them
(`isCert_of_certReady`), and `refsFor` references each honest stored
block at its round (`mem_refsFor_of_cut`).
-/

namespace LeanDag

namespace Node

variable {Validator BlockId Payload : Type} [Fintype Validator] [DecidableEq Validator]
variable [LinearOrder BlockId]
variable {cfg : Config Validator BlockId Payload}

omit [Fintype Validator] in
/-- `refsAt`'s references pass the tests, or are `refsFor`'s. -/
theorem refsAt_cases (st : Store Validator BlockId Payload) (r : ℕ) (o : Option BlockId) :
    (reachReady cfg st (refsAt cfg st r o) r && certReady cfg st (refsAt cfg st r o) r) = true ∨
      refsAt cfg st r o = refsFor cfg st r o := by
  unfold refsAt
  dsimp only
  split
  · exact Or.inl ‹_›
  · rename_i h
    rcases hf : List.find? _ _ with _ | R
    · exact Or.inr rfl
    · have := List.find?_some hf
      simp only [Bool.and_eq_true] at this
      exact Or.inl (by simpa using this.1)

omit [Fintype Validator] in
/-- **The build rule's two exits**: a block built above round `r` passes
the reach and certificate tests on the store, or the round's timer fired
and its references are `refsFor`'s. -/
theorem tryBuild_exit {s s' : State Validator BlockId Payload}
    {out : List (Output Validator BlockId Payload)} (h : tryBuild cfg s = some (s', out)) :
    ∃ r, s.top = some r ∧ cfg.q ≤ (authorsIn s.store.toRecord s.store.ids r).card ∧
      ((reachReady cfg s.store (refsAt cfg s.store r s.own) r = true ∧
          certReady cfg s.store (refsAt cfg s.store r s.own) r = true) ∨
        (r ∈ s.fired ∧ refsAt cfg s.store r s.own = refsFor cfg s.store r s.own)) ∧
      out = built cfg [(cfg.idOf ⟨r + 1, cfg.me, refsAt cfg s.store r s.own,
          cfg.payload (r + 1)⟩,
        ⟨r + 1, cfg.me, refsAt cfg s.store r s.own, cfg.payload (r + 1)⟩)] := by
  unfold tryBuild at h
  split at h
  · rename_i r hr
    dsimp only at h
    split at h
    · rename_i hc
      split at h
      · rw [Option.some.injEq, Prod.mk.injEq] at h
        refine ⟨r, hr, hc.1, ?_, by rw [← h.2]; simp [built]⟩
        rcases hc.2 with hf | hready
        · rcases refsAt_cases (cfg := cfg) s.store r s.own with h' | h'
          · simp only [Bool.and_eq_true] at h'
            exact Or.inl h'
          · exact Or.inr ⟨hf, h'⟩
        · exact Or.inl hready
      · exact absurd h (by simp)
    · exact absurd h (by simp)
  · exact absurd h (by simp)

omit [Fintype Validator] in
/-- **What `refsFor` references**: a round-`r` block the store holds that
is its author's only one there, if the author is not the node, or the
node's own block `o` there. -/
theorem mem_refsFor {st : Store Validator BlockId Payload} {r : ℕ} {o : Option BlockId}
    {j : BlockId} (hj : j ∈ st.ids) (hr : (st.blk j).round = r)
    (huniq : ∀ i ∈ st.ids, (st.blk i).round = r → (st.blk i).creator = (st.blk j).creator →
      i = j)
    (hown : (st.blk j).creator = cfg.me → o = some j) :
    j ∈ refsFor cfg st r o := by
  unfold refsFor
  dsimp only
  have hjR : j ∈ blocksAt st.toRecord r := Finset.mem_filter.mpr ⟨hj, hr⟩
  refine Finset.mem_biUnion.mpr ⟨(st.blk j).creator, Finset.mem_image_of_mem _ hjR, ?_⟩
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
  unfold tryBuild at h
  split at h
  · dsimp only at h
    split at h
    · split at h
      · rw [Option.some.injEq, Prod.mk.injEq] at h
        rw [← h.1]; exact Calm.refl _
      · exact absurd h (by simp)
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
  split <;> exact Calm.refl _

omit [Fintype Validator] in
theorem calm_advance (s : State Validator BlockId Payload) :
    Calm s (Node.advance cfg s).1 :=
  Calm.trans (calm_progress _ s) (calm_decideStep _)

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
  | deliver id b =>
    simp only [Node.step]
    split
    · intro r h
      have := calm_quiesce (cfg := cfg) _ _ h
      exact Or.inl this
    · exact fun r h => Or.inl h
  | timer t =>
    intro r h
    rcases Finset.mem_insert.mp (calm_quiesce (cfg := cfg) _ _ h) with rfl | h
    · exact Or.inr rfl
    · exact Or.inl h
  | fetchRequest peer ids => exact fun r h => Or.inl h

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
        tryBuild cfg x = some (y, o) ∧ e ∈ persists o
  | 0, s, _, _, e, he => by simp [Node.progress, persists] at he
  | fuel + 1, s, hs, hK, e, he => by
    rcases hb : tryBuild cfg s with _ | ⟨s₁, out⟩
    · simp [Node.progress, hb, persists] at he
    · simp only [Node.progress, hb] at he hK
      rw [persists_append] at he hK
      have hK₁ : ∀ e ∈ persists out, e ∈ K := fun e he => hK e (List.mem_append_left _ he)
      rcases List.mem_append.mp he with he | he
      · exact ⟨s, s₁, out, hs, hb, he⟩
      · exact progress_witness Q K hQ fuel s₁ (hQ s s₁ out hs hb hK₁)
          (fun e he => hK e (List.mem_append_right _ he)) e he

variable (cfg) in
/-- **The node's own block at its top is stored**, as `own`. -/
def OwnTop (s : State Validator BlockId Payload) : Prop :=
  ∀ r, s.top = some r → ∃ j, s.own = some j ∧ j ∈ s.store.ids ∧ (s.store.blk j).round = r ∧
    (s.store.blk j).creator = cfg.me

omit [Fintype Validator] in
theorem OwnTop.grow {s s' : State Validator BlockId Payload} (h : OwnTop cfg s)
    (hg : Grows s.store s'.store) (ht : s'.top = s.top) (ho : s'.own = s.own) :
    OwnTop cfg s' := by
  intro r hr
  obtain ⟨j, hj, hji, hjr, hjc⟩ := h r (ht ▸ hr)
  exact ⟨j, ho ▸ hj, hg.1 hji, by rw [hg.blk hji, hjr], by rw [hg.blk hji, hjc]⟩

omit [Fintype Validator] in
theorem OwnTop.tryBuild {s s' : State Validator BlockId Payload}
    {out : List (Output Validator BlockId Payload)} (h : tryBuild cfg s = some (s', out)) :
    OwnTop cfg s' := by
  unfold Node.tryBuild at h
  split at h
  · dsimp only at h
    split at h
    · split at h
      · rw [Option.some.injEq, Prod.mk.injEq] at h
        rw [← h.1]
        intro r hr
        simp only [Option.some.injEq] at hr
        subst hr
        refine ⟨_, rfl, Finset.mem_insert_self _ _, ?_, ?_⟩ <;>
          simp [Store.blk, Store.insert, Std.TreeMap.getD_insert_self]
      · exact absurd h (by simp)
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
  simp only [Node.advance]
  have h₁ := OwnTop.progress (s.store.topRound + 2) h
  generalize Node.progress cfg (s.store.topRound + 2) s = r at h₁
  have h₂ : OwnTop cfg (Node.decideStep cfg r.1).1 := by
    have hown : (Node.decideStep cfg r.1).1.own = r.1.own := by
      unfold Node.decideStep; dsimp only; split <;> rfl
    exact h₁.grow (by rw [decideStep_store]; exact Grows.refl _) (decideStep_top _) hown
  exact h₂.grow (Grows.flush _ _ _) rfl rfl

omit [Fintype Validator] in
theorem OwnTop.settle {s : State Validator BlockId Payload} (h : OwnTop cfg s) :
    OwnTop cfg (Node.settle cfg s).1 :=
  quiesce_ind (fun _ h => h.advance) _ _ h

/-- **A step keeps the node's own block at its top stored.** -/
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
        refine ⟨_, rfl, Finset.mem_insert_self _ _, ?_, ?_⟩ <;>
          simp [Store.blk, Store.insert, Std.TreeMap.getD_insert_self, Config.genesis]
      · exact h
    · exact h
  | deliver id b =>
    simp only [Node.step]
    split
    · exact OwnTop.settle (h.grow (Grows.flush _ _ _) rfl rfl)
    · exact h
  | timer t => exact OwnTop.settle (h.grow (Grows.refl _) rfl rfl)
  | fetchRequest peer ids => exact h

/-- **Node `v`'s own block at its top is stored before every event.** -/
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
store a cut of `U` grown from `s`'s, its top held and its own block at
its top stored, each round it counts as fired fired before or by `inp`,
and its blocks known in `K` and valid. -/
structure BuildState (U : BlockRecord Validator BlockId Payload P H)
    (K : Set (BlockId × Block Validator BlockId Payload))
    (s : State Validator BlockId Payload) (inp : Input Validator BlockId Payload)
    (x : State Validator BlockId Payload) : Prop where
  cut : IsCut U x.store
  held : Held cfg x
  own : OwnTop cfg x
  grows : Grows s.store x.store
  fired : ∀ r ∈ x.fired, r ∈ s.fired ∨ inp = .timer r
  inv : ∃ B, Inv cfg x K B

omit [Fintype Validator] in
theorem BuildState.tryBuild {U : BlockRecord Validator BlockId Payload P H}
    {K : Set (BlockId × Block Validator BlockId Payload)} (hg : Ground U K cfg.q)
    {s x y : State Validator BlockId Payload} {inp : Input Validator BlockId Payload}
    {o : List (Output Validator BlockId Payload)} (h : BuildState cfg U K s inp x)
    (hb : Node.tryBuild cfg x = some (y, o)) (hK : ∀ e ∈ persists o, e ∈ K) :
    BuildState cfg U K s inp y := by
  obtain ⟨_, _, _, _, _, _, -, -, -, -, -, hst, -⟩ := tryBuild_some hb
  refine ⟨h.cut.tryBuild hg hb hK, h.held.tryBuild hb, OwnTop.tryBuild hb,
    h.grows.trans (hst ▸ Grows.insert x.store),
    fun r hr => h.fired r (calm_tryBuild hb hr), ?_⟩
  obtain ⟨B, hi⟩ := h.inv
  obtain ⟨e, he, hi'⟩ := hi.tryBuild hb
  refine ⟨_, hi'.mono fun z hz => ?_⟩
  rcases hz with hz | hz
  · exact hz
  · rw [Set.mem_singleton_iff] at hz
    exact hK z (by rw [he, persists_built, hz]; exact List.mem_singleton_self _)

omit [Fintype Validator] in
/-- **A pass keeps a state the node builds from.** -/
theorem BuildState.advance {U : BlockRecord Validator BlockId Payload P H}
    {K : Set (BlockId × Block Validator BlockId Payload)} (hg : Ground U K cfg.q)
    {s x : State Validator BlockId Payload} {inp : Input Validator BlockId Payload}
    (h : BuildState cfg U K s inp x) (hp : ∀ e ∈ x.pending, e ∈ K)
    (hK : ∀ e ∈ persists (Node.advance cfg x).2, e ∈ K) :
    BuildState cfg U K s inp (Node.advance cfg x).1 := by
  refine ⟨h.cut.advanceStore hg hp hK, h.held.advance, h.own.advance,
    h.grows.trans (Grows.advance x), fun r hr => h.fired r (calm_advance x hr), ?_⟩
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
      Node.tryBuild cfg x = some (y, o) ∧ e ∈ persists o := by
  have hpe : persists (Node.advance cfg s₀).2 =
      persists (Node.progress cfg (s₀.store.topRound + 2) s₀).2 := by
    simp only [Node.advance]
    rw [persists_append, decideStep_persist, List.append_nil]
  rw [hpe] at hK ⊢
  exact progress_witness (BuildState cfg U K s inp) K
    (fun _ _ _ hx hb hK => hx.tryBuild hg hb hK)
    _ s₀ h₀ hK

omit [Fintype Validator] in
theorem quiesce_witness {U : BlockRecord Validator BlockId Payload P H}
    {K : Set (BlockId × Block Validator BlockId Payload)} (hg : Ground U K cfg.q)
    {s : State Validator BlockId Payload} {inp : Input Validator BlockId Payload} :
    ∀ (n : ℕ) (s₀ : State Validator BlockId Payload), BuildState cfg U K s inp s₀ →
    (∀ e ∈ s₀.pending, e ∈ K) → (∀ e ∈ persists (quiesce cfg n s₀).2, e ∈ K) →
    ∀ e ∈ persists (quiesce cfg n s₀).2, ∃ x y o, BuildState cfg U K s inp x ∧
      Node.tryBuild cfg x = some (y, o) ∧ e ∈ persists o
  | 0, s₀, _, _, _ => by intro e he; simp [Node.quiesce, persists] at he
  | n + 1, s₀, h₀, hp, hK => by
    rcases quiesce_succ_cases (cfg := cfg) n s₀ with he | he <;> rw [he] at hK ⊢
    · exact advance_witness hg h₀ hK
    · rw [persists_append] at hK
      intro e he'
      rw [persists_append] at he'
      rcases List.mem_append.mp he' with he' | he'
      · exact advance_witness hg h₀ (fun e he => hK e (List.mem_append_left _ he)) e he'
      · exact quiesce_witness hg n _
          (h₀.advance hg hp (fun e he => hK e (List.mem_append_left _ he)))
          (fun e he => hp e ((advance_sub (cfg := cfg) s₀).1 e he))
          (fun e he => hK e (List.mem_append_right _ he)) e he'

omit [Fintype Validator] in
/-- **Each block a settle persists comes from one build**, at a state the
node builds from. -/
theorem settle_witness {U : BlockRecord Validator BlockId Payload P H}
    {K : Set (BlockId × Block Validator BlockId Payload)} (hg : Ground U K cfg.q)
    {s s₀ : State Validator BlockId Payload} {inp : Input Validator BlockId Payload}
    (h₀ : BuildState cfg U K s inp s₀) (hp : ∀ e ∈ s₀.pending, e ∈ K)
    (hK : ∀ e ∈ persists (Node.settle cfg s₀).2, e ∈ K) :
    ∀ e ∈ persists (Node.settle cfg s₀).2, ∃ x y o, BuildState cfg U K s inp x ∧
      Node.tryBuild cfg x = some (y, o) ∧ e ∈ persists o :=
  quiesce_witness hg _ s₀ h₀ hp hK

/-- **Each block a step persists is the genesis block or comes from one
build**, at a state the node builds from. -/
theorem step_witness {U : BlockRecord Validator BlockId Payload P H}
    {K : Set (BlockId × Block Validator BlockId Payload)} (hg : Ground U K cfg.q)
    {s : State Validator BlockId Payload} {inp : Input Validator BlockId Payload}
    {B₀ : List (BlockId × Block Validator BlockId Payload)} (hi : Inv cfg s K B₀)
    (hc : IsCut U s.store) (hh : Held cfg s) (hown : OwnTop cfg s)
    (hp : ∀ e ∈ s.pending, e ∈ K) (hd : ∀ e ∈ delivered cfg [inp], e ∈ K)
    (hb : ∀ e ∈ persists (Node.step cfg s inp).2, e ∈ K) :
    ∀ e ∈ persists (Node.step cfg s inp).2, e.2.round = 0 ∨ ∃ x y o,
      BuildState cfg U K s inp x ∧ Node.tryBuild cfg x = some (y, o) ∧ e ∈ persists o := by
  -- a step that settles `s₀` after outputs persisting only round-`0` blocks
  have hset : ∀ (s₀ : State Validator BlockId Payload)
      (pre : List (Output Validator BlockId Payload)),
      BuildState cfg U K s inp s₀ → (∀ e ∈ s₀.pending, e ∈ K) →
      (∀ e ∈ persists pre, e.2.round = 0) →
      Node.step cfg s inp = ((Node.settle cfg s₀).1, pre ++ (Node.settle cfg s₀).2) →
      ∀ e ∈ persists (Node.step cfg s inp).2, e.2.round = 0 ∨ ∃ x y o,
        BuildState cfg U K s inp x ∧ Node.tryBuild cfg x = some (y, o) ∧ e ∈ persists o := by
    intro s₀ pre h₀ hp₀ hpre he e hev
    rw [he] at hb hev
    rw [persists_append] at hb hev
    rcases List.mem_append.mp hev with hev | hev
    · exact Or.inl (hpre e hev)
    · exact Or.inr (settle_witness hg h₀ hp₀ (fun e he => hb e (List.mem_append_right _ he))
        e hev)
  have hsame : Node.step cfg s inp = (s, []) →
      ∀ e ∈ persists (Node.step cfg s inp).2, e.2.round = 0 ∨ ∃ x y o,
        BuildState cfg U K s inp x ∧ Node.tryBuild cfg x = some (y, o) ∧ e ∈ persists o := by
    intro he e hev; rw [he] at hev; simp [persists] at hev
  cases inp with
  | start =>
    by_cases h₁ : s.top = none ∧ cfg.Admissible
    · by_cases h₂ : cfg.idOf cfg.genesis ∉ s.store.ids ∧
          rowValid cfg.q (Function.update s.store.blk (cfg.idOf cfg.genesis) cfg.genesis)
            cfg.genesis
      · let st := s.store.insert (cfg.idOf cfg.genesis) cfg.genesis h₂.1
          (fun _ hj => absurd hj (Finset.notMem_empty _))
          (fun j hj => absurd hj (Finset.notMem_empty j))
        have hx : (cfg.idOf cfg.genesis, cfg.genesis) ∈ K :=
          hb _ (by simp only [Node.step, dif_pos h₂, if_pos h₁]; simp [persists])
        have hrefs : cfg.genesis.refs ⊆ s.store.ids := fun _ hj => absurd hj (Finset.notMem_empty _)
        have hcst : IsCut U st := hc.insert (hg.real _ hx
          (fun _ hj => absurd hj (Finset.notMem_empty _))
          (validAt_of_cut hc h₂.1 hrefs h₂.2))
        let gid := cfg.idOf cfg.genesis
        let s₀ : State Validator BlockId Payload :=
          { s with store := st, top := some 0, own := some gid }
        have hh₀ : Held cfg s₀ :=
          ⟨fun t ht => ⟨_, Finset.mem_insert_self _ _, by
            change some 0 = some t at ht
            simp only [Option.some.injEq] at ht
            omega⟩, hh.junk⟩
        have ho₀ : OwnTop cfg s₀ := by
          intro r hr
          change some 0 = some r at hr
          rw [Option.some.injEq] at hr
          subst hr
          refine ⟨gid, rfl, Finset.mem_insert_self _ _, ?_, ?_⟩
          · change (st.blk gid).round = 0
            simp [st, gid, Store.blk, Store.insert, Std.TreeMap.getD_insert_self,
              Config.genesis]
          · change (st.blk gid).creator = cfg.me
            simp [st, gid, Store.blk, Store.insert, Std.TreeMap.getD_insert_self,
              Config.genesis]
        have hi₀ : Inv cfg s₀ K [] :=
          ⟨known_insert (hnew := h₂.1) (hrefs := fun _ hj => absurd hj (Finset.notMem_empty _))
              (hpred := fun j hj => absurd hj (Finset.notMem_empty j))
              (fun j hj => hi.known j hj) hx,
            fun x hx => hi.pend x hx,
            Or.inr ⟨0, rfl, ⟨by simp, fun x hx => absurd hx List.not_mem_nil⟩⟩,
            fun x hx => absurd hx List.not_mem_nil, fun x hx => absurd hx List.not_mem_nil,
            hi.valid.insert (hnew := h₂.1) (hrefs := fun _ hj => absurd hj (Finset.notMem_empty _))
              (hpred := fun j hj => absurd hj (Finset.notMem_empty j)) h₂.2⟩
        refine hset s₀ (built cfg [(cfg.idOf cfg.genesis, cfg.genesis)])
          ⟨hcst, hh₀, ho₀, (Grows.insert s.store : Grows s.store st), fun r hr => Or.inl hr,
            ⟨[], hi₀⟩⟩ hp ?_
          (by simp only [Node.step, dif_pos h₂, if_pos h₁]; rfl)
        intro e he
        simp only [built, persists, List.flatMap_cons, List.flatMap_nil, List.append_nil,
          List.filterMap_cons, List.filterMap_nil, List.mem_singleton] at he
        subst he
        rfl
      · exact hsame (by simp only [Node.step, dif_neg h₂, if_pos h₁])
    · exact hsame (by simp only [Node.step, if_neg h₁])
  | deliver id b =>
    by_cases hA : Admits cfg s id b
    · let s₁ := afterFlush (cfg := cfg) s id b
      let miss := missing s₁ id b
      have hx : (id, b) ∈ K := hd _ (by simp [delivered, hA.1])
      have hg₁ := Grows.flush (cfg := cfg) (s.pending.length + 1) s.store ((id, b) :: s.pending)
      have hpend : ∀ e ∈ (id, b) :: s.pending, e ∈ K := fun e he => by
        rcases List.mem_cons.mp he with rfl | he
        · exact hx
        · exact hp e he
      have hc₁ : IsCut U s₁.store := IsCut.flush hg _ _ hc hpend
      let s₂ := { s₁ with requested := s₁.requested ++ miss.map fun x => (x, id) }
      have hfl := flush_known (cfg := cfg) (K := K) (s.pending.length + 1) (st := s.store)
        (pend := (id, b) :: s.pending) (fun j hj => hi.known j hj) hi.valid hpend
      have hinv₂ : Inv cfg s₂ K B₀ :=
        ⟨hfl.1, hfl.2.1, hi.rounds, hi.good, hi.sub, hfl.2.2⟩
      refine hset s₂ (if miss.isEmpty then [] else [.fetch b.creator miss])
        ⟨hc₁, hh.grow hg₁ rfl, hown.grow hg₁ rfl rfl, hg₁, fun r hr => Or.inl hr, ⟨B₀, hinv₂⟩⟩
        (fun e he => hpend e (flush_pending_sub _ _ _ e he)) ?_ (step_deliver hA)
      intro e he
      split at he <;> simp [persists] at he
    · exact hsame (step_deliver_not hA)
  | timer r =>
    refine hset { s with fired := insert r s.fired } []
      ⟨hc, hh.grow (Grows.refl _) rfl, hown.grow (Grows.refl _) rfl rfl, Grows.refl _,
        fun t ht => ?_,
        ⟨B₀, hi.of_eq rfl rfl rfl⟩⟩ hp (by simp [persists]) rfl
    rcases Finset.mem_insert.mp ht with rfl | ht
    · exact Or.inr rfl
    · exact Or.inl ht
  | fetchRequest peer ids =>
    intro e he
    change e ∈ persists (answer s peer ids) at he
    unfold answer persists at he
    rw [List.filterMap_map] at he
    simp at he

variable (cfg) in
/-- **Outputs whose timers follow builds**: each timer set for round `r` is
set for `timeout r`, beside a block of round `r` persisted. -/
def TimersBuilt (out : List (Output Validator BlockId Payload)) : Prop :=
  ∀ r a, Output.setTimer r a ∈ out → a = cfg.timeout r ∧ ∃ e ∈ persists out, e.2.round = r

omit [Fintype Validator] in
theorem TimersBuilt.append {x y : List (Output Validator BlockId Payload)}
    (hx : TimersBuilt cfg x) (hy : TimersBuilt cfg y) : TimersBuilt cfg (x ++ y) := by
  intro r a h
  rw [persists_append]
  rcases List.mem_append.mp h with h | h
  · obtain ⟨ha, e, he, her⟩ := hx r a h
    exact ⟨ha, e, List.mem_append_left _ he, her⟩
  · obtain ⟨ha, e, he, her⟩ := hy r a h
    exact ⟨ha, e, List.mem_append_right _ he, her⟩

omit [Fintype Validator] in
theorem TimersBuilt.of_none {x : List (Output Validator BlockId Payload)}
    (h : ∀ r a, Output.setTimer r a ∉ x) : TimersBuilt cfg x :=
  fun r a hm => absurd hm (h r a)

omit [Fintype Validator] in
theorem timersBuilt_built (bs : List (BlockId × Block Validator BlockId Payload)) :
    TimersBuilt cfg (built cfg bs) := by
  intro r a h
  obtain ⟨e, he, ho⟩ := List.mem_flatMap.mp h
  simp only [List.mem_cons, List.not_mem_nil, or_false] at ho
  rcases ho with ho | ho | ho
  · cases ho
  · cases ho
  · simp only [Output.setTimer.injEq] at ho
    obtain ⟨rfl, rfl⟩ := ho
    refine ⟨rfl, e, ?_, rfl⟩
    rw [persists_built]
    exact he

omit [Fintype Validator] in
theorem timersBuilt_progress : ∀ (fuel : ℕ) (s : State Validator BlockId Payload),
    TimersBuilt cfg (Node.progress cfg fuel s).2
  | 0, _ => TimersBuilt.of_none fun _ _ h => by simp [Node.progress] at h
  | fuel + 1, s => by
    unfold Node.progress
    split
    · rename_i s₁ out hb
      obtain ⟨r, id, b, hnew, hrefs, hpred, -, -, -, -, -, -, -, -, -, hout⟩ :=
        tryBuild_some hb
      rw [hout]
      exact (timersBuilt_built _).append (timersBuilt_progress fuel s₁)
    · exact TimersBuilt.of_none fun _ _ h => by simp at h

omit [Fintype Validator] in
theorem timersBuilt_advance (s : State Validator BlockId Payload) :
    TimersBuilt cfg (Node.advance cfg s).2 := by
  simp only [Node.advance]
  refine (timersBuilt_progress _ s).append (TimersBuilt.of_none fun r a h => ?_)
  unfold Node.decideStep at h
  dsimp only at h
  split at h
  · obtain ⟨_, _, h⟩ := List.mem_map.mp h
    cases h
  · simp at h

variable (cfg) in
/-- **Outputs whose timers follow builds, or the timer's own firing**: each
timer set for round `r` is set for `timeout r`, beside a block of round
`r` persisted, or on round `r`'s timer. -/
def TimersSet (inp : Input Validator BlockId Payload)
    (out : List (Output Validator BlockId Payload)) : Prop :=
  ∀ r a, Output.setTimer r a ∈ out →
    a = cfg.timeout r ∧ ((∃ e ∈ persists out, e.2.round = r) ∨ inp = .timer r)

omit [Fintype Validator] in
theorem TimersBuilt.set {inp : Input Validator BlockId Payload}
    {out : List (Output Validator BlockId Payload)} (h : TimersBuilt cfg out) :
    TimersSet cfg inp out :=
  fun r a hm => ⟨(h r a hm).1, Or.inl (h r a hm).2⟩

/-- **A step sets its timers beside its builds.** -/
theorem timersBuilt_step (s : State Validator BlockId Payload)
    (inp : Input Validator BlockId Payload) : TimersSet cfg inp (Node.step cfg s inp).2 := by
  have hset : ∀ s₀ : State Validator BlockId Payload, TimersBuilt cfg (Node.settle cfg s₀).2 :=
    fun s₀ =>
      (quiesce_rel (P := fun _ => True) (R := fun _ out _ => TimersBuilt cfg out)
        (fun _ => TimersBuilt.of_none fun _ _ h => absurd h List.not_mem_nil)
        (fun _ _ _ _ _ h₁ h₂ => h₁.append h₂) (fun s _ => ⟨timersBuilt_advance s, trivial⟩) _ s₀
        trivial).1
  refine TimersBuilt.set ?_
  cases inp with
  | start =>
    simp only [Node.step]
    split
    · split
      · exact (timersBuilt_built (cfg := cfg) [(cfg.idOf cfg.genesis, cfg.genesis)]).append
          (hset _)
      · exact TimersBuilt.of_none fun _ _ h => by simp at h
    · exact TimersBuilt.of_none fun _ _ h => by simp at h
  | deliver id b =>
    simp only [Node.step]
    split
    · refine (TimersBuilt.of_none fun r a h => ?_).append (hset _)
      split at h <;> simp at h
    · exact TimersBuilt.of_none fun _ _ h => by simp at h
  | timer t => exact hset _
  | fetchRequest peer ids =>
    refine TimersBuilt.of_none fun r a h => ?_
    change Output.setTimer r a ∈ answer s peer ids at h
    unfold answer at h
    simp at h

omit [Fintype Validator] [DecidableEq Validator] in
/-- **A cut's paths are the record's**: what a stored block reaches in the
store it reaches in the record. -/
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
    (hready : reachReady cfg st refs r = true) (hrefs : refs ⊆ st.ids) {k m : ℕ}
    (hm : m < cfg.p.voteOffset) (hk : cfg.slots.slotRound k + m = r)
    (hlead : cfg.slots.leader k ∈ H) {L : BlockId} (hL : IsLeaderBlock (S := cfg.slots) U k L)
    {c : BlockId} (hcrefs : (U.block c).refs = refs) : Reaches U c L := by
  unfold reachReady at hready
  have h₁ := List.all_eq_true.mp hready m (List.mem_range.mpr hm)
  rw [if_pos (by omega)] at h₁
  have h₂ := List.all_eq_true.mp h₁ k (by rw [← hk, Nat.add_sub_cancel]; exact mem_slotsAt k)
  obtain ⟨L', hL', c', hc', hhist⟩ := of_decide_eq_true h₂
  obtain ⟨hL's, hL'c, hL'r⟩ := Finset.mem_filter.mp hL'
  have hreach : ReachesFrom U.block c' L' :=
    hc.reachesFrom (hrefs hc') (reaches_of_mem_historyUptoFrom hhist)
  have hlead' : IsLeaderBlock (S := cfg.slots) U k L' :=
    ⟨(hc L' hL's).1, by rw [hc.round hL's]; exact hL'r, by rw [hc.creator hL's]; exact hL'c⟩
  rw [isLeaderBlock_unique_of_honest (S := cfg.slots) hlead hL hlead']
  exact Relation.ReflTransGen.head (show c' ∈ (U.block c).refs by rw [hcrefs]; exact hc') hreach

omit [Fintype Validator] in
/-- **`refsFor` on a cut references each stored block of an honest author
at its round**, given the node's own block there as `o` if the author is
the node. -/
theorem mem_refsFor_of_cut {U : BlockRecord Validator BlockId Payload P H}
    {st : Store Validator BlockId Payload} (hc : IsCut U st) {r : ℕ} {o : Option BlockId}
    {b : BlockId} (hb : b ∈ st.ids) (hbr : (st.blk b).round = r)
    (hhon : (st.blk b).creator ∈ H)
    (ho : (st.blk b).creator = cfg.me → ∃ j, o = some j ∧ j ∈ st.ids ∧
      (st.blk j).round = r ∧ (st.blk j).creator = cfg.me) :
    b ∈ refsFor cfg st r o := by
  have huniq : ∀ i ∈ st.ids, (st.blk i).round = r → (st.blk i).creator = (st.blk b).creator →
      i = b := fun i hi hir hic =>
    U.no_equivocation i (hc i hi).1 b (hc b hb).1 (by rw [hc.creator hi, hic]; exact hhon)
      (by rw [hc.creator hi, hc.creator hb, hic]) (by rw [hc.round hi, hc.round hb, hir, hbr])
  refine mem_refsFor hb hbr huniq fun hme => ?_
  obtain ⟨j, hoj, hj, hjr, hjc⟩ := ho hme
  rw [hoj, huniq j hj hjr (by rw [hjc, hme])]

omit [Fintype Validator] in
/-- **The certificate test, read on the record**: where votes are
certified a round later, a block of round `r + 1` whose references pass
the certificate test on a cut certifies, in the record, the block of each
honest leader of a slot whose vote round is `r`. -/
theorem isCert_of_certReady [P.Mechanised] (hσ : cfg.σ = boundedSel)
    {U : BlockRecord Validator BlockId Payload P H} {st : Store Validator BlockId Payload}
    (hc : IsCut U st) {refs : Finset BlockId} {r : ℕ} (hready : certReady cfg st refs r = true)
    (hrefs : refs ⊆ st.ids) (hvc : cfg.p.voteIsCert = false) {k : ℕ}
    (hk : cfg.slots.slotRound k + cfg.p.voteOffset = r) (hlead : cfg.slots.leader k ∈ H)
    {L : BlockId} (hL : IsLeaderBlock (S := cfg.slots) U k L) {c : BlockId}
    (hcrefs : (U.block c).refs = refs) : Scheme.IsCert cfg.p boundedSel U c L := by
  unfold certReady at hready
  rw [hvc, if_neg (by simp), if_pos (by omega)] at hready
  have h₂ := List.all_eq_true.mp hready k
    (by rw [← hk, Nat.add_sub_cancel]; exact mem_slotsAt k)
  obtain ⟨L', hL', hcount⟩ := of_decide_eq_true h₂
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
