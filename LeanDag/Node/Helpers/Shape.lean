import LeanDag.Node.Helpers.Reliable
/-!
# The shape of a reliable node's step

`docs/validator.md` §5.2. A pass builds every round from the top it
starts at up to the top it reaches, at rounds above that top, each with
its timer, and keeps the fired timers (`PassShape`). A step either changes
nothing and outputs no block and no timer, or settles a state with the
same top (`step_shape`). A node whose round's timer fired, or whose
references pass the tests, builds given a quorum of the round
(`tryBuild_isSome`).
-/

namespace LeanDag

namespace Node

variable {Validator BlockId Payload : Type} [Fintype Validator] [DecidableEq Validator]
variable [LinearOrder BlockId]
variable {cfg : Config Validator BlockId Payload}

/-- **Silent outputs**: no block and no timer. -/
def Silent (out : List (Output Validator BlockId Payload)) : Prop :=
  persists out = [] ∧ ∀ r a, Output.setTimer r a ∉ out

omit [Fintype Validator] [DecidableEq Validator] [LinearOrder BlockId] in
theorem Silent.nil : Silent ([] : List (Output Validator BlockId Payload)) :=
  ⟨rfl, fun _ _ h => absurd h List.not_mem_nil⟩

omit [Fintype Validator] [DecidableEq Validator] [LinearOrder BlockId] in
theorem Silent.of_quiet {x : List (Output Validator BlockId Payload)}
    (h : ∀ o ∈ x, (∀ id b, o ≠ .persist id b) ∧ ∀ r a, o ≠ .setTimer r a) : Silent x := by
  refine ⟨List.filterMap_eq_nil_iff.mpr fun o ho => ?_, fun r a hr => (h _ hr).2 r a rfl⟩
  cases o with
  | persist id b => exact absurd rfl ((h _ ho).1 id b)
  | _ => rfl

/-! ## Through one pass -/

omit [Fintype Validator] in
theorem tryBuild_fired {s s' : State Validator BlockId Payload}
    {out : List (Output Validator BlockId Payload)} (h : tryBuild cfg s = some (s', out)) :
    s'.fired = s.fired := by
  unfold tryBuild at h
  split at h
  · dsimp only at h
    split at h
    · split at h
      · rw [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, -⟩ := h
        rfl
      · cases h
    · cases h
  · cases h

omit [Fintype Validator] in
/-- **Building** keeps the fired timers, and builds
every round above the top it starts at up to the top it reaches, above
that top. -/
theorem progress_shape : ∀ (fuel : ℕ) (s : State Validator BlockId Payload),
    let p := Node.progress cfg fuel s
    p.1.fired = s.fired ∧ (s.top = none → p.1.top = none) ∧
      (∀ e ∈ persists p.2, s.top.getD 0 < e.2.round) ∧
      (s.top.isSome → ∀ ρ, s.top.getD 0 < ρ → ρ ≤ p.1.top.getD 0 →
        ∃ e ∈ persists p.2, e.2.round = ρ)
  | 0, s => ⟨rfl, id, fun e he => absurd he (by simp [Node.progress, persists]),
      fun _ ρ h₁ h₂ => absurd h₂ (by simp [Node.progress]; omega)⟩
  | fuel + 1, s => by
    intro p
    unfold p Node.progress
    split
    · rename_i s₁ out hb
      obtain ⟨r, id, b, -, -, -, hr, hbr, -, -, -, -, ht₁, -, -, hout⟩ := tryBuild_some hb
      have hf := tryBuild_fired hb
      obtain ⟨ih₂, -, ih₃, ih₄⟩ := progress_shape fuel s₁
      dsimp only
      have hp : persists (out ++ (Node.progress cfg fuel s₁).2) =
          (id, b) :: persists (Node.progress cfg fuel s₁).2 := by
        rw [persists_append, hout, persists_built]; rfl
      refine ⟨ih₂.trans hf, (fun h => by rw [hr] at h; cases h), fun e he => ?_,
        fun _ ρ h₁ h₂ => ?_⟩
      · rw [hp] at he
        rcases List.mem_cons.mp he with rfl | he
        · rw [hr]; simp [hbr]
        · have := ih₃ e he
          rw [ht₁] at this; rw [hr]; simp only [Option.getD_some] at this ⊢; omega
      · rw [hp]
        rw [hr] at h₁
        simp only [Option.getD_some] at h₁
        by_cases hρ : ρ = r + 1
        · exact ⟨(id, b), List.mem_cons_self .., by rw [hbr, hρ]⟩
        · obtain ⟨e, he, her⟩ := ih₄ (by rw [ht₁]; rfl) ρ (by rw [ht₁]; simp; omega) h₂
          exact ⟨e, List.mem_cons_of_mem _ he, her⟩
    · exact ⟨rfl, id, fun e he => absurd he (by simp [persists]),
        fun _ ρ h₁ h₂ => absurd h₂ (by simp only; omega)⟩

omit [Fintype Validator] in
theorem decideStep_shape (s : State Validator BlockId Payload) :
    let d := Node.decideStep cfg s
    d.1.fired = s.fired ∧ d.1.top = s.top ∧ d.1.store = s.store ∧
      Silent d.2 := by
  intro d
  unfold d Node.decideStep
  dsimp only
  split
  · refine ⟨rfl, rfl, rfl, Silent.of_quiet fun o h => ?_⟩
    obtain ⟨_, -, rfl⟩ := List.mem_map.mp h
    exact ⟨fun _ _ h => (nomatch h), fun _ _ h => (nomatch h)⟩
  · exact ⟨rfl, rfl, rfl, Silent.nil⟩

omit [Fintype Validator] in
theorem timer_of_built {bs : List (BlockId × Block Validator BlockId Payload)}
    {e : BlockId × Block Validator BlockId Payload} (he : e ∈ bs) :
    Output.setTimer e.2.round (cfg.timeout e.2.round) ∈ built cfg bs :=
  List.mem_flatMap.mpr ⟨e, he, by simp⟩

variable (cfg) in
/-- **The shape of a pass**: its blocks lie above the top it starts at,
one at each round up to the top it reaches, each with its timer; it keeps
the fired timers and rises. -/
structure PassShape (s : State Validator BlockId Payload)
    (out : List (Output Validator BlockId Payload)) (s' : State Validator BlockId Payload) :
    Prop where
  above : ∀ e ∈ persists out, s.top.getD 0 < e.2.round
  every : s.top.isSome → ∀ ρ, s.top.getD 0 < ρ → ρ ≤ s'.top.getD 0 →
    ∃ e ∈ persists out, e.2.round = ρ
  timer : ∀ e ∈ persists out, Output.setTimer e.2.round (cfg.timeout e.2.round) ∈ out
  fired : s.fired ⊆ s'.fired
  rises : Rises s s'
  none : s.top = none → s'.top = none

theorem PassShape.refl (s : State Validator BlockId Payload) : PassShape cfg s [] s :=
  ⟨fun e he => absurd he (by simp [persists]),
    fun _ ρ h₁ h₂ => absurd h₂ (by omega), fun e he => absurd he (by simp [persists]),
    subset_rfl, Rises.refl s, id⟩

theorem PassShape.trans {a b c : State Validator BlockId Payload}
    {o₁ o₂ : List (Output Validator BlockId Payload)} (h₁ : PassShape cfg a o₁ b)
    (h₂ : PassShape cfg b o₂ c) : PassShape cfg a (o₁ ++ o₂) c := by
  have hab := h₁.rises
  have hbc := h₂.rises
  refine ⟨fun e he => ?_, fun hs ρ hρ₁ hρ₂ => ?_, fun e he => ?_,
    h₁.fired.trans h₂.fired, hab.trans hbc, fun h => h₂.none (h₁.none h)⟩
  · rw [persists_append] at he
    rcases List.mem_append.mp he with he | he
    · exact h₁.above e he
    · exact lt_of_le_of_lt hab.1 (h₂.above e he)
  · rw [persists_append]
    by_cases hρ : ρ ≤ b.top.getD 0
    · obtain ⟨e, he, her⟩ := h₁.every hs ρ hρ₁ hρ
      exact ⟨e, List.mem_append_left _ he, her⟩
    · obtain ⟨e, he, her⟩ := h₂.every (hab.2.1 hs) ρ (by omega) hρ₂
      exact ⟨e, List.mem_append_right _ he, her⟩
  · rw [persists_append] at he
    rcases List.mem_append.mp he with he | he
    · exact List.mem_append_left _ (h₁.timer e he)
    · exact List.mem_append_right _ (h₂.timer e he)

/-- **The shape of one pass.** -/
theorem advance_shape (s : State Validator BlockId Payload) :
    PassShape cfg s (Node.advance cfg s).2 (Node.advance cfg s).1 := by
  obtain ⟨p₂, p₀, p₃, p₄⟩ := progress_shape (cfg := cfg) (s.store.topRound + 2) s
  obtain ⟨bs, hbs⟩ := progress_built (cfg := cfg) (s.store.topRound + 2) s
  have hra := rises_advance (cfg := cfg) s
  generalize hP : Node.progress cfg (s.store.topRound + 2) s = P at p₂ p₀ p₃ p₄ hbs
  obtain ⟨d₂, d₃, -, d₅⟩ := decideStep_shape (cfg := cfg) P.1
  generalize hD : Node.decideStep cfg P.1 = D at d₂ d₃ d₅
  have hadv : Node.advance cfg s = ({ D.1 with
      store := (flush cfg (D.1.pending.length + 1) D.1.store D.1.pending).1,
      pending := (flush cfg (D.1.pending.length + 1) D.1.store D.1.pending).2 },
      P.2 ++ D.2) := by
    simp only [Node.advance, hP, hD]
  rw [hadv] at hra ⊢
  have hpers : persists (P.2 ++ D.2) = bs := by
    rw [persists_append, hbs, persists_built, d₅.1]; simp
  refine ⟨fun e he => ?_, fun hs ρ h₁ h₂ => ?_, fun e he => ?_, ?_, hra, fun h => ?_⟩
  · rw [hpers] at he
    exact p₃ e (by rw [hbs, persists_built]; exact he)
  · rw [hpers]
    obtain ⟨e, he, her⟩ := p₄ hs ρ h₁ (by
      change ρ ≤ D.1.top.getD 0 at h₂
      rw [d₃] at h₂; exact h₂)
    rw [hbs, persists_built] at he
    exact ⟨e, he, her⟩
  · rw [hpers] at he
    rw [hbs]
    exact List.mem_append_left _ (timer_of_built he)
  · change s.fired ⊆ D.1.fired
    rw [d₂, p₂]
  · change D.1.top = none
    rw [d₃]; exact p₀ h

theorem quiesce_shape (n : ℕ) (s : State Validator BlockId Payload) :
    PassShape cfg s (quiesce cfg n s).2 (quiesce cfg n s).1 :=
  (quiesce_rel (P := fun _ => True) (R := PassShape cfg) PassShape.refl
    (fun _ _ _ _ _ h₁ h₂ => h₁.trans h₂) (fun s _ => ⟨advance_shape s, trivial⟩) n s trivial).1

/-! ## A settle and a step -/

/-- **A settle** has the shape of its passes. -/
theorem settle_shape (x : State Validator BlockId Payload) :
    PassShape cfg x (Node.settle cfg x).2 (Node.settle cfg x).1 :=
  quiesce_shape _ x

omit [Fintype Validator] [DecidableEq Validator] [LinearOrder BlockId] in
theorem silent_of {x : List (Output Validator BlockId Payload)}
    (h : ∀ o ∈ x, match o with
      | .persist _ _ => False | .setTimer _ _ => False | _ => True) :
    Silent x :=
  Silent.of_quiet fun o ho => by
    have := h o ho
    refine ⟨fun id b he => ?_, fun r a he => ?_⟩ <;> subst he <;> exact this

/-- **The shape of a step**: it leaves the state alone with silent
outputs, or settles a state with the node's top and fired timers, after
outputs persisting nothing or, at its start, after its genesis block with
its timer. -/
theorem step_shape (s : State Validator BlockId Payload) (inp : Input Validator BlockId Payload) :
    ((Node.step cfg s inp).1 = s ∧ Silent (Node.step cfg s inp).2) ∨
    ∃ x pre, Node.step cfg s inp = ((Node.settle cfg x).1, pre ++ (Node.settle cfg x).2) ∧
      x.top.getD 0 = s.top.getD 0 ∧ s.fired ⊆ x.fired ∧
      ((persists pre = [] ∧ x.top = s.top) ∨ (s.top = none ∧ x.top = some 0 ∧
        ∃ g : BlockId × Block Validator BlockId Payload,
          pre = [.persist g.1 g.2, .broadcast g.1 g.2, .setTimer 0 (cfg.timeout 0)] ∧
          g.2.round = 0 ∧ g.1 ∈ x.store.ids ∧ (x.store.blk g.1).round = 0)) := by
  have hq : ∀ x, x = s → ((x, ([] : List (Output Validator BlockId Payload))).1 = s ∧
      Silent ([] : List (Output Validator BlockId Payload))) := fun x hx => ⟨hx, Silent.nil⟩
  have hnil : ∀ x : State Validator BlockId Payload,
      (Node.settle cfg x) = ((Node.settle cfg x).1, [] ++ (Node.settle cfg x).2) := fun x => by
    simp
  cases inp with
  | start =>
    simp only [Node.step]
    split
    · rename_i h₁
      split
      · rename_i h₂
        refine Or.inr ⟨_, _, rfl, by simp [h₁.1], subset_rfl, Or.inr ⟨h₁.1, rfl,
          ⟨_, cfg.genesis⟩, rfl, rfl, Finset.mem_insert_self _ _, ?_⟩⟩
        simp [Store.blk, Store.insert, Std.TreeMap.getD_insert_self, Config.genesis]
      · exact Or.inl (hq s rfl)
    · exact Or.inl (hq s rfl)
  | deliver id b =>
    by_cases hA : Admits cfg s id b
    · rw [step_deliver hA]
      refine Or.inr ⟨_, _, rfl, rfl, subset_rfl, Or.inl ⟨?_, rfl⟩⟩
      refine (silent_of fun o ho => ?_).1
      split at ho
      · cases ho
      · rw [List.mem_singleton] at ho; subst ho; trivial
    · rw [step_deliver_not hA]
      exact Or.inl ⟨rfl, Silent.nil⟩
  | timer r =>
    exact Or.inr ⟨{ s with fired := insert r s.fired }, [], hnil _, rfl,
      Finset.subset_insert _ _, Or.inl ⟨rfl, rfl⟩⟩
  | fetchRequest p ids =>
    refine Or.inl ⟨rfl, silent_of fun o ho => ?_⟩
    simp only [Node.step, answer, List.mem_map] at ho
    obtain ⟨j, -, rfl⟩ := ho; trivial

section StepFacts

variable {s : State Validator BlockId Payload} {inp : Input Validator BlockId Payload}

/-- **A step builds every round above the top before up to the top it
reaches.** -/
theorem step_every
    (hsome : (Node.step cfg s inp).1.top.isSome) :
    ∀ ρ, (s.top = none ∨ s.top.getD 0 < ρ) → ρ ≤ (Node.step cfg s inp).1.top.getD 0 →
      ∃ e ∈ persists (Node.step cfg s inp).2, e.2.round = ρ := by
  intro ρ hρ hρt
  rcases step_shape (cfg := cfg) s inp with ⟨he, -⟩ | ⟨x, pre, he, ht, -, hpre⟩
  · rw [he] at hsome hρt
    rcases hρ with hρ | hρ
    · rw [hρ] at hsome; cases hsome
    · omega
  · rw [he] at hsome hρt ⊢
    rw [persists_append]
    have hS := settle_shape (cfg := cfg) x
    rcases hpre with ⟨-, hxt⟩ | ⟨hn, hx0, g, rfl, hg, -⟩
    · by_cases hn : s.top = none
      · have := hS.none (by rw [hxt, hn])
        rw [this] at hsome; cases hsome
      · have hρ' : s.top.getD 0 < ρ := hρ.resolve_left hn
        obtain ⟨e, he', her⟩ := hS.every (by
          rw [hxt]; exact Option.ne_none_iff_isSome.mp hn) ρ
          (by rw [ht]; exact hρ') hρt
        exact ⟨e, List.mem_append_right _ he', her⟩
    · by_cases h0 : ρ = 0
      · exact ⟨g, List.mem_append_left _ (by simp [persists]), by rw [hg, h0]⟩
      · obtain ⟨e, he', her⟩ := hS.every (by rw [hx0]; rfl) ρ
          (by rw [hx0]; simp; omega) hρt
        exact ⟨e, List.mem_append_right _ he', her⟩

/-- **A step sets the timer of each round it builds.** -/
theorem step_timer :
    ∀ e ∈ persists (Node.step cfg s inp).2,
      Output.setTimer e.2.round (cfg.timeout e.2.round) ∈ (Node.step cfg s inp).2 := by
  rcases step_shape (cfg := cfg) s inp with ⟨-, hq⟩ | ⟨x, pre, he, -, -, hpre⟩
  · rw [hq.1]; intro e he; cases he
  · rw [he, persists_append]
    intro e he'
    rcases List.mem_append.mp he' with he' | he'
    · rcases hpre with ⟨hp, -⟩ | ⟨-, -, g, rfl, hg, -⟩
      · rw [hp] at he'; cases he'
      · simp only [persists] at he'
        simp at he'
        subst he'
        rw [hg]
        exact List.mem_append_left _ (by simp)
    · exact List.mem_append_right _ ((settle_shape (cfg := cfg) x).timer e he')

/-- **A step keeps the fired timers.** -/
theorem step_fired : s.fired ⊆ (Node.step cfg s inp).1.fired := by
  rcases step_shape (cfg := cfg) s inp with ⟨he, -⟩ | ⟨x, pre, he, -, hf, -⟩
  · rw [he]
  · rw [he]
    exact hf.trans (settle_shape (cfg := cfg) x).fired

end StepFacts

/-! ## Building on a timer -/

omit [Fintype Validator] in
/-- **`refsFor`'s references**: stored blocks of the round, one per
author of the round, the node's own block for itself if it has one. -/
theorem refsFor_spec {st : Store Validator BlockId Payload} {r : ℕ} {o : Option BlockId}
    (ho : ∀ j, o = some j → j ∈ st.ids ∧ (st.blk j).round = r ∧ (st.blk j).creator = cfg.me) :
    refsFor cfg st r o ⊆ st.ids ∧ (∀ j ∈ refsFor cfg st r o, (st.blk j).round = r) ∧
      creatorsOf st.blk (refsFor cfg st r o) = authorsIn st.toRecord st.ids r ∧
      ∀ i ∈ refsFor cfg st r o, ∀ j ∈ refsFor cfg st r o,
        (st.blk i).creator = (st.blk j).creator → i = j := by
  set R := blocksAt st.toRecord r with hR
  have hRi : ∀ i ∈ R, i ∈ st.ids ∧ (st.blk i).round = r := fun i hi => by
    simpa [hR, blocksAt, Store.toRecord] using hi
  -- the block chosen for author `a`
  let pick : Validator → Finset BlockId := fun a =>
    if a = cfg.me ∧ o.isSome then o.toFinset
    else (Scheme.leastOf (R.filter fun i => (st.blk i).creator = a)).toFinset
  have hpick : ∀ a ∈ creatorsOf st.blk R, ∃ j, pick a = {j} ∧ j ∈ st.ids ∧
      (st.blk j).round = r ∧ (st.blk j).creator = a := by
    intro a ha
    by_cases hc : a = cfg.me ∧ o.isSome
    · obtain ⟨j, hj⟩ := Option.isSome_iff_exists.mp hc.2
      obtain ⟨h₁, h₂, h₃⟩ := ho j hj
      refine ⟨j, ?_, h₁, h₂, by rw [h₃, hc.1]⟩
      show (if a = cfg.me ∧ o.isSome then o.toFinset else _) = {j}
      rw [if_pos hc, hj]; rfl
    · obtain ⟨i, hi, hia⟩ := Finset.mem_image.mp ha
      have hne : (R.filter fun i => (st.blk i).creator = a).Nonempty :=
        ⟨i, Finset.mem_filter.mpr ⟨hi, hia⟩⟩
      obtain ⟨L, hL⟩ : ∃ L, Scheme.leastOf (R.filter fun i => (st.blk i).creator = a) = some L := by
        unfold Scheme.leastOf; rw [dif_pos hne]; exact ⟨_, rfl⟩
      obtain ⟨hLm, -⟩ := Scheme.leastOf_eq_some hL
      obtain ⟨hLR, hLa⟩ := Finset.mem_filter.mp hLm
      refine ⟨L, ?_, (hRi L hLR).1, (hRi L hLR).2, hLa⟩
      show (if a = cfg.me ∧ o.isSome then o.toFinset else _) = {L}
      rw [if_neg hc, hL]; rfl
  have hdef : refsFor cfg st r o = (creatorsOf st.blk R).biUnion pick := rfl
  have hmem : ∀ j ∈ refsFor cfg st r o, ∃ a ∈ creatorsOf st.blk R, j ∈ st.ids ∧
      (st.blk j).round = r ∧ (st.blk j).creator = a ∧ pick a = {j} := by
    intro j hj
    rw [hdef] at hj
    obtain ⟨a, ha, hja⟩ := Finset.mem_biUnion.mp hj
    obtain ⟨j', hp, h₁, h₂, h₃⟩ := hpick a ha
    rw [hp, Finset.mem_singleton] at hja
    subst hja
    exact ⟨a, ha, h₁, h₂, h₃, hp⟩
  refine ⟨fun j hj => (hmem j hj).choose_spec.2.1, fun j hj => (hmem j hj).choose_spec.2.2.1,
    ?_, fun i hi j hj hij => ?_⟩
  · have hauth : authorsIn st.toRecord st.ids r = creatorsOf st.blk R := rfl
    rw [hauth]
    ext a
    constructor
    · intro ha
      obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp ha
      obtain ⟨a', ha', -, -, hja, -⟩ := hmem j hj
      rw [hja]; exact ha'
    · intro ha
      obtain ⟨j, hp, -, -, hja⟩ := hpick a ha
      refine Finset.mem_image.mpr ⟨j, ?_, hja⟩
      rw [hdef]
      exact Finset.mem_biUnion.mpr ⟨a, ha, by rw [hp]; exact Finset.mem_singleton_self _⟩
  · obtain ⟨a, -, -, -, hia, hpa⟩ := hmem i hi
    obtain ⟨b', -, -, -, hjb, hpb⟩ := hmem j hj
    have hab : a = b' := by rw [← hia, ← hjb]; exact hij
    subst hab
    rw [hpa] at hpb
    exact (Finset.singleton_inj.mp hpb).symm.symm ▸ rfl

omit [Fintype Validator] in
/-- `refsAt`'s references are `refsFor`'s, or ones the node can build on. -/
theorem refsAt_buildable (st : Store Validator BlockId Payload) (r : ℕ) (o : Option BlockId) :
    refsAt cfg st r o = refsFor cfg st r o ∨ buildable cfg st r (refsAt cfg st r o) = true := by
  unfold refsAt
  dsimp only
  split
  · exact Or.inl rfl
  · rcases hf : List.find? _ _ with _ | R
    · exact Or.inl rfl
    · right
      have := List.find?_some hf
      simp only [Bool.and_eq_true] at this
      simpa using this.2

omit [Fintype Validator] in
/-- **A node whose round's timer fired, or whose references pass the
tests, builds**, given a quorum of the round, its own block there stored,
and no stored block with the identifier of a next block of its own. -/
theorem tryBuild_isSome {s : State Validator BlockId Payload} {r : ℕ} (ht : s.top = some r)
    (hf : r ∈ s.fired ∨ (reachReady cfg s.store (refsAt cfg s.store r s.own) r = true ∧
      certReady cfg s.store (refsAt cfg s.store r s.own) r = true))
    (hq : cfg.q ≤ (authorsIn s.store.toRecord s.store.ids r).card)
    (ho : ∀ j, s.own = some j → j ∈ s.store.ids ∧ (s.store.blk j).round = r ∧
      (s.store.blk j).creator = cfg.me)
    (hfresh : ∀ R, cfg.idOf ⟨r + 1, cfg.me, R, cfg.payload (r + 1)⟩ ∉ s.store.ids) :
    (tryBuild cfg s).isSome := by
  unfold tryBuild
  rw [ht]
  dsimp only
  rw [if_pos ⟨hq, hf⟩]
  have hB : buildable cfg s.store r (refsAt cfg s.store r s.own) = true := by
    rcases refsAt_buildable (cfg := cfg) s.store r s.own with he | he
    · rw [he]
      obtain ⟨hsub, hrd, hcr, hdis⟩ := refsFor_spec (cfg := cfg) (st := s.store) (r := r) ho
      have hnin : ∀ j ∈ refsFor cfg s.store r s.own,
          j ≠ cfg.idOf ⟨r + 1, cfg.me, refsFor cfg s.store r s.own, cfg.payload (r + 1)⟩ :=
        fun j hj h => hfresh _ (h ▸ hsub hj)
      unfold buildable
      refine decide_eq_true ⟨hfresh _, hsub, fun j hj => by simp; rw [hrd j hj],
        ⟨fun j hj => ?_, fun _ => ?_, fun i hi j hj hij => ?_⟩⟩
      · simp only at hj ⊢
        rw [Function.update_of_ne (hnin j hj), hrd j hj]
      · simp only [creators, creatorsOf]
        rw [Finset.image_congr (g := fun i => (s.store.blk i).creator)
          (fun j hj => by simp only; rw [Function.update_of_ne (hnin j hj)])]
        change cfg.q ≤ (creatorsOf s.store.blk _).card
        rw [hcr]; exact hq
      · simp only at hi hj hij
        rw [Function.update_of_ne (hnin i hi), Function.update_of_ne (hnin j hj)] at hij
        exact hdis i hi j hj hij
    · exact he
  unfold buildable at hB
  rw [dif_pos (of_decide_eq_true hB)]
  rfl

end Node

end LeanDag
