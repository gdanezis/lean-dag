import LeanDag.Node.Helpers.Reliable
/-!
# The shape of a reliable node's step

`docs/validator.md` §5.2. A pass builds every round from the top it
starts at up to the top it reaches, at rounds above that top, each with
its retry timer, and keeps the fired timers (`PassShape`). A step either
changes nothing and outputs no block and no timer, or settles a state
with the same top (`step_shape`). A node whose round's timer fired, that
is behind the round above, or whose references pass the tests, builds
given a quorum of the round (`tryBuild_isSome`).
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
    s'.fired = s.fired ∧ s'.recovering = false := by
  obtain ⟨_, _, _, -, h, -⟩ := tryBuild_cases h
  unfold buildAbove at h
  dsimp only at h
  split at h
  · split at h
    · rw [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, -⟩ := h
      exact ⟨release_fired _, release_recovering _⟩
    · cases h
  · cases h

omit [Fintype Validator] in
theorem decideStep_recovering (s : State Validator BlockId Payload) :
    (Node.decideStep cfg s).1.recovering = s.recovering := by
  unfold Node.decideStep
  dsimp only
  split
  · exact release_recovering _
  · rfl

omit [Fintype Validator] in
/-- **Building** keeps the fired timers; builds above the top it starts at;
when it starts not recovering, builds every round up to the top it
reaches and stays not recovering; and builds the top it reaches. -/
theorem progress_shape : ∀ (fuel : ℕ) (s : State Validator BlockId Payload),
    let p := Node.progress cfg fuel s
    p.1.fired = s.fired ∧ (s.top = none → p.1.top = none) ∧
      (∀ e ∈ persists p.2, s.top.getD 0 < e.2.round) ∧
      (s.top.isSome → s.recovering = false → ∀ ρ, s.top.getD 0 < ρ → ρ ≤ p.1.top.getD 0 →
        ∃ e ∈ persists p.2, e.2.round = ρ) ∧
      (s.recovering = false → p.1.recovering = false) ∧
      (p.1.top ≠ s.top → ∃ e ∈ persists p.2, p.1.top = some e.2.round) ∧
      (p.1.top ≠ s.top → p.1.recovering = false)
  | 0, s => ⟨rfl, id, fun e he => absurd he (by simp [Node.progress, persists]),
      fun _ _ ρ h₁ h₂ => absurd h₂ (by simp [Node.progress]; omega), id,
      fun h => absurd rfl h, fun h => absurd rfl h⟩
  | fuel + 1, s => by
    intro p
    unfold p Node.progress
    split
    · rename_i s₁ out hb
      obtain ⟨r, id, b, -, -, -, hr, hbr, -, -, -, -, ht₁, -, -, hout⟩ := tryBuild_some hb
      obtain ⟨hf, hrec₁⟩ := tryBuild_fired hb
      obtain ⟨ih₂, -, ih₃, ih₄, ih₅, ih₆, -⟩ := progress_shape fuel s₁
      dsimp only
      have hp : persists (out ++ (Node.progress cfg fuel s₁).2) =
          (id, b) :: persists (Node.progress cfg fuel s₁).2 := by
        rw [persists_append, hout, persists_built]; rfl
      have hsr : s.top.getD 0 ≤ r := hr.2.1
      refine ⟨ih₂.trans hf, (fun h => by rw [h] at hr; exact absurd hr.1 (by simp)),
        fun e he => ?_, fun _ hrec ρ h₁ h₂ => ?_, fun _ => ih₅ hrec₁, fun _ => ?_,
        fun _ => ih₅ hrec₁⟩
      · rw [hp] at he
        rcases List.mem_cons.mp he with rfl | he
        · simp only [hbr]; omega
        · have := ih₃ e he
          rw [ht₁] at this; simp only [Option.getD_some] at this; omega
      · rw [hp]
        have hrt : s.top = some r := hr.2.2 hrec
        rw [hrt] at h₁
        simp only [Option.getD_some] at h₁
        by_cases hρ : ρ = r + 1
        · exact ⟨(id, b), List.mem_cons_self .., by rw [hbr, hρ]⟩
        · obtain ⟨e, he, her⟩ := ih₄ (by rw [ht₁]; rfl) hrec₁ ρ (by rw [ht₁]; simp; omega) h₂
          exact ⟨e, List.mem_cons_of_mem _ he, her⟩
      · rw [hp]
        by_cases hpt : (Node.progress cfg fuel s₁).1.top = s₁.top
        · exact ⟨(id, b), List.mem_cons_self .., by rw [hpt, ht₁, hbr]⟩
        · obtain ⟨e, he, het⟩ := ih₆ hpt
          exact ⟨e, List.mem_cons_of_mem _ he, het⟩
    · exact ⟨rfl, id, fun e he => absurd he (by simp [persists]),
        fun _ _ ρ h₁ h₂ => absurd h₂ (by simp only; omega), id, fun h => absurd rfl h,
        fun h => absurd rfl h⟩

omit [Fintype Validator] in
theorem decideStep_shape (s : State Validator BlockId Payload) :
    let d := Node.decideStep cfg s
    d.1.fired = s.fired ∧ d.1.top = s.top ∧ d.1.disk = s.disk ∧
      Silent d.2 := by
  intro d
  unfold d Node.decideStep
  dsimp only
  split
  · refine ⟨release_fired _, release_top _, release_disk _, Silent.of_quiet fun o h => ?_⟩
    obtain ⟨_, -, rfl⟩ := List.mem_map.mp h
    exact ⟨fun _ _ h => (nomatch h), fun _ _ h => (nomatch h)⟩
  · exact ⟨rfl, rfl, rfl, Silent.nil⟩

omit [Fintype Validator] in
theorem timer_of_built {bs : List (BlockId × Block Validator BlockId Payload)}
    {e : BlockId × Block Validator BlockId Payload} (he : e ∈ bs) :
    Output.setTimer (e.2.round - 1) (2 * cfg.timeout (e.2.round - 1)) ∈ built cfg bs :=
  List.mem_flatMap.mpr ⟨e, he, by simp⟩

variable (cfg) in
/-- **The shape of a pass**: its blocks lie above the top it starts at,
one at each round up to the top it reaches, each with the timer of the
round below it, the retry timer; it keeps
the fired timers and rises. -/
structure PassShape (s : State Validator BlockId Payload)
    (out : List (Output Validator BlockId Payload)) (s' : State Validator BlockId Payload) :
    Prop where
  above : ∀ e ∈ persists out, s.top.getD 0 < e.2.round
  every : s.top.isSome → s.recovering = false → ∀ ρ, s.top.getD 0 < ρ → ρ ≤ s'.top.getD 0 →
    ∃ e ∈ persists out, e.2.round = ρ
  timer : ∀ e ∈ persists out,
    Output.setTimer (e.2.round - 1) (2 * cfg.timeout (e.2.round - 1)) ∈ out
  fired : s.fired ⊆ s'.fired
  rises : Rises s s'
  none : s.top = none → s'.top = none
  stays : s.recovering = false → s'.recovering = false
  built : s'.top ≠ s.top → ∃ e ∈ persists out, s'.top = some e.2.round
  clears : s'.top ≠ s.top → s'.recovering = false

theorem PassShape.refl (s : State Validator BlockId Payload) : PassShape cfg s [] s :=
  ⟨fun e he => absurd he (by simp [persists]),
    fun _ _ ρ h₁ h₂ => absurd h₂ (by omega), fun e he => absurd he (by simp [persists]),
    subset_rfl, Rises.refl s, id, id, fun h => absurd rfl h, fun h => absurd rfl h⟩

theorem PassShape.trans {a b c : State Validator BlockId Payload}
    {o₁ o₂ : List (Output Validator BlockId Payload)} (h₁ : PassShape cfg a o₁ b)
    (h₂ : PassShape cfg b o₂ c) : PassShape cfg a (o₁ ++ o₂) c := by
  have hab := h₁.rises
  have hbc := h₂.rises
  refine ⟨fun e he => ?_, fun hs hrec ρ hρ₁ hρ₂ => ?_, fun e he => ?_,
    h₁.fired.trans h₂.fired, hab.trans hbc, fun h => h₂.none (h₁.none h),
    fun h => h₂.stays (h₁.stays h), fun hne => ?_, fun hne => ?_⟩
  · rw [persists_append] at he
    rcases List.mem_append.mp he with he | he
    · exact h₁.above e he
    · exact lt_of_le_of_lt hab.1 (h₂.above e he)
  · rw [persists_append]
    by_cases hρ : ρ ≤ b.top.getD 0
    · obtain ⟨e, he, her⟩ := h₁.every hs hrec ρ hρ₁ hρ
      exact ⟨e, List.mem_append_left _ he, her⟩
    · obtain ⟨e, he, her⟩ := h₂.every (hab.2.1 hs) (h₁.stays hrec) ρ (by omega) hρ₂
      exact ⟨e, List.mem_append_right _ he, her⟩
  · rw [persists_append] at he
    rcases List.mem_append.mp he with he | he
    · exact List.mem_append_left _ (h₁.timer e he)
    · exact List.mem_append_right _ (h₂.timer e he)
  · rw [persists_append]
    by_cases hcb : c.top = b.top
    · obtain ⟨e, he, het⟩ := h₁.built (by rw [← hcb]; exact hne)
      exact ⟨e, List.mem_append_left _ he, by rw [hcb, het]⟩
    · obtain ⟨e, he, het⟩ := h₂.built hcb
      exact ⟨e, List.mem_append_right _ he, het⟩
  · by_cases hcb : c.top = b.top
    · exact h₂.stays (h₁.clears (by rw [← hcb]; exact hne))
    · exact h₂.clears hcb

/-- **The shape of one pass.** -/
theorem advance_shape (s : State Validator BlockId Payload) :
    PassShape cfg s (Node.advance cfg s).2 (Node.advance cfg s).1 := by
  obtain ⟨p₂, p₀, p₃, p₄, p₅, p₆, p₇⟩ := progress_shape (cfg := cfg) (s.disk.topRound + 2) s
  obtain ⟨bs, hbs⟩ := progress_built (cfg := cfg) (s.disk.topRound + 2) s
  have hra := rises_advance (cfg := cfg) s
  generalize hP : Node.progress cfg (s.disk.topRound + 2) s = P at p₂ p₀ p₃ p₄ p₅ p₆ p₇ hbs
  obtain ⟨d₂, d₃, -, d₅⟩ := decideStep_shape (cfg := cfg) P.1
  generalize hD : Node.decideStep cfg P.1 = D at d₂ d₃ d₅
  have hadv : Node.pass cfg s = (flushSyncs cfg (D.1.syncs.length + 1) D.1, P.2 ++ D.2) := by
    simp only [Node.pass, hP, hD]
  have hpers : persists (Node.advance cfg s).2 = bs := by
    rw [advance_snd, persists_append, persists_arm, List.append_nil, hadv, persists_append, hbs,
      persists_built, d₅.1]; simp
  have htop : (Node.advance cfg s).1.top = D.1.top := by rw [advance_top, hadv, flushSyncs_top]
  have hrec : (Node.advance cfg s).1.recovering = P.1.recovering := by
    rw [advance_recovering, hadv]
    change (flushSyncs cfg (D.1.syncs.length + 1) D.1).recovering = _
    rw [flushSyncs_recovering, ← hD, decideStep_recovering]
  refine ⟨fun e he => ?_, fun hs hr ρ h₁ h₂ => ?_, fun e he => ?_, ?_, hra, fun h => ?_,
    fun h => by rw [hrec]; exact p₅ h, fun hne => ?_, fun hne => by
      rw [hrec]; rw [htop, d₃] at hne; exact p₇ hne⟩
  · rw [hpers] at he
    exact p₃ e (by rw [hbs, persists_built]; exact he)
  · rw [hpers]
    obtain ⟨e, he, her⟩ := p₄ hs hr ρ h₁ (by rw [htop, d₃] at h₂; exact h₂)
    rw [hbs, persists_built] at he
    exact ⟨e, he, her⟩
  · rw [hpers] at he
    rw [advance_snd, hadv, hbs]
    exact List.mem_append_left _ (List.mem_append_left _ (timer_of_built he))
  · rw [advance_fired, hadv]
    change s.fired ⊆ (flushSyncs cfg (D.1.syncs.length + 1) D.1).fired
    rw [flushSyncs_fired, d₂, p₂]
  · rw [htop, d₃]; exact p₀ h
  · rw [htop, d₃] at hne ⊢
    obtain ⟨e, he, het⟩ := p₆ hne
    rw [hbs, persists_built] at he
    exact ⟨e, by rw [hpers]; exact he, het⟩

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

omit [Fintype Validator] in
/-- A timer keeps the fired rounds not below the top. -/
theorem fired_timer {s : State Validator BlockId Payload} {r : ℕ} :
    ∀ y ∈ s.fired, s.top.getD 0 ≤ y → y ∈ fire s r :=
  fun _ hy ht => Finset.mem_insert_of_mem (Finset.mem_filter.mpr ⟨hy, ht⟩)

/-- **The shape of a step**: it leaves the state alone and persists
nothing, or settles a state with the node's top and fired timers, after
outputs persisting nothing or, at its start, after its genesis block with
its timer, and before outputs persisting nothing. -/
theorem step_shape (s : State Validator BlockId Payload) (inp : Input Validator BlockId Payload) :
    ((Node.step cfg s inp).1 = s ∧ persists (Node.step cfg s inp).2 = []) ∨
    ∃ x pre post, (Node.step cfg s inp).1 = (Node.settle cfg x).1 ∧
      (Node.step cfg s inp).2 = pre ++ (Node.settle cfg x).2 ++ post ∧ persists post = [] ∧
      x.top.getD 0 = s.top.getD 0 ∧ (∀ y ∈ s.fired, s.top.getD 0 ≤ y → y ∈ x.fired) ∧
      ((persists pre = [] ∧ x.top = s.top) ∨ (s.top = none ∧ x.top = some 0 ∧
        ∃ g : BlockId × Block Validator BlockId Payload,
          pre = [.persist g.1 g.2, .broadcast g.1 g.2, .setTimer 0 (2 * cfg.timeout 0)] ∧
          g.2.round = 0 ∧ g.1 ∈ x.disk.ids ∧ (x.disk.blk g.1).round = 0 ∧
          x.recovering = false)) ∧
      (x.recovering = true → (s.recovering = true ∧ ∀ r, inp ≠ .timer r) ∨ inp = .restart) := by
  have hq : ∀ x, x = s → ((x, ([] : List (Output Validator BlockId Payload))).1 = s ∧
      persists ([] : List (Output Validator BlockId Payload)) = []) := fun x hx => ⟨hx, rfl⟩
  cases inp with
  | start =>
    simp only [Node.step]
    split
    · rename_i h₁
      split
      · rename_i h₂
        refine Or.inr ⟨_, _, [], rfl, by rw [List.append_nil], rfl, by simp [h₁.1], fun _ h _ => h,
          Or.inr ⟨h₁.1, rfl, ⟨_, cfg.genesis⟩, rfl, rfl, (by simp [Store.insert_ids]), ?_⟩,
          fun h => by cases h⟩
        exact ⟨by simp [Store.blk, Store.insert, Std.TreeMap.getD_insert_self, Config.genesis],
          rfl⟩
      · exact Or.inl (hq s rfl)
    · exact Or.inl (hq s rfl)
  | deliver u id b =>
    rcases step_receipt (cfg := cfg) (s := s) (Or.inl ⟨u, id, b, rfl⟩) with
      he | ⟨s₁, pre, hr, hpre, he⟩
    · rw [he]; exact Or.inl ⟨rfl, rfl⟩
    · rw [he]
      refine Or.inr ⟨s₁, pre, [], rfl, by rw [List.append_nil], rfl, by rw [hr.top],
        fun _ h _ => by rwa [hr.fired], Or.inl ⟨?_, hr.top⟩,
        fun h => Or.inl ⟨by rw [hr.recovering] at h; exact h, fun r hr => by cases hr⟩⟩
      refine (silent_of fun o ho => ?_).1
      obtain ⟨_, _, _, _, rfl⟩ := hpre o ho; trivial
  | stream u L =>
    rcases step_receipt (cfg := cfg) (s := s) (Or.inr ⟨u, L, rfl⟩) with he | ⟨s₁, pre, hr, hpre, he⟩
    · rw [he]; exact Or.inl ⟨rfl, rfl⟩
    · rw [he]
      refine Or.inr ⟨s₁, pre, [], rfl, by rw [List.append_nil], rfl, by rw [hr.top],
        fun _ h _ => by rwa [hr.fired], Or.inl ⟨?_, hr.top⟩,
        fun h => Or.inl ⟨by rw [hr.recovering] at h; exact h, fun r hr => by cases hr⟩⟩
      refine (silent_of fun o ho => ?_).1
      obtain ⟨_, _, _, _, rfl⟩ := hpre o ho; trivial
  | timer r =>
    right
    rcases step_timer_snd (cfg := cfg) s r with h | h
    · exact ⟨{ s with fired := fire s r, recovering := false }, [], [], step_timer_fst s r,
        by rw [h]; simp, rfl, rfl, fired_timer, Or.inl ⟨rfl, rfl⟩, fun h => by cases h⟩
    · exact ⟨{ s with fired := fire s r, recovering := false }, [],
        Node.resend cfg (Node.settle cfg { s with fired := fire s r, recovering := false }).1,
        step_timer_fst s r, by rw [h]; simp,
        persists_resend _, rfl, fired_timer, Or.inl ⟨rfl, rfl⟩, fun h => by cases h⟩
  | syncRequest p t fr ids =>
    refine Or.inl ⟨rfl, (silent_of fun o ho => ?_).1⟩
    simp only [Node.step] at ho
    split at ho
    · cases ho
    · rw [List.mem_singleton] at ho; subst ho; trivial
  | ask p r =>
    refine Or.inl ⟨rfl, (silent_of fun o ho => ?_).1⟩
    simp only [Node.step] at ho
    split at ho
    · cases ho
    · split at ho
      · rw [List.mem_singleton] at ho; subst ho; trivial
      · cases ho
  | restart =>
    refine Or.inr ⟨{ s with recovering := true }, Node.resend cfg s ++ Node.rearm cfg s, [],
      rfl, by simp only [Node.step, List.append_nil], rfl, rfl, fun _ h _ => h,
      Or.inl ⟨?_, rfl⟩, fun _ => Or.inr rfl⟩
    rw [persists_append, persists_resend, persists_rearm, List.append_nil]

section StepFacts

variable {s : State Validator BlockId Payload} {inp : Input Validator BlockId Payload}

/-- **A step builds every round above the top before up to the top it
reaches**, when it is no restart, and a timer or starts not recovering. -/
theorem step_every (hinp : inp ≠ .restart) (hrec : s.recovering = false ∨ ∃ r, inp = .timer r)
    (hsome : (Node.step cfg s inp).1.top.isSome) :
    ∀ ρ, (s.top = none ∨ s.top.getD 0 < ρ) → ρ ≤ (Node.step cfg s inp).1.top.getD 0 →
      ∃ e ∈ persists (Node.step cfg s inp).2, e.2.round = ρ := by
  intro ρ hρ hρt
  rcases step_shape (cfg := cfg) s inp with ⟨he, -⟩ |
      ⟨x, pre, post, he, ho, hpost, ht, -, hpre, hxr⟩
  · rw [he] at hsome hρt
    rcases hρ with hρ | hρ
    · rw [hρ] at hsome; cases hsome
    · omega
  · rw [he] at hsome hρt
    rw [ho, persists_append, hpost, List.append_nil, persists_append]
    have hS := settle_shape (cfg := cfg) x
    have hx : x.recovering = false := by
      cases h : x.recovering
      · rfl
      · rcases hxr h with ⟨h', ht'⟩ | h'
        · rcases hrec with hrec | ⟨r, hr⟩
          · rw [hrec] at h'; cases h'
          · exact absurd hr (ht' r)
        · exact absurd h' hinp
    rcases hpre with ⟨-, hxt⟩ | ⟨hn, hx0, g, rfl, hg, -⟩
    · by_cases hn : s.top = none
      · have := hS.none (by rw [hxt, hn])
        rw [this] at hsome; cases hsome
      · have hρ' : s.top.getD 0 < ρ := hρ.resolve_left hn
        obtain ⟨e, he', her⟩ := hS.every (by
          rw [hxt]; exact Option.ne_none_iff_isSome.mp hn) hx ρ
          (by rw [ht]; exact hρ') hρt
        exact ⟨e, List.mem_append_right _ he', her⟩
    · by_cases h0 : ρ = 0
      · exact ⟨g, List.mem_append_left _ (by simp [persists]), by rw [hg, h0]⟩
      · obtain ⟨e, he', her⟩ := hS.every (by rw [hx0]; rfl) hx ρ
          (by rw [hx0]; simp; omega) hρt
        exact ⟨e, List.mem_append_right _ he', her⟩

/-- **A step builds only above the top it starts at.** -/
theorem step_above :
    ∀ e ∈ persists (Node.step cfg s inp).2, s.top = none ∨ s.top.getD 0 < e.2.round := by
  rcases step_shape (cfg := cfg) s inp with ⟨-, hq⟩ | ⟨x, pre, post, -, he, hpost, hxt, -, hpre, -⟩
  · rw [hq]; intro e he; cases he
  · rw [he, persists_append, hpost, List.append_nil, persists_append]
    intro e he'
    rcases List.mem_append.mp he' with he' | he'
    · rcases hpre with ⟨hp, -⟩ | ⟨hn, -⟩
      · rw [hp] at he'; cases he'
      · exact Or.inl hn
    · right; rw [← hxt]; exact (settle_shape (cfg := cfg) x).above e he'

/-- **A step that moves the top builds the round it reaches.** -/
theorem step_built_top (h : (Node.step cfg s inp).1.top ≠ s.top) :
    ∃ e ∈ persists (Node.step cfg s inp).2, (Node.step cfg s inp).1.top = some e.2.round := by
  rcases step_shape (cfg := cfg) s inp with ⟨he, -⟩ | ⟨x, pre, post, hs, he, hpost, -, -, hpre, -⟩
  · rw [he] at h; exact absurd rfl h
  · rw [hs] at h ⊢
    rw [he, persists_append, hpost, List.append_nil, persists_append]
    by_cases hx : (Node.settle cfg x).1.top = x.top
    · rcases hpre with ⟨-, hxt⟩ | ⟨-, hx0, g, rfl, hg, -⟩
      · rw [hx, hxt] at h; exact absurd rfl h
      · refine ⟨g, List.mem_append_left _ (by simp [persists]), by rw [hx, hx0, hg]⟩
    · obtain ⟨e, he', het⟩ := (settle_shape (cfg := cfg) x).built hx
      exact ⟨e, List.mem_append_right _ he', het⟩

/-- **A step after which the node still recovers** was no timer, and left
the top alone; the node recovered before, or the step is a restart. -/
theorem step_recovering (h : (Node.step cfg s inp).1.recovering = true) :
    (Node.step cfg s inp).1.top = s.top ∧ (∀ r, inp ≠ .timer r) ∧
      (inp = .restart ∨ s.recovering = true) := by
  have htimer : ∀ r, inp ≠ .timer r := by
    intro r hr
    subst hr
    rw [step_timer_fst] at h
    rw [(settle_shape (cfg := cfg)
      { s with fired := fire s r, recovering := false }).stays rfl] at h
    cases h
  rcases step_shape (cfg := cfg) s inp with ⟨he, -⟩ | ⟨x, pre, post, hs, -, -, -, -, hpre, hxr⟩
  · rw [he] at h ⊢
    exact ⟨rfl, htimer, Or.inr h⟩
  · rw [hs] at h ⊢
    have hS := settle_shape (cfg := cfg) x
    have hxt : (Node.settle cfg x).1.top = x.top := by
      by_contra hne; rw [hS.clears hne] at h; cases h
    have hxrec : x.recovering = true := by
      cases hx : x.recovering
      · rw [hS.stays hx] at h; cases h
      · rfl
    rcases hpre with ⟨-, h₁⟩ | ⟨-, -, -, -, -, -, -, hx0⟩
    · refine ⟨hxt.trans h₁, htimer, ?_⟩
      rcases hxr hxrec with ⟨h', -⟩ | h'
      · exact Or.inr h'
      · exact Or.inl h'
    · rw [hx0] at hxrec; cases hxrec

/-- **A step sets the retry timer of each round it builds.** -/
theorem step_timer :
    ∀ e ∈ persists (Node.step cfg s inp).2,
      Output.setTimer (e.2.round - 1) (2 * cfg.timeout (e.2.round - 1)) ∈
        (Node.step cfg s inp).2 := by
  rcases step_shape (cfg := cfg) s inp with ⟨-, hq⟩ | ⟨x, pre, post, -, he, hpost, -, -, hpre, -⟩
  · rw [hq]; intro e he; cases he
  · rw [he, persists_append, hpost, List.append_nil]
    intro e he'
    refine List.mem_append_left _ ?_
    rw [persists_append] at he'
    rcases List.mem_append.mp he' with he' | he'
    · rcases hpre with ⟨hp, -⟩ | ⟨-, -, g, rfl, hg, -⟩
      · rw [hp] at he'; cases he'
      · simp only [persists] at he'
        simp at he'
        subst he'
        rw [hg]
        exact List.mem_append_left _ (by simp)
    · exact List.mem_append_right _ ((settle_shape (cfg := cfg) x).timer e he')

/-- **A step keeps the fired timers** not below the top. -/
theorem step_fired {r : ℕ} (hr : r ∈ s.fired) (ht : s.top.getD 0 ≤ r) :
    r ∈ (Node.step cfg s inp).1.fired := by
  rcases step_shape (cfg := cfg) s inp with ⟨he, -⟩ | ⟨x, pre, post, he, -, -, -, hf, -, -⟩
  · rw [he]; exact hr
  · rw [he]
    exact (settle_shape (cfg := cfg) x).fired (hf r hr ht)

end StepFacts

/-! ## Building on a timer -/

omit [Fintype Validator] in
/-- **`refsFor`'s references**: blocks of the store at the round, one per
author of the round not left out, the node's own block for itself if it
has one. -/
theorem refsFor_spec {st : Store Validator BlockId Payload} {r : ℕ} {o : Option BlockId}
    {E : Finset (Validator × BlockId × BlockId)}
    (ho : ∀ j, o = some j → j ∈ st.ids ∧ (st.blk j).round = r ∧ (st.blk j).creator = cfg.me) :
    refsFor cfg st r o E ⊆ st.ids ∧ (∀ j ∈ refsFor cfg st r o E, (st.blk j).round = r) ∧
      creatorsOf st.blk (refsFor cfg st r o E) =
        authorsIn st.toRecord st.ids r \ excluded cfg st r E ∧
      ∀ i ∈ refsFor cfg st r o E, ∀ j ∈ refsFor cfg st r o E,
        (st.blk i).creator = (st.blk j).creator → i = j := by
  set R := blocksAt st.toRecord r with hR
  have hRi : ∀ i ∈ R, i ∈ st.ids ∧ (st.blk i).round = r := fun i hi => by
    simpa [hR, blocksAt, Store.toRecord] using hi
  set A := creatorsOf st.blk R \ excluded cfg st r E with hA
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
  have hdef : refsFor cfg st r o E = A.biUnion pick := by
    unfold refsFor; rw [Store.atRound_eq]
  have hmem : ∀ j ∈ refsFor cfg st r o E, ∃ a ∈ A, j ∈ st.ids ∧
      (st.blk j).round = r ∧ (st.blk j).creator = a ∧ pick a = {j} := by
    intro j hj
    rw [hdef] at hj
    obtain ⟨a, ha, hja⟩ := Finset.mem_biUnion.mp hj
    obtain ⟨j', hp, h₁, h₂, h₃⟩ := hpick a (Finset.mem_sdiff.mp ha).1
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
      obtain ⟨j, hp, -, -, hja⟩ := hpick a (Finset.mem_sdiff.mp ha).1
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
/-- **`refsAt`'s references can be built on** when `refsFor`'s or a lent set
can. -/
theorem refsAt_buildable_of (st : Store Validator BlockId Payload) (r : ℕ) (o : Option BlockId)
    (E : Finset (Validator × BlockId × BlockId))
    (h : buildable cfg st r (refsFor cfg st r o E) E = true ∨
      ∃ R ∈ lents cfg st r E, buildable cfg st r R E = true) :
    buildable cfg st r (refsAt cfg st r o E) E = true := by
  unfold refsAt
  dsimp only
  split
  · rename_i h'
    simp only [Bool.and_eq_true] at h'
    exact h'.2
  · split
    · rename_i R hR
      have := List.find?_some hR
      simp only [Bool.and_eq_true] at this
      exact this.2
    · split
      · assumption
      · rename_i hown
        rcases h with h | ⟨R, hR, hb⟩
        · exact absurd h hown
        · obtain ⟨R', hR'⟩ := Option.isSome_iff_exists.mp
            ((List.find?_isSome (p := fun R => buildable cfg st r R E)).mpr ⟨R, hR, hb⟩)
          rw [hR']
          simpa using List.find?_some hR'

omit [Fintype Validator] in
/-- **References the node can build on**: held, one round below, of
distinct authors, `q` of them, none of an author they expose, under a
faithful payload source and a fresh identifier. -/
theorem buildable_of {st : Store Validator BlockId Payload} {r : ℕ} {R : Finset BlockId}
    (E : Finset (Validator × BlockId × BlockId)) (hfa : cfg.Faithful)
    (hsub : R ⊆ st.ids) (hrd : ∀ j ∈ R, (st.blk j).round = r)
    (hdis : ∀ i ∈ R, ∀ j ∈ R, (st.blk i).creator = (st.blk j).creator → i = j)
    (hq : cfg.q ≤ (creatorsOf st.blk R).card)
    (hex : ∀ j ∈ R, (st.blk j).creator ∉ R.biUnion fun k => cfg.xp.ex (st.blk k).payload)
    (hfresh : cfg.idOf (blockOn cfg st r R E) ∉ st.ids) :
    buildable cfg st r R E = true := by
  unfold buildable
  set b := blockOn cfg st r R E with hbdef
  have hbr : b.round = r + 1 := rfl
  have hbR : b.refs = R := rfl
  have hnin : ∀ j ∈ R, j ≠ cfg.idOf b := fun j hj h => hfresh (h ▸ hsub hj)
  have hup : ∀ j ∈ R, Function.update st.blk (cfg.idOf b) b j = st.blk j :=
    fun j hj => Function.update_of_ne (hnin j hj) _ _
  obtain ⟨hev, hexp⟩ := hfa (r + 1) (E.filter fun e => e.1 ∉ creatorsOf st.blk R)
    (named (E.filter fun e => e.1 ∉ creatorsOf st.blk R) ∪
      R.biUnion fun j => cfg.xp.ex (st.blk j).payload)
  have hbp : b.payload = cfg.payload (r + 1) (E.filter fun e => e.1 ∉ creatorsOf st.blk R)
      (named (E.filter fun e => e.1 ∉ creatorsOf st.blk R) ∪
        R.biUnion fun j => cfg.xp.ex (st.blk j).payload) := rfl
  refine decide_eq_true ⟨by rw [hbR]; exact hsub, fun j hj => by
      rw [hbR] at hj; rw [hbr, hrd j hj],
    ⟨fun j hj => ?_, fun _ => ?_, ⟨fun i hi j hj hij => ?_, ?_, fun j hj => ?_⟩⟩⟩
  · rw [hbR] at hj
    rw [hup j hj, hrd j hj, hbr]
  · simp only [creators, creatorsOf]
    rw [hbR, Finset.image_congr (g := fun i => (st.blk i).creator)
      (fun j hj => by simp only; rw [hup j hj])]
    exact hq
  · rw [hbR] at hi hj
    rw [hup i hi, hup j hj] at hij
    exact hdis i hi j hj hij
  · rw [hbp, hev, hexp, hbR]
    congr 1
    exact Finset.biUnion_congr rfl fun j hj => by rw [hup j hj]
  · rw [hbR] at hj
    rw [hbp, hexp, hup j hj]
    intro hm
    rcases Finset.mem_union.mp hm with hm | hm
    · obtain ⟨e, he, hea⟩ := Finset.mem_image.mp hm
      have := (Finset.mem_filter.mp (Finset.mem_filter.mp he).1).2
      exact this (hea ▸ Finset.mem_image_of_mem _ hj)
    · exact hex j hj hm

omit [Fintype Validator] in
/-- **`refsFor`'s references can be built on** once `q` authors of the round
are not left out. -/
theorem refsFor_buildable {st : Store Validator BlockId Payload} {r : ℕ} {o : Option BlockId}
    (E : Finset (Validator × BlockId × BlockId)) (hfa : cfg.Faithful)
    (ho : ∀ j, o = some j → j ∈ st.ids ∧ (st.blk j).round = r ∧ (st.blk j).creator = cfg.me)
    (hq : cfg.q ≤ (authorsIn st.toRecord st.ids r \ excluded cfg st r E).card)
    (hfresh : cfg.idOf (blockOn cfg st r (refsFor cfg st r o E) E) ∉ st.ids) :
    buildable cfg st r (refsFor cfg st r o E) E = true := by
  obtain ⟨hsub, hrd, hcr, hdis⟩ := refsFor_spec (cfg := cfg) (st := st) (r := r) (E := E) ho
  refine buildable_of E hfa hsub hrd hdis (by rw [hcr]; exact hq) (fun j hj hm => ?_) hfresh
  have hjA : (st.blk j).creator ∈ authorsIn st.toRecord st.ids r \ excluded cfg st r E := by
    rw [← hcr]; exact Finset.mem_image_of_mem _ hj
  refine (Finset.mem_sdiff.mp hjA).2 (Finset.mem_union_right _ ?_)
  obtain ⟨k, hk, hkm⟩ := Finset.mem_biUnion.mp hm
  exact Finset.mem_biUnion.mpr ⟨k, Store.mem_atRound.mpr ⟨hsub hk, hrd k hk⟩, hkm⟩

omit [Fintype Validator] in
/-- **A held valid round-`r + 1` block lends references the node can build
on.** -/
theorem lent_buildable_of {st : Store Validator BlockId Payload} {r : ℕ} {z : BlockId}
    (E : Finset (Validator × BlockId × BlockId)) (hfa : cfg.Faithful)
    (hz : z ∈ st.ids) (hzr : (st.blk z).round = r + 1)
    (hv : rowValid cfg.q cfg.xp st.blk (st.blk z))
    (hfresh : cfg.idOf (blockOn cfg st r (lent st z) E) ∉ st.ids) :
    buildable cfg st r (lent st z) E = true := by
  unfold lent at hfresh ⊢
  refine buildable_of E hfa (fun j hj => st.complete z hz j hj) (fun j hj => ?_)
    (fun i hi j hj hij => hv.clause.1 i hi j hj hij)
    (hv.quorum (by rw [hzr]; omega)) (fun j hj hm => ?_) hfresh
  · have := st.pred z hz j hj
    change (st.blk j).round + 1 = (st.blk z).round at this
    omega
  · refine hv.clause.2.2 j hj ?_
    rw [hv.clause.2.1]
    exact Finset.mem_union_right _ hm

omit [Fintype Validator] in
/-- **A node not recovering whose round's timer fired, or that is behind
the round above, builds**, given a quorum of the round, its own block there
on disk, `refsFor`'s or a lent set it can build on, no block on disk with
the identifier of its next block, and its memory from the round up. -/
theorem tryBuild_isSome {s : State Validator BlockId Payload} {r : ℕ} (ht : s.top = some r)
    (hrec : s.recovering = false)
    (hf : r ∈ s.fired ∨ behind cfg s.disk r)
    (hq : cfg.q ≤ (authorsIn s.disk.toRecord s.disk.ids r).card)
    (ho : ∀ j, s.own = some j → j ∈ s.disk.ids ∧ (s.disk.blk j).round = r ∧
      (s.disk.blk j).creator = cfg.me)
    (hB : buildable cfg s.disk r (refsFor cfg s.disk r s.own s.evidence) s.evidence = true ∨
      ∃ R ∈ lents cfg s.disk r s.evidence, buildable cfg s.disk r R s.evidence = true)
    (hfresh : ∀ (P : Payload) R, cfg.idOf ⟨r + 1, cfg.me, R, P⟩ ∉ s.disk.ids)
    (hF : s.floor ≤ r) :
    (tryBuild cfg s).isSome := by
  unfold tryBuild
  rw [ht]
  dsimp only
  rw [if_neg (by simp [hrec])]
  unfold buildAbove
  dsimp only
  rw [if_pos ⟨by rw [s.mirrors.authorsAt_eq hF, Store.authorsAt_eq]; exact hq,
    hf.imp id fun h => Or.inl ((s.mirrors.behind_iff (by omega)).mpr h)⟩]
  have hown : ∀ c ∈ refsFor cfg s.disk r s.own s.evidence,
      c ∈ s.disk.ids ∧ (s.disk.blk c).round = r := fun c hc => by
    rcases mem_refsFor_of hc with hc | hc
    · exact Store.mem_atRound.mp hc
    · exact ⟨(ho c hc).1, (ho c hc).2.1⟩
  have hB' : buildable cfg s.memory r (refsAt cfg s.memory r s.own s.evidence) s.evidence =
      true := by
    refine refsAt_buildable_of s.memory r s.own s.evidence ?_
    rw [s.mirrors.refsFor_eq hF, s.mirrors.lents_eq hF s.evidence, s.mirrors.buildable_eq hF hown]
    rcases hB with hB | ⟨R, hR, hb⟩
    · exact Or.inl hB
    · exact Or.inr ⟨R, hR, by
        rw [s.mirrors.buildable_eq hF fun c hc => Store.mem_atRound.mp (mem_lents_round hR c hc)]
        exact hb⟩
  unfold buildable at hB'
  rw [dif_pos ⟨hfresh _ _, of_decide_eq_true hB'⟩]
  rfl

end Node

end LeanDag
