import LeanDag.Node.Helpers.Reliable
/-!
# The shape of a reliable node's step

`docs/validator.md` §13.2. A pass builds every round from the top it
starts at up to the top it reaches, at rounds above that top, each with
its timer, keeps the fired timers at or above the top it reaches, and
raises the horizon only with an announced certificate, to at most `Λ`
below the lesser of its slot round and the top it reaches. A step of a
node not recovering, other than a restart, either changes nothing and
outputs no block, announcement or timer, or settles a state with the same
top and horizon (`step_shape`).
-/

namespace LeanDag

namespace Node

variable {Validator BlockId Payload : Type} [Fintype Validator] [DecidableEq Validator]
variable [LinearOrder BlockId]
variable {cfg : Config Validator BlockId Payload}

/-- **Silent outputs**: no block, no announcement and no timer. -/
def Silent (out : List (Output Validator BlockId Payload)) : Prop :=
  persists out = [] ∧ (∀ c, Output.announce c ∉ out) ∧ ∀ r a, Output.setTimer r a ∉ out

omit [Fintype Validator] [DecidableEq Validator] [LinearOrder BlockId] in
theorem Silent.nil : Silent ([] : List (Output Validator BlockId Payload)) :=
  ⟨rfl, fun _ h => absurd h List.not_mem_nil, fun _ _ h => absurd h List.not_mem_nil⟩

omit [Fintype Validator] [DecidableEq Validator] [LinearOrder BlockId] in
theorem Silent.append {x y : List (Output Validator BlockId Payload)} (hx : Silent x)
    (hy : Silent y) : Silent (x ++ y) :=
  ⟨by rw [persists_append, hx.1, hy.1]; rfl,
    fun c h => (List.mem_append.mp h).elim (hx.2.1 c) (hy.2.1 c),
    fun r a h => (List.mem_append.mp h).elim (hx.2.2 r a) (hy.2.2 r a)⟩

omit [Fintype Validator] [DecidableEq Validator] [LinearOrder BlockId] in
theorem Silent.of_quiet {x : List (Output Validator BlockId Payload)}
    (h : ∀ o ∈ x, (∀ id b, o ≠ .persist id b) ∧ (∀ c, o ≠ .announce c) ∧
      ∀ r a, o ≠ .setTimer r a) : Silent x := by
  refine ⟨List.filterMap_eq_nil_iff.mpr fun o ho => ?_, fun c hc => (h _ hc).2.1 c rfl,
    fun r a hr => (h _ hr).2.2 r a rfl⟩
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
      obtain ⟨r, id, b, -, -, -, -, hr, hbr, -, -, -, -, ht₁, -, -, hout⟩ := tryBuild_some hb
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
theorem proposeAt_shape (x : State Validator BlockId Payload) :
    (proposeAt cfg x).1.fired = x.fired ∧
      (proposeAt cfg x).1.top = x.top ∧ (proposeAt cfg x).1.store = x.store ∧
      Silent (proposeAt cfg x).2 := by
  obtain ⟨ps, c, lp, ch, he, ho⟩ := proposeAt_eq (cfg := cfg) x
  refine ⟨by rw [he], by rw [he], by rw [he], Silent.of_quiet fun o ho' => ?_⟩
  obtain ⟨k, h', rfl⟩ := ho o ho'
  refine ⟨?_, ?_, ?_⟩ <;> intros <;> simp_all

omit [Fintype Validator] in
theorem decideStep_shape (s : State Validator BlockId Payload) :
    let d := Node.decideStep cfg s
    d.1.fired = s.fired ∧ d.1.top = s.top ∧ d.1.store = s.store ∧
      Silent d.2 := by
  intro d
  unfold d Node.decideStep
  dsimp only
  split
  · obtain ⟨h₂, h₃, h₄, h₅⟩ := proposeAt_shape (cfg := cfg) _
    refine ⟨h₂, h₃, h₄, (Silent.of_quiet fun o h => ?_).append h₅⟩
    obtain ⟨_, -, rfl⟩ := List.mem_map.mp h
    refine ⟨?_, ?_, ?_⟩ <;> intros <;> simp_all
  · exact proposeAt_shape s

omit [Fintype Validator] in
/-- **Collecting** keeps the top, drops the fired timers below the new
horizon only, and, if the node is not recovering, raises the horizon
only with an announced certificate, to at most `Λ` below the lesser of
its slot round and the top. -/
theorem collect_shape (s : State Validator BlockId Payload) :
    let g := Node.collect cfg s
    g.1.top = s.top ∧ persists g.2 = [] ∧ (∀ r a, Output.setTimer r a ∉ g.2) ∧
      (∀ r ∈ s.fired, s.top.getD 0 ≤ r → r ∈ g.1.fired) ∧ s.store.base ≤ g.1.store.base ∧
      (s.recovering = false → s.store.base < g.1.store.base → ∃ c, Output.announce c ∈ g.2 ∧
        g.1.store.base ≤ min (cfg.per * (c.height / cfg.m)) (s.top.getD 0) - cfg.lag) := by
  intro g
  unfold g Node.collect
  split
  · rename_i t hts
    dsimp only
    split
    · rename_i hG
      refine ⟨rfl, by simp [persists], by simp, fun r hr hrt => ?_, hG.le, fun hs _ => ?_⟩
      · rw [hts] at hrt
        simp only [Option.getD_some] at hrt
        exact Finset.mem_filter.mpr ⟨hr, (horizonAt_le_top s t).trans hrt⟩
      · rcases hc : s.cert with _ | c
        · exfalso
          have h0 : s.certHeight = 0 := by simp [State.certHeight, hc]
          have hF := horizonAt_le_frontier (cfg := cfg) s t
          rw [h0] at hF
          simp at hF
          omega
        · refine ⟨c, List.mem_cons_of_mem _ (by simp), ?_⟩
          change horizonAt cfg s t ≤ _
          rw [horizonAt_of hs]
          have hcH : s.certHeight = c.height := by simp [State.certHeight, hc]
          have h₁ : cfg.per * (min s.lo s.certHeight / cfg.m) ≤ cfg.per * (c.height / cfg.m) :=
            Nat.mul_le_mul_left _ (Nat.div_le_div_right (by rw [hcH]; exact min_le_right _ _))
          rw [hts]
          have := min_le_min h₁ (le_refl t)
          simp only [Option.getD_some]
          omega
    · exact ⟨rfl, rfl, by simp, fun r hr _ => hr, le_rfl, fun _ h => absurd h (lt_irrefl _)⟩
  · exact ⟨rfl, rfl, by simp, fun r hr _ => hr, le_rfl, fun _ h => absurd h (lt_irrefl _)⟩

omit [Fintype Validator] in
theorem timer_of_built {bs : List (BlockId × Block Validator BlockId Payload)}
    {e : BlockId × Block Validator BlockId Payload} (he : e ∈ bs) :
    Output.setTimer e.2.round (cfg.timeout e.2.round) ∈ built cfg bs :=
  List.mem_flatMap.mpr ⟨e, he, by simp⟩

variable (cfg) in
/-- **The shape of a pass.** -/
structure PassShape (s : State Validator BlockId Payload)
    (out : List (Output Validator BlockId Payload)) (s' : State Validator BlockId Payload) :
    Prop where
  above : ∀ e ∈ persists out, s.top.getD 0 < e.2.round
  every : s.top.isSome → ∀ ρ, s.top.getD 0 < ρ → ρ ≤ s'.top.getD 0 →
    ∃ e ∈ persists out, e.2.round = ρ
  timer : ∀ e ∈ persists out, Output.setTimer e.2.round (cfg.timeout e.2.round) ∈ out
  fired : ∀ r ∈ s.fired, s'.top.getD 0 ≤ r → r ∈ s'.fired
  base : s.store.base ≤ s'.store.base
  rise : s.recovering = false → s.store.base < s'.store.base → ∃ c, Output.announce c ∈ out ∧
    s'.store.base ≤ min (cfg.per * (c.height / cfg.m)) (s'.top.getD 0) - cfg.lag
  rises : Rises s s'
  none : s.top = none → s'.top = none
  calm : s'.recovering = s.recovering

theorem PassShape.refl (s : State Validator BlockId Payload) : PassShape cfg s [] s :=
  ⟨fun e he => absurd he (by simp [persists]),
    fun _ ρ h₁ h₂ => absurd h₂ (by omega), fun e he => absurd he (by simp [persists]),
    fun _ hr _ => hr, le_rfl, fun _ h => absurd h (lt_irrefl _), Rises.refl s, id, rfl⟩

theorem PassShape.trans {a b c : State Validator BlockId Payload}
    {o₁ o₂ : List (Output Validator BlockId Payload)} (h₁ : PassShape cfg a o₁ b)
    (h₂ : PassShape cfg b o₂ c) : PassShape cfg a (o₁ ++ o₂) c := by
  have hab := h₁.rises
  have hbc := h₂.rises
  refine ⟨fun e he => ?_, fun hs ρ hρ₁ hρ₂ => ?_, fun e he => ?_,
    fun r hr hrc => ?_, h₁.base.trans h₂.base, fun hrec hlt => ?_, hab.trans hbc,
    fun h => h₂.none (h₁.none h), h₂.calm.trans h₁.calm⟩
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
  · exact h₂.fired r (h₁.fired r hr (le_trans hbc.1 hrc)) hrc
  · by_cases hbc' : b.store.base < c.store.base
    · obtain ⟨x, hx, hxb⟩ := h₂.rise (h₁.calm.trans hrec) hbc'
      exact ⟨x, List.mem_append_right _ hx, hxb⟩
    · have heq : c.store.base = b.store.base := le_antisymm (not_lt.mp hbc') h₂.base
      obtain ⟨x, hx, hxb⟩ := h₁.rise hrec (by rw [← heq]; exact hlt)
      have := hbc.1
      exact ⟨x, List.mem_append_left _ hx, by
        rw [heq]
        have := min_le_min (le_refl (cfg.per * (x.height / cfg.m))) this
        omega⟩

/-- **The shape of one pass.** -/
theorem advance_shape (s : State Validator BlockId Payload) :
    PassShape cfg s (Node.advance cfg s).2 (Node.advance cfg s).1 := by
  obtain ⟨p₂, p₀, p₃, p₄⟩ := progress_shape (cfg := cfg) (s.store.topRound + 2) s
  obtain ⟨bs, hbs⟩ := progress_built (cfg := cfg) (s.store.topRound + 2) s
  have hpb := progress_base (cfg := cfg) (s.store.topRound + 2) s
  have hrp := rises_progress (cfg := cfg) (s.store.topRound + 2) s
  have hcalm := (calm_advance (cfg := cfg) s).2
  have hPs := (calm_progress (cfg := cfg) (s.store.topRound + 2) s).2
  generalize hP : Node.progress cfg (s.store.topRound + 2) s = P at p₂ p₀ p₃ p₄ hbs hpb hrp hPs
  obtain ⟨d₂, d₃, d₄, d₅⟩ := decideStep_shape (cfg := cfg) P.1
  have hDs := (calm_decideStep (cfg := cfg) P.1).2.trans hPs
  generalize hD : Node.decideStep cfg P.1 = D at d₂ d₃ d₄ d₅ hDs
  obtain ⟨g₂, g₃, g₄, g₅, g₆, g₇⟩ := collect_shape (cfg := cfg) D.1
  have hra := rises_advance (cfg := cfg) s
  have hadv : Node.advance cfg s = ({ (Node.collect cfg D.1).1 with
      store := (flush cfg ((Node.collect cfg D.1).1.pending.length + 1)
        (Node.collect cfg D.1).1.store (Node.collect cfg D.1).1.pending).1,
      pending := (flush cfg ((Node.collect cfg D.1).1.pending.length + 1)
        (Node.collect cfg D.1).1.store (Node.collect cfg D.1).1.pending).2 },
      P.2 ++ D.2 ++ (Node.collect cfg D.1).2) := by
    simp only [Node.advance, hP, hD]
  rw [hadv] at hra hcalm ⊢
  generalize hG : Node.collect cfg D.1 = G at g₂ g₃ g₄ g₅ g₆ g₇ hra hcalm ⊢
  have hfb := flush_base (cfg := cfg) (G.1.pending.length + 1) G.1.store G.1.pending
  have hpers : persists (P.2 ++ D.2 ++ G.2) = bs := by
    rw [persists_append, persists_append, hbs, persists_built, d₅.1, g₃]; simp
  refine ⟨fun e he => ?_, fun hs ρ h₁ h₂ => ?_, fun e he => ?_, fun r hr hrt => ?_, ?_,
    fun hrec hlt => ?_, hra, fun h => ?_, hcalm⟩
  · rw [hpers] at he
    exact p₃ e (by rw [hbs, persists_built]; exact he)
  · rw [hpers]
    obtain ⟨e, he, her⟩ := p₄ hs ρ h₁ (by
      change ρ ≤ G.1.top.getD 0 at h₂
      rw [g₂, d₃] at h₂; exact h₂)
    rw [hbs, persists_built] at he
    exact ⟨e, he, her⟩
  · rw [hpers] at he
    rw [hbs]
    exact List.mem_append_left _ (List.mem_append_left _ (timer_of_built he))
  · change G.1.top.getD 0 ≤ r at hrt
    change r ∈ G.1.fired
    refine g₅ r (by rw [d₂, p₂]; exact hr) ?_
    rw [g₂] at hrt; exact hrt
  · change s.store.base ≤ (flush cfg _ G.1.store G.1.pending).1.base
    rw [hfb, ← hpb, ← d₄]; exact g₆
  · change s.store.base < (flush cfg _ G.1.store G.1.pending).1.base at hlt
    rw [hfb] at hlt
    have hbD : D.1.store.base = s.store.base := by rw [d₄, hpb]
    obtain ⟨c, hc, hcb⟩ := g₇ (hDs.trans hrec) (by rw [hbD]; exact hlt)
    refine ⟨c, List.mem_append_right _ hc, ?_⟩
    change (flush cfg _ G.1.store G.1.pending).1.base ≤
      min (cfg.per * (c.height / cfg.m)) (G.1.top.getD 0) - cfg.lag
    rw [hfb, g₂]; exact hcb
  · change G.1.top = none
    rw [g₂, d₃]; exact p₀ h

theorem quiesce_shape (n : ℕ) (s : State Validator BlockId Payload) :
    PassShape cfg s (quiesce cfg n s).2 (quiesce cfg n s).1 :=
  (quiesce_rel (P := fun _ => True) (R := PassShape cfg) PassShape.refl
    (fun _ _ _ _ _ h₁ h₂ => h₁.trans h₂) (fun s _ => ⟨advance_shape s, trivial⟩) n s trivial).1

/-! ## What a pass builds it stores -/

/-- **The blocks of `out` kept in `s'`**: stored at their round, or below
the horizon. -/
def KeepsBuilt (out : List (Output Validator BlockId Payload))
    (s' : State Validator BlockId Payload) : Prop :=
  ∀ e ∈ persists out, (e.1 ∈ s'.store.ids ∧ (s'.store.blk e.1).round = e.2.round) ∨
    e.2.round < s'.store.base

omit [Fintype Validator] [DecidableEq Validator] in
theorem KeepsBuilt.of_retains {out : List (Output Validator BlockId Payload)}
    {b c : State Validator BlockId Payload} (h : KeepsBuilt out b)
    (hr : Retains b.store c.store) (hb : b.store.base ≤ c.store.base) : KeepsBuilt out c := by
  intro e he
  rcases h e he with ⟨hj, hjr⟩ | hlt
  · by_cases hc : c.store.base ≤ (b.store.blk e.1).round
    · obtain ⟨hjc, hrc⟩ := hr e.1 hj hc
      exact Or.inl ⟨hjc, hrc.trans hjr⟩
    · right; rw [← hjr]; omega
  · right; omega

omit [Fintype Validator] in
theorem progress_keeps : ∀ (fuel : ℕ) (s : State Validator BlockId Payload),
    KeepsBuilt (Node.progress cfg fuel s).2 (Node.progress cfg fuel s).1
  | 0, s => fun e he => absurd he (by simp [Node.progress, persists])
  | fuel + 1, s => by
    unfold Node.progress
    split
    · rename_i s₁ out hb
      obtain ⟨r, id, b, hnew, hab, hrefs, hpred, -, -, -, -, -, hst, -, -, -, hout⟩ :=
        tryBuild_some hb
      dsimp only
      intro e he
      rw [persists_append, hout, persists_built] at he
      rcases List.mem_append.mp he with he | he
      · rw [List.mem_singleton] at he; subst he
        have hg := (Grows.progress (cfg := cfg) fuel s₁).1
        have hbs := progress_base (cfg := cfg) fuel s₁
        have hin : id ∈ s₁.store.ids := by rw [hst]; exact Finset.mem_insert_self _ _
        have hr₁ : (s₁.store.blk id).round = b.round := by
          rw [hst]; simp [Store.blk, Store.insert, lookup, Std.TreeMap.getD_insert_self]
        exact Or.inl ⟨(hg.2 hbs).1 hin, by rw [Grows.blk hg hbs hin, hr₁]⟩
      · exact progress_keeps fuel s₁ e he
    · intro e he; simp [persists] at he

omit [Fintype Validator] in
theorem advance_keeps_built (s : State Validator BlockId Payload) :
    KeepsBuilt (Node.advance cfg s).2 (Node.advance cfg s).1 := by
  have h₁ := progress_keeps (cfg := cfg) (s.store.topRound + 2) s
  simp only [Node.advance]
  generalize Node.progress cfg (s.store.topRound + 2) s = P at h₁
  have hd := decideStep_store (cfg := cfg) P.1
  have hdp := decideStep_persist (cfg := cfg) P.1
  have hcp := collect_persist (cfg := cfg) (Node.decideStep cfg P.1).1
  have hrc := retains_collect (cfg := cfg) (Node.decideStep cfg P.1).1
  have hbc := (Grows.collect (cfg := cfg) (Node.decideStep cfg P.1).1).1
  generalize Node.decideStep cfg P.1 = D at hd hdp hcp hrc hbc
  generalize Node.collect cfg D.1 = G at hcp hrc hbc
  intro e he
  rw [persists_append, persists_append, hdp, hcp, List.append_nil, List.append_nil] at he
  have hfb := flush_base (cfg := cfg) (G.1.pending.length + 1) G.1.store G.1.pending
  have hfg := Grows.flush (cfg := cfg) (G.1.pending.length + 1) G.1.store G.1.pending
  have hR : Retains P.1.store (flush cfg (G.1.pending.length + 1) G.1.store G.1.pending).1 :=
    (hd ▸ hrc).trans (Retains.of_grows hfg hfb) (by rw [hfb])
  have hB : P.1.store.base ≤ (flush cfg (G.1.pending.length + 1) G.1.store G.1.pending).1.base := by
    rw [hfb, ← hd]; exact hbc
  exact KeepsBuilt.of_retains (c := { G.1 with
    store := (flush cfg (G.1.pending.length + 1) G.1.store G.1.pending).1,
    pending := (flush cfg (G.1.pending.length + 1) G.1.store G.1.pending).2 }) h₁ hR hB e he

omit [Fintype Validator] in
theorem quiesce_keeps_built (n : ℕ) (s : State Validator BlockId Payload) :
    KeepsBuilt (quiesce cfg n s).2 (quiesce cfg n s).1 :=
  (quiesce_rel (P := fun _ => True)
    (R := fun a out b => KeepsBuilt out b ∧ Retains a.store b.store ∧
      a.store.base ≤ b.store.base)
    (fun _ => ⟨fun e he => absurd he (by simp [persists]), Retains.refl _, le_rfl⟩)
    (fun _ _ _ _ _ h₁ h₂ => ⟨fun e he => by
      rw [persists_append] at he
      rcases List.mem_append.mp he with he | he
      · exact (h₁.1.of_retains h₂.2.1 h₂.2.2) e he
      · exact h₂.1 e he, h₁.2.1.trans h₂.2.1 h₂.2.2, h₁.2.2.trans h₂.2.2⟩)
    (fun s _ => ⟨⟨advance_keeps_built s, retains_advance s, (Grows.advance s).1⟩, trivial⟩)
    n s trivial).1.1

/-! ## A settle and a step -/

/-- **A settle of a node not recovering** has the shape of its passes. -/
theorem settle_shape {x : State Validator BlockId Payload} (hs : x.recovering = false) :
    PassShape cfg x (Node.settle cfg x).2 (Node.settle cfg x).1 := by
  rw [settle_of_idle hs]
  exact quiesce_shape _ x

omit [Fintype Validator] [DecidableEq Validator] [LinearOrder BlockId] in
theorem silent_of {x : List (Output Validator BlockId Payload)}
    (h : ∀ o ∈ x, match o with
      | .persist _ _ => False | .announce _ => False | .setTimer _ _ => False | _ => True) :
    Silent x :=
  Silent.of_quiet fun o ho => by
    have := h o ho
    refine ⟨fun id b he => ?_, fun c he => ?_, fun r a he => ?_⟩ <;> subst he <;> exact this

/-- **The shape of a step** of a node not recovering, other than a
restart: it leaves the state alone with silent outputs, or settles a
state with the node's top, fired timers and horizon, after silent outputs
or, at its start, after its genesis block with its timer. -/
theorem step_shape {s : State Validator BlockId Payload} {inp : Input Validator BlockId Payload}
    (hs : s.recovering = false) (hr : inp ≠ .restart) :
    ((Node.step cfg s inp).1 = s ∧ Silent (Node.step cfg s inp).2) ∨
    ∃ x pre, Node.step cfg s inp = ((Node.settle cfg x).1, pre ++ (Node.settle cfg x).2) ∧
      x.recovering = false ∧ x.store.base = s.store.base ∧ x.top.getD 0 = s.top.getD 0 ∧
      s.fired ⊆ x.fired ∧
      ((Silent pre ∧ x.top = s.top) ∨ (s.top = none ∧ x.top = some 0 ∧
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
        refine Or.inr ⟨_, _, rfl, rfl, rfl, by simp [h₁.1], subset_rfl, Or.inr ⟨h₁.1, rfl,
          ⟨_, cfg.genesis⟩, rfl, rfl, Finset.mem_insert_self _ _, ?_⟩⟩
        simp [Store.blk, Store.insert, lookup, Std.TreeMap.getD_insert_self, Config.genesis]
      · exact Or.inl (hq s rfl)
    · exact Or.inl (hq s rfl)
  | deliver id b =>
    by_cases hA : Admits cfg s id b
    · rw [step_deliver hA]
      refine Or.inr ⟨_, _, rfl, hs, flush_base _ _ _, rfl, subset_rfl, Or.inl ⟨?_, rfl⟩⟩
      refine silent_of fun o ho => ?_
      simp only [askOut, List.mem_append] at ho
      rcases ho with (ho | ho) | ho
      · obtain ⟨_, _, rfl⟩ := evidence_relay ho; trivial
      · split at ho
        · cases ho
        · rw [List.mem_singleton] at ho; subst ho; trivial
      · split at ho
        · rw [List.mem_singleton] at ho; subst ho; trivial
        · cases ho
    · rw [step_deliver_not_of hA hs]
      exact Or.inl ⟨rfl, Silent.nil⟩
  | timer r =>
    rw [step_timer_of hs]
    exact Or.inr ⟨_, [], hnil _, hs, rfl, rfl, Finset.subset_insert _ _, Or.inl ⟨Silent.nil, rfl⟩⟩
  | restart => exact absurd rfl hr
  | baseOffer p G bs =>
    rw [show Node.step cfg s (.baseOffer p G bs) = (s, []) by
      simp only [Node.step, hs, Bool.false_eq_true, false_and, if_false]]
    exact Or.inl ⟨rfl, Silent.nil⟩
  | baseRequest p =>
    refine Or.inl ⟨rfl, silent_of fun o ho => ?_⟩
    simp only [Node.step, List.mem_cons, List.mem_append, List.mem_map] at ho
    rcases ho with (rfl | ⟨c, -, rfl⟩) | ho
    · trivial
    · trivial
    · rw [if_neg (by simp [hs])] at ho; cases ho
  | fetchRequest p G ids =>
    refine Or.inl ⟨rfl, silent_of fun o ho => ?_⟩
    simp only [Node.step, answer, List.mem_map] at ho
    obtain ⟨j, -, rfl⟩ := ho; trivial
  | decisionRequest p lo =>
    refine Or.inl ⟨rfl, silent_of fun o ho => ?_⟩
    simp only [Node.step] at ho
    split at ho
    · unfold serveFrom at ho
      split at ho
      · split at ho
        · rw [List.mem_singleton] at ho; subst ho; trivial
        · cases ho
      · cases ho
    · cases ho
  | certOffer p c ds =>
    rcases certOffer_cases (cfg := cfg) s p c ds with ⟨h₁, -, -⟩ | ⟨l, hcl, ds', -, -, -, he⟩ |
      ⟨l, hcl, -, -, he⟩ | ⟨l, hcl, he⟩
    all_goals try obtain rfl := certs_of_not hcl hs
    · rw [hs] at h₁; cases h₁
    · rw [he, adopt_eq]
      refine Or.inr ⟨_, _, rfl, hs, rfl, rfl, subset_rfl, Or.inl ⟨silent_of fun o ho => ?_, rfl⟩⟩
      obtain ⟨_, -, rfl⟩ := List.mem_map.mp ho; trivial
    · rw [he]
      exact Or.inr ⟨_, [], hnil _, hs, rfl, rfl, subset_rfl, Or.inl ⟨Silent.nil, rfl⟩⟩
    · rw [he]; exact Or.inl ⟨rfl, Silent.nil⟩
  | announced p c =>
    rcases announced_cases (cfg := cfg) s p c with ⟨-, -, he⟩ | he | he <;> rw [he]
    · exact Or.inr ⟨_, [], hnil _, hs, rfl, rfl, subset_rfl, Or.inl ⟨Silent.nil, rfl⟩⟩
    · refine Or.inl ⟨rfl, silent_of fun o ho => ?_⟩
      rw [List.mem_singleton] at ho; subst ho; trivial
    · exact Or.inl ⟨rfl, Silent.nil⟩
  | proposal p k kh =>
    rw [step_proposal]
    split
    · obtain ⟨n, hn⟩ := seek_eq (cfg := cfg) (record cfg s p k kh) k kh
      refine Or.inr ⟨_, _, rfl, by rw [hn]; exact hs, by rw [hn]; rfl, by rw [hn]; rfl,
        by rw [hn]; exact subset_rfl, Or.inl ⟨silent_of fun o ho => ?_, by rw [hn]; rfl⟩⟩
      unfold seek at ho
      dsimp only at ho
      split at ho
      · obtain ⟨_, -, rfl⟩ := List.mem_map.mp ho; trivial
      · cases ho
    · exact Or.inl ⟨rfl, Silent.nil⟩

section StepFacts

variable {s : State Validator BlockId Payload} {inp : Input Validator BlockId Payload}

/-- **A step raises the horizon only with an announced certificate**, to
at most `Λ` below the lesser of its slot round and the top after. -/
theorem step_rise (hs : s.recovering = false) (hr : inp ≠ .restart)
    (hlt : s.store.base < (Node.step cfg s inp).1.store.base) :
    ∃ c, Output.announce c ∈ (Node.step cfg s inp).2 ∧
      (Node.step cfg s inp).1.store.base ≤
        min (cfg.per * (c.height / cfg.m)) ((Node.step cfg s inp).1.top.getD 0) - cfg.lag := by
  rcases step_shape (cfg := cfg) hs hr with ⟨he, -⟩ | ⟨x, pre, he, hx, hb, -, -, -⟩
  · rw [he] at hlt; exact absurd hlt (lt_irrefl _)
  · rw [he] at hlt ⊢
    obtain ⟨c, hc, hcb⟩ := (settle_shape (cfg := cfg) hx).rise hx (by rw [hb]; exact hlt)
    exact ⟨c, List.mem_append_right _ hc, hcb⟩

/-- **What a step builds lies above the top before**, but the genesis
block at the start. -/
theorem step_above (hs : s.recovering = false) (hr : inp ≠ .restart) :
    ∀ e ∈ persists (Node.step cfg s inp).2,
      s.top.getD 0 < e.2.round ∨ (s.top = none ∧ e.2.round = 0) := by
  rcases step_shape (cfg := cfg) hs hr with ⟨-, hq⟩ | ⟨x, pre, he, hx, -, ht, -, hpre⟩
  · rw [hq.1]; intro e he; cases he
  · rw [he, persists_append]
    intro e he'
    rcases List.mem_append.mp he' with he' | he'
    · rcases hpre with ⟨hp, -⟩ | ⟨hn, -, g, rfl, hg, -⟩
      · rw [hp.1] at he'; cases he'
      · simp only [persists] at he'
        simp at he'
        subst he'
        exact Or.inr ⟨hn, hg⟩
    · left
      have := (settle_shape (cfg := cfg) hx).above e he'
      change x.top.getD 0 < _ at this
      rw [← ht]; exact this

/-- **A step builds every round above the top before up to the top it
reaches.** -/
theorem step_every (hs : s.recovering = false) (hr : inp ≠ .restart)
    (hsome : (Node.step cfg s inp).1.top.isSome) :
    ∀ ρ, (s.top = none ∨ s.top.getD 0 < ρ) → ρ ≤ (Node.step cfg s inp).1.top.getD 0 →
      ∃ e ∈ persists (Node.step cfg s inp).2, e.2.round = ρ := by
  intro ρ hρ hρt
  rcases step_shape (cfg := cfg) hs hr with ⟨he, -⟩ | ⟨x, pre, he, hx, -, ht, -, hpre⟩
  · rw [he] at hsome hρt
    rcases hρ with hρ | hρ
    · rw [hρ] at hsome; cases hsome
    · omega
  · rw [he] at hsome hρt ⊢
    rw [persists_append]
    have hS := settle_shape (cfg := cfg) hx
    rcases hpre with ⟨-, hxt⟩ | ⟨hn, hx0, g, rfl, hg, -⟩
    · by_cases hn : s.top = none
      · have := hS.none (by change x.top = none; rw [hxt, hn])
        rw [this] at hsome; cases hsome
      · have hρ' : s.top.getD 0 < ρ := hρ.resolve_left hn
        obtain ⟨e, he', her⟩ := hS.every (by
          change x.top.isSome; rw [hxt]; exact Option.ne_none_iff_isSome.mp hn) ρ
          (by change x.top.getD 0 < ρ; rw [ht]; exact hρ') hρt
        exact ⟨e, List.mem_append_right _ he', her⟩
    · by_cases h0 : ρ = 0
      · exact ⟨g, List.mem_append_left _ (by simp [persists]), by rw [hg, h0]⟩
      · obtain ⟨e, he', her⟩ := hS.every (by change x.top.isSome; rw [hx0]; rfl) ρ
          (by change x.top.getD 0 < ρ; rw [hx0]; simp; omega) hρt
        exact ⟨e, List.mem_append_right _ he', her⟩

/-- **A step sets the timer of each round it builds.** -/
theorem step_timer (hs : s.recovering = false) (hr : inp ≠ .restart) :
    ∀ e ∈ persists (Node.step cfg s inp).2,
      Output.setTimer e.2.round (cfg.timeout e.2.round) ∈ (Node.step cfg s inp).2 := by
  rcases step_shape (cfg := cfg) hs hr with ⟨-, hq⟩ | ⟨x, pre, he, hx, -, -, -, hpre⟩
  · rw [hq.1]; intro e he; cases he
  · rw [he, persists_append]
    intro e he'
    rcases List.mem_append.mp he' with he' | he'
    · rcases hpre with ⟨hp, -⟩ | ⟨-, -, g, rfl, hg, -⟩
      · rw [hp.1] at he'; cases he'
      · simp only [persists] at he'
        simp at he'
        subst he'
        rw [hg]
        exact List.mem_append_left _ (by simp)
    · exact List.mem_append_right _ ((settle_shape (cfg := cfg) hx).timer e he')

/-- **A step keeps a fired timer** at or above the top it reaches. -/
theorem step_fired (hs : s.recovering = false) (hr : inp ≠ .restart) :
    ∀ ρ ∈ s.fired, (Node.step cfg s inp).1.top.getD 0 ≤ ρ → ρ ∈ (Node.step cfg s inp).1.fired := by
  rcases step_shape (cfg := cfg) hs hr with ⟨he, -⟩ | ⟨x, pre, he, hx, -, -, hf, -⟩
  · rw [he]; exact fun ρ h _ => h
  · rw [he]
    exact fun ρ h hρ => (settle_shape (cfg := cfg) hx).fired ρ (hf h) hρ

/-- **What a step builds it stores**, at its round, or the block lies
below the horizon. -/
theorem step_keeps_built (hs : s.recovering = false) (hr : inp ≠ .restart) :
    KeepsBuilt (Node.step cfg s inp).2 (Node.step cfg s inp).1 := by
  rcases step_shape (cfg := cfg) hs hr with ⟨-, hq⟩ | ⟨x, pre, he, hx, -, -, -, hpre⟩
  · intro e he; rw [hq.1] at he; cases he
  · rw [he]
    intro e he'
    rw [persists_append] at he'
    rcases List.mem_append.mp he' with he' | he'
    · rcases hpre with ⟨hp, -⟩ | ⟨-, -, g, rfl, hg, hgi, hgr⟩
      · rw [hp.1] at he'; cases he'
      · simp only [persists] at he'
        simp at he'
        subst he'
        have hR := retains_quiesce (cfg := cfg) (passes cfg x) x
        rw [← settle_of_idle hx] at hR
        have hk : KeepsBuilt [Output.persist e.1 e.2] x := fun e' he'' => by
          simp [persists] at he''
          subst he''
          exact Or.inl ⟨hgi, by rw [hgr, hg]⟩
        exact hk.of_retains hR.1 hR.2 e (by simp [persists])
    · have := quiesce_keeps_built (cfg := cfg) (passes cfg x) x
      rw [← settle_of_idle hx] at this
      exact this e he'

end StepFacts

/-! ## Building on a timer -/

omit [Fintype Validator] in
/-- **`refsFor`'s references**: stored blocks of the round, one per
author of the round it may reference, holding `X` exposed, the node's
own block for itself if it has one. -/
theorem refsFor_spec {st : Store Validator BlockId Payload} {r : ℕ} {o : Option BlockId}
    {X : Finset Validator}
    (ho : ∀ j, o = some j → j ∈ st.ids ∧ (st.blk j).round = r ∧ (st.blk j).creator = cfg.me) :
    refsFor cfg st r o X ⊆ st.ids ∧ (∀ j ∈ refsFor cfg st r o X, (st.blk j).round = r) ∧
      creatorsOf st.blk (refsFor cfg st r o X) = usableAuthors st X r ∧
      ∀ i ∈ refsFor cfg st r o X, ∀ j ∈ refsFor cfg st r o X,
        (st.blk i).creator = (st.blk j).creator → i = j := by
  set R := (blocksAt st.toRecord r).filter fun i => usable st X i with hR
  have hRi : ∀ i ∈ R, i ∈ st.ids ∧ (st.blk i).round = r := fun i hi => by
    have := (Finset.mem_filter.mp hi).1
    simpa [blocksAt, Store.toRecord] using this
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
  have hdef : refsFor cfg st r o X = (creatorsOf st.blk R).biUnion pick := rfl
  have hmem : ∀ j ∈ refsFor cfg st r o X, ∃ a ∈ creatorsOf st.blk R, j ∈ st.ids ∧
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
  · have hauth : usableAuthors st X r = creatorsOf st.blk R := rfl
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
theorem refsAt_buildable (st : Store Validator BlockId Payload) (r : ℕ) (o : Option BlockId)
    (X : Finset Validator) :
    refsAt cfg st r o X = refsFor cfg st r o X ∨ buildable cfg st r (refsAt cfg st r o X) = true := by
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
a horizon at or below the round, and no stored block with the identifier
of a next block of its own. -/
theorem tryBuild_isSome {s : State Validator BlockId Payload} {r : ℕ} (ht : s.top = some r)
    (hf : r ∈ s.fired ∨ (reachReady cfg s.store (refsAt cfg s.store r s.own s.exposed) r = true ∧
      certReady cfg s.store (refsAt cfg s.store r s.own s.exposed) r = true))
    (hq : cfg.q ≤ (usableAuthors s.store s.exposed r).card)
    (ho : ∀ j, s.own = some j → j ∈ s.store.ids ∧ (s.store.blk j).round = r ∧
      (s.store.blk j).creator = cfg.me)
    (hb : s.store.base ≤ r)
    (hfresh : ∀ R, cfg.idOf ⟨r + 1, cfg.me, R, cfg.payload (r + 1)⟩ ∉ s.store.ids) :
    (tryBuild cfg s).isSome := by
  unfold tryBuild
  rw [ht]
  dsimp only
  rw [if_pos ⟨hq, hf⟩]
  have hB : buildable cfg s.store r (refsAt cfg s.store r s.own s.exposed) = true := by
    rcases refsAt_buildable (cfg := cfg) s.store r s.own s.exposed with he | he
    · rw [he]
      obtain ⟨hsub, hrd, hcr, hdis⟩ := refsFor_spec (cfg := cfg) (st := s.store) (r := r) (X := s.exposed) ho
      have hnin : ∀ j ∈ refsFor cfg s.store r s.own s.exposed,
          j ≠ cfg.idOf ⟨r + 1, cfg.me, refsFor cfg s.store r s.own s.exposed, cfg.payload (r + 1)⟩ :=
        fun j hj h => hfresh _ (h ▸ hsub hj)
      unfold buildable
      refine decide_eq_true ⟨hfresh _, by simp; omega, fun _ => hsub,
        fun _ j hj => by simp; rw [hrd j hj], ⟨fun j hj => ?_, fun _ => ?_, fun i hi j hj hij => ?_⟩⟩
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
