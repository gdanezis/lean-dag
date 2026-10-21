import LeanDag.Node.Helpers.Commits
/-!
# A node's store stays a cut through bootstraps

A bootstrap at a round the record reaches keeps the store a cut of the
record (`IsCut.boot`): the pruned store is one, the attested base is
known blocks at that round, and the offered blocks are known. With every other step (`IsCut.step`), the store stays a
cut along a run whose bootstraps are at rounds the record reaches, and
every decision a step outputs is a verdict on a view of the record
(`Verdict`): the decision step reads as `tryDecide` on such a view, which
derives what it outputs (`Loop.sound`). A node's base offers came from
its inputs (`step_offers`).
-/

namespace LeanDag

namespace Node

open Scheme

variable {Validator BlockId Payload : Type} [Fintype Validator] [DecidableEq Validator]
variable [LinearOrder BlockId]
variable {cfg : Config Validator BlockId Payload}
variable {P : Validity Validator BlockId Payload} [P.Mechanised] {H : Finset Validator}
variable {U : BlockRecord Validator BlockId Payload P H}
variable {K : Set (BlockId × Block Validator BlockId Payload)}

variable (cfg U) in
/-- **A verdict on the record**: a slot's decision that the scheme derives
on some view of `U`, at the bounded vote. -/
def Verdict (e : ℕ × Option BlockId) : Prop :=
  letI := cfg.slots
  ∃ V : U.View, (schemeAnchored cfg.p boundedSel).Decided U V e.1 e.2

/-! ## Offers -/

omit [Fintype Validator] in
theorem tryBuild_certs {s s' : State Validator BlockId Payload}
    {out : List (Output Validator BlockId Payload)} (h : tryBuild cfg s = some (s', out)) :
    s'.offers = s.offers ∧ s'.certs = s.certs := by
  unfold tryBuild at h
  split at h
  · dsimp only at h
    split at h
    · split at h
      · rw [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, -⟩ := h
        exact ⟨rfl, rfl⟩
      · exact absurd h (by simp)
    · exact absurd h (by simp)
  · exact absurd h (by simp)

omit [Fintype Validator] in
/-- **Advancing keeps the offers**, of bases and of certificates. -/
theorem advance_offered (s : State Validator BlockId Payload) :
    (advance cfg s).1.offers = s.offers ∧ (advance cfg s).1.certs = s.certs := by
  have hp : ∀ (fuel : ℕ) (s : State Validator BlockId Payload),
      (progress cfg fuel s).1.offers = s.offers ∧ (progress cfg fuel s).1.certs = s.certs := by
    intro fuel
    induction fuel with
    | zero => intro _; exact ⟨rfl, rfl⟩
    | succ n ih =>
      intro s
      unfold Node.progress
      split
      · rename_i s₁ out h
        rw [(ih s₁).1, (ih s₁).2, (tryBuild_certs h).1, (tryBuild_certs h).2]
        exact ⟨rfl, rfl⟩
      · exact ⟨rfl, rfl⟩
  have hd : ∀ s : State Validator BlockId Payload,
      (decideStep cfg s).1.offers = s.offers ∧ (decideStep cfg s).1.certs = s.certs := by
    intro s; unfold Node.decideStep; dsimp only; split
    all_goals
      obtain ⟨-, -, -, -, hof, -, -, -, -, -, hce⟩ := proposeAt_keeps (cfg := cfg) _
      exact ⟨hof, hce⟩
  have hc : ∀ s : State Validator BlockId Payload,
      (collect cfg s).1.offers = s.offers ∧ (collect cfg s).1.certs = s.certs := by
    intro s; unfold Node.collect; split
    · dsimp only; split <;> exact ⟨rfl, rfl⟩
    · exact ⟨rfl, rfl⟩
  simp only [Node.advance]
  change (collect cfg (decideStep cfg (progress cfg (s.store.topRound + 2) s).1).1).1.offers = _ ∧
    (collect cfg (decideStep cfg (progress cfg (s.store.topRound + 2) s).1).1).1.certs = _
  rw [(hc _).1, (hc _).2, (hd _).1, (hd _).2, (hp _ _).1, (hp _ _).2]
  exact ⟨rfl, rfl⟩

omit [Fintype Validator] in
theorem quiesce_offered (n : ℕ) (s : State Validator BlockId Payload) :
    (quiesce cfg n s).1.offers = s.offers ∧ (quiesce cfg n s).1.certs = s.certs :=
  (quiesce_rel (P := fun _ => True) (R := fun a _ b => b.offers = a.offers ∧ b.certs = a.certs)
    (fun _ => ⟨rfl, rfl⟩) (fun _ _ _ _ _ h₁ h₂ => ⟨h₂.1.trans h₁.1, h₂.2.trans h₁.2⟩)
    (fun s _ => ⟨advance_offered s, trivial⟩) n s trivial).1

omit [Fintype Validator] in
theorem settle_offered (s : State Validator BlockId Payload) :
    (Node.settle cfg s).1.offers = s.offers ∧ (Node.settle cfg s).1.certs = s.certs := by
  rcases settle_cases (cfg := cfg) s with h | ⟨s₁, hj, h⟩ <;> rw [h]
  · exact quiesce_offered _ s
  · obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, hof, -⟩ := tryResume_some hj
    have hce : s₁.certs = s.certs := by
      unfold tryResume at hj
      split at hj
      · dsimp only at hj
        split at hj
        · split at hj
          · rw [Option.some.injEq] at hj; subst hj; rfl
          · cases hj
        · cases hj
      · cases hj
    rw [(quiesce_offered _ s₁).1, (quiesce_offered _ s₁).2, hof, hce]
    exact ⟨rfl, rfl⟩

omit [Fintype Validator] in
/-- **Trying to bootstrap keeps no offer it did not hold.** -/
theorem bootFrom_offered (s : State Validator BlockId Payload) :
    (∀ o ∈ (bootFrom cfg s).1.offers, o ∈ s.offers) ∧
      ∀ c ∈ (bootFrom cfg s).1.certs, c ∈ s.certs := by
  rcases bootFrom_cases (cfg := cfg) s with he | ⟨s₂, ads, hb, he⟩ <;> rw [he]
  · exact ⟨fun _ h => h, fun _ h => h⟩
  · obtain ⟨t, G, c, ds, hbG, -, -, -, -, -, -, -, -, -, -, hof, -, -, -, -, hce, -⟩ :=
      tryBoot_some hb
    rw [(advance_offered s₂).1, (advance_offered s₂).2, hof, hce]
    exact ⟨fun _ h => absurd h List.not_mem_nil, fun _ h => absurd h List.not_mem_nil⟩

/-- **The offers a node holds were given to it**, at this step or before:
a base offer as a base offer, a certificate as a certificate offer. -/
theorem step_offered (s : State Validator BlockId Payload) (i : Input Validator BlockId Payload) :
    (∀ o ∈ (Node.step cfg s i).1.offers, o ∈ s.offers ∨ i = .baseOffer o.1 o.2.1 o.2.2) ∧
      ∀ c ∈ (Node.step cfg s i).1.certs, c ∈ s.certs ∨ ∃ p, i = .certOffer p c.1 c.2 := by
  cases i with
  | start =>
    simp only [Node.step]
    split
    · split
      · rw [(settle_offered _).1, (settle_offered _).2]
        exact ⟨fun o ho => Or.inl ho, fun c hc => Or.inl hc⟩
      · exact ⟨fun o ho => Or.inl ho, fun c hc => Or.inl hc⟩
    · exact ⟨fun o ho => Or.inl ho, fun c hc => Or.inl hc⟩
  | deliver id b =>
    simp only [Node.step]
    split
    · rw [(settle_offered _).1, (settle_offered _).2]
      exact ⟨fun o ho => Or.inl ho, fun c hc => Or.inl hc⟩
    · exact ⟨fun o ho => Or.inl ho, fun c hc => Or.inl hc⟩
  | timer r =>
    simp only [Node.step]
    rw [(settle_offered _).1, (settle_offered _).2]
    exact ⟨fun o ho => Or.inl ho, fun c hc => Or.inl hc⟩
  | restart =>
    simp only [Node.step]
    rw [(settle_offered _).1, (settle_offered _).2]
    exact ⟨fun o ho => by simp [State.recover] at ho, fun c hc => by simp [State.recover] at hc⟩
  | fetchRequest => exact ⟨fun o ho => Or.inl ho, fun c hc => Or.inl hc⟩
  | baseRequest => exact ⟨fun o ho => Or.inl ho, fun c hc => Or.inl hc⟩
  | proposal p k kh =>
    rw [step_proposal]
    split
    · obtain ⟨n, hn⟩ := seek_eq (cfg := cfg) (record cfg s p k kh) k kh
      rw [hn, (settle_offered _).1, (settle_offered _).2]
      exact ⟨fun o ho => Or.inl ho, fun c hc => Or.inl hc⟩
    · exact ⟨fun o ho => Or.inl ho, fun c hc => Or.inl hc⟩
  | decisionRequest => exact ⟨fun o ho => Or.inl ho, fun c hc => Or.inl hc⟩
  | baseOffer p G bs =>
    rw [step_offer]
    split
    · obtain ⟨h₁, h₂⟩ := bootFrom_offered (cfg := cfg) (withOffer s p G bs)
      refine ⟨fun o ho => ?_, fun c hc => Or.inl (h₂ c hc)⟩
      rcases List.mem_cons.mp (h₁ o ho) with rfl | ho
      · exact Or.inr rfl
      · exact Or.inl (List.mem_filter.mp ho).1
    · exact ⟨fun o ho => Or.inl ho, fun c hc => Or.inl hc⟩
  | certOffer p c ds =>
    rcases certOffer_cases (cfg := cfg) s p c ds with ⟨-, -, he⟩ | ⟨-, ds', -, -, ha, he⟩ |
      ⟨-, -, -, he⟩ | ⟨-, he⟩ <;> rw [he]
    · obtain ⟨h₁, h₂⟩ := bootFrom_offered (cfg := cfg) (withCert s c ds)
      refine ⟨fun o ho => Or.inl (h₁ o ho), fun c' hc => ?_⟩
      rcases List.mem_cons.mp (h₂ c' hc) with rfl | hc
      · exact Or.inr ⟨p, rfl⟩
      · exact Or.inl hc
    · rw [adopt_eq, (settle_offered _).1, (settle_offered _).2]
      exact ⟨fun o ho => Or.inl ho, fun c hc => Or.inl hc⟩
    · unfold confirm
      rw [(settle_offered _).1, (settle_offered _).2]
      exact ⟨fun o ho => Or.inl ho, fun c hc => Or.inl hc⟩
    · exact ⟨fun o ho => Or.inl ho, fun c hc => Or.inl hc⟩
  | announced p c =>
    rcases announced_cases (cfg := cfg) s p c with ⟨-, -, he⟩ | he | he <;> rw [he]
    · unfold confirm
      rw [(settle_offered _).1, (settle_offered _).2]
      exact ⟨fun o ho => Or.inl ho, fun c hc => Or.inl hc⟩
    · exact ⟨fun o ho => Or.inl ho, fun c hc => Or.inl hc⟩
    · exact ⟨fun o ho => Or.inl ho, fun c hc => Or.inl hc⟩

/-! ## The store stays a cut -/

omit [Fintype Validator] in
/-- **A bootstrap at a round the record reaches keeps the store a cut.** -/
theorem IsCut.boot (hg : Ground U K cfg.q) {s s' : State Validator BlockId Payload}
    {ads : List (ℕ × Option BlockId)} (hc : IsCut U s.store) (hb : tryBoot cfg s = some (s', ads))
    (hoff : ∀ o ∈ s.offers, ∀ e ∈ o.2.2, e.1 = cfg.idOf e.2 → e ∈ K)
    (hp : ∀ e ∈ s.pending, e ∈ K) (hspan : Spans U s'.store.base) : IsCut U s'.store := by
  obtain ⟨t, G, c, ds, hbG, -, -, -, -, hst, -⟩ := tryBoot_some hb
  set st₀ := (keptBase cfg (baseAt cfg s G)).foldl (fun st e => Node.accept cfg st e.1 e.2)
    (s.store.prune G hbG.le)
    with hst₀
  have hb₀ : st₀.base = G := by rw [hst₀, foldl_base]; rfl
  have hbs : s'.store.base = G := by rw [hst, flush_base]; exact hb₀
  rw [hbs] at hspan
  have hfo : ∀ x ∈ s.offers.flatMap (·.2.2), x.1 = cfg.idOf x.2 → x ∈ K := by
    intro x hx hid
    obtain ⟨o, ho, hxo⟩ := List.mem_flatMap.mp hx
    exact hoff o ho x hxo hid
  have hc₀ : IsCut U st₀ := by
    rw [hst₀]
    refine IsCut.foldl hg _ (hc.prune hbG.le) hspan fun x hx => ?_
    obtain ⟨hx, hcx⟩ := List.mem_filter.mp (mem_keptBase hx)
    simp only [decide_eq_true_eq] at hcx
    exact hfo x hx hcx.2.1
  rw [hst]
  refine IsCut.flush hg _ _ hc₀ (by change Spans U st₀.base; rw [hb₀]; exact hspan) fun x hx => ?_
  rcases List.mem_append.mp hx with hx | hx
  · obtain ⟨hx, -, hcx⟩ := mem_bootWindow hx
    exact hfo x hx hcx
  · exact hp x (List.mem_filter.mp hx).1

variable {q f : ℕ} [P.Quorate q]

/-- **What a decision step outputs is a verdict on the record**, from a
store that is a cut of it. -/
theorem verdict_decideStep (hσ : cfg.σ = boundedSel) (ht : cfg.p.Tolerates H f q)
    {s : State Validator BlockId Payload} (hc : IsCut U s.store) (hh : Held cfg s) :
    ∀ e ∈ commitsOf (decideStep cfg s).2, Verdict cfg U e := by
  letI := cfg.slots
  have hw : 2 ≤ cfg.p.waveLength := by
    rcases ht.2.2 with ⟨-, hw, -⟩ | ⟨-, hw, -⟩ | ⟨-, hw, -⟩ | ⟨-, hw, -⟩ <;> omega
  obtain ⟨hl, -, hcv, -⟩ := coveredLaws (boundedSel (P := P) (honest := H)) ht
  intro e he
  unfold Node.decideStep at he
  dsimp only at he
  split at he
  · rename_i hlt
    rw [commitsOf_append, commitsOf_map, proposeAt_commits, List.append_nil] at he
    obtain ⟨V', -, hiff⟩ := hc.extend ⟨∅, Finset.empty_subset _,
      fun _ h => absurd h (Finset.notMem_empty _)⟩ (fun i hi => absurd hi (Finset.notMem_empty i))
    have hT : tryDecide cfg.p cfg.σ s.store.toRecord s.store.view s.lo
        (decidable cfg s.store.topRound - 1) =
        tryDecide cfg.p boundedSel U V' s.lo (decidable cfg s.store.topRound - 1) := by
      rw [hσ]
      exact (ViewsAbove.of_store hiff fun i hi => (hc i hi).2).tryDecide_eq cfg.p hw _ hh.horizon
    rw [hT] at he
    exact ⟨V', (Loop.sound _ _ _ P H cfg.p boundedSel U V' s.lo _ hl hcv (by omega)).2 e he⟩
  · rw [proposeAt_commits] at he; simp at he

/-- **Advancing from a cut**: the store stays one, and the decisions are
verdicts. -/
theorem IsCut.advance (hg : Ground U K cfg.q) (hσ : cfg.σ = boundedSel)
    (ht : cfg.p.Tolerates H f q) {s : State Validator BlockId Payload} (hc : IsCut U s.store)
    (hh : Held cfg s) (hp : ∀ e ∈ s.pending, e ∈ K)
    (hb : ∀ e ∈ persists (Node.advance cfg s).2, e ∈ K) :
    IsCut U (Node.advance cfg s).1.store ∧
      ∀ e ∈ commitsOf (Node.advance cfg s).2, Verdict cfg U e := by
  obtain ⟨bs, hbs⟩ := progress_built (cfg := cfg) (s.store.topRound + 2) s
  have hp₁ := (progress_pending (cfg := cfg) (s.store.topRound + 2) s).1
  simp only [Node.advance] at hb ⊢
  rw [persists_append, persists_append] at hb
  have hc₁ := IsCut.progress hg _ hc hh fun e he => hb e
    (List.mem_append_left _ (List.mem_append_left _ he))
  have hh₁ := Held.progress (s.store.topRound + 2) hh
  generalize Node.progress cfg (s.store.topRound + 2) s = r at hbs hp₁ hc₁ hh₁ ⊢
  have hd := decideStep_store (cfg := cfg) r.1
  have hdp := (decideStep_pending (cfg := cfg) r.1).1
  have hv := verdict_decideStep (U := U) hσ ht hc₁ hh₁
  have hc₂ : IsCut U (Node.decideStep cfg r.1).1.store := by rw [hd]; exact hc₁
  obtain ⟨hh₃, -⟩ := Held.collect hh₁.decideStep
  have hc₃ := hc₂.collect (cfg := cfg)
  have hco := commitsOf_collect (cfg := cfg) (Node.decideStep cfg r.1).1
  have hcp := (collect_sub (cfg := cfg) (Node.decideStep cfg r.1).1).1
  generalize Node.collect cfg (Node.decideStep cfg r.1).1 = g at hh₃ hc₃ hco hcp ⊢
  have hgp : ∀ e ∈ g.1.pending, e ∈ K := fun e he => hp e (by
    have := hcp e he; rwa [hdp, hp₁] at this)
  refine ⟨IsCut.flush hg (g.1.pending.length + 1) g.1.pending hc₃ (hc₃.spans hh₃) hgp, ?_⟩
  intro e he
  rw [commitsOf_append, commitsOf_append, hbs, commitsOf_built, hco, List.nil_append,
    List.append_nil] at he
  exact hv e he

/-- **The passes from a cut**: the store stays one, and the decisions are
verdicts. -/
theorem IsCut.quiesce (hg : Ground U K cfg.q) (hσ : cfg.σ = boundedSel)
    (ht : cfg.p.Tolerates H f q) : ∀ (n : ℕ) {s : State Validator BlockId Payload},
    IsCut U s.store → Held cfg s → (∀ e ∈ s.pending, e ∈ K) →
    (∀ e ∈ persists (Node.quiesce cfg n s).2, e ∈ K) →
    IsCut U (Node.quiesce cfg n s).1.store ∧
      ∀ e ∈ commitsOf (Node.quiesce cfg n s).2, Verdict cfg U e
  | 0, s, hc, _, _, _ => ⟨hc, fun e he => by simp [Node.quiesce, commitsOf] at he⟩
  | n + 1, s, hc, hh, hp, hb => by
    rcases quiesce_succ_cases (cfg := cfg) n s with he | he <;> rw [he] at hb ⊢
    · exact hc.advance hg hσ ht hh hp hb
    · rw [persists_append] at hb
      obtain ⟨hc₁, hv₁⟩ := hc.advance hg hσ ht hh hp fun e he => hb e (List.mem_append_left _ he)
      obtain ⟨hc₂, hv₂⟩ := IsCut.quiesce hg hσ ht n hc₁ hh.advance
        (fun e he => hp e ((advance_sub (cfg := cfg) s).1 e he))
        fun e he => hb e (List.mem_append_right _ he)
      refine ⟨hc₂, fun e he => ?_⟩
      rw [commitsOf_append] at he
      exact (List.mem_append.mp he).elim (hv₁ e) (hv₂ e)

/-- **Settling from a cut**: the store stays one, and the decisions are
verdicts. -/
theorem IsCut.settle (hg : Ground U K cfg.q) (hσ : cfg.σ = boundedSel)
    (ht : cfg.p.Tolerates H f q) {s : State Validator BlockId Payload} (hc : IsCut U s.store)
    (hh : Held cfg s) (hp : ∀ e ∈ s.pending, e ∈ K)
    (hb : ∀ e ∈ persists (Node.settle cfg s).2, e ∈ K) :
    IsCut U (Node.settle cfg s).1.store ∧
      ∀ e ∈ commitsOf (Node.settle cfg s).2, Verdict cfg U e := by
  rcases settle_cases (cfg := cfg) s with he | ⟨s₁, hj, he⟩ <;> rw [he] at hb ⊢
  · exact IsCut.quiesce hg hσ ht _ hc hh hp hb
  · obtain ⟨hst, hpd, -⟩ := tryResume_keeps hj
    exact IsCut.quiesce hg hσ ht _ (by rw [hst]; exact hc) (hh.tryResume hj)
      (by rw [hpd]; exact hp) hb

/-- **Trying to bootstrap from a cut**, at a round the record reaches,
with offered certificates whose decisions, where their chain has the
certificate's head, are verdicts: the store stays a cut, and the
decisions are verdicts. -/
theorem IsCut.bootFrom (hg : Ground U K cfg.q) (hσ : cfg.σ = boundedSel)
    (ht : cfg.p.Tolerates H f q) {s₁ : State Validator BlockId Payload}
    (hc : IsCut U s₁.store) (hh : Held cfg s₁) (hp : ∀ e ∈ s₁.pending, e ∈ K)
    (hoff : ∀ o ∈ s₁.offers, ∀ e ∈ o.2.2, e.1 = cfg.idOf e.2 → e ∈ K)
    (hcv : ∀ x ∈ s₁.certs, cfg.q ≤ x.1.signers.length → x.1.signers.Nodup →
      cfg.headOf x.2 = x.1.head → ∀ e ∈ x.2, Verdict cfg U e)
    (hb : ∀ e ∈ persists (Node.bootFrom cfg s₁).2, e ∈ K)
    (hspan : ∀ s₂ ads, tryBoot cfg s₁ = some (s₂, ads) → Spans U s₂.store.base) :
    IsCut U (Node.bootFrom cfg s₁).1.store ∧
      ∀ e ∈ commitsOf (Node.bootFrom cfg s₁).2, Verdict cfg U e := by
  rcases bootFrom_cases (cfg := cfg) s₁ with he | ⟨s₂, ads, hbt, he⟩ <;> rw [he] at hb ⊢
  · exact ⟨hc, fun e he => by simp [commitsOf] at he⟩
  · rw [persists_append] at hb
    have hc₂ := IsCut.boot hg hc hbt hoff hp (hspan s₂ ads hbt)
    have hh₂ := hh.boot hbt
    obtain ⟨t', G', c, ds, hb', -, -, -, hcf, -, hpd, -, -, -, -, -, -, -, hads, -⟩ :=
      tryBoot_some hbt
    obtain ⟨h₁, h₂⟩ := hc₂.advance hg hσ ht hh₂ (fun e he => by
      rw [hpd] at he
      rcases List.mem_append.mp (flush_pending_sub (cfg := cfg) _ _ _ e he) with he | he
      · obtain ⟨he, -, hce⟩ := mem_bootWindow he
        obtain ⟨o, ho, heo⟩ := List.mem_flatMap.mp he
        exact hoff o ho e heo hce
      · exact hp e (List.mem_filter.mp he).1) (fun e he => hb e (List.mem_append_right _ he))
    refine ⟨h₁, fun e he => ?_⟩
    rw [commitsOf_append, commitsOf_map] at he
    rcases List.mem_append.mp he with he | he
    · obtain ⟨hcm, hv⟩ := certFor_valid hcf
      obtain ⟨hq, hnd, -, hhd, -⟩ := (validCert_iff (cfg := cfg)).mp hv
      rw [hads] at he
      exact hcv (c, ds) hcm hq hnd hhd e (List.mem_of_mem_drop he)
    · exact h₂ e he

/-- The state with the offer an input gives recorded, if any. -/
def withInput (s : State Validator BlockId Payload) :
    Input Validator BlockId Payload → State Validator BlockId Payload
  | .baseOffer p G bs => withOffer s p G bs
  | .certOffer _ c ds => withCert s c ds
  | _ => s

omit [Fintype Validator] in
/-- The offers of a state with an input's offer recorded: its own, and
the input's. -/
theorem withInput_offered {s : State Validator BlockId Payload}
    {i : Input Validator BlockId Payload} :
    (∀ o ∈ (withInput s i).offers, o ∈ s.offers ∨ i = .baseOffer o.1 o.2.1 o.2.2) ∧
      ∀ c ∈ (withInput s i).certs, c ∈ s.certs ∨ ∃ p, i = .certOffer p c.1 c.2 := by
  cases i with
  | baseOffer p G bs =>
    refine ⟨fun o ho => ?_, fun c hc => Or.inl hc⟩
    rcases List.mem_cons.mp ho with rfl | ho
    · exact Or.inr rfl
    · exact Or.inl (List.mem_filter.mp ho).1
  | certOffer p c ds =>
    refine ⟨fun o ho => Or.inl ho, fun c' hc => ?_⟩
    rcases List.mem_cons.mp hc with rfl | hc
    · exact Or.inr ⟨p, rfl⟩
    · exact Or.inl hc
  | _ => exact ⟨fun o ho => Or.inl ho, fun c hc => Or.inl hc⟩

/-- **A step from a cut**, bootstrapping only at rounds the record
reaches and from certificates whose decisions are verdicts: the store
stays a cut, and the decisions are verdicts. -/
theorem IsCut.step (hg : Ground U K cfg.q) (hσ : cfg.σ = boundedSel)
    (ht : cfg.p.Tolerates H f q) {s : State Validator BlockId Payload}
    (i : Input Validator BlockId Payload) (hc : IsCut U s.store) (hh : Held cfg s)
    (hp : ∀ e ∈ s.pending, e ∈ K)
    (hoff : ∀ o ∈ s.offers, ∀ e ∈ o.2.2, e.1 = cfg.idOf e.2 → e ∈ K)
    (hd : ∀ e ∈ delivered cfg [i], e ∈ K)
    (hb : ∀ e ∈ persists (Node.step cfg s i).2, e ∈ K)
    (hcv : ∀ x ∈ (withInput s i).certs, cfg.q ≤ x.1.signers.length → x.1.signers.Nodup →
      cfg.headOf x.2 = x.1.head → ∀ e ∈ x.2, Verdict cfg U e)
    (hspan : ∀ s₂ ads, tryBoot cfg (withInput s i) = some (s₂, ads) → Spans U s₂.store.base)
    (hadopt : ∀ p c ds, i = .certOffer p c ds → ∀ ds', ds'.Sublist ds →
      adoptable cfg s c ds' = true → ∀ e ∈ ds', Verdict cfg U e) :
    IsCut U (Node.step cfg s i).1.store ∧
      ∀ e ∈ commitsOf (Node.step cfg s i).2, Verdict cfg U e := by
  have hset : ∀ (s₀ : State Validator BlockId Payload) (pre : List (Output Validator BlockId Payload)),
      IsCut U s₀.store → Held cfg s₀ → (∀ e ∈ s₀.pending, e ∈ K) → commitsOf pre = [] →
      Node.step cfg s i = ((Node.settle cfg s₀).1, pre ++ (Node.settle cfg s₀).2) →
      IsCut U (Node.step cfg s i).1.store ∧
        ∀ e ∈ commitsOf (Node.step cfg s i).2, Verdict cfg U e := by
    intro s₀ pre hc₀ hh₀ hp₀ hpre he
    rw [he] at hb ⊢
    rw [persists_append] at hb
    rw [commitsOf_append, hpre, List.nil_append]
    exact hc₀.settle hg hσ ht hh₀ hp₀ fun e he => hb e (List.mem_append_right _ he)
  have hsame : ∀ s' : State Validator BlockId Payload, s'.store = s.store →
      Node.step cfg s i = (s', []) →
      IsCut U (Node.step cfg s i).1.store ∧
        ∀ e ∈ commitsOf (Node.step cfg s i).2, Verdict cfg U e := by
    intro s' hs he; rw [he, hs]; exact ⟨hc, fun e he => by simp [commitsOf] at he⟩
  cases i with
  | start =>
    by_cases h₁ : s.top = none ∧ cfg.Admissible
    · by_cases h₂ : cfg.idOf cfg.genesis ∉ s.store.ids ∧ s.store.base ≤ cfg.genesis.round ∧
          rowValid cfg.q (Function.update s.store.blk (cfg.idOf cfg.genesis) cfg.genesis)
            cfg.genesis
      · let st := s.store.insert _ _ h₂.1 h₂.2.1 (fun _ => Finset.empty_subset _)
          (fun _ j hj => absurd hj (Finset.notMem_empty j))
        have h0 := hh.low h₁.1
        have hx : (cfg.idOf cfg.genesis, cfg.genesis) ∈ K :=
          hb _ (by simp only [Node.step, dif_pos h₂, if_pos h₁]; simp [persists])
        have hcst : IsCut U st := hc.insert (hg.base _ hx s.store.base
          (by simp [Config.genesis]) (Or.inl h0))
        let gid := cfg.idOf cfg.genesis
        have hh₀ : Held cfg
            { { s with store := st, top := some 0, own := some gid } with
            owner := slotted cfg [(gid, cfg.genesis)] ++ s.owner, recovering := false } := by
          refine ⟨fun t ht => ⟨_, Finset.mem_insert_self _ _, ?_⟩, hh.horizon,
            fun ht => absurd ht (by simp), fun t _ => ?_, hh.junk⟩
          · simp only [Option.some.injEq] at ht
            simp only [st, Store.blk, Store.insert, lookup, Std.TreeMap.getD_insert_self,
              atBase_round]
            exact ht.ge
          · change s.store.base ≤ t
            omega
        exact hset { { s with store := st, top := some 0, own := some gid } with
            owner := slotted cfg [(gid, cfg.genesis)] ++ s.owner, recovering := false }
          (built cfg [(cfg.idOf cfg.genesis, cfg.genesis)]) hcst hh₀ hp
          (commitsOf_built _) (by simp only [Node.step, dif_pos h₂, if_pos h₁]; rfl)
      · exact hsame s rfl (by simp only [Node.step, dif_neg h₂, if_pos h₁])
    · exact hsame s rfl (by simp only [Node.step, if_neg h₁])
  | deliver id b =>
    by_cases hA : Admits cfg s id b
    · let s₁ := afterFlush (cfg := cfg) s id b
      let miss := askable cfg s₁ id (missing s₁ id b)
      have hx : (id, b) ∈ K := hd _ (by simp [delivered, ← hA.1])
      have hg₁ := Grows.flush (cfg := cfg) (s.pending.length + 1) s.store ((id, b) :: s.pending)
      have hb₁ := flush_base (cfg := cfg) (s.pending.length + 1) s.store ((id, b) :: s.pending)
      have hpend : ∀ e ∈ (id, b) :: s.pending, e ∈ K := fun e he => by
        rcases List.mem_cons.mp he with rfl | he
        · exact hx
        · exact hp e he
      let s₂ := { s₁ with requested := s₁.requested ++ miss.map fun (x : BlockId × ℕ) => (x.1, id, x.2) }
      exact hset { s₂ with asked := askedAfter (cfg := cfg) s b }
        (evidence s id b ++
          (if miss.isEmpty then [] else [.fetch b.creator s.store.base (miss.map Prod.fst)]) ++
          askOut (cfg := cfg) s b)
        (IsCut.flush hg _ _ hc (hc.spans hh) hpend) (hh.grow hg₁ hb₁ rfl le_rfl)
        (fun e he => hpend e (flush_pending_sub _ _ _ e he))
        (by
          rw [commitsOf_append, commitsOf_append, commitsOf_evidence]; unfold askOut
          split <;> split <;> rfl) (step_deliver hA)
    · have h' : ¬ (id = cfg.idOf b ∧ b.creator ≠ cfg.me ∧ s.store.base ≤ b.round ∧
          id ∉ s.store.ids ∧ id ∉ s.pending.map Prod.fst ∧ kept cfg s id b) := hA
      exact hsame s rfl (by simp only [Node.step, if_neg h'])
  | timer r =>
    exact hset { s with fired := Insert.insert r s.fired } [] hc
      (hh.grow (Grows.refl _) rfl rfl le_rfl) hp rfl (by simp only [Node.step]; rfl)
  | fetchRequest peer G ids =>
    rw [show Node.step cfg s (.fetchRequest peer G ids) = (s, answer s peer G ids) from rfl]
    refine ⟨hc, fun e he => ?_⟩
    unfold answer commitsOf at he
    rw [List.filterMap_map] at he
    simp at he
  | restart =>
    exact hset s.recover [.requestBase] hc
      (hh.grow (Grows.refl _) rfl rfl le_rfl) (fun e he => by simp [State.recover] at he) rfl
      (by simp only [Node.step]; rfl)
  | baseRequest peer =>
    rw [show Node.step cfg s (.baseRequest peer) = (s, .serveBase peer s.store.base
      s.store.window :: s.cert.toList.map (fun c => .serveCert peer c
        (s.decided.drop (s.lo - c.height)).reverse)) from rfl]
    exact ⟨hc, fun e he => by cases hcert : s.cert <;> simp [commitsOf, hcert] at he⟩
  | proposal p k kh =>
    by_cases hpm : p ≠ cfg.me
    · obtain ⟨n, hn⟩ := seek_eq (cfg := cfg) (record cfg s p k kh) k kh
      exact hset (seek cfg (record cfg s p k kh) k kh).1 (seek cfg (record cfg s p k kh) k kh).2
        (by rw [hn]; exact hc) (by rw [hn]; exact hh.grow (Grows.refl _) rfl rfl le_rfl)
        (by rw [hn]; exact hp)
        (commitsOf_requests fun o ho => Or.inl (seek_out (cfg := cfg) _ k kh o ho))
        (by rw [step_proposal, if_pos hpm])
    · rw [step_proposal, if_neg hpm]; exact ⟨hc, fun e he => by simp [commitsOf] at he⟩
  | decisionRequest p lo =>
    rw [step_decisionRequest, commitsOf_requests fun o ho => Or.inr (by
      split at ho
      · exact ⟨p, serveFrom_out s p lo o ho⟩
      · simp at ho)]
    exact ⟨hc, fun e he => absurd he List.not_mem_nil⟩
  | baseOffer p G bs =>
    by_cases hcnd : s.recovering ∧ p ≠ cfg.me
    · rw [step_offer, if_pos hcnd] at hb ⊢
      have hoff' : ∀ o ∈ (withOffer s p G bs).offers, ∀ e ∈ o.2.2, e.1 = cfg.idOf e.2 →
          e ∈ K := by
        intro o ho e heo hid
        rcases List.mem_cons.mp ho with rfl | ho
        · exact hd e (by simp [delivered, heo, hid])
        · exact hoff o (List.mem_filter.mp ho).1 e heo hid
      exact IsCut.bootFrom hg hσ ht (s₁ := withOffer s p G bs) hc
        (hh.grow (s' := withOffer s p G bs) (Grows.refl _) rfl rfl le_rfl) hp hoff' hcv hb hspan
    · exact hsame s rfl (by rw [step_offer, if_neg hcnd])
  | certOffer p c ds =>
    by_cases hcnd : s.recovering ∧ p ≠ cfg.me
    · rw [step_certOffer, if_pos hcnd] at hb ⊢
      exact IsCut.bootFrom hg hσ ht (s₁ := withCert s c ds) hc
        (hh.grow (s' := withCert s c ds) (Grows.refl _) rfl rfl le_rfl) hp hoff hcv hb hspan
    · rcases certOffer_cases (cfg := cfg) s p c ds with ⟨h₁, h₂, -⟩ | ⟨-, ds', hsub, -, ha, he⟩ |
        ⟨-, -, -, he⟩ | ⟨-, he⟩
      · exact absurd ⟨h₁, h₂⟩ hcnd
      · rw [he, adopt_eq] at hb ⊢
        rw [persists_append] at hb
        obtain ⟨h₁, h₂⟩ := IsCut.settle (s := adopted s c ds') hg hσ ht hc
          (hh.grow (Grows.refl _) rfl rfl (adoptable_lo ha).le) hp
          fun e he => hb e (List.mem_append_right _ he)
        refine ⟨h₁, fun e he => ?_⟩
        rw [commitsOf_append, commitsOf_map] at he
        rcases List.mem_append.mp he with he | he
        · exact hadopt p c ds rfl ds' hsub ha e he
        · exact h₂ e he
      · exact hset { s with cert := some c, props := above (some c) s.props } [] hc
          (hh.grow (Grows.refl _) rfl rfl le_rfl) hp rfl (by rw [he]; rfl)
      · exact hsame s rfl he
  | announced p c =>
    rcases announced_cases (cfg := cfg) s p c with ⟨-, -, he⟩ | he | he
    · exact hset { s with cert := some c, props := above (some c) s.props } [] hc
        (hh.grow (Grows.refl _) rfl rfl le_rfl) hp rfl (by rw [he]; rfl)
    · rw [he]; exact ⟨hc, fun e he => by simp [commitsOf] at he⟩
    · exact hsame s rfl he

end Node

end LeanDag
