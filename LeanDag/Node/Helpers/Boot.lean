import LeanDag.Node.Helpers.Commits
/-!
# A node's store stays a cut along a run

With every step (`IsCut.step`), the store stays a cut of the record and
every decision a step outputs is a verdict on a view of the record
(`Verdict`): the decision step reads as `tryDecide` on such a view, which
derives what it outputs (`Loop.sound`). A recovering node's horizon may
lie at the round of a slot it decided; the record reaches that round,
since a verdict's slot lies at a round the record reaches
(`Verdict.spans`).
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

/-! ## The store stays a cut -/

omit [Fintype Validator] in
/-- **The record reaches a verdict's slot**: a skip holds a block at the
slot's vote round. -/
theorem Verdict.spans (hpos : 0 < cfg.p.skipThreshold) {e : ℕ × Option BlockId}
    (h : Verdict cfg U e) : Spans U (cfg.slots.slotRound e.1) := by
  letI := cfg.slots
  obtain ⟨V, hd⟩ := h
  refine Or.inr (AnchoredRule.Decided.reaches (fun k hs => ?_) hd)
  change cfg.p.skipThreshold ≤ (heldAuthors U V (blamersAt cfg.p boundedSel U k)).card at hs
  obtain ⟨v, hv⟩ := Finset.card_pos.mp (lt_of_lt_of_le hpos hs)
  obtain ⟨b, hb, -, -⟩ := mem_heldAuthors.mp hv
  obtain ⟨hbU, hbr⟩ := mem_blocksAt.mp (Finset.mem_filter.mp hb).1
  exact ⟨b, hbU, by rw [hbr]; omega⟩

omit [Fintype Validator] in
/-- **The record reaches every slot a node decided**, its decisions being
verdicts on slots `0, …, lo − 1`. -/
theorem SpansDecided.of_verdicts (hpos : 0 < cfg.p.skipThreshold)
    {s : State Validator BlockId Payload}
    (hL : s.decided.reverse.map Prod.fst = List.range s.lo)
    (hv : ∀ e ∈ s.decided, Verdict cfg U e) : SpansDecided cfg U s := by
  intro k hk
  have : k ∈ s.decided.reverse.map Prod.fst := by rw [hL]; exact List.mem_range.mpr hk
  obtain ⟨e, he, rfl⟩ := List.mem_map.mp this
  exact (hv e (List.mem_reverse.mp he)).spans hpos

omit [Fintype Validator] in
/-- **Adopting verdicts keeps the record reaching every decided slot.** -/
theorem SpansDecided.adopted (hpos : 0 < cfg.p.skipThreshold) {s : State Validator BlockId Payload}
    {c : Cert Validator BlockId} {ds : List (ℕ × Option BlockId)} (hR : SpansDecided cfg U s)
    (ha : adoptable cfg s c ds = true) (hv : ∀ e ∈ ds, Verdict cfg U e) :
    SpansDecided cfg U (adopted s c ds) := by
  intro k hk
  change k < c.height at hk
  by_cases hks : k < s.lo
  · exact hR k hks
  · unfold adoptable at ha
    simp only [Bool.and_eq_true, decide_eq_true_eq] at ha
    have hm : k ∈ ds.map Prod.fst := by
      rw [ha.1.2]; exact List.mem_range'_1.mpr ⟨by omega, by omega⟩
    obtain ⟨e, he, rfl⟩ := List.mem_map.mp hm
    exact (hv e he).spans hpos

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

/-- **Advancing from a cut**: the store stays one, the record reaches
every slot a recovering node decided, and the decisions are verdicts. -/
theorem IsCut.advance (hg : Ground U K cfg.q) (hσ : cfg.σ = boundedSel)
    (ht : cfg.p.Tolerates H f q) {s : State Validator BlockId Payload} (hc : IsCut U s.store)
    (hh : Held cfg s) (hr : s.recovering = true → SpansDecided cfg U s)
    (hp : ∀ e ∈ s.pending, e ∈ K)
    (hb : ∀ e ∈ persists (Node.advance cfg s).2, e ∈ K) :
    IsCut U (Node.advance cfg s).1.store ∧
      ((Node.advance cfg s).1.recovering = true → SpansDecided cfg U (Node.advance cfg s).1) ∧
      ∀ e ∈ commitsOf (Node.advance cfg s).2, Verdict cfg U e := by
  obtain ⟨hcA, hrA⟩ := hc.advanceStore hg hh hr hp hb
  refine ⟨hcA, hrA, ?_⟩
  obtain ⟨bs, hbs⟩ := progress_built (cfg := cfg) (s.store.topRound + 2) s
  simp only [Node.advance] at hb ⊢
  rw [persists_append, persists_append] at hb
  have hc₁ := IsCut.progress hg _ hc hh fun e he => hb e
    (List.mem_append_left _ (List.mem_append_left _ he))
  have hh₁ := Held.progress (s.store.topRound + 2) hh
  generalize Node.progress cfg (s.store.topRound + 2) s = r at hbs hc₁ hh₁ ⊢
  have hv := verdict_decideStep (U := U) hσ ht hc₁ hh₁
  have hco := commitsOf_collect (cfg := cfg) (Node.decideStep cfg r.1).1
  generalize Node.collect cfg (Node.decideStep cfg r.1).1 = g at hco ⊢
  intro e he
  rw [commitsOf_append, commitsOf_append, hbs, commitsOf_built, hco, List.nil_append,
    List.append_nil] at he
  exact hv e he

/-- **The passes from a cut**: the store stays one, the record reaches
every slot a recovering node decided, and the decisions are verdicts. -/
theorem IsCut.quiesce (hg : Ground U K cfg.q) (hσ : cfg.σ = boundedSel)
    (ht : cfg.p.Tolerates H f q) : ∀ (n : ℕ) {s : State Validator BlockId Payload},
    IsCut U s.store → Held cfg s → (s.recovering = true → SpansDecided cfg U s) →
    (∀ e ∈ s.pending, e ∈ K) → (∀ e ∈ persists (Node.quiesce cfg n s).2, e ∈ K) →
    IsCut U (Node.quiesce cfg n s).1.store ∧
      ((Node.quiesce cfg n s).1.recovering = true → SpansDecided cfg U (Node.quiesce cfg n s).1) ∧
      ∀ e ∈ commitsOf (Node.quiesce cfg n s).2, Verdict cfg U e
  | 0, s, hc, _, hr, _, _ => ⟨hc, hr, fun e he => by simp [Node.quiesce, commitsOf] at he⟩
  | n + 1, s, hc, hh, hr, hp, hb => by
    rcases quiesce_succ_cases (cfg := cfg) n s with he | he <;> rw [he] at hb ⊢
    · exact hc.advance hg hσ ht hh hr hp hb
    · rw [persists_append] at hb
      obtain ⟨hc₁, hr₁, hv₁⟩ :=
        hc.advance hg hσ ht hh hr hp fun e he => hb e (List.mem_append_left _ he)
      obtain ⟨hc₂, hr₂, hv₂⟩ := IsCut.quiesce hg hσ ht n hc₁ hh.advance hr₁
        (fun e he => hp e ((advance_sub (cfg := cfg) s).1 e he))
        fun e he => hb e (List.mem_append_right _ he)
      refine ⟨hc₂, hr₂, fun e he => ?_⟩
      rw [commitsOf_append] at he
      exact (List.mem_append.mp he).elim (hv₁ e) (hv₂ e)

/-- **Settling from a cut**: the store stays one, and the decisions are
verdicts. -/
theorem IsCut.settle (hg : Ground U K cfg.q) (hσ : cfg.σ = boundedSel)
    (ht : cfg.p.Tolerates H f q) {s : State Validator BlockId Payload} (hc : IsCut U s.store)
    (hh : Held cfg s) (hr : s.recovering = true → SpansDecided cfg U s)
    (hp : ∀ e ∈ s.pending, e ∈ K)
    (hb : ∀ e ∈ persists (Node.settle cfg s).2, e ∈ K) :
    IsCut U (Node.settle cfg s).1.store ∧
      ∀ e ∈ commitsOf (Node.settle cfg s).2, Verdict cfg U e := by
  rcases settle_cases (cfg := cfg) s with he | ⟨s₁, hj, he⟩ <;> rw [he] at hb ⊢
  · obtain ⟨hc', -, hv'⟩ := IsCut.quiesce hg hσ ht _ hc hh hr hp hb
    exact ⟨hc', hv'⟩
  · obtain ⟨_, _, _, _, hcase, hst, hpd, -, -, hlo, -⟩ := tryResume_some hj
    have hr₁ : s₁.recovering = true → SpansDecided cfg U s₁ := fun h₁ k hk => by
      rcases hcase with ⟨-, -, h₀⟩ | ⟨-, hrec, -⟩
      · rw [h₀] at h₁; cases h₁
      · exact hr hrec k (hlo ▸ hk)
    obtain ⟨hc', -, hv'⟩ := IsCut.quiesce hg hσ ht _ (by rw [hst]; exact hc) (hh.tryResume hj)
      hr₁ (by rw [hpd]; exact hp) hb
    exact ⟨hc', hv'⟩

/-- **A step from a cut**, the record reaching every slot the node
decided, adopting only verdicts: the store stays a cut, and the decisions
are verdicts. -/
theorem IsCut.step (hg : Ground U K cfg.q) (hσ : cfg.σ = boundedSel)
    (ht : cfg.p.Tolerates H f q) (hpos : 0 < cfg.p.skipThreshold)
    {s : State Validator BlockId Payload}
    (i : Input Validator BlockId Payload) (hc : IsCut U s.store) (hh : Held cfg s)
    (hp : ∀ e ∈ s.pending, e ∈ K) (hR : SpansDecided cfg U s)
    (hd : ∀ e ∈ delivered cfg [i], e ∈ K)
    (hb : ∀ e ∈ persists (Node.step cfg s i).2, e ∈ K)
    (hadopt : ∀ p c ds, i = .certOffer p c ds → ∀ ds', ds'.Sublist ds →
      adoptable cfg s c ds' = true → ∀ e ∈ ds', Verdict cfg U e) :
    IsCut U (Node.step cfg s i).1.store ∧
      ∀ e ∈ commitsOf (Node.step cfg s i).2, Verdict cfg U e := by
  have hset : ∀ (s₀ : State Validator BlockId Payload) (pre : List (Output Validator BlockId Payload)),
      IsCut U s₀.store → Held cfg s₀ → (s₀.recovering = true → SpansDecided cfg U s₀) →
      (∀ e ∈ s₀.pending, e ∈ K) → commitsOf pre = [] →
      Node.step cfg s i = ((Node.settle cfg s₀).1, pre ++ (Node.settle cfg s₀).2) →
      IsCut U (Node.step cfg s i).1.store ∧
        ∀ e ∈ commitsOf (Node.step cfg s i).2, Verdict cfg U e := by
    intro s₀ pre hc₀ hh₀ hr₀ hp₀ hpre he
    rw [he] at hb ⊢
    rw [persists_append] at hb
    rw [commitsOf_append, hpre, List.nil_append]
    exact hc₀.settle hg hσ ht hh₀ hr₀ hp₀ fun e he => hb e (List.mem_append_right _ he)
  have hsame : ∀ (s' : State Validator BlockId Payload) (out : List (Output Validator BlockId Payload)),
      s'.store = s.store → commitsOf out = [] → Node.step cfg s i = (s', out) →
      IsCut U (Node.step cfg s i).1.store ∧
        ∀ e ∈ commitsOf (Node.step cfg s i).2, Verdict cfg U e := by
    intro s' out hs ho he; rw [he, hs, ho]; exact ⟨hc, fun e he => absurd he List.not_mem_nil⟩
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
          refine ⟨fun t ht => Or.inl ⟨_, Finset.mem_insert_self _ _, ?_⟩, hh.horizon,
            fun ht => absurd ht (by simp), fun t _ => ?_, hh.junk⟩
          · simp only [Option.some.injEq] at ht
            simp only [st, Store.blk, Store.insert, lookup, Std.TreeMap.getD_insert_self,
              atBase_round]
            exact ht.ge
          · change s.store.base ≤ t
            omega
        exact hset { { s with store := st, top := some 0, own := some gid } with
            owner := slotted cfg [(gid, cfg.genesis)] ++ s.owner, recovering := false }
          (built cfg [(cfg.idOf cfg.genesis, cfg.genesis)]) hcst hh₀ (fun _ => hR) hp
          (commitsOf_built _) (by simp only [Node.step, dif_pos h₂, if_pos h₁]; rfl)
      · exact hsame s [] rfl rfl (by simp only [Node.step, dif_neg h₂, if_pos h₁])
    · exact hsame s [] rfl rfl (by simp only [Node.step, if_neg h₁])
  | deliver id b =>
    by_cases hA : Admits cfg s id b
    · let s₁ := afterFlush (cfg := cfg) s id b
      let miss := missing s₁ id b
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
        (IsCut.flush hg _ _ hc (hc.spans hh fun _ => hR) hpend)
        (hh.grow hg₁ hb₁ rfl le_rfl (fun hr => hr)) (fun _ => hR)
        (fun e he => hpend e (flush_pending_sub _ _ _ e he))
        (by
          rw [commitsOf_append, commitsOf_append, commitsOf_evidence]; unfold askOut
          split <;> split <;> rfl) (step_deliver hA)
    · rcases step_deliver_not (cfg := cfg) hA with he | ⟨a, he⟩
      · exact hsame s [] rfl rfl he
      · exact hsame { s with asked := a, recovering := true } [.requestBase] rfl rfl he
  | timer r =>
    exact hset { s with fired := Insert.insert r s.fired } (timerAsk s r) hc
      (hh.grow (Grows.refl _) rfl rfl le_rfl) (fun _ => hR) hp (commitsOf_timerAsk s r)
      (step_timer_eq s r)
  | fetchRequest peer G ids =>
    rw [show Node.step cfg s (.fetchRequest peer G ids) = (s, answer s peer G ids) from rfl]
    refine ⟨hc, fun e he => ?_⟩
    unfold answer commitsOf at he
    rw [List.filterMap_map] at he
    simp at he
  | restart =>
    exact hset s.recover [.requestBase] hc
      (hh.grow (Grows.refl _) rfl rfl le_rfl) (fun _ => hR)
      (fun e he => by simp [State.recover] at he) rfl
      (by simp only [Node.step]; rfl)
  | baseRequest peer =>
    rw [commitsOf_baseRequest, step_baseRequest_state]
    exact ⟨hc, fun e he => absurd he List.not_mem_nil⟩
  | proposal p k kh =>
    by_cases hpm : p ≠ cfg.me
    · exact hset (record cfg s p k kh) ([] : List (Output Validator BlockId Payload))
        (by exact hc) (by exact hh.grow (Grows.refl _) rfl rfl le_rfl) (fun _ => hR)
        (by exact hp)
        rfl
        (by rw [step_proposal, if_pos hpm])
    · rw [step_proposal, if_neg hpm]; exact ⟨hc, fun e he => by simp [commitsOf] at he⟩
  | decisionRequest p lo =>
    rw [step_decisionRequest, commitsOf_requests fun o ho => Or.inr (by
      split at ho
      · exact ⟨p, serveFrom_out s p lo o ho⟩
      · simp at ho)]
    exact ⟨hc, fun e he => absurd he List.not_mem_nil⟩
  | baseOffer p G =>
    by_cases hcnd : s.recovering ∧ p ≠ cfg.me
    · rw [step_offer, if_pos hcnd] at hb ⊢
      exact IsCut.settle hg hσ ht (s := withOffer s p G) hc
        (hh.grow (s' := withOffer s p G) (Grows.refl _) rfl rfl le_rfl) (fun _ => hR) hp hb
    · exact hsame s [] rfl rfl (by rw [step_offer, if_neg hcnd])
  | certOffer p c ds =>
    rcases certOffer_cases (cfg := cfg) s p c ds with ⟨ds', hsub, -, ha, he⟩ | ⟨-, -, he⟩ |
      he
    · rw [he, adopt_eq] at hb ⊢
      rw [persists_append] at hb
      have hv := hadopt p c ds rfl ds' hsub ha
      obtain ⟨h₁, h₂⟩ := IsCut.settle (s := adopted s c ds') hg hσ ht hc
        (hh.grow (Grows.refl _) rfl rfl (adoptable_lo ha).le)
        (fun _ => SpansDecided.adopted hpos hR ha hv) hp
        fun e he => hb e (List.mem_append_right _ he)
      refine ⟨h₁, fun e he => ?_⟩
      rw [commitsOf_append, commitsOf_map] at he
      rcases List.mem_append.mp he with he | he
      · exact hv e he
      · exact h₂ e he
    · exact hset { s with cert := some c, props := above (some c) s.props } [] hc
        (hh.grow (Grows.refl _) rfl rfl le_rfl) (fun _ => hR) hp rfl (by rw [he]; rfl)
    · exact hsame s [] rfl rfl he
  | announced p c =>
    rcases announced_cases (cfg := cfg) s p c with ⟨-, -, he⟩ | he | he
    · exact hset { s with cert := some c, props := above (some c) s.props } [] hc
        (hh.grow (Grows.refl _) rfl rfl le_rfl) (fun _ => hR) hp rfl (by rw [he]; rfl)
    · rw [he]; exact ⟨hc, fun e he => by simp [commitsOf] at he⟩
    · exact hsame s [] rfl rfl he

end Node

end LeanDag
