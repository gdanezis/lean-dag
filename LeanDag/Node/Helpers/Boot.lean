import LeanDag.Node.Helpers.Commits
/-!
# A node's store stays a cut through bootstraps

A bootstrap at a round the record reaches keeps the store a cut of the
record (`IsCut.boot`): the pruned store is one, the attested base and the
node's new own block are known blocks at that round, and the offered
blocks are known. With every other step (`IsCut.step`), the store stays a
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
theorem advance_offers (s : State Validator BlockId Payload) :
    (advance cfg s).1.offers = s.offers := by
  have hp : ∀ (fuel : ℕ) (s : State Validator BlockId Payload),
      (progress cfg fuel s).1.offers = s.offers := by
    intro fuel
    induction fuel with
    | zero => intro _; rfl
    | succ n ih =>
      intro s
      unfold Node.progress
      split
      · rename_i s₁ out h
        rw [ih, tryBuild_offers h]
      · rfl
  have hd : ∀ s : State Validator BlockId Payload, (decideStep cfg s).1.offers = s.offers := by
    intro s; unfold Node.decideStep; dsimp only; split <;> rfl
  have hc : ∀ s : State Validator BlockId Payload, (collect cfg s).1.offers = s.offers := by
    intro s; unfold Node.collect; split
    · dsimp only; split <;> rfl
    · rfl
  simp only [Node.advance]
  change (collect cfg (decideStep cfg (progress cfg (s.store.topRound + 2) s).1).1).1.offers = _
  rw [hc, hd, hp]

omit [Fintype Validator] in
theorem settle_offers (s : State Validator BlockId Payload) :
    (Node.settle cfg s).1.offers = s.offers := by
  rcases settle_cases (cfg := cfg) s with h | ⟨s₁, out, hj, h⟩ <;> rw [h]
  · exact advance_offers s
  · rw [advance_offers, tryJump_offers hj]

/-- **A base offer a node holds was given to it**, at this step or before. -/
theorem step_offers (s : State Validator BlockId Payload) (i : Input Validator BlockId Payload) :
    ∀ o ∈ (Node.step cfg s i).1.offers, o ∈ s.offers ∨ i = .baseOffer o.1 o.2.1 o.2.2 := by
  intro o ho
  cases i with
  | start =>
    simp only [Node.step] at ho
    split at ho
    · split at ho
      · rw [settle_offers] at ho; exact Or.inl ho
      · exact Or.inl ho
    · exact Or.inl ho
  | deliver id b =>
    simp only [Node.step] at ho
    split at ho
    · rw [settle_offers] at ho; exact Or.inl ho
    · exact Or.inl ho
  | timer r => simp only [Node.step] at ho; rw [settle_offers] at ho; exact Or.inl ho
  | restart =>
    simp only [Node.step] at ho; rw [settle_offers] at ho; simp [State.recover] at ho
  | jump v1 B1 v2 B2 =>
    rw [step_jump] at ho
    split at ho
    · exact Or.inl ho
    · rw [settle_offers] at ho; exact Or.inl ho
  | fetchRequest => exact Or.inl ho
  | baseRequest => exact Or.inl ho
  | baseOffer p G bs =>
    rw [step_offer] at ho
    split at ho
    · split at ho
      · rename_i s₂ out hb
        rw [advance_offers] at ho
        obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, hof, -⟩ := tryBoot_some hb
        rw [hof] at ho; exact absurd ho List.not_mem_nil
      · rcases List.mem_cons.mp ho with rfl | ho
        · exact Or.inr rfl
        · exact Or.inl (List.mem_filter.mp ho).1
    · exact Or.inl ho

/-! ## The store stays a cut -/

omit [Fintype Validator] in
/-- **A bootstrap at a round the record reaches keeps the store a cut.** -/
theorem IsCut.boot (hg : Ground U K cfg.q) {s s' : State Validator BlockId Payload}
    {out : List (Output Validator BlockId Payload)} (hc : IsCut U s.store)
    (hb : tryBoot cfg s = some (s', out))
    (hoff : ∀ o ∈ s.offers, ∀ e ∈ o.2.2, e.1 = cfg.idOf e.2 → e ∈ K)
    (hp : ∀ e ∈ s.pending, e ∈ K) (hgK : ∀ e ∈ persists out, e ∈ K)
    (hspan : Spans U s'.store.base) : IsCut U s'.store := by
  obtain ⟨t, G, hbG, -, -, -, hg', hst, -, -, -, -, -, -, -, hout⟩ := tryBoot_some hb
  dsimp only at hg' hst
  set st₀ := (baseAt cfg s G).foldl (fun st e => Node.accept cfg st e.1 e.2)
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
    obtain ⟨hx, hcx⟩ := List.mem_filter.mp hx
    simp only [decide_eq_true_eq] at hcx
    exact hfo x hx hcx.2.1
  have hgk : (cfg.idOf ⟨G, cfg.me, ∅, cfg.payload G⟩, ⟨G, cfg.me, ∅, cfg.payload G⟩) ∈ K :=
    hgK _ (by rw [hout, persists_built]; exact List.mem_singleton_self _)
  have hc₁ := hc₀.insert (hnew := hg'.1) (hab := hg'.2)
    (hrefs := fun _ => Finset.empty_subset _) (hpred := fun _ j hj => absurd hj (Finset.notMem_empty j))
    (by rw [hb₀]; exact hg.base _ hgk G le_rfl hspan)
  rw [hst]
  refine IsCut.flush hg _ _ hc₁ (by change Spans U st₀.base; rw [hb₀]; exact hspan) fun x hx => ?_
  rcases List.mem_append.mp hx with hx | hx
  · obtain ⟨hx, hcx⟩ := List.mem_filter.mp hx
    simp only [decide_eq_true_eq] at hcx
    exact hfo x hx hcx.2
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
    rw [commitsOf_map] at he
    obtain ⟨V', -, hiff⟩ := hc.extend ⟨∅, Finset.empty_subset _,
      fun _ h => absurd h (Finset.notMem_empty _)⟩ (fun i hi => absurd hi (Finset.notMem_empty i))
    have hT : tryDecide cfg.p cfg.σ s.store.toRecord s.store.view s.lo
        (decidable cfg s.store.topRound - 1) =
        tryDecide cfg.p boundedSel U V' s.lo (decidable cfg s.store.topRound - 1) := by
      rw [hσ]
      exact (ViewsAbove.of_store hiff fun i hi => (hc i hi).2).tryDecide_eq cfg.p hw _ hh.horizon
    rw [hT] at he
    exact ⟨V', (Loop.sound _ _ _ P H cfg.p boundedSel U V' s.lo _ hl hcv (by omega)).2 e he⟩
  · simp [commitsOf] at he

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

/-- **Settling from a cut**: the store stays one, and the decisions are
verdicts. -/
theorem IsCut.settle (hg : Ground U K cfg.q) (hσ : cfg.σ = boundedSel)
    (ht : cfg.p.Tolerates H f q) {s : State Validator BlockId Payload} (hc : IsCut U s.store)
    (hh : Held cfg s) (hp : ∀ e ∈ s.pending, e ∈ K)
    (hb : ∀ e ∈ persists (Node.settle cfg s).2, e ∈ K) :
    IsCut U (Node.settle cfg s).1.store ∧
      ∀ e ∈ commitsOf (Node.settle cfg s).2, Verdict cfg U e := by
  rcases settle_cases (cfg := cfg) s with he | ⟨s₁, out, hj, he⟩ <;> rw [he] at hb ⊢
  · exact hc.advance hg hσ ht hh hp hb
  · rw [persists_append] at hb
    obtain ⟨hpd, -, -, -, -⟩ := tryJump_keeps hj
    obtain ⟨r0, B1, B2, F, e, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hout⟩ :=
      tryJump_some hj
    have hc₁ := hc.tryJump hg hj fun e he => hb e (List.mem_append_left _ he)
    obtain ⟨h₁, h₂⟩ := hc₁.advance hg hσ ht (hh.tryJump hj) (by rw [hpd]; exact hp)
      fun e he => hb e (List.mem_append_right _ he)
    refine ⟨h₁, fun e' he' => ?_⟩
    rw [commitsOf_append, hout, commitsOf_jumped, List.nil_append] at he'
    exact h₂ e' he'

/-- **A step from a cut**, bootstrapping only at rounds the record
reaches: the store stays a cut, and the decisions are verdicts. -/
theorem IsCut.step (hg : Ground U K cfg.q) (hσ : cfg.σ = boundedSel)
    (ht : cfg.p.Tolerates H f q) {s : State Validator BlockId Payload}
    (i : Input Validator BlockId Payload) (hc : IsCut U s.store) (hh : Held cfg s)
    (hp : ∀ e ∈ s.pending, e ∈ K)
    (hoff : ∀ o ∈ s.offers, ∀ e ∈ o.2.2, e.1 = cfg.idOf e.2 → e ∈ K)
    (hd : ∀ e ∈ delivered cfg [i], e ∈ K) (hr : ∀ e ∈ received cfg s i, e ∈ K)
    (hb : ∀ e ∈ persists (Node.step cfg s i).2, e ∈ K)
    (hspan : ∀ p G bs s₂ out, i = .baseOffer p G bs →
      tryBoot cfg (withOffer s p G bs) = some (s₂, out) → Spans U s₂.store.base) :
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
            { s with store := st, top := some 0, own := some gid, recovering := false } := by
          refine ⟨fun t ht => ⟨_, rfl, Finset.mem_insert_self _ _, ?_⟩, hh.horizon,
            fun ht => absurd ht (by simp), fun t _ => ?_, fun ht => absurd ht (by simp), hh.junk⟩
          · simp only [Option.some.injEq] at ht
            simp only [st, gid, Store.blk, Store.insert, lookup, Std.TreeMap.getD_insert_self,
              atBase_round]
            exact ht
          · change s.store.base ≤ t
            omega
        exact hset { s with store := st, top := some 0, own := some gid, recovering := false }
          (built cfg [(cfg.idOf cfg.genesis, cfg.genesis)]) hcst hh₀ hp
          (commitsOf_built _) (by simp only [Node.step, dif_pos h₂, if_pos h₁]; rfl)
      · exact hsame s rfl (by simp only [Node.step, dif_neg h₂, if_pos h₁])
    · exact hsame s rfl (by simp only [Node.step, if_neg h₁])
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
        ((if miss.isEmpty then [] else [.fetch (miss.map Prod.fst)]) ++ askOut (cfg := cfg) s b)
        (IsCut.flush hg _ _ hc (hc.spans hh) hpend) (hh.grow hg₁ hb₁ rfl rfl le_rfl)
        (fun e he => hpend e (flush_pending_sub _ _ _ e he))
        (by rw [commitsOf_append]; unfold askOut; split <;> split <;> rfl) (step_deliver hA)
    · have h' : ¬ (id = cfg.idOf b ∧ b.creator ≠ cfg.me ∧ s.store.base ≤ b.round ∧
          id ∉ s.store.ids ∧ id ∉ s.pending.map Prod.fst) := hA
      exact hsame s rfl (by simp only [Node.step, if_neg h'])
  | timer r =>
    exact hset { s with fired := Insert.insert r s.fired } [] hc
      (hh.grow (Grows.refl _) rfl rfl rfl le_rfl) hp rfl (by simp only [Node.step]; rfl)
  | fetchRequest peer ids =>
    rw [show Node.step cfg s (.fetchRequest peer ids) = (s, answer s peer ids) from rfl]
    refine ⟨hc, fun e he => ?_⟩
    unfold answer commitsOf at he
    rw [List.filterMap_map] at he
    simp at he
  | jump v1 B1 v2 B2 =>
    by_cases hF : (jumpIn cfg s v1 B1 v2 B2).isEmpty
    · exact hsame s rfl (by rw [step_jump, if_pos hF])
    · have hg₁ := Grows.flush (cfg := cfg)
        (s.pending.length + (jumpIn cfg s v1 B1 v2 B2).length + 1) s.store
        (jumpIn cfg s v1 B1 v2 B2 ++ s.pending)
      have hb₁ := flush_base (cfg := cfg)
        (s.pending.length + (jumpIn cfg s v1 B1 v2 B2).length + 1) s.store
        (jumpIn cfg s v1 B1 v2 B2 ++ s.pending)
      have hpend : ∀ e ∈ jumpIn cfg s v1 B1 v2 B2 ++ s.pending, e ∈ K := fun e he => by
        rcases List.mem_append.mp he with he | he
        · exact hr e he
        · exact hp e he
      exact hset (afterJump (cfg := cfg) s v1 B1 v2 B2) []
        (IsCut.flush hg _ _ hc (hc.spans hh) hpend) (hh.grow hg₁ hb₁ rfl rfl le_rfl)
        (fun e he => hpend e (flush_pending_sub _ _ _ e he)) rfl
        (by rw [step_jump, if_neg hF]; rfl)
  | restart =>
    exact hset s.recover [.requestBase] hc
      (hh.grow (Grows.refl _) rfl rfl rfl le_rfl) (fun e he => by simp [State.recover] at he) rfl
      (by simp only [Node.step]; rfl)
  | baseRequest peer =>
    rw [show Node.step cfg s (.baseRequest peer) =
      (s, [.serveBase peer s.store.base s.store.window]) from rfl]
    exact ⟨hc, fun e he => by simp [commitsOf] at he⟩
  | baseOffer p G bs =>
    by_cases hcnd : s.recovering ∧ p ≠ cfg.me
    · rcases hbt : tryBoot cfg (withOffer s p G bs) with _ | ⟨s₂, out⟩
      · exact hsame (withOffer s p G bs) rfl (by rw [step_offer, if_pos hcnd, hbt])
      · have he : Node.step cfg s (.baseOffer p G bs) =
            ((Node.advance cfg s₂).1, out ++ (Node.advance cfg s₂).2) := by
          rw [step_offer, if_pos hcnd, hbt]
        rw [he] at hb ⊢
        rw [persists_append] at hb
        have hoff' : ∀ o ∈ (withOffer s p G bs).offers, ∀ e ∈ o.2.2, e.1 = cfg.idOf e.2 →
            e ∈ K := by
          intro o ho e heo hid
          rcases List.mem_cons.mp ho with rfl | ho
          · exact hd e (by simp [delivered, heo, hid])
          · exact hoff o (List.mem_filter.mp ho).1 e heo hid
        have hc₂ := IsCut.boot hg (s := withOffer s p G bs) hc hbt hoff' hp
          (fun e he => hb e (List.mem_append_left _ he)) (hspan p G bs s₂ out rfl hbt)
        have hh₂ := (Held.grow hh (Grows.refl _) rfl rfl rfl le_rfl :
          Held cfg (withOffer s p G bs)).boot hbt
        obtain ⟨t', G', hb', -, -, -, hg', -, hpd, -, -, -, -, -, -, hout⟩ := tryBoot_some hbt
        obtain ⟨h₁, h₂⟩ := hc₂.advance hg hσ ht hh₂ (fun e he => by
          rw [hpd] at he
          rcases List.mem_append.mp (flush_pending_sub (cfg := cfg) _ _ _ e he) with he | he
          · obtain ⟨he, hce⟩ := List.mem_filter.mp he
            simp only [decide_eq_true_eq] at hce
            obtain ⟨o, ho, heo⟩ := List.mem_flatMap.mp he
            exact hoff' o ho e heo hce.2
          · exact hp e (List.mem_filter.mp he).1) fun e he => hb e (List.mem_append_right _ he)
        refine ⟨h₁, fun e' he' => ?_⟩
        rw [commitsOf_append, hout, commitsOf_built, List.nil_append] at he'
        exact h₂ e' he'
    · exact hsame s rfl (by rw [step_offer, if_neg hcnd])

end Node

end LeanDag
