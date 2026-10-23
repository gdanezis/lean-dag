import LeanDag.Node.Helpers.Commits
/-!
# A node's disk stays a cut along a run

With every step (`IsCut.step`), the disk stays a cut of the record and
every decision a step outputs is a verdict on a view of the record
(`Verdict`). The decision step reads as `tryDecide` on the view of the
record holding exactly the disk's blocks, and `Loop.sound` derives what
it outputs (`verdict_decideStep`).
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

variable {q f : ℕ} [P.Quorate q]

/-- **What a decision step outputs is a verdict on the record**, from a
disk that is a cut of it. -/
theorem verdict_decideStep (hσ : cfg.σ = boundedSel) (ht : cfg.p.Tolerates H f q)
    {s : State Validator BlockId Payload} (hc : IsCut U s.disk) :
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
    obtain ⟨hlt, hfl, -⟩ := hlt
    rw [commitsOf_map] at he
    obtain ⟨V', -, hiff⟩ := hc.extend ⟨∅, Finset.empty_subset _,
      fun _ h => absurd h (Finset.notMem_empty _)⟩ (fun i hi => absurd hi (Finset.notMem_empty i))
    have hT : tryDecide cfg.p boundedSel s.disk.toRecord s.disk.view s.lo
        (decidable cfg s.disk.topRound - 1) =
        tryDecide cfg.p boundedSel U V' s.lo (decidable cfg s.disk.topRound - 1) :=
      (ViewsAbove.of_store hiff fun i hi => hc.eq hi).tryDecide_eq cfg.p hw _ (Nat.zero_le _)
    rw [tryDecide_memory hσ hw s hfl, hT] at he
    exact ⟨V', (Loop.sound _ _ _ P H cfg.p boundedSel U V' s.lo _ hl hcv (by omega)).2 e he⟩
  · simp [commitsOf] at he

/-- **Advancing from a cut**: the disk stays one, and the decisions are
verdicts. -/
theorem IsCut.advance (hg : Ground U K cfg.q) (hσ : cfg.σ = boundedSel)
    (ht : cfg.p.Tolerates H f q) {s : State Validator BlockId Payload} (hc : IsCut U s.disk)
    (hp : ∀ e ∈ s.pending, e ∈ K)
    (hb : ∀ e ∈ persists (Node.advance cfg s).2, e ∈ K) :
    IsCut U (Node.advance cfg s).1.disk ∧
      ∀ e ∈ commitsOf (Node.advance cfg s).2, Verdict cfg U e := by
  refine ⟨hc.advanceStore hg hp hb, ?_⟩
  obtain ⟨bs, hbs⟩ := progress_built (cfg := cfg) (s.disk.topRound + 2) s
  rw [advance_snd, persists_append, persists_arm, List.append_nil] at hb
  rw [advance_snd, commitsOf_append, commitsOf_arm, List.append_nil]
  simp only [Node.pass] at hb ⊢
  rw [persists_append] at hb
  have hc₁ := IsCut.progress hg _ hc fun e he => hb e (List.mem_append_left _ he)
  generalize Node.progress cfg (s.disk.topRound + 2) s = r at hbs hc₁ ⊢
  have hv := verdict_decideStep (U := U) hσ ht hc₁
  intro e he
  rw [commitsOf_append, hbs, commitsOf_built, List.nil_append] at he
  exact hv e he

/-- **The passes from a cut**: the disk stays one, and the decisions are
verdicts. -/
theorem IsCut.quiesce (hg : Ground U K cfg.q) (hσ : cfg.σ = boundedSel)
    (ht : cfg.p.Tolerates H f q) : ∀ (n : ℕ) {s : State Validator BlockId Payload},
    IsCut U s.disk → (∀ e ∈ s.pending, e ∈ K) →
    (∀ e ∈ persists (Node.quiesce cfg n s).2, e ∈ K) →
    IsCut U (Node.quiesce cfg n s).1.disk ∧
      ∀ e ∈ commitsOf (Node.quiesce cfg n s).2, Verdict cfg U e
  | 0, s, hc, _, _ => ⟨hc, fun e he => by simp [Node.quiesce, commitsOf] at he⟩
  | n + 1, s, hc, hp, hb => by
    rcases quiesce_succ_cases (cfg := cfg) n s with he | he <;> rw [he] at hb ⊢
    · exact hc.advance hg hσ ht hp hb
    · rw [persists_append] at hb
      obtain ⟨hc₁, hv₁⟩ := hc.advance hg hσ ht hp fun e he => hb e (List.mem_append_left _ he)
      obtain ⟨hc₂, hv₂⟩ := IsCut.quiesce hg hσ ht n hc₁
        (fun e he => hp e (advance_sub (cfg := cfg) s e he))
        fun e he => hb e (List.mem_append_right _ he)
      refine ⟨hc₂, fun e he => ?_⟩
      rw [commitsOf_append] at he
      exact (List.mem_append.mp he).elim (hv₁ e) (hv₂ e)

/-- **Settling from a cut**: the disk stays one, and the decisions are
verdicts. -/
theorem IsCut.settle (hg : Ground U K cfg.q) (hσ : cfg.σ = boundedSel)
    (ht : cfg.p.Tolerates H f q) {s : State Validator BlockId Payload} (hc : IsCut U s.disk)
    (hp : ∀ e ∈ s.pending, e ∈ K)
    (hb : ∀ e ∈ persists (Node.settle cfg s).2, e ∈ K) :
    IsCut U (Node.settle cfg s).1.disk ∧
      ∀ e ∈ commitsOf (Node.settle cfg s).2, Verdict cfg U e :=
  IsCut.quiesce hg hσ ht (passes cfg s) hc hp hb

/-- **A step from a cut**: the disk stays a cut, and the decisions are
verdicts. -/
theorem IsCut.step (hg : Ground U K cfg.q) (hσ : cfg.σ = boundedSel)
    (ht : cfg.p.Tolerates H f q) {s : State Validator BlockId Payload}
    (i : Input Validator BlockId Payload) (hc : IsCut U s.disk)
    (hp : ∀ e ∈ s.pending, e ∈ K)
    (hd : ∀ e ∈ delivered cfg [i], e ∈ K)
    (hb : ∀ e ∈ persists (Node.step cfg s i).2, e ∈ K) :
    IsCut U (Node.step cfg s i).1.disk ∧
      ∀ e ∈ commitsOf (Node.step cfg s i).2, Verdict cfg U e := by
  -- a step that settles a state `s₀`, after outputs without decisions
  have hset : ∀ (s₀ : State Validator BlockId Payload)
      (pre : List (Output Validator BlockId Payload)),
      IsCut U s₀.disk → (∀ e ∈ s₀.pending, e ∈ K) → commitsOf pre = [] →
      Node.step cfg s i = ((Node.settle cfg s₀).1, pre ++ (Node.settle cfg s₀).2) →
      IsCut U (Node.step cfg s i).1.disk ∧
        ∀ e ∈ commitsOf (Node.step cfg s i).2, Verdict cfg U e := by
    intro s₀ pre hc₀ hp₀ hpre he
    rw [he] at hb ⊢
    rw [persists_append] at hb
    rw [commitsOf_append, hpre, List.nil_append]
    exact hc₀.settle hg hσ ht hp₀ fun e he => hb e (List.mem_append_right _ he)
  have hsame : Node.step cfg s i = (s, []) →
      IsCut U (Node.step cfg s i).1.disk ∧
        ∀ e ∈ commitsOf (Node.step cfg s i).2, Verdict cfg U e := by
    intro he; rw [he]; exact ⟨hc, fun e he => absurd he List.not_mem_nil⟩
  cases i with
  | start =>
    by_cases h₁ : s.top = none ∧ cfg.Admissible
    · by_cases h₂ : cfg.idOf cfg.genesis ∉ s.disk.ids ∧
          rowValid cfg.q (Function.update s.disk.blk (cfg.idOf cfg.genesis) cfg.genesis)
            cfg.genesis
      · let st := s.disk.insert (cfg.idOf cfg.genesis) cfg.genesis h₂.1
          (fun _ hj => absurd hj (Finset.notMem_empty _))
          (fun j hj => absurd hj (Finset.notMem_empty j))
        have hx : (cfg.idOf cfg.genesis, cfg.genesis) ∈ K :=
          hb _ (by simp only [Node.step, dif_pos h₂, if_pos h₁]; simp [persists])
        have hnil : cfg.genesis.refs ⊆ s.disk.ids := fun _ hj => absurd hj (Finset.notMem_empty _)
        obtain ⟨hU₁, hU₂⟩ := hg.real _ hx (fun _ hj => absurd hj (Finset.notMem_empty _))
          (validAt_of_cut hc h₂.1 hnil h₂.2)
        have hcst : IsCut U st := hc.insert ⟨hU₁, hU₂⟩
        let gid := cfg.idOf cfg.genesis
        exact hset { keep s (cfg.idOf cfg.genesis) cfg.genesis h₂.1
            (fun _ hj => absurd hj (Finset.notMem_empty _))
            (fun j hj => absurd hj (Finset.notMem_empty j)) with
            top := some 0, own := some gid }
          (built cfg [(cfg.idOf cfg.genesis, cfg.genesis)]) hcst hp
          (commitsOf_built _) (by simp only [Node.step, dif_pos h₂, if_pos h₁]; rfl)
      · exact hsame (by simp only [Node.step, dif_neg h₂, if_pos h₁])
    · exact hsame (by simp only [Node.step, if_neg h₁])
  | deliver id b =>
    by_cases hA : Admits cfg s id b
    · let s₁ := afterFlush (cfg := cfg) s id b
      let miss := missing s₁ b
      have hx : (id, b) ∈ K := hd _ (by simp [delivered, hA.1])
      have hpend : ∀ e ∈ (id, b) :: s.pending, e ∈ K := fun e he => by
        rcases List.mem_cons.mp he with rfl | he
        · exact hx
        · exact hp e he
      have hc₁ : IsCut U s₁.disk := by rw [afterFlush_disk]; exact IsCut.flush hg _ _ hc hpend
      exact hset s₁
        (if miss.isEmpty then [] else [.fetch b.creator (s.top.getD 0) miss])
        hc₁ (fun e he => hpend e (flush_pending_sub _ _ _ e (by rwa [afterFlush_pending] at he)))
        (by split <;> rfl) (step_deliver hA)
    · exact hsame (step_deliver_not hA)
  | timer r =>
    rw [persists_step_timer] at hb
    rw [step_timer_fst, commitsOf_step_timer]
    exact (hc : IsCut U { s with fired := Insert.insert r s.fired }.disk).settle hg hσ ht hp hb
  | fetchRequest peer r ids =>
    rw [show Node.step cfg s (.fetchRequest peer r ids) = (s, answer cfg s peer r ids) from rfl]
    refine ⟨hc, fun e he => ?_⟩
    unfold answer commitsOf at he
    rw [List.filterMap_map] at he
    simp at he
  | restart =>
    show IsCut U s.disk ∧ ∀ e ∈ commitsOf (Node.resend cfg s ++ Node.rearm cfg s), Verdict cfg U e
    rw [commitsOf_append, commitsOf_resend, commitsOf_rearm, List.append_nil]
    exact ⟨hc, fun e he => absurd he List.not_mem_nil⟩

end Node

end LeanDag
