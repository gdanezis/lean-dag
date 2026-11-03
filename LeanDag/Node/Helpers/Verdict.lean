import LeanDag.Node.Helpers.Commits
/-!
# A node's disk stays good along a run

With every step (`AllGood.step`), a disk whose blocks are good stays so,
when the store takes in only good blocks (`Grounds`), and every decision a
step outputs satisfies what each decision step from a good disk gives
(`DecidesWell`). On a record grounding what the node knew, a cut is a good
disk (`IsCut`), and a decision step from it outputs verdicts on a view of
the record (`Verdict`): it reads as `tryDecide` on the view of the record
holding exactly the disk's blocks, and `Loop.sound` derives what it
outputs (`verdict_decideStep`).
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
    have hT : tryDecide cfg.p boundedSel s.disk.toRecord s.disk.view s.lo
        (decidable cfg s.disk.topRound - 1) =
        tryDecide cfg.p boundedSel U hc.histView s.lo (decidable cfg s.disk.topRound - 1) :=
      (hc.viewsAbove (R := cfg.slots.slotRound s.lo) fun i hi hR => by
        by_contra hk
        have := s.low i hk
        omega).tryDecide_eq cfg.p hw _ le_rfl
    rw [tryDecide_memory hσ hw s hfl, hT] at he
    exact ⟨hc.histView, (Loop.sound _ _ _ P H cfg.p boundedSel U hc.histView s.lo _ hl hcv
      (by omega)).2 e he⟩
  · simp [commitsOf] at he

variable {Good : BlockId → Block Validator BlockId Payload → Prop}
variable {Q : ℕ × Option BlockId → Prop}

variable (cfg) in
/-- **Each decision step from a good disk outputs decisions satisfying `Q`.** -/
def DecidesWell (Good : BlockId → Block Validator BlockId Payload → Prop)
    (Q : ℕ × Option BlockId → Prop) : Prop :=
  ∀ s : State Validator BlockId Payload, AllGood Good s.disk →
    ∀ e ∈ commitsOf (Node.decideStep cfg s).2, Q e

omit [Fintype Validator] in
/-- **A pass from a good disk**: the disk stays good, and the decisions
satisfy `Q`. -/
theorem AllGood.advance (hg : Grounds cfg Good K) (hdec : DecidesWell cfg Good Q)
    {s : State Validator BlockId Payload} (hc : AllGood Good s.disk)
    (hp : ∀ e ∈ s.syncs, e.2.1 ∈ K)
    (hb : ∀ e ∈ persists (Node.advance cfg s).2, e ∈ K) :
    AllGood Good (Node.advance cfg s).1.disk ∧
      ∀ e ∈ commitsOf (Node.advance cfg s).2, Q e := by
  refine ⟨hc.advanceStore hg hp hb, ?_⟩
  obtain ⟨bs, hbs⟩ := progress_built (cfg := cfg) (s.disk.topRound + 2) s
  rw [advance_snd, persists_append, persists_arm, List.append_nil] at hb
  rw [advance_snd, commitsOf_append, commitsOf_arm, List.append_nil]
  simp only [Node.pass] at hb ⊢
  rw [persists_append] at hb
  have hc₁ := AllGood.progress hg _ hc fun e he => hb e (List.mem_append_left _ he)
  generalize Node.progress cfg (s.disk.topRound + 2) s = r at hbs hc₁ ⊢
  have hv := hdec _ hc₁
  intro e he
  rw [commitsOf_append, hbs, commitsOf_built, List.nil_append] at he
  exact hv e he

omit [Fintype Validator] in
/-- **The passes from a good disk.** -/
theorem AllGood.quiesce (hg : Grounds cfg Good K) (hdec : DecidesWell cfg Good Q) :
    ∀ (n : ℕ) {s : State Validator BlockId Payload},
    AllGood Good s.disk → (∀ e ∈ s.syncs, e.2.1 ∈ K) →
    (∀ e ∈ persists (Node.quiesce cfg n s).2, e ∈ K) →
    AllGood Good (Node.quiesce cfg n s).1.disk ∧
      ∀ e ∈ commitsOf (Node.quiesce cfg n s).2, Q e
  | 0, s, hc, _, _ => ⟨hc, fun e he => by simp [Node.quiesce, commitsOf] at he⟩
  | n + 1, s, hc, hp, hb => by
    rcases quiesce_succ_cases (cfg := cfg) n s with he | he <;> rw [he] at hb ⊢
    · exact hc.advance hg hdec hp hb
    · rw [persists_append] at hb
      obtain ⟨hc₁, hv₁⟩ := hc.advance hg hdec hp fun e he => hb e (List.mem_append_left _ he)
      obtain ⟨hc₂, hv₂⟩ := AllGood.quiesce hg hdec n hc₁
        (fun e he => hp e (advance_sub (cfg := cfg) s e he))
        fun e he => hb e (List.mem_append_right _ he)
      refine ⟨hc₂, fun e he => ?_⟩
      rw [commitsOf_append] at he
      exact (List.mem_append.mp he).elim (hv₁ e) (hv₂ e)

omit [Fintype Validator] in
/-- **Settling from a good disk.** -/
theorem AllGood.settle (hg : Grounds cfg Good K) (hdec : DecidesWell cfg Good Q)
    {s : State Validator BlockId Payload} (hc : AllGood Good s.disk)
    (hp : ∀ e ∈ s.syncs, e.2.1 ∈ K)
    (hb : ∀ e ∈ persists (Node.settle cfg s).2, e ∈ K) :
    AllGood Good (Node.settle cfg s).1.disk ∧
      ∀ e ∈ commitsOf (Node.settle cfg s).2, Q e :=
  AllGood.quiesce hg hdec (passes cfg s) hc hp hb

/-- **A step from a good disk**: the disk stays good, and the decisions
satisfy `Q`. -/
theorem AllGood.step (hg : Grounds cfg Good K) (hdec : DecidesWell cfg Good Q)
    {s : State Validator BlockId Payload}
    (i : Input Validator BlockId Payload) (hc : AllGood Good s.disk)
    (hp : ∀ e ∈ s.syncs, e.2.1 ∈ K)
    (hd : ∀ e ∈ delivered cfg [i], e ∈ K)
    (hb : ∀ e ∈ persists (Node.step cfg s i).2, e ∈ K) :
    AllGood Good (Node.step cfg s i).1.disk ∧
      ∀ e ∈ commitsOf (Node.step cfg s i).2, Q e := by
  -- a step that settles a state `s₀`, after outputs without decisions
  have hset : ∀ (s₀ : State Validator BlockId Payload)
      (pre : List (Output Validator BlockId Payload)),
      AllGood Good s₀.disk → (∀ e ∈ s₀.syncs, e.2.1 ∈ K) → commitsOf pre = [] →
      Node.step cfg s i = ((Node.settle cfg s₀).1, pre ++ (Node.settle cfg s₀).2) →
      AllGood Good (Node.step cfg s i).1.disk ∧
        ∀ e ∈ commitsOf (Node.step cfg s i).2, Q e := by
    intro s₀ pre hc₀ hp₀ hpre he
    rw [he] at hb ⊢
    rw [persists_append] at hb
    rw [commitsOf_append, hpre, List.nil_append]
    exact hc₀.settle hg hdec hp₀ fun e he => hb e (List.mem_append_right _ he)
  have hsame : Node.step cfg s i = (s, []) →
      AllGood Good (Node.step cfg s i).1.disk ∧
        ∀ e ∈ commitsOf (Node.step cfg s i).2, Q e := by
    intro he; rw [he]; exact ⟨hc, fun e he => absurd he List.not_mem_nil⟩
  cases i with
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
        have hnil : cfg.genesis.refs ⊆ s.disk.ids := fun _ hj => absurd hj (Finset.notMem_empty _)
        have hcst : AllGood Good st := hc.insert (hg _ hc _ hx h₂.1 hnil h₂.2)
        let gid := cfg.idOf cfg.genesis
        exact hset { keep s (cfg.idOf cfg.genesis) cfg.genesis h₂.1
            (fun _ hj => absurd hj (Finset.notMem_empty _))
            (fun j hj => absurd hj (Finset.notMem_empty j)) with
            top := some 0, own := some gid, recovering := false }
          (built cfg [(cfg.idOf cfg.genesis, cfg.genesis)]) hcst hp
          (commitsOf_built _) (by simp only [Node.step, dif_pos h₂, if_pos h₁]; rfl)
      · exact hsame (by simp only [Node.step, dif_neg h₂, if_pos h₁])
    · exact hsame (by simp only [Node.step, if_neg h₁])
  | deliver u id b =>
    rcases step_receipt (cfg := cfg) (s := s) (Or.inl ⟨u, id, b, rfl⟩) with
      he | ⟨s₁, pre, hr, hpre, he⟩
    · exact hsame he
    · obtain ⟨hc₁, hp₁⟩ := hr.good hg hc hp hd
      exact hset s₁ pre hc₁ hp₁ (List.filterMap_eq_nil_iff.mpr fun o ho => by
        obtain ⟨_, _, _, _, rfl⟩ := hpre o ho; rfl) he
  | stream u L =>
    rcases step_receipt (cfg := cfg) (s := s) (Or.inr ⟨u, L, rfl⟩) with he | ⟨s₁, pre, hr, hpre, he⟩
    · exact hsame he
    · obtain ⟨hc₁, hp₁⟩ := hr.good hg hc hp hd
      exact hset s₁ pre hc₁ hp₁ (List.filterMap_eq_nil_iff.mpr fun o ho => by
        obtain ⟨_, _, _, _, rfl⟩ := hpre o ho; rfl) he
  | timer r =>
    rw [persists_step_timer] at hb
    rw [step_timer_fst, commitsOf_step_timer]
    exact (hc : AllGood Good { s with fired := Insert.insert r s.fired }.disk).settle hg hdec hp hb
  | syncRequest peer t fr ids =>
    refine ⟨hc, fun e he => ?_⟩
    simp only [Node.step] at he
    split at he <;> simp [commitsOf] at he
  | ask peer r =>
    refine ⟨hc, fun e he => ?_⟩
    simp only [Node.step] at he
    split at he <;> (try split at he) <;> simp [commitsOf] at he
  | restart =>
    rw [persists_step_restart] at hb
    rw [step_restart_fst, commitsOf_step_restart]
    exact (hc : AllGood Good { s with recovering := true }.disk).settle hg hdec hp hb

end Node

end LeanDag
