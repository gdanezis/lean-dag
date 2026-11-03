import LeanDag.Node.Helpers.Commits
/-!
# A node's disk stays good along a run

With every step (`AllGood.step`), a disk whose blocks are good while a
condition `C` holds of the next undecided slot stays so, when `C` only
weakens as the slot grows and the store takes in only good blocks
(`Grounds`), and every decision a step outputs satisfies what each
decision step from such a disk gives (`DecidesWell`). At a node that
drops, the blocks below the round of a slot at which `C` holds are to be
good, which covers the blocks a decision on a proof takes in without
their references (`AllGood.decideOn`), and the verdict a proof gives is to
satisfy what the decisions do. On a record grounding what the node knew, a cut is a good
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
variable {C : ℕ → Prop} {Q : ℕ × Option BlockId → Prop}

variable (cfg) in
/-- **Each decision step from a disk good while `C` holds of the next
undecided slot outputs decisions satisfying `Q`.** -/
def DecidesWell (Good : BlockId → Block Validator BlockId Payload → Prop) (C : ℕ → Prop)
    (Q : ℕ × Option BlockId → Prop) : Prop :=
  ∀ s : State Validator BlockId Payload, (C s.lo → AllGood Good s.disk) →
    ∀ e ∈ commitsOf (Node.decideStep cfg s).2, Q e

omit [Fintype Validator] in
/-- **A pass does not lower the next undecided slot.** -/
theorem advance_lo_ge (s : State Validator BlockId Payload) : s.lo ≤ (Node.advance cfg s).1.lo := by
  rw [advance_lo]
  simp only [Node.pass, flushSyncs_lo]
  exact (Grows.progress (cfg := cfg) _ s).2.symm.le.trans (decideStep_lo _)

omit [Fintype Validator] in
/-- **Taking in a known block of a proof keeps the store good**, when the
blocks below `F` are good. -/
theorem AllGood.takeOn (hg : Grounds cfg Good K) {F : ℕ} {st : Store Validator BlockId Payload}
    (hbase : ∀ x ∈ K, x.2.round < F → Good x.1 x.2) (hc : AllGood Good st)
    {e : BlockId × Block Validator BlockId Payload} (he : e ∈ K) :
    AllGood Good (takeOn cfg F st e) := by
  unfold Node.takeOn
  split
  · rename_i h
    intro j hj
    rw [Store.base_ids] at hj
    rw [Store.full_base]
    split
    · rename_i hje; subst hje; exact hbase e he h.2.1
    · rename_i hje; exact hc j ((Finset.mem_insert.mp hj).resolve_left hje)
  · exact hc.accept hg he

variable (hC : ∀ n n' : ℕ, n ≤ n' → C n' → C n)
include hC

omit [Fintype Validator] in
/-- **A pass from a disk good while `C` holds**: the disk stays so, and the
decisions satisfy `Q`. -/
theorem AllGood.advance (hg : Grounds cfg Good K) (hdec : DecidesWell cfg Good C Q)
    {s : State Validator BlockId Payload} (hc : C s.lo → AllGood Good s.disk)
    (hp : ∀ e ∈ s.syncs, e.2.1 ∈ K)
    (hb : ∀ e ∈ persists (Node.advance cfg s).2, e ∈ K) :
    (C (Node.advance cfg s).1.lo → AllGood Good (Node.advance cfg s).1.disk) ∧
      ∀ e ∈ commitsOf (Node.advance cfg s).2, Q e := by
  refine ⟨fun h => (hc (hC _ _ (advance_lo_ge s) h)).advanceStore hg hp hb, ?_⟩
  obtain ⟨bs, hbs⟩ := progress_built (cfg := cfg) (s.disk.topRound + 2) s
  rw [advance_snd, persists_append, persists_arm, List.append_nil] at hb
  rw [advance_snd, commitsOf_append, commitsOf_arm, List.append_nil]
  simp only [Node.pass] at hb ⊢
  rw [persists_append] at hb
  have hc₁ : C (Node.progress cfg (s.disk.topRound + 2) s).1.lo →
      AllGood Good (Node.progress cfg (s.disk.topRound + 2) s).1.disk := fun h =>
    AllGood.progress hg _ (hc (by rwa [(Grows.progress (cfg := cfg) _ s).2] at h))
      fun e he => hb e (List.mem_append_left _ he)
  generalize Node.progress cfg (s.disk.topRound + 2) s = r at hbs hc₁ ⊢
  have hv := hdec _ hc₁
  intro e he
  rw [commitsOf_append, hbs, commitsOf_built, List.nil_append] at he
  exact hv e he

omit [Fintype Validator] in
/-- **The passes from a disk good while `C` holds.** -/
theorem AllGood.quiesce (hg : Grounds cfg Good K) (hdec : DecidesWell cfg Good C Q) :
    ∀ (n : ℕ) {s : State Validator BlockId Payload},
    (C s.lo → AllGood Good s.disk) → (∀ e ∈ s.syncs, e.2.1 ∈ K) →
    (∀ e ∈ persists (Node.quiesce cfg n s).2, e ∈ K) →
    (C (Node.quiesce cfg n s).1.lo → AllGood Good (Node.quiesce cfg n s).1.disk) ∧
      ∀ e ∈ commitsOf (Node.quiesce cfg n s).2, Q e
  | 0, s, hc, _, _ => ⟨hc, fun e he => by simp [Node.quiesce, commitsOf] at he⟩
  | n + 1, s, hc, hp, hb => by
    rcases quiesce_succ_cases (cfg := cfg) n s with he | he <;> rw [he] at hb ⊢
    · exact AllGood.advance hC hg hdec hc hp hb
    · rw [persists_append] at hb
      obtain ⟨hc₁, hv₁⟩ := AllGood.advance hC hg hdec hc hp
        fun e he => hb e (List.mem_append_left _ he)
      obtain ⟨hc₂, hv₂⟩ := AllGood.quiesce hg hdec n hc₁
        (fun e he => hp e (advance_sub (cfg := cfg) s e he))
        fun e he => hb e (List.mem_append_right _ he)
      refine ⟨hc₂, fun e he => ?_⟩
      rw [commitsOf_append] at he
      exact (List.mem_append.mp he).elim (hv₁ e) (hv₂ e)

omit [Fintype Validator] in
/-- **Settling from a disk good while `C` holds.** -/
theorem AllGood.settle (hg : Grounds cfg Good K) (hdec : DecidesWell cfg Good C Q)
    {s : State Validator BlockId Payload} (hc : C s.lo → AllGood Good s.disk)
    (hp : ∀ e ∈ s.syncs, e.2.1 ∈ K)
    (hb : ∀ e ∈ persists (Node.settle cfg s).2, e ∈ K) :
    (C (Node.settle cfg s).1.lo → AllGood Good (Node.settle cfg s).1.disk) ∧
      ∀ e ∈ commitsOf (Node.settle cfg s).2, Q e :=
  AllGood.quiesce hC hg hdec (passes cfg s) hc hp hb

omit [Fintype Validator] in
/-- **Deciding on a proof of known blocks keeps the disk good while `C`
holds**, when the blocks below the next undecided slot's round are good. -/
theorem AllGood.decideOn (hg : Grounds cfg Good K) {s : State Validator BlockId Payload}
    (hc : C s.lo → AllGood Good s.disk) (hfl : s.floor ≤ floorOf cfg s) {k : ℕ}
    (hk : s.lo ≤ k + 1) (d : Option BlockId) {L : List (BlockId × Block Validator BlockId Payload)}
    (hL : ∀ e ∈ hashed cfg L, e ∈ K)
    (hbase : ∀ x ∈ K, x.2.round < cfg.slots.slotRound (k + 1) → Good x.1 x.2) :
    C (k + 1) → AllGood Good (Node.decideOn cfg s k d L).disk := by
  intro hCk
  let s₁ : State Validator BlockId Payload :=
    { s with
      lo := k + 1
      decided := (k, d) :: s.decided
      proofs := (k, ((hashed cfg L).map Prod.fst).toFinset) :: s.proofs }
  have e : Node.decideOn cfg s k d L = ((hashed cfg L).mergeSort fun x y =>
      decide (x.2.round ≤ y.2.round)).foldl (Node.takeProof cfg) (release cfg s₁) := rfl
  have hF : (release cfg s₁).floor ≤ cfg.slots.slotRound (k + 1) := by
    rw [release_floor]
    refine max_le (hfl.trans ((min_le_left _ _).trans (cfg.slots.mono (by omega))))
      (min_le_left _ _)
  have h₀ : ∀ (l : List (BlockId × Block Validator BlockId Payload)), (∀ x ∈ l, x ∈ K) →
      ∀ (F : ℕ) (st : Store Validator BlockId Payload), F ≤ cfg.slots.slotRound (k + 1) →
        AllGood Good st → AllGood Good (l.foldl (Node.takeOn cfg F) st) := by
    intro l
    induction l with
    | nil => exact fun _ _ _ _ h => h
    | cons x l ih =>
      intro hl F st hFk h
      exact ih (fun y hy => hl y (List.mem_cons_of_mem _ hy)) F _ hFk
        (h.takeOn hg (fun y hy hr => hbase y hy (by omega)) (hl x List.mem_cons_self))
  rw [e, (foldl_takeProof _ _).1]
  exact h₀ _ (fun x hx => hL x (List.mem_mergeSort.mp hx)) _ _ hF
    ((hc (hC _ _ hk hCk)).restrips (release_disk s₁))

/-- **A step from a disk good while `C` holds of the next undecided slot**:
the disk stays so, and the decisions satisfy `Q`. At a node that drops, the
blocks below the next undecided slot's round are to be good, and a verdict a
proof of known blocks gives is to satisfy `Q`. -/
theorem AllGood.step (hg : Grounds cfg Good K) (hdec : DecidesWell cfg Good C Q)
    (hbase : cfg.drops = true → ∀ n, C n → ∀ x ∈ K, x.2.round < cfg.slots.slotRound n →
      Good x.1 x.2)
    (hprf : cfg.drops = true → ∀ k L d, verdictOn cfg k L = some d →
      (∀ e ∈ hashed cfg L, e ∈ K) → Q (k, d))
    {s : State Validator BlockId Payload}
    (i : Input Validator BlockId Payload) (hc : C s.lo → AllGood Good s.disk)
    (hfl : s.floor ≤ floorOf cfg s) (hp : ∀ e ∈ s.syncs, e.2.1 ∈ K)
    (hd : ∀ e ∈ delivered cfg [i], e ∈ K)
    (hb : ∀ e ∈ persists (Node.step cfg s i).2, e ∈ K) :
    (C (Node.step cfg s i).1.lo → AllGood Good (Node.step cfg s i).1.disk) ∧
      ∀ e ∈ commitsOf (Node.step cfg s i).2, Q e := by
  -- a step that settles a state `s₀`, after outputs without decisions
  have hset : ∀ (s₀ : State Validator BlockId Payload)
      (pre : List (Output Validator BlockId Payload)),
      (C s₀.lo → AllGood Good s₀.disk) → (∀ e ∈ s₀.syncs, e.2.1 ∈ K) → commitsOf pre = [] →
      Node.step cfg s i = ((Node.settle cfg s₀).1, pre ++ (Node.settle cfg s₀).2) →
      (C (Node.step cfg s i).1.lo → AllGood Good (Node.step cfg s i).1.disk) ∧
        ∀ e ∈ commitsOf (Node.step cfg s i).2, Q e := by
    intro s₀ pre hc₀ hp₀ hpre he
    rw [he] at hb ⊢
    rw [persists_append] at hb
    rw [commitsOf_append, hpre, List.nil_append]
    exact AllGood.settle hC hg hdec hc₀ hp₀ fun e he => hb e (List.mem_append_right _ he)
  have hsame : Node.step cfg s i = (s, []) →
      (C (Node.step cfg s i).1.lo → AllGood Good (Node.step cfg s i).1.disk) ∧
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
        have hcst : C s.lo → AllGood Good st := fun h =>
          (hc h).insert (hg _ (hc h) _ hx h₂.1 hnil h₂.2)
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
    · refine hset s₁ pre (fun h => (hr.good hg (hc (by rwa [hr.lo] at h)) hp hd).1)
        (fun e he' => ?_) (List.filterMap_eq_nil_iff.mpr fun o ho => by
          obtain ⟨_, _, _, _, rfl⟩ := hpre o ho; rfl) he
      rcases hr.syncs e he' with h | h
      · obtain ⟨x, hx, hxe⟩ := List.mem_map.mp h; rw [← hxe]; exact hp x hx
      · exact hd _ h
  | stream u L =>
    rcases step_receipt (cfg := cfg) (s := s) (Or.inr ⟨u, L, rfl⟩) with he | ⟨s₁, pre, hr, hpre, he⟩
    · exact hsame he
    · refine hset s₁ pre (fun h => (hr.good hg (hc (by rwa [hr.lo] at h)) hp hd).1)
        (fun e he' => ?_) (List.filterMap_eq_nil_iff.mpr fun o ho => by
          obtain ⟨_, _, _, _, rfl⟩ := hpre o ho; rfl) he
      rcases hr.syncs e he' with h | h
      · obtain ⟨x, hx, hxe⟩ := List.mem_map.mp h; rw [← hxe]; exact hp x hx
      · exact hd _ h
  | timer r =>
    rw [persists_step_timer] at hb
    rw [step_timer_fst, commitsOf_step_timer]
    exact AllGood.settle hC hg hdec (s := { s with fired := fire s r, recovering := false })
      hc hp hb
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
    exact AllGood.settle hC hg hdec (s := { s with recovering := true }) hc hp hb
  | askProof peer k =>
    refine ⟨hc, fun e he => ?_⟩
    simp only [Node.step] at he
    split at he <;> (try split at he) <;> simp [commitsOf] at he
  | proof u k L =>
    by_cases hcnd : cfg.drops = true ∧ u ∉ s.detected ∧ k = s.lo
    · obtain ⟨hdr, hu, rfl⟩ := hcnd
      cases hv : verdictOn cfg s.lo L with
      | none => exact hsame (by simp [Node.step, hdr, hu, hv])
      | some d =>
        have hL : ∀ e ∈ hashed cfg L, e ∈ K := fun e he => hd e (by
          unfold hashed at he; simpa [delivered] using he)
        have he : Node.step cfg s (.proof u s.lo L) =
            ((Node.settle cfg (Node.tidy (Node.decideOn cfg s s.lo d L))).1,
              .commit s.lo d :: (Node.settle cfg (Node.tidy (Node.decideOn cfg s s.lo d L))).2 ++
                [.askProof (Node.settle cfg (Node.tidy (Node.decideOn cfg s s.lo d L))).1.lo]) := by
          simp [Node.step, hdr, hu, hv]
        obtain ⟨-, -, -, -, hlo, -⟩ := decideOn_rest (cfg := cfg) s s.lo d L
        rw [he] at hb ⊢
        obtain ⟨hc₂, hv₂⟩ := AllGood.settle hC hg hdec
          (s := Node.tidy (Node.decideOn cfg s s.lo d L))
          (fun h => AllGood.decideOn hC hg hc hfl (by omega) d hL
            (hbase hdr (s.lo + 1) (by rwa [← hlo])) (by rwa [← hlo]))
          (fun e he => hp e (by
            rw [← (decideOn_rest (cfg := cfg) s s.lo d L).1]
            exact (tidy_eq _).2.2.2.2.2.2.2.2.2.2 he))
          fun e he => hb e (by
            rw [List.cons_append, persists, List.filterMap_cons]
            simp only
            rw [← persists, persists_append]
            exact List.mem_append_left _ he)
        refine ⟨hc₂, fun e he => ?_⟩
        rw [List.cons_append, commitsOf, List.filterMap_cons] at he
        simp only at he
        rw [← commitsOf, commitsOf_append] at he
        rcases List.mem_cons.mp he with rfl | he
        · exact hprf hdr s.lo L d hv hL
        · rcases List.mem_append.mp he with he | he
          · exact hv₂ e he
          · simp [commitsOf] at he
    · exact hsame (by simp [Node.step, hcnd])

end Node

end LeanDag
