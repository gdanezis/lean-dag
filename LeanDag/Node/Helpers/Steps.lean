import LeanDag.Node.Helpers.Flush
/-!
# What one step does to the syncs and the disk

A pass adds no sync (`advance_sub`, `settle_sub`). A delivery or a stream
piece either changes nothing or is a receipt (`Received`, `step_receipt`):
the disk gains blocks of the old syncs or of the input, the syncs' blocks
are old ones or the input's, and what the claims read besides is as
before. Every block of the node's own that a step outputs is on the disk
after it (`step_persist`), and after every step no sync's block is ready
(`noReady_step`).
-/

namespace LeanDag

namespace Node

variable {Validator BlockId Payload : Type} [Fintype Validator] [DecidableEq Validator]
variable [LinearOrder BlockId]
variable {cfg : Config Validator BlockId Payload} {g : BlockId → Block Validator BlockId Payload}

omit [Fintype Validator] in
/-- A build keeps the syncs. -/
theorem tryBuild_syncs {s s' : State Validator BlockId Payload}
    {out : List (Output Validator BlockId Payload)} (h : tryBuild cfg s = some (s', out)) :
    s'.syncs = s.syncs := by
  obtain ⟨_, _, _, -, h, -⟩ := tryBuild_cases h
  unfold buildAbove at h
  dsimp only at h
  split at h
  · split at h
    · rw [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, -⟩ := h
      exact release_syncs _
    · exact absurd h (by simp)
  · exact absurd h (by simp)

omit [Fintype Validator] in
/-- Building keeps the syncs. -/
theorem progress_syncs : ∀ (fuel : ℕ) (s : State Validator BlockId Payload),
    (Node.progress cfg fuel s).1.syncs = s.syncs
  | 0, _ => rfl
  | fuel + 1, s => by
    unfold Node.progress
    split
    · rename_i s₁ out h
      exact (progress_syncs fuel s₁).trans (tryBuild_syncs h)
    · rfl

omit [Fintype Validator] in
/-- Deciding keeps the syncs. -/
theorem decideStep_syncs (s : State Validator BlockId Payload) :
    (Node.decideStep cfg s).1.syncs = s.syncs := by
  unfold Node.decideStep
  dsimp only
  split
  · exact release_syncs _
  · rfl

omit [Fintype Validator] [DecidableEq Validator] in
/-- A store that grows into one reading as `g` reads as `g`. -/
theorem ReadsAs.of_grows {st st' : Store Validator BlockId Payload} (h : ReadsAs g st')
    (hg : Grows st st') : ReadsAs g st :=
  fun j hj => by rw [← hg.blk hj]; exact h j (hg.1 hj)

omit [Fintype Validator] in
/-- A pass adds no sync. -/
theorem advance_sub (s : State Validator BlockId Payload) :
    ∀ e ∈ (Node.advance cfg s).1.syncs, e ∈ s.syncs := by
  have hp := progress_syncs (cfg := cfg) (s.disk.topRound + 2) s
  have hd := decideStep_syncs (cfg := cfg) (Node.progress cfg (s.disk.topRound + 2) s).1
  intro e he
  rw [advance_syncs] at he
  simp only [Node.pass] at he
  have := (flushSyncs_eq (cfg := cfg) _ _).2.2.1 he
  rwa [hd, hp] at this

omit [Fintype Validator] in
/-- The passes add no sync. -/
theorem quiesce_sub (n : ℕ) (s : State Validator BlockId Payload) :
    ∀ e ∈ (quiesce cfg n s).1.syncs, e ∈ s.syncs :=
  (quiesce_rel (P := fun _ => True)
    (R := fun a _ b => ∀ e ∈ b.syncs, e ∈ a.syncs)
    (fun _ _ h => h)
    (fun _ _ _ _ _ h₁ h₂ e he => h₁ e (h₂ e he))
    (fun s _ => ⟨advance_sub s, trivial⟩) n s trivial).1

omit [Fintype Validator] in
/-- **A settle adds no sync.** -/
theorem settle_sub (s : State Validator BlockId Payload) :
    ∀ e ∈ (Node.settle cfg s).1.syncs, e ∈ s.syncs :=
  quiesce_sub _ s

variable (cfg) in
/-- **A receipt** of the input `inp` from `s` to `s₁`: the disk gains blocks
of the syncs or of the input, the syncs' blocks are the old ones or the
input's, and what the claims read besides is as before. -/
structure Received (inp : Input Validator BlockId Payload)
    (s s₁ : State Validator BlockId Payload) : Prop where
  disk : ∃ L : List (BlockId × Block Validator BlockId Payload),
    (∀ e ∈ L, e ∈ s.syncs.map (·.2.1) ∨ e ∈ delivered cfg [inp]) ∧
      s₁.disk = L.foldl (fun st e => acceptOn cfg st e.1 e.2) s.disk
  syncs : ∀ e ∈ s₁.syncs, e.2.1 ∈ s.syncs.map (·.2.1) ∨ e.2.1 ∈ delivered cfg [inp]
  floor : s₁.floor = s.floor
  top : s₁.top = s.top
  own : s₁.own = s.own
  fired : s₁.fired = s.fired
  lo : s₁.lo = s.lo
  decided : s₁.decided = s.decided
  armed : s₁.armed = s.armed
  recovering : s₁.recovering = s.recovering

omit [Fintype Validator] in
/-- **Taking in blocks of the syncs or the input is a receipt**, the syncs
dropped to a part. -/
theorem received_absorb {inp : Input Validator BlockId Payload}
    {s : State Validator BlockId Payload}
    {L : List (BlockId × Block Validator BlockId Payload)}
    (hL : ∀ e ∈ L, e ∈ s.syncs.map (·.2.1) ∨ e ∈ delivered cfg [inp]) :
    Received cfg inp s (tidy (absorb cfg s L)) := by
  obtain ⟨h₁, h₂, h₃, h₄, h₅, h₆, h₇, h₈, h₉, -⟩ := absorb_rest (cfg := cfg) s L
  have ht := tidy_eq (absorb cfg s L)
  refine ⟨⟨L, hL, by rw [ht.1, absorb_disk]⟩, fun e he => ?_, h₁, h₃, h₄, h₅, h₆, h₇, h₈, h₉⟩
  have := ht.2.2.2.2.2.2.2.2.2.2 he
  rw [h₂] at this
  exact Or.inl (List.mem_map_of_mem this)

omit [Fintype Validator] in
/-- **Changing the syncs to blocks of the old ones or of the input is a
receipt.** -/
theorem received_syncs {inp : Input Validator BlockId Payload} {s : State Validator BlockId Payload}
    {S : List (Validator × (BlockId × Block Validator BlockId Payload) × List BlockId)}
    (hS : ∀ e ∈ S, e.2.1 ∈ s.syncs.map (·.2.1) ∨ e.2.1 ∈ delivered cfg [inp]) :
    Received cfg inp s { s with syncs := S } :=
  ⟨⟨[], fun _ h => absurd h List.not_mem_nil, rfl⟩, hS, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

omit [Fintype Validator] in
/-- **A receipt grows the disk.** -/
theorem Received.grows {inp : Input Validator BlockId Payload}
    {s s₁ : State Validator BlockId Payload} (h : Received cfg inp s s₁) :
    Grows s.disk s₁.disk := by
  obtain ⟨L, -, hL⟩ := h.disk
  rw [hL]; exact Grows.foldl _ _

omit [Fintype Validator] in
/-- **Accepting the syncs' blocks grows the disk.** -/
theorem Grows.flushSyncs (fuel : ℕ) (s : State Validator BlockId Payload) :
    Grows s.disk (Node.flushSyncs cfg fuel s).disk := by
  obtain ⟨L, -, hL⟩ := (flushSyncs_eq (cfg := cfg) fuel s).1
  rw [hL]; exact Grows.foldl _ _

omit [Fintype Validator] in
/-- **A receipt of known blocks keeps the invariant.** -/
theorem Received.inv {inp : Input Validator BlockId Payload}
    {s s₁ : State Validator BlockId Payload}
    (hr : Received cfg inp s s₁) {K : Set (BlockId × Block Validator BlockId Payload)}
    {B : List (BlockId × Block Validator BlockId Payload)} (hi : Inv cfg s K B)
    (hd : ∀ e ∈ delivered cfg [inp], e ∈ K) : Inv cfg s₁ K B := by
  obtain ⟨L, hL, hdk⟩ := hr.disk
  have hLK : ∀ e ∈ L, e ∈ K := fun e he => by
    rcases hL e he with h | h
    · obtain ⟨x, hx, rfl⟩ := List.mem_map.mp h; exact hi.pend x hx
    · exact hd e h
  have hfl := foldl_accept_known (cfg := cfg) L hi.known hi.valid hLK
  have hg := hr.grows
  refine ⟨by rw [hdk]; exact hfl.1, fun e he => ?_, by rw [hr.top]; exact hi.rounds, hi.good,
    hi.sub, by rw [hdk]; exact hfl.2, fun j hj => ?_, ?_⟩
  · rcases hr.syncs e he with h | h
    · obtain ⟨x, hx, hxe⟩ := List.mem_map.mp h; rw [← hxe]; exact hi.pend x hx
    · exact hd _ h
  · rw [hr.own] at hj
    exact ⟨hg.1 (hi.own j hj).1, by rw [hg.blk (hi.own j hj).1]; exact (hi.own j hj).2⟩
  · rw [hr.floor, show floorOf cfg s₁ = floorOf cfg s by simp only [floorOf, hr.lo, hr.top]]
    exact hi.floor

omit [Fintype Validator] in
theorem Received.trans {inp : Input Validator BlockId Payload}
    {s s₁ s₂ : State Validator BlockId Payload} (h₁ : Received cfg inp s s₁)
    (h₂ : Received cfg inp s₁ s₂) : Received cfg inp s s₂ := by
  obtain ⟨L₁, hL₁, hd₁⟩ := h₁.disk
  obtain ⟨L₂, hL₂, hd₂⟩ := h₂.disk
  refine ⟨⟨L₁ ++ L₂, fun e he => ?_, by rw [hd₂, hd₁, List.foldl_append]⟩, fun e he => ?_,
    h₂.floor.trans h₁.floor, h₂.top.trans h₁.top, h₂.own.trans h₁.own, h₂.fired.trans h₁.fired,
    h₂.lo.trans h₁.lo, h₂.decided.trans h₁.decided, h₂.armed.trans h₁.armed,
    h₂.recovering.trans h₁.recovering⟩
  · rcases List.mem_append.mp he with he | he
    · exact hL₁ e he
    · rcases hL₂ e he with h | h
      · obtain ⟨x, hx, rfl⟩ := List.mem_map.mp h
        exact h₁.syncs x hx
      · exact Or.inr h
  · rcases h₂.syncs e he with h | h
    · obtain ⟨x, hx, hxe⟩ := List.mem_map.mp h
      rw [← hxe]; exact h₁.syncs x hx
    · exact Or.inr h

/-- **A delivery**, unfolded. -/
theorem step_deliver_eq (s : State Validator BlockId Payload) (u : Validator) (id : BlockId)
    (b : Block Validator BlockId Payload) :
    Node.step cfg s (.deliver u id b) =
      if id = cfg.idOf b ∧ b.creator = u ∧ u ≠ cfg.me ∧ u ∉ s.detected ∧ id ∉ s.disk.ids then
        if ready cfg s (id, b) then Node.settle cfg (tidy (accept cfg s id b))
        else if (0 < b.round → cfg.q ≤ b.refs.card) ∧ (s.syncs.find? fun e => decide (e.1 = u)).all
            (fun e => decide (e.2.1.2.round < b.round)) then
          ((Node.settle cfg { s with syncs := (u, (id, b), ([] : List BlockId)) ::
              (s.syncs.filter fun e => decide (e.1 ≠ u)) }).1,
            request { s with syncs := (u, (id, b), ([] : List BlockId)) ::
              (s.syncs.filter fun e => decide (e.1 ≠ u)) } (u, (id, b), []) ::
            (Node.settle cfg { s with syncs := (u, (id, b), ([] : List BlockId)) ::
              (s.syncs.filter fun e => decide (e.1 ≠ u)) }).2)
        else (s, [])
      else (s, []) := rfl

/-- **A delivery either changes nothing or is a receipt**, after requests,
followed by a settle. -/
theorem step_receipt_deliver (s : State Validator BlockId Payload) (u : Validator) (id : BlockId)
    (b : Block Validator BlockId Payload) :
    Node.step cfg s (.deliver u id b) = (s, []) ∨ ∃ s₁ pre,
      Received cfg (.deliver u id b) s s₁ ∧
      (∀ o ∈ pre, ∃ peer t fr ids, o = .sync peer t fr ids) ∧
      Node.step cfg s (.deliver u id b) =
        ((Node.settle cfg s₁).1, pre ++ (Node.settle cfg s₁).2) := by
  rw [step_deliver_eq]
  by_cases hc : id = cfg.idOf b ∧ b.creator = u ∧ u ≠ cfg.me ∧ u ∉ s.detected ∧ id ∉ s.disk.ids
  · have hd : (id, b) ∈ delivered cfg [Input.deliver u id b] := by simp [delivered, hc.1]
    rw [if_pos hc]
    by_cases hr : ready cfg s (id, b) = true
    · rw [if_pos hr]
      refine Or.inr ⟨tidy (accept cfg s id b), [], received_absorb (L := [(id, b)]) fun e he => ?_,
        fun _ h => absurd h List.not_mem_nil, rfl⟩
      rw [List.mem_singleton] at he; subst he; exact Or.inr hd
    · rw [if_neg hr]
      split
      · refine Or.inr ⟨_, [_], received_syncs fun e he => ?_, fun o ho => ?_, rfl⟩
        · rcases List.mem_cons.mp he with rfl | he
          · exact Or.inr hd
          · exact Or.inl (List.mem_map_of_mem (List.mem_of_mem_filter he))
        · rw [List.mem_singleton] at ho; subst ho; exact ⟨_, _, _, _, rfl⟩
      · exact Or.inl rfl
  · rw [if_neg hc]; exact Or.inl rfl

/-- **A stream piece from a peer with a sync**, unfolded. -/
theorem step_stream_eq (s : State Validator BlockId Payload) (u : Validator)
    (L : List (BlockId × Block Validator BlockId Payload))
    {e : Validator × (BlockId × Block Validator BlockId Payload) × List BlockId}
    (he : (s.syncs.find? fun e => decide (e.1 = u)) = some e) :
    Node.step cfg s (.stream u L) =
      match (tidy (absorb cfg s (inHistory cfg e.2.1 L))).syncs.find? fun e => decide (e.1 = u) with
      | none => Node.settle cfg (tidy (absorb cfg s (inHistory cfg e.2.1 L)))
      | some e₁ =>
        let s₁ := tidy (absorb cfg s (inHistory cfg e.2.1 L))
        let asked := (e₁.2.2 ++ missingIn s₁ (e₁.2.1 :: inHistory cfg e.2.1 L)).dedup
        let e₂ := (u, e₁.2.1, asked)
        let s₂ := { s₁ with syncs := s₁.syncs.map fun x => if x.1 = u then e₂ else x }
        let r := Node.settle cfg s₂
        let moved := s₂.disk.ids.card ≠ s.disk.ids.card ∨ asked.length ≠ e₁.2.2.length
        (r.1, (if moved then [request s₂ e₂] else []) ++ r.2) := by
  simp only [Node.step, he]
  rfl

/-- **A stream piece either changes nothing or is a receipt**, after
requests, followed by a settle. -/
theorem step_receipt_stream (s : State Validator BlockId Payload) (u : Validator)
    (L : List (BlockId × Block Validator BlockId Payload)) :
    Node.step cfg s (.stream u L) = (s, []) ∨ ∃ s₁ pre,
      Received cfg (.stream u L) s s₁ ∧
      (∀ o ∈ pre, ∃ peer t fr ids, o = .sync peer t fr ids) ∧
      Node.step cfg s (.stream u L) = ((Node.settle cfg s₁).1, pre ++ (Node.settle cfg s₁).2) := by
  cases hf : s.syncs.find? fun e => decide (e.1 = u) with
  | none => left; simp only [Node.step, hf]
  | some e =>
    rw [step_stream_eq s u L hf]
    have hL : ∀ x ∈ inHistory cfg e.2.1 L, x ∈ s.syncs.map (·.2.1) ∨
        x ∈ delivered cfg [Input.stream u L] := fun x hx => by
      unfold inHistory at hx
      obtain ⟨hxL, hxp⟩ := List.mem_filter.mp (List.mem_mergeSort.mp hx)
      simp only [Bool.and_eq_true, decide_eq_true_eq] at hxp
      exact Or.inr (by simp [delivered, List.mem_filter, hxL, hxp.1.1])
    have hr := received_absorb (cfg := cfg) (s := s) hL
    cases hf₁ : (tidy (absorb cfg s (inHistory cfg e.2.1 L))).syncs.find?
        fun e => decide (e.1 = u) with
    | none => exact Or.inr ⟨_, [], hr, fun _ h => absurd h List.not_mem_nil, rfl⟩
    | some e₁ =>
      refine Or.inr ⟨_, _, hr.trans (received_syncs fun x hx => ?_), fun o ho => ?_, rfl⟩
      · obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hx
        split
        · exact Or.inl (List.mem_map.mpr ⟨e₁, List.mem_of_find?_eq_some hf₁, rfl⟩)
        · exact Or.inl (List.mem_map_of_mem hy)
      · split at ho
        · rw [List.mem_singleton] at ho; subst ho; exact ⟨_, _, _, _, rfl⟩
        · exact absurd ho List.not_mem_nil

/-- **A delivery or a stream piece either changes nothing or is a
receipt**, after requests, followed by a settle. -/
theorem step_receipt {s : State Validator BlockId Payload} {inp : Input Validator BlockId Payload}
    (hinp : (∃ u id b, inp = .deliver u id b) ∨ ∃ u L, inp = .stream u L) :
    Node.step cfg s inp = (s, []) ∨ ∃ s₁ pre, Received cfg inp s s₁ ∧
      (∀ o ∈ pre, ∃ peer t fr ids, o = .sync peer t fr ids) ∧
      Node.step cfg s inp = ((Node.settle cfg s₁).1, pre ++ (Node.settle cfg s₁).2) := by
  rcases hinp with ⟨u, id, b, rfl⟩ | ⟨u, L, rfl⟩
  · exact step_receipt_deliver s u id b
  · exact step_receipt_stream s u L

/-- **A step's syncs hold the old syncs' blocks or the input's.** -/
theorem step_syncs (s : State Validator BlockId Payload) (inp : Input Validator BlockId Payload) :
    ∀ e ∈ (Node.step cfg s inp).1.syncs,
      e.2.1 ∈ s.syncs.map (·.2.1) ∨ e.2.1 ∈ delivered cfg [inp] := by
  have hset : ∀ s₀ : State Validator BlockId Payload,
      (∀ e ∈ s₀.syncs, e.2.1 ∈ s.syncs.map (·.2.1) ∨ e.2.1 ∈ delivered cfg [inp]) →
      ∀ e ∈ (Node.settle cfg s₀).1.syncs,
        e.2.1 ∈ s.syncs.map (·.2.1) ∨ e.2.1 ∈ delivered cfg [inp] :=
    fun s₀ h₀ e he => h₀ e (settle_sub s₀ e he)
  have hold : ∀ e ∈ s.syncs, e.2.1 ∈ s.syncs.map (·.2.1) ∨ e.2.1 ∈ delivered cfg [inp] :=
    fun e he => Or.inl (List.mem_map_of_mem he)
  cases inp with
  | start =>
    simp only [Node.step]
    split
    · split
      · exact hset _ hold
      · exact hold
    · exact hold
  | deliver u id b =>
    rcases step_receipt (cfg := cfg) (s := s) (Or.inl ⟨u, id, b, rfl⟩) with
      he | ⟨s₁, pre, hr, -, he⟩
    · rw [he]; exact hold
    · rw [he]; exact hset s₁ hr.syncs
  | stream u L =>
    rcases step_receipt (cfg := cfg) (s := s) (Or.inr ⟨u, L, rfl⟩) with he | ⟨s₁, pre, hr, -, he⟩
    · rw [he]; exact hold
    · rw [he]; exact hset s₁ hr.syncs
  | timer r => rw [step_timer_fst]; exact hset _ hold
  | syncRequest peer t fr ids => simp only [Node.step]; exact hold
  | restart => exact hset _ hold

omit [Fintype Validator] in
/-- **What building persists is on the disk after it.** -/
theorem progress_persist : ∀ (fuel : ℕ) (s : State Validator BlockId Payload),
    ∀ e ∈ persists (Node.progress cfg fuel s).2, e.1 ∈ (Node.progress cfg fuel s).1.disk.ids ∧
      (Node.progress cfg fuel s).1.disk.blk e.1 = e.2
  | 0, _, e, he => by simp [Node.progress, persists] at he
  | fuel + 1, s, e, he => by
    rcases hb : tryBuild cfg s with _ | ⟨s₁, out⟩
    · simp [Node.progress, hb, persists] at he
    · simp only [Node.progress, hb] at he ⊢
      obtain ⟨r, id, b, hnew, hrefs, hpred, -, -, -, -, -, hst, -, -, -, hout⟩ :=
        tryBuild_some hb
      have hg := (Grows.progress (cfg := cfg) fuel s₁).1
      rw [hout] at he
      simp only [built, List.flatMap_cons, List.flatMap_nil, List.append_nil, List.cons_append,
        List.nil_append, persists, List.filterMap_cons] at he
      rcases List.mem_cons.mp he with rfl | he
      · have hin : id ∈ s₁.disk.ids := by rw [hst]; exact Store.mem_insert_self
        refine ⟨hg.1 hin, ?_⟩
        rw [hg.blk hin, hst]
        simp only [Store.blk, Store.insert, Std.TreeMap.getD_insert_self]
      · exact progress_persist fuel s₁ e he

omit [Fintype Validator] [DecidableEq Validator] [LinearOrder BlockId] in
/-- Commits persist no block. -/
theorem persists_commits (ds : List (ℕ × Option BlockId)) :
    persists (ds.map fun e => (Output.commit e.1 e.2 : Output Validator BlockId Payload)) =
      [] := by
  induction ds with
  | nil => rfl
  | cons e ds ih => simp [persists]

omit [Fintype Validator] in
/-- Deciding persists no block. -/
theorem decideStep_persist (s : State Validator BlockId Payload) :
    persists (Node.decideStep cfg s).2 = [] := by
  unfold Node.decideStep
  dsimp only
  split
  · exact persists_commits _
  · rfl

omit [Fintype Validator] in
/-- **What a pass persists is on the disk after it.** -/
theorem advance_persist (s : State Validator BlockId Payload) :
    ∀ e ∈ persists (Node.advance cfg s).2, e.1 ∈ (Node.advance cfg s).1.disk.ids ∧
      (Node.advance cfg s).1.disk.blk e.1 = e.2 := by
  intro e he
  have hp := progress_persist (cfg := cfg) (s.disk.topRound + 2) s
  rw [advance_disk]
  simp only [Node.advance, Node.pass] at he ⊢
  generalize Node.progress cfg (s.disk.topRound + 2) s = r at hp he ⊢
  rw [persists_append, persists_append, decideStep_persist, persists_arm, List.append_nil,
    List.append_nil] at he
  obtain ⟨hin, hval⟩ := hp e he
  have hd := decideStep_disk (cfg := cfg) r.1
  generalize Node.decideStep cfg r.1 = d at hd ⊢
  rw [← hd] at hin hval
  obtain ⟨L, -, hL⟩ := (flushSyncs_eq (cfg := cfg) (d.1.syncs.length + 1) d.1).1
  have hgf := Grows.foldl (cfg := cfg) L d.1.disk
  rw [hL]
  exact ⟨hgf.1 hin, by rw [hgf.blk hin]; exact hval⟩

omit [Fintype Validator] in
/-- **What the passes persist is on the disk after them.** -/
theorem quiesce_persist : ∀ (n : ℕ) (s : State Validator BlockId Payload),
    ∀ e ∈ persists (quiesce cfg n s).2, e.1 ∈ (quiesce cfg n s).1.disk.ids ∧
      (quiesce cfg n s).1.disk.blk e.1 = e.2
  | 0, s => by intro e he; simp [Node.quiesce, persists] at he
  | n + 1, s => by
    rcases quiesce_succ_cases (cfg := cfg) n s with he | he <;> rw [he]
    · exact advance_persist s
    · have hga := Grows.quiesce (cfg := cfg) n (Node.advance cfg s).1
      intro e he
      rw [persists_append] at he
      rcases List.mem_append.mp he with he | he
      · obtain ⟨hin, hval⟩ := advance_persist s e he
        exact ⟨hga.1 hin, by rw [hga.blk hin]; exact hval⟩
      · exact quiesce_persist n _ e he

omit [Fintype Validator] in
/-- **What a settle persists is on the disk after it.** -/
theorem settle_persist (s : State Validator BlockId Payload) :
    ∀ e ∈ persists (Node.settle cfg s).2, e.1 ∈ (Node.settle cfg s).1.disk.ids ∧
      (Node.settle cfg s).1.disk.blk e.1 = e.2 :=
  quiesce_persist _ s

omit [Fintype Validator] in
/-- What a settle persists, after outputs persisting at most one block on
disk, is on the disk after it. -/
theorem settle_persist_of {s₀ : State Validator BlockId Payload}
    {pre : List (Output Validator BlockId Payload)}
    (hpre : persists pre = [] ∨ ∃ e₀, persists pre = [e₀] ∧ e₀.1 ∈ s₀.disk.ids ∧
      s₀.disk.blk e₀.1 = e₀.2) :
    ∀ e ∈ persists (pre ++ (Node.settle cfg s₀).2), e.1 ∈ (Node.settle cfg s₀).1.disk.ids ∧
      (Node.settle cfg s₀).1.disk.blk e.1 = e.2 := by
  intro e he
  rw [persists_append] at he
  rcases List.mem_append.mp he with he | he
  · rcases hpre with hpre | ⟨e₀, hpre, hin, hval⟩
    · rw [hpre] at he; exact absurd he (List.not_mem_nil)
    · rw [hpre, List.mem_singleton] at he
      subst he
      have hg := Grows.settle (cfg := cfg) s₀
      exact ⟨hg.1 hin, by rw [hg.blk hin]; exact hval⟩
  · exact settle_persist s₀ e he

/-- **What a step persists is on the disk after it.** -/
theorem step_persist {s : State Validator BlockId Payload} {inp : Input Validator BlockId Payload} :
    ∀ e ∈ persists (Node.step cfg s inp).2, e.1 ∈ (Node.step cfg s inp).1.disk.ids ∧
      (Node.step cfg s inp).1.disk.blk e.1 = e.2 := by
  cases inp with
  | start =>
    by_cases h₁ : s.top = none ∧ cfg.Admissible
    · by_cases h₂ : cfg.idOf cfg.genesis ∉ s.disk.ids ∧
          rowValid cfg.q (Function.update s.disk.blk (cfg.idOf cfg.genesis) cfg.genesis)
            cfg.genesis
      · let st := s.disk.insert (cfg.idOf cfg.genesis) cfg.genesis h₂.1
          (fun _ hj => absurd hj (Finset.notMem_empty _))
          (fun j hj => absurd hj (Finset.notMem_empty j))
        let s₀ : State Validator BlockId Payload :=
          { keep s (cfg.idOf cfg.genesis) cfg.genesis h₂.1
              (fun _ hj => absurd hj (Finset.notMem_empty _))
              (fun j hj => absurd hj (Finset.notMem_empty j)) with
              top := some 0, own := some (cfg.idOf cfg.genesis), recovering := false }
        have he : Node.step cfg s .start =
            ((Node.settle cfg s₀).1, built cfg [(cfg.idOf cfg.genesis, cfg.genesis)] ++
              (Node.settle cfg s₀).2) := by
          simp only [Node.step, dif_pos h₂, if_pos h₁]; rfl
        rw [he]
        exact settle_persist_of (Or.inr ⟨(cfg.idOf cfg.genesis, cfg.genesis), by
          simp [built, persists], (by simp [s₀, keep, Store.insert_ids]), by
          simp [s₀, keep, Store.insert_blk]⟩)
      · simp only [Node.step, dif_neg h₂, if_pos h₁]; simp [persists]
    · simp only [Node.step, if_neg h₁]; simp [persists]
  | deliver u id b =>
    rcases step_receipt (cfg := cfg) (s := s) (Or.inl ⟨u, id, b, rfl⟩) with
      h | ⟨s₁, pre, -, hpre, h⟩
    · rw [h]; simp [persists]
    · rw [h]
      refine settle_persist_of (Or.inl (List.filterMap_eq_nil_iff.mpr fun o ho => ?_))
      obtain ⟨_, _, _, _, rfl⟩ := hpre o ho; rfl
  | stream u L =>
    rcases step_receipt (cfg := cfg) (s := s) (Or.inr ⟨u, L, rfl⟩) with h | ⟨s₁, pre, -, hpre, h⟩
    · rw [h]; simp [persists]
    · rw [h]
      refine settle_persist_of (Or.inl (List.filterMap_eq_nil_iff.mpr fun o ho => ?_))
      obtain ⟨_, _, _, _, rfl⟩ := hpre o ho; rfl
  | timer r =>
    intro e he
    rw [step_timer_fst]
    rcases step_timer_snd (cfg := cfg) s r with h | h <;> rw [h] at he
    · exact settle_persist { s with fired := fire s r, recovering := false } e he
    · rw [persists_append, persists_resend, List.append_nil] at he
      exact settle_persist { s with fired := fire s r, recovering := false } e he
  | syncRequest peer t fr ids =>
    intro e he
    simp only [Node.step] at he
    split at he <;> simp [persists] at he
  | restart =>
    intro e he
    change e ∈ persists (Node.resend cfg s ++ Node.rearm cfg s ++
      (Node.settle cfg { s with recovering := true }).2) at he
    rw [persists_append, persists_append, persists_resend, persists_rearm, List.nil_append,
      List.nil_append] at he
    exact settle_persist { s with recovering := true } e he

variable (cfg) in
/-- No sync's block is ready. -/
def NoReady (s : State Validator BlockId Payload) : Prop :=
  ∀ e ∈ s.syncs, readyOn cfg s.disk e.2.1 = false

omit [Fintype Validator] in
/-- **A ready block of a list is held after accepting the list.** -/
theorem foldl_holds : ∀ (l : List (BlockId × Block Validator BlockId Payload))
    {st : Store Validator BlockId Payload} {e : BlockId × Block Validator BlockId Payload},
    e ∈ l → readyOn cfg st e = true → e.1 ∈ (l.foldl (fun s e => acceptOn cfg s e.1 e.2) st).ids
  | [], _, _, he, _ => absurd he List.not_mem_nil
  | x :: l, st, e, he, hr => by
    rw [List.foldl_cons]
    rcases List.mem_cons.mp he with rfl | he
    · refine (Grows.foldl (cfg := cfg) l _).1 ?_
      unfold acceptOn
      split
      · exact Store.mem_insert_self
      · rename_i hc
        by_contra hin
        exact hc ⟨hin, by simpa [readyOn] using hr⟩
    · exact foldl_holds l he (ready_mono (Grows.accept (cfg := cfg) st x.1 x.2) hr)

omit [Fintype Validator] in
/-- **No sync's block is left ready** by more passes than syncs. -/
theorem flushSyncs_no_ready : ∀ (fuel : ℕ) (s : State Validator BlockId Payload),
    s.syncs.length < fuel → NoReady cfg (Node.flushSyncs cfg fuel s)
  | 0, _, h => absurd h (Nat.not_lt_zero _)
  | fuel + 1, s, h => by
    unfold Node.flushSyncs
    dsimp only
    split
    · rename_i hE
      intro e he
      rw [List.isEmpty_iff, List.partition_eq_filter_filter, List.filter_eq_nil_iff] at hE
      have := hE e he
      rw [ready_eq] at this
      simpa using this
    · rename_i hE
      apply flushSyncs_no_ready
      obtain ⟨x, hx⟩ := List.exists_mem_of_ne_nil _ (by rwa [List.isEmpty_iff] at hE)
      rw [List.partition_eq_filter_filter] at hx
      obtain ⟨hxs, hxr⟩ := List.mem_filter.mp hx
      have hheld : x.2.1.1 ∈ (Node.absorb cfg s (((s.syncs.partition fun e =>
          ready cfg s e.2.1).1).map (·.2.1))).disk.ids := by
        rw [absorb_disk]
        refine foldl_holds _ (List.mem_map_of_mem ?_) (by rw [← ready_eq]; exact hxr)
        rw [List.partition_eq_filter_filter]; exact hx
      have hlt : (Node.tidy (Node.absorb cfg s (((s.syncs.partition fun e =>
          ready cfg s e.2.1).1).map (·.2.1)))).syncs.length < s.syncs.length := by
        unfold Node.tidy
        rw [(absorb_rest (cfg := cfg) s _).2.1]
        exact List.length_filter_lt_length_iff_exists.mpr ⟨x, hxs, by
          simp only [decide_eq_true_eq, not_and, not_not]
          exact fun hn => absurd hheld hn⟩
      omega

omit [Fintype Validator] in
/-- **Accepting the syncs' blocks keeps no more syncs, and changes nothing
if it keeps as many.** -/
theorem flushSyncs_bound : ∀ (fuel : ℕ) (s : State Validator BlockId Payload),
    (Node.flushSyncs cfg fuel s).syncs.length ≤ s.syncs.length ∧
      ((Node.flushSyncs cfg fuel s).syncs.length = s.syncs.length →
        Node.flushSyncs cfg fuel s = s)
  | 0, _ => ⟨le_rfl, fun _ => rfl⟩
  | fuel + 1, s => by
    unfold Node.flushSyncs
    dsimp only
    split
    · exact ⟨le_rfl, fun _ => rfl⟩
    · rename_i hE
      obtain ⟨x, hx⟩ := List.exists_mem_of_ne_nil _ (by rwa [List.isEmpty_iff] at hE)
      rw [List.partition_eq_filter_filter] at hx
      obtain ⟨hxs, hxr⟩ := List.mem_filter.mp hx
      have hheld : x.2.1.1 ∈ (Node.absorb cfg s (((s.syncs.partition fun e =>
          ready cfg s e.2.1).1).map (·.2.1))).disk.ids := by
        rw [absorb_disk]
        refine foldl_holds _ (List.mem_map_of_mem ?_) (by rw [← ready_eq]; exact hxr)
        rw [List.partition_eq_filter_filter]; exact hx
      have hlt : (Node.tidy (Node.absorb cfg s (((s.syncs.partition fun e =>
          ready cfg s e.2.1).1).map (·.2.1)))).syncs.length < s.syncs.length := by
        unfold Node.tidy
        rw [(absorb_rest (cfg := cfg) s _).2.1]
        exact List.length_filter_lt_length_iff_exists.mpr ⟨x, hxs, by
          simp only [decide_eq_true_eq, not_and, not_not]
          exact fun hn => absurd hheld hn⟩
      have h₁ := (flushSyncs_bound fuel (Node.tidy (Node.absorb cfg s (((s.syncs.partition fun e =>
          ready cfg s e.2.1).1).map (·.2.1))))).1
      exact ⟨by omega, fun h => by omega⟩

omit [Fintype Validator] in
/-- After at least one pass no sync's block is ready. -/
theorem noReady_quiesce : ∀ (n : ℕ) (s : State Validator BlockId Payload),
    NoReady cfg (quiesce cfg (n + 1) s).1
  | n, s => by
    rcases quiesce_succ_cases (cfg := cfg) n s with he | he <;> rw [he]
    · simp only [NoReady, advance_syncs, advance_disk, Node.pass]
      exact flushSyncs_no_ready _ _ (Nat.lt_succ_self _)
    · cases n with
      | zero =>
        simp only [NoReady, Node.quiesce, advance_syncs, advance_disk, Node.pass]
        exact flushSyncs_no_ready _ _ (Nat.lt_succ_self _)
      | succ n => exact noReady_quiesce n _

omit [Fintype Validator] in
/-- After a settle no sync's block is ready. -/
theorem noReady_settle (s : State Validator BlockId Payload) :
    NoReady cfg (Node.settle cfg s).1 := by
  obtain ⟨n, hn⟩ := passes_succ (cfg := cfg) s
  unfold Node.settle
  rw [hn]
  exact noReady_quiesce n s

/-- **After every step no sync's block is ready.** -/
theorem noReady_step {s : State Validator BlockId Payload} (h : NoReady cfg s)
    (inp : Input Validator BlockId Payload) : NoReady cfg (Node.step cfg s inp).1 := by
  cases inp with
  | start =>
    simp only [Node.step]
    split
    · split
      · exact noReady_settle _
      · exact h
    · exact h
  | deliver u id b =>
    rcases step_receipt (cfg := cfg) (s := s) (Or.inl ⟨u, id, b, rfl⟩) with he | ⟨s₁, pre, -, -, he⟩
    · rw [he]; exact h
    · rw [he]; exact noReady_settle _
  | stream u L =>
    rcases step_receipt (cfg := cfg) (s := s) (Or.inr ⟨u, L, rfl⟩) with he | ⟨s₁, pre, -, -, he⟩
    · rw [he]; exact h
    · rw [he]; exact noReady_settle _
  | timer r => rw [step_timer_fst]; exact noReady_settle _
  | syncRequest peer t fr ids => simp only [Node.step]; exact h
  | restart => exact noReady_settle _

end Node

end LeanDag
