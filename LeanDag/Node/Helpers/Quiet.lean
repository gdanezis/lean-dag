import LeanDag.Node.Helpers.Wait
import LeanDag.Node.Helpers.Steps
/-!
# A settle stops because nothing changes

`docs/validator.md` §3.5. Within a settle the node's blocks of other
authors lie at or below a round the state fixes, so it builds only up to
the round above it, and its next undecided slot is bounded too. Each pass
but the last raises its top or its next undecided slot, or leaves fewer
blocks pending, so `passes s` passes reach one that changes none of them
(`quiesce_stops`). The state it leaves can build, decide and accept
nothing more (`Settled`, `settle_settled`).
-/

namespace LeanDag

namespace Node

variable {Validator BlockId Payload : Type} [Fintype Validator] [DecidableEq Validator]
variable [LinearOrder BlockId]
variable {cfg : Config Validator BlockId Payload}

/-! ## The blocks a settle holds -/

/-- **The blocks a state holds lie in `K`**: the blocks on its disk and its
pending ones. -/
def InK (K : Set (BlockId × Block Validator BlockId Payload)) (s : State Validator BlockId Payload) :
    Prop :=
  (∀ j ∈ s.disk.ids, (j, s.disk.blk j) ∈ K) ∧ ∀ e ∈ s.pending, e ∈ K

variable (cfg) in
/-- **The blocks of a settle from a state of rounds at most `R`**: of any
author at most `R`, the node's own at most `R + 1`. -/
def Below (R : ℕ) : Set (BlockId × Block Validator BlockId Payload) :=
  {x | x.2.round ≤ R ∨ (x.2.creator = cfg.me ∧ x.2.round ≤ R + 1)}

omit [Fintype Validator] in
/-- A build keeps the blocks in `K`, given the block it builds. -/
theorem InK.tryBuild {K : Set (BlockId × Block Validator BlockId Payload)}
    {s s' : State Validator BlockId Payload} {out : List (Output Validator BlockId Payload)}
    (h : InK K s) (hb : Node.tryBuild cfg s = some (s', out))
    (hK : ∀ e ∈ persists out, e ∈ K) : InK K s' := by
  obtain ⟨r, id, b, hnew, hrefs, hpred, -, -, -, hid, -, hst, -, hpd, -, hout⟩ :=
    tryBuild_some hb
  refine ⟨?_, by rw [hpd]; exact h.2⟩
  rw [hst]
  exact known_insert h.1 (hK _ (by rw [hout]; simp [built, persists]))

omit [Fintype Validator] in
/-- Building keeps the blocks in `K`, given the blocks it builds. -/
theorem InK.progress {K : Set (BlockId × Block Validator BlockId Payload)} :
    ∀ (fuel : ℕ) {s : State Validator BlockId Payload}, InK K s →
      (∀ e ∈ persists (Node.progress cfg fuel s).2, e ∈ K) →
      InK K (Node.progress cfg fuel s).1
  | 0, _, h, _ => h
  | fuel + 1, s, h, hK => by
    rcases hb : Node.tryBuild cfg s with _ | ⟨s₁, out⟩
    · simp only [Node.progress, hb]; exact h
    · simp only [Node.progress, hb] at hK ⊢
      rw [persists_append] at hK
      exact InK.progress fuel (h.tryBuild hb fun e he => hK e (List.mem_append_left _ he))
        fun e he => hK e (List.mem_append_right _ he)

omit [Fintype Validator] in
/-- **A pass keeps the blocks in `K`**, given the blocks it builds. -/
theorem InK.advance {K : Set (BlockId × Block Validator BlockId Payload)}
    {s : State Validator BlockId Payload} (h : InK K s)
    (hK : ∀ e ∈ persists (Node.advance cfg s).2, e ∈ K) : InK K (Node.advance cfg s).1 := by
  rw [advance_snd, persists_append, persists_arm, List.append_nil] at hK
  rw [InK, advance_disk, advance_pending]
  simp only [Node.pass, flush_disk, flush_pending] at hK ⊢
  rw [persists_append] at hK
  have h₁ := InK.progress _ h fun e he => hK e (List.mem_append_left _ he)
  generalize Node.progress cfg (s.disk.topRound + 2) s = r at h₁ ⊢
  have h₂ : InK K (Node.decideStep cfg r.1).1 := by
    rw [InK, decideStep_disk, decideStep_pending (cfg := cfg) r.1]; exact h₁
  exact flush_in (cfg := cfg) ((Node.decideStep cfg r.1).1.pending.length + 1) h₂.1 h₂.2

/-! ## Bounds within a settle -/

omit [Fintype Validator] in
/-- A block in `Below R` read from the disk is the node's own, or at a
round at most `R`. -/
theorem below_blk {R : ℕ} {s : State Validator BlockId Payload} (h : InK (Below cfg R) s)
    {j : BlockId} (hj : j ∈ s.disk.ids) :
    (s.disk.blk j).round ≤ R ∨ ((s.disk.blk j).creator = cfg.me ∧ (s.disk.blk j).round ≤ R + 1) :=
  h.1 j hj

omit [Fintype Validator] in
/-- **The disk's top round** within a settle is at most `R + 1`. -/
theorem below_topRound {R : ℕ} {s : State Validator BlockId Payload}
    (h : InK (Below cfg R) s) : s.disk.topRound ≤ R + 1 := by
  rw [Store.topRound_eq]
  refine Finset.sup_le fun j hj => ?_
  rcases below_blk h hj with h | h
  · omega
  · exact h.2

omit [Fintype Validator] in
/-- **A build within a settle** is above a round at most `R`, for a quorum
of two or more. -/
theorem below_build {R : ℕ} (hq : 2 ≤ cfg.q) {s s' : State Validator BlockId Payload}
    {out : List (Output Validator BlockId Payload)} (h : InK (Below cfg R) s)
    (hb : Node.tryBuild cfg s = some (s', out)) :
    ∃ r, s'.top = some (r + 1) ∧ s.top.getD 0 ≤ r ∧ r ≤ R := by
  obtain ⟨t, r, o, ht, hb, hro⟩ := tryBuild_cases hb
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, htop, -⟩ := buildAbove_some hb
  refine ⟨r, htop, by rw [ht]; rcases hro with ⟨rfl, -⟩ | ⟨-, hlt, -⟩ <;> simp <;> omega, ?_⟩
  unfold buildAbove at hb
  dsimp only at hb
  split at hb
  · rename_i hc
    have hc := hc.1.trans (Finset.card_le_card (s.mirrors.authorsAt_sub r))
    rw [Store.authorsAt_eq] at hc
    -- a second author at round `r`
    have h2 : 1 < (authorsIn s.disk.toRecord s.disk.ids r).card := by omega
    obtain ⟨a, ha, b, hb', hab⟩ := Finset.one_lt_card.mp h2
    have hne : a ≠ cfg.me ∨ b ≠ cfg.me := by
      rcases Classical.em (a = cfg.me) with ha' | ha'
      · exact Or.inr fun hb'' => hab (ha'.trans hb''.symm)
      · exact Or.inl ha'
    rcases hne with hne | hne
    · obtain ⟨j, hj, hjr, hjc⟩ := mem_authorsIn.mp ha
      have hjs : j ∈ s.disk.ids := hj
      rcases below_blk h hjs with h' | h'
      · have : (s.disk.blk j).round = r := hjr
        omega
      · exact absurd (hjc ▸ h'.1) hne
    · obtain ⟨j, hj, hjr, hjc⟩ := mem_authorsIn.mp hb'
      have hjs : j ∈ s.disk.ids := hj
      rcases below_blk h hjs with h' | h'
      · have : (s.disk.blk j).round = r := hjr
        omega
      · exact absurd (hjc ▸ h'.1) hne
  · exact absurd hb (by simp)

omit [Fintype Validator] in
/-- **Building within a settle**: the blocks stay in `Below R`, those
built are, and the top stays or rises, to at most `R + 1`. -/
theorem progress_below (hq : 2 ≤ cfg.q) {R : ℕ} : ∀ (fuel : ℕ) {s : State Validator BlockId Payload},
    InK (Below cfg R) s →
    InK (Below cfg R) (Node.progress cfg fuel s).1 ∧
      (∀ e ∈ persists (Node.progress cfg fuel s).2, e ∈ Below cfg R) ∧
      ((Node.progress cfg fuel s).1.top = s.top ∨
        ((Node.progress cfg fuel s).1.top.getD 0 ≤ R + 1 ∧
          s.top.getD 0 < (Node.progress cfg fuel s).1.top.getD 0))
  | 0, _, h => by
    simp only [Node.progress]
    exact ⟨h, fun e he => by simp [persists] at he, by simp⟩
  | fuel + 1, s, h => by
    rcases hb : Node.tryBuild cfg s with _ | ⟨s₁, out⟩
    · simp only [Node.progress, hb]
      exact ⟨h, fun e he => by simp [persists] at he, by simp⟩
    · simp only [Node.progress, hb]
      obtain ⟨r, htop', hsr, hrR⟩ := below_build hq h hb
      obtain ⟨r', id, b, -, -, -, -, hbr, hbc, -, -, -, htop, -, -, hout⟩ := tryBuild_some hb
      have hrr : r' = r := by
        rw [htop'] at htop; have := Option.some.inj htop; omega
      have hbR : b.round ≤ R + 1 := by rw [hbr, hrr]; omega
      have hout' : ∀ e ∈ persists out, e ∈ Below cfg R := by
        intro e he
        rw [hout] at he
        simp only [built, persists, List.flatMap_cons, List.flatMap_nil, List.append_nil,
          List.filterMap_cons, List.filterMap_nil, List.mem_singleton] at he
        subst he
        exact Or.inr ⟨hbc, hbR⟩
      have h₁ := h.tryBuild hb hout'
      obtain ⟨h₂, hK₂, ht₂⟩ := progress_below hq fuel h₁
      have hs₁ : s₁.top.getD 0 = r + 1 := by rw [htop, hrr]; rfl
      refine ⟨h₂, fun e he => ?_, Or.inr ?_⟩
      · rw [persists_append] at he
        exact (List.mem_append.mp he).elim (hout' e) (hK₂ e)
      · rcases ht₂ with ht₂ | ⟨ht₂, ht₂'⟩
        · rw [ht₂, hs₁]; omega
        · rw [hs₁] at ht₂'; exact ⟨ht₂, by omega⟩

omit [Fintype Validator] in
/-- **Deciding** keeps the disk, the pending blocks and the top, and
raises the next undecided slot to at most the slots at the disk's
rounds. -/
theorem decideStep_bound (s : State Validator BlockId Payload) :
    let d := (Node.decideStep cfg s).1
    d.disk = s.disk ∧ d.pending = s.pending ∧ d.top = s.top ∧ s.lo ≤ d.lo ∧
      d.lo ≤ max s.lo (decidable cfg s.disk.topRound) :=
  ⟨decideStep_disk s, decideStep_pending s, decideStep_top s, decideStep_lo s,
    decideStep_lo_le s⟩

/-! ## A pass -/

omit [Fintype Validator] in
/-- **A flush** keeps fewer pending blocks, and leaves the store and the
pending blocks as they were if it keeps as many. -/
theorem flush_bound : ∀ (fuel : ℕ) (st : Store Validator BlockId Payload)
    (pend : List (BlockId × Block Validator BlockId Payload)),
    (flushOn cfg fuel st pend).2.length ≤ pend.length ∧
      ((flushOn cfg fuel st pend).2.length = pend.length →
        flushOn cfg fuel st pend = (st, pend))
  | 0, _, _ => ⟨le_rfl, fun _ => rfl⟩
  | fuel + 1, st, pend => by
    unfold flushOn
    dsimp only
    split
    · exact ⟨le_rfl, fun _ => rfl⟩
    · rename_i hE
      rw [List.partition_eq_filter_filter] at hE ⊢
      have hl := List.length_eq_length_filter_add (fun e => readyOn cfg st e) (l := pend)
      have hpos : 0 < (pend.filter fun e => readyOn cfg st e).length := by
        rw [List.isEmpty_iff] at hE
        exact List.length_pos_of_ne_nil hE
      obtain ⟨h₁, -⟩ := flush_bound fuel
        ((pend.filter fun e => readyOn cfg st e).foldl (fun s e => acceptOn cfg s e.1 e.2) st)
        (pend.filter (not ∘ fun e => readyOn cfg st e))
      simp only [Function.comp_def] at hl h₁ ⊢
      refine ⟨by omega, fun h => ?_⟩
      omega

omit [Fintype Validator] in
/-- **A flush that leaves the disk and the pending blocks leaves the
state.** -/
theorem flush_self : ∀ {fuel : ℕ} {s : State Validator BlockId Payload},
    flushOn cfg fuel s.disk s.pending = (s.disk, s.pending) → flush cfg fuel s = s
  | 0, _, _ => rfl
  | fuel + 1, s, h => by
    have hr : (fun e => ready cfg s e) = fun e => readyOn cfg s.disk e := funext (ready_eq s)
    unfold flush
    dsimp only
    rw [hr]
    split
    · rfl
    · rename_i hE
      exfalso
      have hlen := congrArg (fun p => p.2.length) h
      simp only at hlen
      unfold flushOn at hlen
      dsimp only at hlen
      rw [if_neg hE] at hlen
      have h₁ := (flush_bound (cfg := cfg) fuel
        ((s.pending.partition fun e => readyOn cfg s.disk e).1.foldl
          (fun st e => acceptOn cfg st e.1 e.2) s.disk)
        (s.pending.partition fun e => readyOn cfg s.disk e).2).1
      rw [List.partition_eq_filter_filter] at hE hlen h₁
      have hl := List.length_eq_length_filter_add (fun e => readyOn cfg s.disk e) (l := s.pending)
      have hpos : 0 < (s.pending.filter fun e => readyOn cfg s.disk e).length := by
        rw [List.isEmpty_iff] at hE
        exact List.length_pos_of_ne_nil hE
      simp only [Function.comp_def] at hl h₁ hlen
      omega

omit [Fintype Validator] in
/-- **A decision step that leaves the next undecided slot changes
nothing.** -/
theorem decideStep_eq_of_lo {s : State Validator BlockId Payload}
    (h : (Node.decideStep cfg s).1.lo = s.lo) : Node.decideStep cfg s = (s, []) := by
  unfold Node.decideStep at h ⊢
  dsimp only at h ⊢
  split at h
  · rename_i hc
    rw [release_lo] at h
    simp only [Nat.add_eq_left, List.length_eq_zero_iff] at h
    exact absurd h hc.2.2
  · rename_i hc
    rw [if_neg hc]

variable (cfg) in
/-- **A pass that stops**: it changes none of the top, the number of
pending blocks and the next undecided slot. -/
def Stops (s : State Validator BlockId Payload) : Prop :=
  (advance cfg s).1.top = s.top ∧ (advance cfg s).1.pending.length = s.pending.length ∧
    (advance cfg s).1.lo = s.lo

omit [Fintype Validator] in
theorem quiesce_stop {n : ℕ} {s : State Validator BlockId Payload} (h : Stops cfg s) :
    quiesce cfg (n + 1) s = advance cfg s := by
  rw [quiesce_succ]; exact if_pos h

omit [Fintype Validator] in
theorem quiesce_go {n : ℕ} {s : State Validator BlockId Payload} (h : ¬ Stops cfg s) :
    quiesce cfg (n + 1) s = ((quiesce cfg n (advance cfg s).1).1,
      (advance cfg s).2 ++ (quiesce cfg n (advance cfg s).1).2) := by
  rw [quiesce_succ]; exact if_neg h

variable (cfg) in
/-- **Within a settle from rounds at most `R`**: the blocks in `Below R`,
the top at most `R + 1`, the next undecided slot at most `L`. -/
def Within (R L : ℕ) (s : State Validator BlockId Payload) : Prop :=
  InK (Below cfg R) s ∧ s.top.getD 0 ≤ R + 1 ∧ s.lo ≤ L

/-- What a pass that does not stop lowers. -/
def passMeasure (B L : ℕ) (s : State Validator BlockId Payload) : ℕ :=
  s.pending.length + (B - s.top.getD 0) + (L - s.lo)

omit [Fintype Validator] in
theorem within_advance {R L : ℕ} (s : State Validator BlockId Payload) :
    Within cfg R L (Node.advance cfg s).1 ↔ Within cfg R L (Node.pass cfg s).1 := by
  simp only [Within, InK, advance_disk, advance_pending, advance_top, advance_lo]

omit [Fintype Validator] in
theorem passMeasure_advance (B L : ℕ) (s : State Validator BlockId Payload) :
    passMeasure B L (Node.advance cfg s).1 = passMeasure B L (Node.pass cfg s).1 := by
  simp only [passMeasure, advance_pending, advance_top, advance_lo]

omit [Fintype Validator] in
theorem stops_iff (s : State Validator BlockId Payload) :
    Stops cfg s ↔ (Node.pass cfg s).1.top = s.top ∧
      (Node.pass cfg s).1.pending.length = s.pending.length ∧ (Node.pass cfg s).1.lo = s.lo := by
  simp only [Stops, advance_top, advance_pending, advance_lo]

omit [Fintype Validator] in
/-- **A pass within a settle** stays within it, and lowers the measure
unless it stops. -/
theorem Within.advance (hq : 2 ≤ cfg.q) {R L : ℕ} (hL : decidable cfg (R + 1) ≤ L)
    {s : State Validator BlockId Payload} (h : Within cfg R L s) :
    Within cfg R L (Node.advance cfg s).1 ∧
      (¬ Stops cfg s → passMeasure (R + 1) L (Node.advance cfg s).1 < passMeasure (R + 1) L s) := by
  rw [within_advance, passMeasure_advance]
  obtain ⟨hp₁, hK₁, ht₁⟩ := progress_below (cfg := cfg) hq (s.disk.topRound + 2) h.1
  set r := Node.progress cfg (s.disk.topRound + 2) s with hr
  obtain ⟨hdst, hdpd, hdtop, hdlo, hdlo'⟩ := decideStep_bound (cfg := cfg) r.1
  set d := (Node.decideStep cfg r.1).1 with hd
  obtain ⟨hfl, -⟩ := flush_bound (cfg := cfg) (d.pending.length + 1) d.disk d.pending
  have hadv : (Node.pass cfg s).1 = flush cfg (d.pending.length + 1) d := rfl
  have hrpd : r.1.pending = s.pending := progress_pending (cfg := cfg) _ s
  have hrlo : r.1.lo = s.lo := (Grows.progress (cfg := cfg) _ s).2
  -- the new top
  have htop' : (Node.pass cfg s).1.top = r.1.top := by rw [hadv, flush_top]; exact hdtop
  have hrt : r.1.top.getD 0 ≤ R + 1 := by
    rcases ht₁ with ht₁ | ⟨ht₁, -⟩
    · rw [ht₁]; exact h.2.1
    · exact ht₁
  have hrtR : r.1.disk.topRound ≤ R + 1 := below_topRound hp₁
  have hdL : d.lo ≤ L := by
    have := decidable_mono (cfg := cfg) hrtR
    rw [hrlo] at hdlo'
    have := h.2.2
    omega
  have hlo' : (Node.pass cfg s).1.lo = d.lo := by rw [hadv, flush_lo]
  refine ⟨⟨?_, by rw [htop']; exact hrt, by rw [hlo']; exact hdL⟩, fun hns => ?_⟩
  · have := InK.advance (cfg := cfg) h.1 (by
      rw [advance_snd, persists_append, persists_arm, List.append_nil]
      simp only [Node.pass]
      rw [persists_append, decideStep_persist, List.append_nil]
      exact hK₁)
    rwa [InK, advance_disk, advance_pending] at this
  unfold passMeasure
  rw [htop', hlo']
  -- the slot
  have hdloR : d.lo = s.lo ∨ (s.lo < d.lo ∧ d.lo ≤ L) := by
    rw [hrlo] at hdlo
    rcases Nat.eq_or_lt_of_le hdlo with he | hlt
    · exact Or.inl he.symm
    · exact Or.inr ⟨hlt, hdL⟩
  set P := (flushOn cfg (d.pending.length + 1) d.disk d.pending).2.length with hP
  have hPle : P ≤ s.pending.length := hfl.trans (by rw [hdpd, hrpd])
  rw [stops_iff] at hns
  rw [htop', hlo'] at hns
  have hall : r.1.top = s.top → P = s.pending.length → d.lo = s.lo → False := by
    intro a b c; apply hns; rw [hadv, flush_pending]; exact ⟨a, b, c⟩
  rw [hadv, flush_pending]
  change P + _ + _ < s.pending.length + _ + _
  rcases ht₁ with ht | ⟨htR, htlt⟩
  · have hTg : r.1.top.getD 0 = s.top.getD 0 := by rw [ht]
    rw [hTg]
    rcases hdloR with hdl | ⟨hdl, hdlL⟩ <;> rcases Nat.eq_or_lt_of_le hPle with hPe | hPl
    all_goals first
      | exact absurd (hall ht hPe (by assumption)) id
      | omega
  · rcases hdloR with hdl | ⟨hdl, hdlL⟩ <;> omega

/-! ## The passes stop -/

omit [Fintype Validator] in
/-- **The passes stop by their condition**: from a state within a settle
whose measure is below the passes left, the last pass is one that stops,
from a state within the settle. -/
theorem quiesce_stops (hq : 2 ≤ cfg.q) {R L : ℕ} (hL : decidable cfg (R + 1) ≤ L) :
    ∀ (n : ℕ) (s : State Validator BlockId Payload), Within cfg R L s →
      passMeasure (R + 1) L s < n →
      ∃ y, Within cfg R L y ∧ Stops cfg y ∧ (quiesce cfg n s).1 = (Node.advance cfg y).1
  | 0, _, _, h => absurd h (Nat.not_lt_zero _)
  | n + 1, s, hw, hm => by
    by_cases hs : Stops cfg s
    · exact ⟨s, hw, hs, by rw [quiesce_stop hs]⟩
    · rw [quiesce_go hs]
      obtain ⟨hw', hlt⟩ := hw.advance hq hL
      exact quiesce_stops hq hL n _ hw' (by have := hlt hs; omega)

omit [Fintype Validator] in
/-- Building keeps a top, no lower. -/
theorem progress_top : ∀ (n : ℕ) {s : State Validator BlockId Payload} {t : ℕ},
    s.top = some t → ∃ t', t ≤ t' ∧ (Node.progress cfg n s).1.top = some t'
  | 0, _, t, h => ⟨t, le_rfl, h⟩
  | n + 1, s, t, h => by
    rcases hb : Node.tryBuild cfg s with _ | ⟨s₁, out⟩
    · simp only [Node.progress, hb]; exact ⟨t, le_rfl, h⟩
    · simp only [Node.progress, hb]
      obtain ⟨r, -, -, -, -, -, hr, -, -, -, -, -, htop, -⟩ := tryBuild_some hb
      have htr : t ≤ r := by have := hr.2.1; rw [h] at this; exact this
      obtain ⟨t', ht', ht''⟩ := progress_top n htop
      exact ⟨t', by omega, ht''⟩

omit [Fintype Validator] in
/-- **Building that leaves the top** built nothing. -/
theorem progress_none {n : ℕ} {s : State Validator BlockId Payload}
    (h : (Node.progress cfg (n + 1) s).1.top = s.top) :
    Node.tryBuild cfg s = none ∧ Node.progress cfg (n + 1) s = (s, []) := by
  rcases hb : Node.tryBuild cfg s with _ | ⟨s₁, out⟩
  · exact ⟨rfl, by simp only [Node.progress, hb]⟩
  · exfalso
    simp only [Node.progress, hb] at h
    obtain ⟨r, -, -, -, -, -, hr, -, -, -, -, -, htop, -⟩ := tryBuild_some hb
    obtain ⟨t', ht', ht''⟩ := progress_top (cfg := cfg) n htop
    obtain ⟨t, ht⟩ := Option.isSome_iff_exists.mp hr.1
    have htr : t ≤ r := by have := hr.2.1; rw [ht] at this; exact this
    rw [ht'', ht, Option.some.injEq] at h
    omega

omit [Fintype Validator] in
/-- Whether the node can build reads only its disk, memory, top, own
block, fired timers, pending blocks and whether it recovers. -/
theorem tryBuild_none_of {s s' : State Validator BlockId Payload}
    (h : Node.tryBuild cfg s = none) (hst : s'.disk = s.disk) (hm : s'.memory = s.memory)
    (ht : s'.top = s.top) (ho : s'.own = s.own) (hf : s'.fired = s.fired)
    (hrc : s'.recovering = s.recovering) (hp : s'.pending = s.pending) :
    Node.tryBuild cfg s' = none := by
  obtain ⟨st, mem, fl, mir, pd, top, own, fired, lo, dc, ar, rc⟩ := s
  obtain ⟨st', mem', fl', mir', pd', top', own', fired', lo', dc', ar', rc'⟩ := s'
  simp only at hst hm ht ho hf hrc hp
  subst hst hm ht ho hf hrc hp
  unfold Node.tryBuild Node.buildAbove Node.pendingTop at h ⊢
  cases top' with
  | none => rfl
  | some r =>
    dsimp only at h ⊢
    split_ifs at h ⊢ <;> simp_all

variable (cfg) in
/-- **A settled state**: it can build nothing, no pending block is ready,
and it decides no further slot. -/
structure Settled (s : State Validator BlockId Payload) : Prop where
  build : Node.tryBuild cfg s = none
  ready : NoReady cfg s
  decided : s.lo < decidable cfg s.disk.topRound → s.floor ≤ cfg.slots.slotRound s.lo →
    Scheme.tryDecide (S := cfg.slots) cfg.p cfg.σ (s.memory.window (cfg.slots.slotRound s.lo))
      (s.memory.windowView (cfg.slots.slotRound s.lo)) s.lo (decidable cfg s.disk.topRound - 1) =
      []

omit [Fintype Validator] in
/-- **A pass that stops leaves a settled state.** -/
theorem Stops.settled {s : State Validator BlockId Payload} (h : Stops cfg s) :
    Settled cfg (Node.advance cfg s).1 := by
  suffices hp : Settled cfg (Node.pass cfg s).1 from
    ⟨tryBuild_none_of hp.build (advance_disk s) (advance_memory s) (advance_top s)
        (advance_own s) (advance_fired s) (advance_recovering s) (advance_pending s),
      by unfold NoReady; rw [advance_pending, advance_disk]; exact hp.ready,
      by rw [advance_lo, advance_disk, advance_floor, advance_memory]; exact hp.decided⟩
  obtain ⟨htop, hpend, hlo⟩ := (stops_iff s).1 h
  have hadv : (Node.pass cfg s).1 = flush cfg ((Node.decideStep cfg
      (Node.progress cfg (s.disk.topRound + 2) s).1).1.pending.length + 1)
      (Node.decideStep cfg (Node.progress cfg (s.disk.topRound + 2) s).1).1 := rfl
  -- nothing built
  have hrt : (Node.progress cfg (s.disk.topRound + 1 + 1) s).1.top = s.top := by
    rw [← htop, hadv, flush_top]
    exact (decideStep_top _).symm
  obtain ⟨hnb, hpr⟩ := progress_none hrt
  have hpr' : Node.progress cfg (s.disk.topRound + 2) s = (s, []) := hpr
  rw [hpr'] at hadv
  -- nothing decided
  have hds : Node.decideStep cfg s = (s, []) :=
    decideStep_eq_of_lo (by rw [← flush_lo (cfg := cfg) _ (Node.decideStep cfg s).1, ← hadv, hlo])
  rw [hds] at hadv
  -- nothing flushed
  obtain ⟨-, hfl⟩ := flush_bound (cfg := cfg) (s.pending.length + 1) s.disk s.pending
  have hfe : flushOn cfg (s.pending.length + 1) s.disk s.pending = (s.disk, s.pending) :=
    hfl (by rw [← flush_pending, ← hadv, hpend])
  have hz : (Node.pass cfg s).1 = s := by rw [hadv]; exact flush_self hfe
  rw [hz]
  refine ⟨hnb, ?_, fun hlt hfl' => ?_⟩
  · have := flush_no_ready (cfg := cfg) (s.pending.length + 1) s.disk s.pending
      (Nat.lt_succ_self _)
    rw [hfe] at this
    exact this
  · by_contra hne
    have hlo' : (Node.decideStep cfg s).1.lo ≠ s.lo := by
      unfold Node.decideStep
      dsimp only
      rw [if_pos ⟨hlt, hfl', hne⟩, release_lo]
      simp only [ne_eq, Nat.add_eq_left, List.length_eq_zero_iff]
      exact hne
    rw [hds] at hlo'
    exact hlo' rfl

/-! ## A settle ends settled -/

omit [Fintype Validator] [DecidableEq Validator] in
/-- A pending block's round is at most `pendingTop`. -/
theorem le_pendingTop {s : State Validator BlockId Payload}
    {e : BlockId × Block Validator BlockId Payload} (he : e ∈ s.pending) :
    e.2.round ≤ pendingTop s := by
  unfold pendingTop
  generalize s.pending = l at he
  induction l with
  | nil => exact absurd he List.not_mem_nil
  | cons x l ih =>
    simp only [List.map_cons, List.foldr_cons]
    rcases List.mem_cons.mp he with rfl | he
    · exact le_max_left _ _
    · exact (ih he).trans (le_max_right _ _)

omit [Fintype Validator] in
/-- **A state is within the settle from it.** -/
theorem within_start (s : State Validator BlockId Payload) :
    Within cfg (max (s.top.getD 0) (max s.disk.topRound (pendingTop s)))
      (max s.lo (decidable cfg (max (s.top.getD 0) (max s.disk.topRound (pendingTop s)) + 1)))
      s := by
  refine ⟨⟨fun j hj => ?_, fun e he => ?_⟩, by omega, le_max_left _ _⟩
  · left
    have hle : (s.disk.blk j).round ≤ s.disk.topRound := by
      rw [Store.topRound_eq]; exact Finset.le_sup (f := fun i => (s.disk.blk i).round) hj
    change (s.disk.blk j).round ≤ _
    omega
  · left
    have := le_pendingTop he
    change e.2.round ≤ _
    omega

omit [Fintype Validator] in
/-- **The passes of a settle stop by their condition**, and leave a
settled state, for a quorum of two or more. -/
theorem quiesce_settled (hq : 2 ≤ cfg.q) (s : State Validator BlockId Payload) :
    Settled cfg (quiesce cfg (passes cfg s) s).1 := by
  obtain ⟨y, -, hy, he⟩ := quiesce_stops hq (le_max_right _ _) (passes cfg s) s
    (within_start s) (by
    unfold passMeasure passes
    dsimp only
    omega)
  rw [he]; exact hy.settled

omit [Fintype Validator] in
/-- **A settle leaves a settled state**, for a quorum of two or more. -/
theorem settle_settled (hq : 2 ≤ cfg.q) (s : State Validator BlockId Payload) :
    Settled cfg (Node.settle cfg s).1 :=
  quiesce_settled hq s

end Node

end LeanDag
