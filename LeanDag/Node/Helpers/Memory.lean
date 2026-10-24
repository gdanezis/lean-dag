import LeanDag.Node.Model.Step
import LeanDag.Node.Helpers.ReadsView
/-!
# The node's disk, read alone

What the node accepts is what the disk alone would accept: a block is
ready in the state exactly when it is ready on the disk (`ready_eq`), and
accepting a block, a stream piece and the syncs' blocks change the disk
as `acceptOn` changes it read alone (`accept_disk`, `absorb_disk`,
`flushSyncs_eq`), and leave the rest of the state but the memory, the
detected authors and the syncs (`accept_rest`, `absorb_rest`). Keeping a
block inserts it on disk (`keep_disk`), and releasing the memory changes
nothing else (`release_disk`, …).
-/

namespace LeanDag

namespace Node

variable {Validator BlockId Payload : Type} [Fintype Validator] [DecidableEq Validator]
variable [LinearOrder BlockId]
variable (cfg : Config Validator BlockId Payload)

/-- **A block is ready on the store `st`**: its references are accepted,
one round below it, and it is valid at the row. -/
def readyOn (st : Store Validator BlockId Payload) (e : BlockId × Block Validator BlockId Payload) :
    Bool :=
  decide (st.Checks cfg.q e.1 e.2)

/-- **Accept a block on the store `st`**: it is kept if it is new and
ready. -/
def acceptOn (st : Store Validator BlockId Payload) (id : BlockId)
    (b : Block Validator BlockId Payload) : Store Validator BlockId Payload :=
  if h : id ∉ st.ids ∧ st.Checks cfg.q id b then st.insert id b h.1 h.2.1 h.2.2.1 else st

variable {cfg}

omit [Fintype Validator] in
theorem ready_eq (s : State Validator BlockId Payload)
    (e : BlockId × Block Validator BlockId Payload) : ready cfg s e = readyOn cfg s.disk e := by
  unfold ready readyOn
  exact decide_eq_decide.mpr s.mirrors.checks_pick

section Keep

variable {s : State Validator BlockId Payload} {id : BlockId} {b : Block Validator BlockId Payload}
  {hnew : id ∉ s.disk.ids} {hrefs : b.refs ⊆ s.disk.ids}
  {hpred : ∀ j ∈ b.refs, (s.disk.blk j).round + 1 = b.round}

omit [Fintype Validator] [DecidableEq Validator] in
@[simp] theorem keep_disk :
    (keep s id b hnew hrefs hpred).disk = s.disk.insert id b hnew hrefs hpred := rfl

end Keep

section Accept

variable (s : State Validator BlockId Payload) (id : BlockId) (b : Block Validator BlockId Payload)

omit [Fintype Validator] in
/-- **Accepting a block changes the disk as accepting on the disk alone.** -/
theorem accept_disk : (accept cfg s id b).disk = acceptOn cfg s.disk id b := by
  unfold accept acceptOn
  by_cases h : id ∉ s.disk.ids ∧ s.disk.Checks cfg.q id b
  · rw [dif_pos (show id ∉ s.disk.ids ∧ (Store.pick s.memory s.disk s.floor b.round).Checks
      cfg.q id b from ⟨h.1, s.mirrors.checks_pick.mpr h.2⟩), dif_pos h]
    split <;> rfl
  · rw [dif_neg (fun h' => h ⟨h'.1, s.mirrors.checks_pick.mp h'.2⟩), dif_neg h]

omit [Fintype Validator] in
/-- **Accepting a block changes only the disk, the memory and the
detected authors**, which only grow. -/
theorem accept_rest :
    (accept cfg s id b).floor = s.floor ∧ (accept cfg s id b).syncs = s.syncs ∧
    (accept cfg s id b).top = s.top ∧ (accept cfg s id b).own = s.own ∧
    (accept cfg s id b).fired = s.fired ∧ (accept cfg s id b).lo = s.lo ∧
    (accept cfg s id b).decided = s.decided ∧ (accept cfg s id b).armed = s.armed ∧
    (accept cfg s id b).recovering = s.recovering ∧
    s.detected ⊆ (accept cfg s id b).detected := by
  unfold accept
  split
  · split
    · exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, Finset.subset_insert _ _⟩
    · exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, subset_rfl⟩
  · exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, subset_rfl⟩

end Accept

omit [Fintype Validator] in
theorem foldl_accept (l : List (BlockId × Block Validator BlockId Payload)) :
    ∀ s : State Validator BlockId Payload,
      (l.foldl (fun s e => accept cfg s e.1 e.2) s).disk =
        l.foldl (fun st e => acceptOn cfg st e.1 e.2) s.disk ∧
      (l.foldl (fun s e => accept cfg s e.1 e.2) s).floor = s.floor ∧
      (l.foldl (fun s e => accept cfg s e.1 e.2) s).syncs = s.syncs ∧
      (l.foldl (fun s e => accept cfg s e.1 e.2) s).top = s.top ∧
      (l.foldl (fun s e => accept cfg s e.1 e.2) s).own = s.own ∧
      (l.foldl (fun s e => accept cfg s e.1 e.2) s).fired = s.fired ∧
      (l.foldl (fun s e => accept cfg s e.1 e.2) s).lo = s.lo ∧
      (l.foldl (fun s e => accept cfg s e.1 e.2) s).decided = s.decided ∧
      (l.foldl (fun s e => accept cfg s e.1 e.2) s).armed = s.armed ∧
      (l.foldl (fun s e => accept cfg s e.1 e.2) s).recovering = s.recovering ∧
      s.detected ⊆ (l.foldl (fun s e => accept cfg s e.1 e.2) s).detected := by
  induction l with
  | nil => intro s; exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, subset_rfl⟩
  | cons e l ih =>
    intro s
    obtain ⟨h₁, h₂, h₃, h₄, h₅, h₆, h₇, h₈, h₉, h₁₀, h₁₁⟩ := ih (accept cfg s e.1 e.2)
    obtain ⟨a₂, a₃, a₄, a₅, a₆, a₇, a₈, a₉, a₁₀, a₁₁⟩ := accept_rest (cfg := cfg) s e.1 e.2
    simp only [List.foldl_cons]
    exact ⟨h₁.trans (by rw [accept_disk]), h₂.trans a₂, h₃.trans a₃, h₄.trans a₄, h₅.trans a₅,
      h₆.trans a₆, h₇.trans a₇, h₈.trans a₈, h₉.trans a₉, h₁₀.trans a₁₀, a₁₁.trans h₁₁⟩

section Absorb

variable (s : State Validator BlockId Payload)
variable (L : List (BlockId × Block Validator BlockId Payload))

omit [Fintype Validator] in
/-- **Taking a stream piece in changes the disk as accepting its blocks on
the disk alone.** -/
@[simp] theorem absorb_disk :
    (absorb cfg s L).disk = L.foldl (fun st e => acceptOn cfg st e.1 e.2) s.disk :=
  (foldl_accept L s).1

omit [Fintype Validator] in
/-- **Taking a stream piece in changes only the disk, the memory and the
detected authors.** -/
theorem absorb_rest :
    (absorb cfg s L).floor = s.floor ∧ (absorb cfg s L).syncs = s.syncs ∧
    (absorb cfg s L).top = s.top ∧ (absorb cfg s L).own = s.own ∧
    (absorb cfg s L).fired = s.fired ∧ (absorb cfg s L).lo = s.lo ∧
    (absorb cfg s L).decided = s.decided ∧ (absorb cfg s L).armed = s.armed ∧
    (absorb cfg s L).recovering = s.recovering ∧ s.detected ⊆ (absorb cfg s L).detected :=
  (foldl_accept L s).2

omit [Fintype Validator] in
/-- **Dropping the syncs done changes only the syncs, to a part of them.** -/
theorem tidy_eq :
    (tidy s).disk = s.disk ∧ (tidy s).floor = s.floor ∧ (tidy s).top = s.top ∧
    (tidy s).own = s.own ∧ (tidy s).fired = s.fired ∧ (tidy s).lo = s.lo ∧
    (tidy s).decided = s.decided ∧ (tidy s).armed = s.armed ∧
    (tidy s).recovering = s.recovering ∧ (tidy s).detected = s.detected ∧
    (tidy s).syncs ⊆ s.syncs :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, List.filter_subset_self _⟩

omit [Fintype Validator] in
/-- **Accepting the syncs' blocks changes the disk as accepting some of
them on the disk alone, and only the disk, the memory, the detected
authors and the syncs, to a part of them.** -/
theorem flushSyncs_eq : ∀ (fuel : ℕ) (s : State Validator BlockId Payload),
    (∃ L : List (BlockId × Block Validator BlockId Payload), (∀ e ∈ L, e ∈ s.syncs.map (·.2.1)) ∧
      (flushSyncs cfg fuel s).disk = L.foldl (fun st e => acceptOn cfg st e.1 e.2) s.disk) ∧
    (flushSyncs cfg fuel s).floor = s.floor ∧ (flushSyncs cfg fuel s).syncs ⊆ s.syncs ∧
    (flushSyncs cfg fuel s).top = s.top ∧ (flushSyncs cfg fuel s).own = s.own ∧
    (flushSyncs cfg fuel s).fired = s.fired ∧ (flushSyncs cfg fuel s).lo = s.lo ∧
    (flushSyncs cfg fuel s).decided = s.decided ∧ (flushSyncs cfg fuel s).armed = s.armed ∧
    (flushSyncs cfg fuel s).recovering = s.recovering ∧
    s.detected ⊆ (flushSyncs cfg fuel s).detected
  | 0, s => ⟨⟨[], fun _ h => absurd h List.not_mem_nil, rfl⟩, rfl, List.Subset.refl _, rfl, rfl,
      rfl, rfl, rfl, rfl, rfl, subset_rfl⟩
  | fuel + 1, s => by
    unfold flushSyncs
    dsimp only
    split
    · exact ⟨⟨[], fun _ h => absurd h List.not_mem_nil, rfl⟩, rfl, List.Subset.refl _, rfl, rfl,
        rfl, rfl, rfl, rfl, rfl, subset_rfl⟩
    · set l := ((s.syncs.partition fun e => ready cfg s e.2.1).1.map (·.2.1))
      have hl : ∀ e ∈ l, e ∈ s.syncs.map (·.2.1) := by
        intro e he
        obtain ⟨x, hx, rfl⟩ := List.mem_map.mp he
        rw [List.partition_eq_filter_filter] at hx
        exact List.mem_map_of_mem (List.mem_filter.mp hx).1
      obtain ⟨⟨L, hL, hd⟩, h₂, h₃, h₄, h₅, h₆, h₇, h₈, h₉, h₁₀, h₁₁⟩ :=
        flushSyncs_eq fuel (tidy (absorb cfg s l))
      obtain ⟨a₂, a₃, a₄, a₅, a₆, a₇, a₈, a₉, a₁₀, a₁₁⟩ := absorb_rest (cfg := cfg) s l
      have ht := tidy_eq (absorb cfg s l)
      refine ⟨⟨l ++ L, fun e he => ?_, ?_⟩, h₂.trans a₂, fun x hx => ?_, h₄.trans a₄,
        h₅.trans a₅, h₆.trans a₆, h₇.trans a₇, h₈.trans a₈, h₉.trans a₉, h₁₀.trans a₁₀,
        a₁₁.trans h₁₁⟩
      · rcases List.mem_append.mp he with he | he
        · exact hl e he
        · obtain ⟨x, hx, rfl⟩ := List.mem_map.mp (hL e he)
          have := ht.2.2.2.2.2.2.2.2.2.2 hx
          rw [a₃] at this
          exact List.mem_map_of_mem this
      · rw [hd, List.foldl_append, ht.1, absorb_disk]
      · have := ht.2.2.2.2.2.2.2.2.2.2 (h₃ hx)
        rwa [a₃] at this

section FlushSyncs

variable (fuel : ℕ) (s : State Validator BlockId Payload)

omit [Fintype Validator] in
@[simp] theorem flushSyncs_floor : (flushSyncs cfg fuel s).floor = s.floor :=
  (flushSyncs_eq fuel s).2.1
omit [Fintype Validator] in
@[simp] theorem flushSyncs_top : (flushSyncs cfg fuel s).top = s.top :=
  (flushSyncs_eq fuel s).2.2.2.1
omit [Fintype Validator] in
@[simp] theorem flushSyncs_own : (flushSyncs cfg fuel s).own = s.own :=
  (flushSyncs_eq fuel s).2.2.2.2.1
omit [Fintype Validator] in
@[simp] theorem flushSyncs_fired : (flushSyncs cfg fuel s).fired = s.fired :=
  (flushSyncs_eq fuel s).2.2.2.2.2.1
omit [Fintype Validator] in
@[simp] theorem flushSyncs_lo : (flushSyncs cfg fuel s).lo = s.lo :=
  (flushSyncs_eq fuel s).2.2.2.2.2.2.1
omit [Fintype Validator] in
@[simp] theorem flushSyncs_decided : (flushSyncs cfg fuel s).decided = s.decided :=
  (flushSyncs_eq fuel s).2.2.2.2.2.2.2.1
omit [Fintype Validator] in
@[simp] theorem flushSyncs_armed : (flushSyncs cfg fuel s).armed = s.armed :=
  (flushSyncs_eq fuel s).2.2.2.2.2.2.2.2.1
omit [Fintype Validator] in
@[simp] theorem flushSyncs_recovering : (flushSyncs cfg fuel s).recovering = s.recovering :=
  (flushSyncs_eq fuel s).2.2.2.2.2.2.2.2.2.1

end FlushSyncs

end Absorb

section Release

variable (s : State Validator BlockId Payload)

omit [Fintype Validator] in
/-- **Releasing the memory changes nothing else.** -/
theorem release_eq : (release cfg s).disk = s.disk ∧ (release cfg s).syncs = s.syncs ∧
    (release cfg s).top = s.top ∧ (release cfg s).own = s.own ∧
    (release cfg s).fired = s.fired ∧ (release cfg s).lo = s.lo ∧
    (release cfg s).decided = s.decided ∧ (release cfg s).armed = s.armed ∧
    (release cfg s).detected = s.detected := by
  unfold release
  split <;> exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

omit [Fintype Validator] in
@[simp] theorem release_disk : (release cfg s).disk = s.disk := (release_eq s).1
omit [Fintype Validator] in
@[simp] theorem release_syncs : (release cfg s).syncs = s.syncs := (release_eq s).2.1
omit [Fintype Validator] in
@[simp] theorem release_top : (release cfg s).top = s.top := (release_eq s).2.2.1
omit [Fintype Validator] in
@[simp] theorem release_own : (release cfg s).own = s.own := (release_eq s).2.2.2.1
omit [Fintype Validator] in
@[simp] theorem release_fired : (release cfg s).fired = s.fired := (release_eq s).2.2.2.2.1
omit [Fintype Validator] in
@[simp] theorem release_lo : (release cfg s).lo = s.lo := (release_eq s).2.2.2.2.2.1
omit [Fintype Validator] in
@[simp] theorem release_decided : (release cfg s).decided = s.decided :=
  (release_eq s).2.2.2.2.2.2.1
omit [Fintype Validator] in
@[simp] theorem release_armed : (release cfg s).armed = s.armed := (release_eq s).2.2.2.2.2.2.2.1
omit [Fintype Validator] in
@[simp] theorem release_detected : (release cfg s).detected = s.detected :=
  (release_eq s).2.2.2.2.2.2.2.2
omit [Fintype Validator] in
@[simp] theorem release_recovering : (release cfg s).recovering = s.recovering := by
  unfold release; split <;> rfl

omit [Fintype Validator] in
theorem release_floor : (release cfg s).floor = max s.floor (floorOf cfg s) := by
  unfold release
  split
  · rename_i h; exact (max_eq_right h.le).symm
  · rename_i h; exact (max_eq_left (not_lt.mp h)).symm

end Release

omit [Fintype Validator] in
/-- **At the bounded vote, the memory and the disk agree from the floor
up.** -/
theorem Store.Mirrors.viewsAbove {m d : Store Validator BlockId Payload} {F : ℕ}
    (h : m.Mirrors d F) : ViewsAbove F boundedSel boundedSel m.view d.view :=
  ViewsAbove.of_boundedSel (fun i hi _ => h.sub hi)
    (fun i hi hr => by
      have hm := h.mem_of hi hr
      exact ⟨hm, by change F ≤ (m.blk i).round; rw [h.round hm]; exact hr⟩)
    (fun i hi _ => (h.round hi).symm) (fun i hi _ => (h.creator hi).symm)
    (fun i hi hr => by
      change F < (m.blk i).round at hr
      rw [h.round hi] at hr
      exact (h.refs (h.sub hi) hr).symm)

omit [Fintype Validator] in
/-- **The decisions on the memory's window are those on the disk**, at the
bounded vote, from a slot whose round the memory holds. -/
theorem tryDecide_memory (hσ : cfg.σ = boundedSel) (hw : 2 ≤ cfg.p.waveLength)
    (s : State Validator BlockId Payload) {lo : ℕ} (hlo : s.floor ≤ cfg.slots.slotRound lo)
    (N : ℕ) :
    Scheme.tryDecide (S := cfg.slots) cfg.p cfg.σ (s.memory.window (cfg.slots.slotRound lo))
        (s.memory.windowView (cfg.slots.slotRound lo)) lo N =
      Scheme.tryDecide (S := cfg.slots) cfg.p boundedSel s.disk.toRecord s.disk.view lo N := by
  rw [tryDecide_window cfg hσ hw, hσ]
  exact s.mirrors.viewsAbove.tryDecide_eq (S := cfg.slots) cfg.p hw N hlo

/-! ## The build reads alike in memory and on disk -/

omit [DecidableEq Validator] [Fintype Validator] [LinearOrder BlockId] in
theorem List.all_congr_mem {α : Type} {l : List α} {f g : α → Bool}
    (h : ∀ x ∈ l, f x = g x) : l.all f = l.all g := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    rw [List.all_cons, List.all_cons, h a List.mem_cons_self,
      ih fun x hx => h x (List.mem_cons_of_mem _ hx)]

omit [Fintype Validator] in
/-- A slot proposed at round `ρ` has `ρ` for its slot round. -/
theorem slotRound_of_mem_slotsAt {ρ k : ℕ} (hk : k ∈ cfg.slotsAt ρ) :
    cfg.slots.slotRound k = ρ := by
  unfold Config.slotsAt at hk
  split at hk
  · rename_i hρ
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hk
    rw [List.mem_range] at hi
    change cfg.per * ((cfg.m * (ρ / cfg.per) + i) / cfg.m) = ρ
    rw [Nat.mul_add_div cfg.m_pos, Nat.div_eq_of_lt hi, Nat.add_zero]
    exact Nat.mul_div_cancel' (Nat.dvd_of_mod_eq_zero hρ)
  · exact absurd hk List.not_mem_nil

namespace Store.Mirrors

variable {m d : Store Validator BlockId Payload} {F : ℕ} (h : m.Mirrors d F)
include h

omit [Fintype Validator] in
theorem mem_of_atRound {r : ℕ} (hr : F ≤ r) {i : BlockId} (hi : i ∈ d.atRound r) : i ∈ m.ids :=
  h.mem_of (Store.mem_atRound.mp hi).1 (by rw [(Store.mem_atRound.mp hi).2]; exact hr)

omit [Fintype Validator] in
theorem leaderBlocks_eq [S : Slots Validator] {k : ℕ} (hk : F ≤ S.slotRound k) :
    m.leaderBlocks k = d.leaderBlocks k := by
  unfold Store.leaderBlocks
  rw [h.atRound_eq hk]
  exact Finset.filter_congr fun b hb => by rw [h.creator (h.mem_of_atRound hk hb)]

omit [Fintype Validator] in
theorem refsFor_eq {r : ℕ} (hr : F ≤ r) (o : Option BlockId) :
    refsFor cfg m r o = refsFor cfg d r o := by
  unfold refsFor
  dsimp only
  rw [h.atRound_eq hr, h.creatorsOf_eq fun i hi => h.mem_of_atRound hr hi]
  refine Finset.biUnion_congr rfl fun a _ => ?_
  split
  · rfl
  · rw [Finset.filter_congr fun i hi => by rw [h.creator (h.mem_of_atRound hr hi)]]

omit [Fintype Validator] in
theorem lent_eq {c : BlockId} (hc : c ∈ d.ids) (hcr : F < (d.blk c).round) (o : Option BlockId) :
    lent cfg m c o = lent cfg d c o := by
  unfold lent
  rw [h.refs hc hcr]
  congr 1
  refine Finset.filter_congr fun j hj => ?_
  have := d.pred c hc j hj
  change (d.blk j).round + 1 = (d.blk c).round at this
  rw [h.creator (h.mem_of (d.complete c hc j hj) (by omega))]

omit [Fintype Validator] in
theorem buildable_eq {r : ℕ} (hr : F ≤ r) (R : Finset BlockId) :
    buildable cfg m r R = buildable cfg d r R := by
  unfold buildable
  exact decide_eq_decide.mpr (h.checks_iff (by simp only; omega))

omit [Fintype Validator] in
theorem reachReady_eq {r : ℕ} (hF : F ≤ r - cfg.p.voteOffset) {R : Finset BlockId}
    (hR : ∀ c ∈ R, c ∈ d.ids ∧ (d.blk c).round = r) :
    reachReady cfg m R r = reachReady cfg d R r := by
  letI := cfg.slots
  unfold reachReady
  refine List.all_congr_mem fun n hn => ?_
  rw [List.mem_range] at hn
  split
  · rename_i hnr
    refine List.all_congr_mem fun k hk => ?_
    have hkr := slotRound_of_mem_slotsAt (cfg := cfg) hk
    rw [h.leaderBlocks_eq (by rw [hkr]; omega)]
    refine decide_eq_decide.mpr (exists_congr fun L => and_congr_right fun _ =>
      exists_congr fun c => and_congr_right fun hc => ?_)
    rw [← historyUptoFrom_above (U := d.toRecord) d.view
      (fun i hi hir => h.refs hi hir) n (hR c hc).1 (by
        change F + n ≤ (d.blk c).round; rw [(hR c hc).2]; omega)]
    rfl
  · rfl

omit [Fintype Validator] in
theorem certReady_eq (hσ : cfg.σ = boundedSel) {r : ℕ} (hF : F ≤ r - cfg.p.voteOffset)
    {R : Finset BlockId} (hR : ∀ c ∈ R, c ∈ d.ids ∧ (d.blk c).round = r) :
    certReady cfg m R r = certReady cfg d R r := by
  letI := cfg.slots
  unfold certReady
  split
  · rfl
  · split
    · rename_i _ hvo
      refine List.all_congr_mem fun k hk => ?_
      have hkr := slotRound_of_mem_slotsAt (cfg := cfg) hk
      have hkF : F ≤ cfg.slots.slotRound k := by rw [hkr]; omega
      rw [h.leaderBlocks_eq hkF]
      refine decide_eq_decide.mpr (exists_congr fun L => and_congr_right fun hL => ?_)
      have hLd := (Finset.mem_filter.mp hL).1
      have hLm : L ∈ m.ids := h.mem_of_atRound hkF hLd
      have hRm : ∀ c ∈ R, c ∈ m.ids := fun c hc =>
        h.mem_of (hR c hc).1 (by rw [(hR c hc).2]; omega)
      have hf : (R.filter fun b => cfg.σ.Votes m.toRecord b L) =
          R.filter fun b => cfg.σ.Votes d.toRecord b L := by
        refine Finset.filter_congr fun b hb => ?_
        rw [hσ]
        exact h.viewsAbove.votes_iff (hRm b hb) (by
            change F ≤ (m.blk b).round; rw [h.round (hRm b hb), (hR b hb).2]; omega) hLm
          (by change F ≤ (m.blk L).round; rw [h.round hLm, (Store.mem_atRound.mp hLd).2]; exact hkF)
      rw [hf, h.creatorsOf_eq fun c hc => hRm c (Finset.mem_filter.mp hc).1]
    · rfl

omit [Fintype Validator] in
theorem behind_iff {r : ℕ} (hr : F ≤ r + 1) : behind cfg m r ↔ behind cfg d r := by
  unfold behind
  rw [h.authorsAt_eq hr]

end Store.Mirrors

omit [DecidableEq Validator] [Fintype Validator] [LinearOrder BlockId] in
theorem List.find?_congr_mem {α : Type} {l : List α} {p q : α → Bool}
    (h : ∀ x ∈ l, p x = q x) : l.find? p = l.find? q := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    rw [List.find?_cons, List.find?_cons, h a List.mem_cons_self,
      ih fun x hx => h x (List.mem_cons_of_mem _ hx)]

omit [Fintype Validator] in
/-- A reference `refsFor` picks is a block of the round, or the node's own. -/
theorem mem_refsFor_of {st : Store Validator BlockId Payload} {r : ℕ} {o : Option BlockId}
    {x : BlockId} (hx : x ∈ refsFor cfg st r o) : x ∈ st.atRound r ∨ o = some x := by
  unfold refsFor at hx
  obtain ⟨a, -, hx⟩ := Finset.mem_biUnion.mp hx
  split at hx
  · exact Or.inr (Option.mem_toFinset.mp hx)
  · exact Or.inl (Finset.mem_filter.mp (mem_of_leastOf (Option.mem_toFinset.mp hx))).1

omit [Fintype Validator] in
/-- A reference `lent` lends is a reference of the block, or the node's own. -/
theorem mem_lent_of {st : Store Validator BlockId Payload} {c : BlockId} {o : Option BlockId}
    {x : BlockId} (hx : x ∈ lent cfg st c o) : x ∈ (st.blk c).refs ∨ o = some x := by
  unfold lent at hx
  rcases Finset.mem_union.mp hx with hx | hx
  · exact Or.inl (Finset.mem_filter.mp hx).1
  · exact Or.inr (Option.mem_toFinset.mp hx)

omit [Fintype Validator] in
/-- **The references the node builds on are those it would pick on disk**,
at the bounded vote, with the memory from `voteOffset` below the round up
and its own block at the round. -/
theorem Store.Mirrors.refsAt_eq {m d : Store Validator BlockId Payload} {F : ℕ}
    (h : m.Mirrors d F) (hσ : cfg.σ = boundedSel) {r : ℕ} (hF : F ≤ r - cfg.p.voteOffset)
    {o : Option BlockId} (ho : ∀ j, o = some j → j ∈ d.ids ∧ (d.blk j).round = r) :
    refsAt cfg m r o = refsAt cfg d r o := by
  have hr : F ≤ r := le_trans hF (Nat.sub_le _ _)
  have hrd : ∀ R : Finset BlockId, (∀ c ∈ R, c ∈ d.ids ∧ (d.blk c).round = r) →
      (reachReady cfg m R r && certReady cfg m R r) =
        (reachReady cfg d R r && certReady cfg d R r) := fun R hR => by
    rw [h.reachReady_eq hF hR, h.certReady_eq hσ hF hR]
  have hown : ∀ c ∈ refsFor cfg d r o, c ∈ d.ids ∧ (d.blk c).round = r := fun c hc => by
    rcases mem_refsFor_of hc with hc | hc
    · exact Store.mem_atRound.mp hc
    · exact ho c hc
  have hlent : ∀ c ∈ d.atRound (r + 1), ∀ x ∈ lent cfg d c o, x ∈ d.ids ∧ (d.blk x).round = r :=
    fun c hc x hx => by
      obtain ⟨hcd, hcr⟩ := Store.mem_atRound.mp hc
      rcases mem_lent_of hx with hx | hx
      · have := d.pred c hcd x hx
        change (d.blk x).round + 1 = (d.blk c).round at this
        exact ⟨d.complete c hcd x hx, by omega⟩
      · exact ho x hx
  have hmem : ∀ c ∈ ((d.atRound (r + 1)).sort (· ≤ ·)), c ∈ d.atRound (r + 1) :=
    fun c hc => (Finset.mem_sort _).mp hc
  have hlist : ((((m.atRound (r + 1)).sort (· ≤ ·)).filter fun c =>
        decide ((m.blk c).creator ≠ cfg.me)).map (lent cfg m · o)).find?
          (fun R => reachReady cfg m R r && certReady cfg m R r && buildable cfg m r R) =
      ((((d.atRound (r + 1)).sort (· ≤ ·)).filter fun c =>
        decide ((d.blk c).creator ≠ cfg.me)).map (lent cfg d · o)).find?
          (fun R => reachReady cfg d R r && certReady cfg d R r && buildable cfg d r R) := by
    rw [h.atRound_eq (by omega : F ≤ r + 1)]
    rw [List.filter_congr fun c hc => by
      rw [h.creator (h.mem_of_atRound (by omega : F ≤ r + 1) (hmem c hc))]]
    rw [List.map_congr_left fun c hc => by
      have hc' := Store.mem_atRound.mp (hmem c (List.mem_of_mem_filter hc))
      exact h.lent_eq hc'.1 (by rw [hc'.2]; omega) o]
    refine List.find?_congr_mem fun R hR => ?_
    obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hR
    rw [hrd _ (hlent c (hmem c (List.mem_of_mem_filter hc))), h.buildable_eq hr]
  have hc := hrd _ hown
  unfold refsAt
  dsimp only
  rw [h.refsFor_eq hr, hlist]
  by_cases hd' :
      (reachReady cfg d (refsFor cfg d r o) r && certReady cfg d (refsFor cfg d r o) r) = true
  · rw [if_pos (hc.trans hd'), if_pos hd']
  · rw [if_neg (fun h' => hd' (hc.symm.trans h')), if_neg hd']

omit [Fintype Validator] in
/-- A reference `refsAt` picks is a block of the round, or the node's own. -/
theorem mem_refsAt_of {st : Store Validator BlockId Payload} {r : ℕ} {o : Option BlockId}
    {x : BlockId} (hx : x ∈ refsAt cfg st r o) : x ∈ st.atRound r ∨ o = some x := by
  unfold refsAt at hx
  dsimp only at hx
  split at hx
  · exact mem_refsFor_of hx
  · rcases hf : List.find? _ _ with _ | R
    · rw [hf] at hx; exact mem_refsFor_of hx
    · rw [hf] at hx
      obtain ⟨c, hc, rfl⟩ := List.mem_map.mp (List.mem_of_find?_eq_some hf)
      have hc' := (Finset.mem_sort _).mp (List.mem_of_mem_filter hc)
      obtain ⟨hcd, hcr⟩ := Store.mem_atRound.mp hc'
      rcases mem_lent_of hx with hx | hx
      · have := st.pred c hcd x hx
        change (st.blk x).round + 1 = (st.blk c).round at this
        exact Or.inl (Store.mem_atRound.mpr ⟨st.complete c hcd x hx, by omega⟩)
      · exact Or.inr hx

omit [Fintype Validator] in
/-- **The build reads alike in memory and on disk**, at the bounded vote,
with the memory from `voteOffset` below the round up and the node's own
block at the round. -/
theorem Store.Mirrors.build_reads {m d : Store Validator BlockId Payload} {F : ℕ}
    (h : m.Mirrors d F) (hσ : cfg.σ = boundedSel) {r : ℕ} (hF : F ≤ r - cfg.p.voteOffset)
    {o : Option BlockId} (ho : ∀ j, o = some j → j ∈ d.ids ∧ (d.blk j).round = r) :
    refsAt cfg m r o = refsAt cfg d r o ∧ refsFor cfg m r o = refsFor cfg d r o ∧
      (behind cfg m r ↔ behind cfg d r) ∧
      reachReady cfg m (refsAt cfg d r o) r = reachReady cfg d (refsAt cfg d r o) r ∧
      certReady cfg m (refsAt cfg d r o) r = certReady cfg d (refsAt cfg d r o) r := by
  have hr : F ≤ r := le_trans hF (Nat.sub_le _ _)
  have hR : ∀ c ∈ refsAt cfg d r o, c ∈ d.ids ∧ (d.blk c).round = r := fun c hc => by
    rcases mem_refsAt_of hc with hc | hc
    · exact Store.mem_atRound.mp hc
    · exact ho c hc
  exact ⟨h.refsAt_eq hσ hF ho, h.refsFor_eq hr o, h.behind_iff (by omega),
    h.reachReady_eq hF hR, h.certReady_eq hσ hF hR⟩

end Node

end LeanDag
