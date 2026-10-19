import LeanDag.Node.Model.Run
import LeanDag.Scheme.Helpers.Votes
/-!
# The filled blocks of a jump

A line runs down one round a step (`lineDown_spec`), so the blocks a jump
message denotes lie at the rounds above the anchor's up to the target's,
each by the jumping node and identified by its hash (`jumpFills_spec`).
Two stores that read alike above the anchor's round, where both hold a
block, derive the same blocks (`jumpFills_congr`). Accepting blocks in
turn keeps what each acceptance keeps (`insertAll_induct`), and holds
the accepted blocks as given (`insertAll_mem`).
-/

namespace LeanDag

namespace Node

variable {Validator BlockId Payload : Type} [DecidableEq Validator] [LinearOrder BlockId]

section Line

variable {s s' : Store Validator BlockId Payload}

theorem refBy_mem {b : Block Validator BlockId Payload} {v : Validator} {i : BlockId}
    (h : refBy s b v = some i) : i ∈ b.refs ∧ (s.blk i).creator = v :=
  Finset.mem_filter.mp (Scheme.leastOf_eq_some h).1

/-- **A line runs down one round a step**, above `lo`, to its top `j`. -/
theorem lineDown_spec (lo : ℕ) : ∀ (d : ℕ) {j : BlockId} {L : List BlockId},
    lineDown s lo d j = some L →
    lo + d < (s.blk j).round ∧ j ∈ L ∧ (∀ l ∈ L, l ∈ s.ids ∧ lo < (s.blk l).round) ∧
      L.map (fun l => (s.blk l).round) = List.range' ((s.blk j).round - d) (d + 1)
  | 0, j, L, h => by
    simp only [lineDown] at h
    split at h
    · rename_i hj
      cases h
      exact ⟨by simpa using hj.2, List.mem_singleton_self _, by simpa using hj, by simp⟩
    · cases h
  | d + 1, j, L, h => by
    simp only [lineDown] at h
    split at h
    · rename_i hj
      cases hr : refBy s (s.blk j) (s.blk j).creator with
      | none => simp [hr] at h
      | some i =>
        cases hl : lineDown s lo d i with
        | none => simp [hr, hl] at h
        | some L' =>
          simp only [hr, hl, Option.bind_some, Option.map_some, Option.some.injEq] at h
          subst h
          obtain ⟨hlt, -, hmem, hmap⟩ := lineDown_spec lo d hl
          have hp : (s.blk i).round + 1 = (s.blk j).round := s.pred j hj.1 i (refBy_mem hr).1
          refine ⟨by omega, List.mem_append_right _ (List.mem_singleton_self _), fun l hl' => ?_, ?_⟩
          · rcases List.mem_append.mp hl' with hl' | hl'
            · exact hmem l hl'
            · rw [List.mem_singleton.mp hl']; exact hj
          · rw [List.map_append, hmap, show (s.blk i).round - d = (s.blk j).round - (d + 1) by omega,
              List.range'_concat (n := d + 1)]
            simp only [List.map_cons, List.map_nil, Nat.one_mul]
            congr 2
            omega
    · cases h

/-- **Two stores reading alike above `lo` follow one line.** -/
theorem lineDown_congr (lo : ℕ)
    (hag : ∀ j ∈ s.ids, j ∈ s'.ids → atBase lo (s.blk j) = atBase lo (s'.blk j)) :
    ∀ (d : ℕ) {j : BlockId} {L L' : List BlockId},
    lineDown s lo d j = some L → lineDown s' lo d j = some L' → L = L'
  | 0, j, L, L', h, h' => by
    simp only [lineDown] at h h'
    split at h
    · split at h'
      · cases h; cases h'; rfl
      · cases h'
    · cases h
  | d + 1, j, L, L', h, h' => by
    simp only [lineDown] at h h'
    split at h
    · split at h'
      · rename_i hj hj'
        have hjr : lo < (s'.blk j).round := hj'.2
        have hb : s.blk j = s'.blk j := by
          have := hag j hj.1 hj'.1
          rwa [atBase_of_lt hj.2, atBase_of_lt hjr] at this
        have href : refBy s (s.blk j) (s.blk j).creator = refBy s' (s'.blk j) (s'.blk j).creator := by
          unfold refBy
          rw [← hb]
          congr 1
          refine Finset.filter_congr fun i hi => ?_
          have hi' : i ∈ s'.ids := s'.complete j hj'.1 i (by
            show i ∈ (s'.blk j).refs
            rw [← hb]; exact hi)
          have := congrArg Block.creator (hag i (s.complete j hj.1 i hi) hi')
          simp only [atBase_creator] at this
          rw [this]
        rw [href] at h
        cases hr : refBy s' (s'.blk j) (s'.blk j).creator with
        | none => simp [hr] at h
        | some i =>
          cases hl : lineDown s lo d i with
          | none => simp [hr, hl] at h
          | some M =>
            cases hl' : lineDown s' lo d i with
            | none => simp [hr, hl'] at h'
            | some M' =>
              simp only [hr, hl, Option.bind_some, Option.map_some, Option.some.injEq] at h
              simp only [hr, hl', Option.bind_some, Option.map_some, Option.some.injEq] at h'
              rw [← h, ← h', lineDown_congr lo hag d hl hl']
      · cases h'
    · cases h

end Line

section Fill

variable (idOf : Block Validator BlockId Payload → BlockId)

/-- **The filled blocks** lie at their line's rounds, each by `v1` and
identified by its hash. -/
theorem fillUp_spec (blk : BlockId → Block Validator BlockId Payload) (v : Validator) :
    ∀ (L : List BlockId) (prev : BlockId),
    (fillUp idOf blk v prev L).map (fun e => e.2.round) = L.map (fun l => (blk l).round) ∧
      ∀ e ∈ fillUp idOf blk v prev L, e.1 = idOf e.2 ∧ e.2.creator = v
  | [], _ => ⟨rfl, fun _ h => absurd h List.not_mem_nil⟩
  | l :: L, prev => by
    have ih := fillUp_spec blk v L
    refine ⟨by simp only [fillUp, List.map_cons, (ih _).1], fun e he => ?_⟩
    simp only [fillUp, List.mem_cons] at he
    rcases he with rfl | he
    · exact ⟨rfl, rfl⟩
    · exact (ih _).2 e he

theorem fillUp_congr {blk blk' : BlockId → Block Validator BlockId Payload} (v : Validator) :
    ∀ (prev : BlockId) (L : List BlockId), (∀ l ∈ L, blk l = blk' l) →
    fillUp idOf blk v prev L = fillUp idOf blk' v prev L
  | _, [], _ => rfl
  | prev, l :: L, h => by
    simp only [fillUp, h l List.mem_cons_self]
    rw [fillUp_congr v _ L fun x hx => h x (List.mem_cons_of_mem _ hx)]

variable {idOf} {s s' : Store Validator BlockId Payload} {v : Validator} {B1 B2 : BlockId}
variable {F F' : List (BlockId × Block Validator BlockId Payload)}

/-- **The blocks a jump message denotes**: at the rounds above the
anchor's up to the target's, in order, each by the jumping node and
identified by its hash. -/
theorem jumpFills_spec (h : jumpFills idOf s v B1 B2 = some F) :
    B1 ∈ s.ids ∧ (s.blk B1).creator = v ∧ s.base ≤ (s.blk B1).round ∧
      (s.blk B1).round < (s.blk B2).round ∧ B2 ∈ s.ids ∧
      F.map (fun e => e.2.round) =
        List.range' ((s.blk B1).round + 1) ((s.blk B2).round - (s.blk B1).round) ∧
      ∀ e ∈ F, e.1 = idOf e.2 ∧ e.2.creator = v := by
  unfold jumpFills at h
  split at h
  · rename_i hc
    cases hl : lineDown s (s.blk B1).round ((s.blk B2).round - (s.blk B1).round - 1) B2 with
    | none => simp [hl] at h
    | some L =>
      simp only [hl, Option.map_some, Option.some.injEq] at h
      subst h
      obtain ⟨-, hj, hmem, hmap⟩ := lineDown_spec _ _ hl
      obtain ⟨h1, h2⟩ := fillUp_spec idOf s.blk v L B1
      refine ⟨hc.1, hc.2.1, hc.2.2.1, hc.2.2.2, (hmem B2 hj).1, ?_, h2⟩
      rw [h1, hmap]
      congr 1 <;> omega
  · cases h

/-- **Two stores reading alike above the anchor's round derive the same
blocks**, where both hold a block. -/
theorem jumpFills_congr (h : jumpFills idOf s v B1 B2 = some F)
    (h' : jumpFills idOf s' v B1 B2 = some F')
    (hag : ∀ j ∈ s.ids, j ∈ s'.ids →
      atBase (s.blk B1).round (s.blk j) = atBase (s.blk B1).round (s'.blk j)) : F = F' := by
  obtain ⟨hB1, -, -, hlt, hB2, -⟩ := jumpFills_spec h
  obtain ⟨hB1', -, -, -, hB2', -⟩ := jumpFills_spec h'
  have hr1 : (s.blk B1).round = (s'.blk B1).round := by
    simpa using congrArg Block.round (hag B1 hB1 hB1')
  have hr2 : (s.blk B2).round = (s'.blk B2).round := by
    simpa using congrArg Block.round (hag B2 hB2 hB2')
  unfold jumpFills at h h'
  rw [if_pos (by simpa using ⟨hB1, (jumpFills_spec (by unfold jumpFills; exact h)).2.1,
    (jumpFills_spec (by unfold jumpFills; exact h)).2.2.1, hlt⟩)] at h
  rw [← hr1, ← hr2] at h'
  split at h'
  · cases hl : lineDown s (s.blk B1).round ((s.blk B2).round - (s.blk B1).round - 1) B2 with
    | none => simp [hl] at h
    | some L =>
      cases hl' : lineDown s' (s.blk B1).round ((s.blk B2).round - (s.blk B1).round - 1) B2 with
      | none => simp [hl'] at h'
      | some L' =>
        simp only [hl, Option.map_some, Option.some.injEq] at h
        simp only [hl', Option.map_some, Option.some.injEq] at h'
        have hL := lineDown_congr _ hag _ hl hl'
        subst hL
        rw [← h, ← h']
        refine fillUp_congr idOf v B1 L fun l hl'' => ?_
        obtain ⟨-, -, hm, -⟩ := lineDown_spec _ _ hl
        obtain ⟨-, -, hm', -⟩ := lineDown_spec _ _ hl'
        have := hag l (hm l hl'').1 (hm' l hl'').1
        rwa [atBase_of_lt (hm l hl'').2, atBase_of_lt (hm' l hl'').2] at this
  · cases h'

end Fill

section Insert

variable {cfg : Config Validator BlockId Payload}

/-- **What each acceptance keeps, accepting in turn keeps.** -/
theorem insertAll_induct (Q : Store Validator BlockId Payload → Prop) :
    ∀ {F : List (BlockId × Block Validator BlockId Payload)},
    (∀ st, ∀ e ∈ F, ∀ (h : e.1 ∉ st.ids ∧ st.base < e.2.round ∧ e.2.refs ⊆ st.ids ∧
        (∀ j ∈ e.2.refs, (st.blk j).round + 1 = e.2.round) ∧
        rowValid cfg.q (Function.update st.blk e.1 e.2) e.2),
      Q st → Q (st.insert e.1 e.2 h.1 h.2.1.le (fun _ => h.2.2.1) (fun _ => h.2.2.2.1))) →
    ∀ {st st' : Store Validator BlockId Payload}, insertAll cfg st F = some st' → Q st → Q st'
  | [], _, st, st', h, hq => by cases h; exact hq
  | e :: F, hs, st, st', h, hq => by
    simp only [insertAll] at h
    split at h
    · rename_i hc
      exact insertAll_induct Q (fun st x hx => hs st x (List.mem_cons_of_mem _ hx)) h
        (hs st e List.mem_cons_self hc hq)
    · cases h

theorem insertAll_base {F : List (BlockId × Block Validator BlockId Payload)}
    {st st' : Store Validator BlockId Payload} (h : insertAll cfg st F = some st') :
    st'.base = st.base :=
  insertAll_induct (cfg := cfg) (fun t => t.base = st.base) (fun _ _ _ _ h => h) h rfl

/-- **The accepted blocks are held as given.** -/
theorem insertAll_mem : ∀ {F : List (BlockId × Block Validator BlockId Payload)}
    {st st' : Store Validator BlockId Payload}, insertAll cfg st F = some st' →
    (∀ j ∈ st.ids, j ∈ st'.ids ∧ st'.map.getD j st'.junk = st.map.getD j st.junk) ∧
      ∀ e ∈ F, e.1 ∈ st'.ids ∧ st'.map.getD e.1 st'.junk = e.2
  | [], st, st', h => by cases h; exact ⟨fun j hj => ⟨hj, rfl⟩, fun _ h => absurd h List.not_mem_nil⟩
  | e :: F, st, st', h => by
    simp only [insertAll] at h
    split at h
    · rename_i hc
      obtain ⟨h1, h2⟩ := insertAll_mem h
      have hold : ∀ j ∈ st.ids, j ∈ (st.insert e.1 e.2 hc.1 hc.2.1.le (fun _ => hc.2.2.1)
          (fun _ => hc.2.2.2.1)).ids ∧
          (st.insert e.1 e.2 hc.1 hc.2.1.le (fun _ => hc.2.2.1) (fun _ => hc.2.2.2.1)).map.getD j
            st.junk = st.map.getD j st.junk := fun j hj =>
        ⟨Finset.mem_insert_of_mem hj,
          treeMap_getD_insert_ne (fun h => hc.1 (h ▸ hj))⟩
      refine ⟨fun j hj => ⟨(h1 j (hold j hj).1).1, (h1 j (hold j hj).1).2.trans (hold j hj).2⟩,
        fun x hx => ?_⟩
      rcases List.mem_cons.mp hx with rfl | hx
      · have hm : x.1 ∈ (st.insert x.1 x.2 hc.1 hc.2.1.le (fun _ => hc.2.2.1)
            (fun _ => hc.2.2.2.1)).ids := Finset.mem_insert_self _ _
        refine ⟨(h1 _ hm).1, (h1 _ hm).2.trans ?_⟩
        exact Std.TreeMap.getD_insert_self
      · exact h2 x hx
    · cases h

end Insert

end Node

end LeanDag
