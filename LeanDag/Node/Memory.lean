import LeanDag.Node.Store
/-!
# An honest node — its memory

`docs/validator.md` §3.1. The node keeps every block it accepts on disk,
and in memory the blocks from a round `F` up, those at `F` without
references: the window of the disk at `F` (`Store.Mirrors`). It computes
on the memory and answers requests from the disk.

`Store.put` adds to the memory a block accepted on disk, and
`Store.above` releases the memory below a higher round; both keep the
memory the disk's window (`Mirrors.put`, `Mirrors.above`). A block's
references are accepted, one round below it, and it is valid at the row
in memory exactly when on disk, if its round is above `F`
(`Mirrors.checks_iff`), and in memory only if on disk
(`Mirrors.checks_disk`); `ready` checks a block on the memory
above `F` and on the disk otherwise (`pick`, `Mirrors.ready_pick`).
-/

namespace LeanDag

namespace Node

variable {Validator BlockId Payload : Type} [DecidableEq Validator] [LinearOrder BlockId]

namespace Store

variable (m d : Store Validator BlockId Payload) (F : ℕ)

/-- **The memory `m` holds the disk `d`'s blocks from round `F` up**,
those at `F` without references. -/
structure Mirrors : Prop where
  mem : ∀ i, i ∈ m.ids ↔ i ∈ d.ids ∧ F ≤ (d.blk i).round
  blk : ∀ i ∈ m.ids, m.blk i = d.windowBlk F i

variable {m d F}

omit [DecidableEq Validator] in
theorem Mirrors.empty {j j' : Block Validator BlockId Payload} :
    (Store.empty j).Mirrors (Store.empty j') F where
  mem i := by simp [Store.empty]
  blk i hi := absurd hi (Finset.notMem_empty i)

namespace Mirrors

variable (h : m.Mirrors d F)
include h

omit [DecidableEq Validator] in
theorem sub {i : BlockId} (hi : i ∈ m.ids) : i ∈ d.ids := ((h.mem i).mp hi).1

omit [DecidableEq Validator] in
theorem mem_of {i : BlockId} (hi : i ∈ d.ids) (hr : F ≤ (d.blk i).round) : i ∈ m.ids :=
  (h.mem i).mpr ⟨hi, hr⟩

omit [DecidableEq Validator] in
theorem notMem {i : BlockId} (hi : i ∉ d.ids) : i ∉ m.ids := fun h' => hi (h.sub h')

omit [DecidableEq Validator] in
theorem round {i : BlockId} (hi : i ∈ m.ids) : (m.blk i).round = (d.blk i).round := by
  rw [h.blk i hi, d.windowBlk_round]

omit [DecidableEq Validator] in
theorem creator {i : BlockId} (hi : i ∈ m.ids) : (m.blk i).creator = (d.blk i).creator := by
  rw [h.blk i hi]
  unfold windowBlk
  dsimp only
  split <;> rfl

omit [DecidableEq Validator] in
theorem refs {i : BlockId} (hi : i ∈ d.ids) (hr : F < (d.blk i).round) :
    (m.blk i).refs = (d.blk i).refs := by
  rw [h.blk i (h.mem_of hi hr.le)]
  unfold windowBlk
  dsimp only
  rw [if_neg (by omega)]

omit [DecidableEq Validator] in
/-- The references of a block above `F`, accepted on disk one round below
it, are in memory. -/
theorem refs_mem {b : Block Validator BlockId Payload} (hrefs : b.refs ⊆ d.ids)
    (hpred : ∀ j ∈ b.refs, (d.blk j).round + 1 = b.round) (hF : F < b.round) :
    b.refs ⊆ m.ids := fun j hj => h.mem_of (hrefs hj) (by have := hpred j hj; omega)

omit [DecidableEq Validator] in
theorem pred_mem {b : Block Validator BlockId Payload} (hrefs : b.refs ⊆ d.ids)
    (hpred : ∀ j ∈ b.refs, (d.blk j).round + 1 = b.round) (hF : F < b.round) :
    ∀ j ∈ b.refs, (m.blk j).round + 1 = b.round := fun j hj => by
  rw [h.round (h.refs_mem hrefs hpred hF hj)]; exact hpred j hj

end Mirrors

/-- **Add a block to the memory at `F`**: as it is above `F`, without
references at `F`, and not below `F`. -/
def put (F : ℕ) (id : BlockId) (b : Block Validator BlockId Payload) (hnew : id ∉ m.ids)
    (hrefs : F < b.round → b.refs ⊆ m.ids)
    (hpred : F < b.round → ∀ j ∈ b.refs, (m.blk j).round + 1 = b.round) :
    Store Validator BlockId Payload :=
  if hF : F < b.round then m.insert id b hnew (hrefs hF) (hpred hF)
  else if b.round = F then
    m.insert id { b with refs := ∅ } hnew (Finset.empty_subset _)
      (fun j hj => absurd hj (Finset.notMem_empty j))
  else m

omit [DecidableEq Validator] in
theorem insert_blk {st : Store Validator BlockId Payload} {id : BlockId}
    {b : Block Validator BlockId Payload} {hnew hrefs hpred} (i : BlockId) :
    (st.insert id b hnew hrefs hpred).blk i = if i = id then b else st.blk i := by
  change (st.map.insert id b).getD i st.junk = _
  split
  · subst i; exact Std.TreeMap.getD_insert_self
  · rename_i hne; exact treeMap_getD_insert_ne (Ne.symm hne)

omit [DecidableEq Validator] in
/-- **Adding a block on disk and in memory keeps the memory the disk's
window.** -/
theorem Mirrors.put (h : m.Mirrors d F) {id : BlockId} {b : Block Validator BlockId Payload}
    (hnew : id ∉ d.ids) (hrefs : b.refs ⊆ d.ids)
    (hpred : ∀ j ∈ b.refs, (d.blk j).round + 1 = b.round) :
    (m.put F id b (h.notMem hnew) (h.refs_mem hrefs hpred) (h.pred_mem hrefs hpred)).Mirrors
      (d.insert id b hnew hrefs hpred) F := by
  have hm := h.notMem hnew
  have hd : ∀ i, i ≠ id → (d.insert id b hnew hrefs hpred).blk i = d.blk i := fun i hi => by
    rw [insert_blk, if_neg hi]
  unfold Store.put
  split
  · rename_i hF
    constructor
    · intro i
      rw [insert_ids, insert_ids, Finset.mem_insert, Finset.mem_insert]
      by_cases hi : i = id
      · subst hi; rw [insert_blk, if_pos rfl]; simp [hF.le]
      · rw [hd i hi, h.mem i]; simp [hi]
    · intro i hi
      rw [insert_ids, Finset.mem_insert] at hi
      rw [insert_blk]
      by_cases hii : i = id
      · subst hii
        unfold windowBlk
        rw [insert_blk, if_pos rfl, if_pos rfl]
        dsimp only
        rw [if_neg (by omega)]
      · rw [if_neg hii, h.blk i (hi.resolve_left hii)]
        unfold windowBlk
        rw [hd i hii]
  · rename_i hF
    split
    · rename_i hb
      constructor
      · intro i
        rw [insert_ids, insert_ids, Finset.mem_insert, Finset.mem_insert]
        by_cases hi : i = id
        · subst hi; rw [insert_blk, if_pos rfl]; simp [hb]
        · rw [hd i hi, h.mem i]; simp [hi]
      · intro i hi
        rw [insert_ids, Finset.mem_insert] at hi
        rw [insert_blk]
        by_cases hii : i = id
        · subst hii
          unfold windowBlk
          rw [insert_blk, if_pos rfl, if_pos rfl]
          dsimp only
          rw [if_pos (by omega)]
        · rw [if_neg hii, h.blk i (hi.resolve_left hii)]
          unfold windowBlk
          rw [hd i hii]
    · rename_i hb
      constructor
      · intro i
        rw [insert_ids, Finset.mem_insert]
        by_cases hi : i = id
        · subst hi
          rw [insert_blk, if_pos rfl]
          exact ⟨fun h' => absurd h' hm, fun ⟨_, h'⟩ => absurd h' (by omega)⟩
        · rw [hd i hi, h.mem i]; simp [hi]
      · intro i hi
        have hii : i ≠ id := fun e => hm (e ▸ hi)
        rw [h.blk i hi]
        unfold windowBlk
        rw [hd i hii]

/-- A block as the memory from round `F` up holds it: none below `F`,
without references at `F`, as it is above. -/
def aboveSel (F : ℕ) (_ : BlockId) (b : Block Validator BlockId Payload) :
    Option (Block Validator BlockId Payload) :=
  if b.round < F then none else if b.round = F then some { b with refs := ∅ } else some b

omit [DecidableEq Validator] in
theorem getElem?_map (st : Store Validator BlockId Payload) {i : BlockId} (hi : i ∈ st.ids) :
    st.map[i]? = some (st.blk i) :=
  Std.TreeMap.getElem?_eq_some_getD_of_contains ((st.mem_map i).mp hi)

omit [DecidableEq Validator] in
theorem getElem?_map_none (st : Store Validator BlockId Payload) {i : BlockId} (hi : i ∉ st.ids) :
    st.map[i]? = none :=
  Std.TreeMap.getElem?_eq_none_of_contains_eq_false
    (Bool.eq_false_iff.mpr fun h => hi ((st.mem_map i).mpr h))

omit [DecidableEq Validator] [LinearOrder BlockId] in
theorem aboveSel_some {F : ℕ} {i : BlockId} {b : Block Validator BlockId Payload} :
    (aboveSel F i b).isSome ↔ F ≤ b.round := by
  unfold aboveSel
  split
  · simp only [Option.isSome_none, Bool.false_eq_true, false_iff]; omega
  · split <;> simp only [Option.isSome_some, true_iff] <;> omega

omit [DecidableEq Validator] [LinearOrder BlockId] in
theorem aboveSel_eq {F : ℕ} {i : BlockId} {b : Block Validator BlockId Payload}
    (h : F ≤ b.round) :
    aboveSel F i b = some (if b.round ≤ F then { b with refs := ∅ } else b) := by
  unfold aboveSel
  rw [if_neg (by omega)]
  split
  · rw [if_pos (by omega)]
  · rw [if_neg (by omega)]

omit [DecidableEq Validator] in
theorem above_getElem? (st : Store Validator BlockId Payload) (F : ℕ) (i : BlockId) :
    (st.map.filterMap (aboveSel F))[i]? =
      if i ∈ st.ids ∧ F ≤ (st.blk i).round then some (st.windowBlk F i) else none := by
  rw [Std.TreeMap.getElem?_filterMap']
  by_cases hi : i ∈ st.ids
  · rw [st.getElem?_map hi, Option.bind_some]
    by_cases hr : F ≤ (st.blk i).round
    · rw [if_pos ⟨hi, hr⟩, aboveSel_eq hr]; rfl
    · rw [if_neg (fun h => hr h.2)]
      exact Option.not_isSome_iff_eq_none.mp (fun h => hr (aboveSel_some.mp h))
  · rw [st.getElem?_map_none hi, if_neg (fun h => hi h.1)]; rfl

omit [DecidableEq Validator] in
theorem above_getD (st : Store Validator BlockId Payload) (F : ℕ) (i : BlockId) :
    (st.map.filterMap (aboveSel F)).getD i st.junk =
      if i ∈ st.ids ∧ F ≤ (st.blk i).round then st.windowBlk F i else st.junk := by
  rw [Std.TreeMap.getD_eq_getD_getElem?, above_getElem?]
  split <;> rfl

omit [DecidableEq Validator] in
theorem above_round (st : Store Validator BlockId Payload) (F : ℕ) {i : BlockId}
    (hi : i ∈ st.ids.filter fun i => F ≤ (st.blk i).round) :
    ((st.map.filterMap (aboveSel F)).getD i st.junk).round = (st.blk i).round := by
  rw [above_getD, if_pos (Finset.mem_filter.mp hi)]
  exact st.windowBlk_round F i

/-- **The memory from round `F` up**: the blocks at `F` and above, those
at `F` without references. -/
def above (st : Store Validator BlockId Payload) (F : ℕ) : Store Validator BlockId Payload where
  map := st.map.filterMap (aboveSel F)
  ids := st.ids.filter fun i => F ≤ (st.blk i).round
  junk := st.junk
  complete := by
    intro i hi j hj
    rw [above_getD, if_pos (Finset.mem_filter.mp hi)] at hj
    obtain ⟨hr, hj⟩ := st.refs_windowBlk hj
    have := st.pred i (Finset.mem_filter.mp hi).1 j hj
    change (st.blk j).round + 1 = (st.blk i).round at this
    exact Finset.mem_filter.mpr ⟨st.complete i (Finset.mem_filter.mp hi).1 j hj, by omega⟩
  pred := by
    intro i hi j hj
    have hj' := hj
    rw [above_getD, if_pos (Finset.mem_filter.mp hi)] at hj'
    obtain ⟨hr, hj'⟩ := st.refs_windowBlk hj'
    have hpr := st.pred i (Finset.mem_filter.mp hi).1 j hj'
    change (st.blk j).round + 1 = (st.blk i).round at hpr
    rw [above_round st F hi, above_round st F (Finset.mem_filter.mpr
      ⟨st.complete i (Finset.mem_filter.mp hi).1 j hj', by omega⟩)]
    exact hpr
  mem_map := by
    intro j
    rw [Std.TreeMap.contains_eq_isSome_getElem?, above_getElem?, Finset.mem_filter]
    split <;> simp_all
  topRound := if F ≤ st.topRound then st.topRound else 0
  topRound_spec := by
    rw [Finset.sup_congr rfl fun i hi => above_round st F hi]
    have hle : ∀ i ∈ st.ids, (st.blk i).round ≤ st.topRound := fun i hi => by
      rw [st.topRound_eq]; exact Finset.le_sup (f := fun i => (st.blk i).round) hi
    split
    · rename_i hF
      refine le_antisymm ?_ (Finset.sup_le fun i hi => hle i (Finset.mem_filter.mp hi).1)
      rcases st.ids.eq_empty_or_nonempty with he | hne
      · rw [st.topRound_eq, he, Finset.sup_empty]; exact Nat.zero_le _
      · obtain ⟨i₀, hi₀, h₀⟩ := Finset.exists_mem_eq_sup st.ids hne fun i => (st.blk i).round
        rw [← st.topRound_eq] at h₀
        rw [h₀]
        exact Finset.le_sup (f := fun i => (st.blk i).round)
          (Finset.mem_filter.mpr ⟨hi₀, by rw [← h₀]; exact hF⟩)
    · rename_i hF
      rw [Finset.filter_eq_empty_iff.mpr fun i hi h' => hF (h'.trans (hle i hi)),
        Finset.sup_empty]
      rfl
  byRound := st.byRound.filter fun r _ => F ≤ r
  byRound_spec := by
    intro r
    rw [Std.TreeMap.getD_filter']
    ext i
    rw [Finset.mem_filter (s := st.ids.filter fun i => F ≤ (st.blk i).round)]
    by_cases hr : F ≤ r
    · rw [show Option.filter (fun _ => decide (F ≤ r)) st.byRound[r]? = st.byRound[r]? by
        simp only [hr, decide_true]; cases st.byRound[r]? <;> rfl,
        ← Std.TreeMap.getD_eq_getD_getElem?]
      change i ∈ st.atRound r ↔ _
      rw [st.atRound_eq, mem_blocksAt]
      constructor
      · rintro ⟨hi, hir⟩
        have hm : i ∈ st.ids.filter fun i => F ≤ (st.blk i).round :=
          Finset.mem_filter.mpr ⟨hi, by change (st.blk i).round = r at hir; omega⟩
        exact ⟨hm, by rw [above_round st F hm]; exact hir⟩
      · rintro ⟨hm, hir⟩
        rw [above_round st F hm] at hir
        exact ⟨(Finset.mem_filter.mp hm).1, hir⟩
    · rw [show Option.filter (fun _ => decide (F ≤ r)) st.byRound[r]? = none by simp [hr]]
      simp only [Option.getD_none, Finset.notMem_empty, false_iff, not_and]
      intro hm hir
      rw [above_round st F hm] at hir
      have := (Finset.mem_filter.mp hm).2
      omega

theorem above_ids (st : Store Validator BlockId Payload) (F : ℕ) :
    (st.above F).ids = st.ids.filter fun i => F ≤ (st.blk i).round := rfl

theorem above_blk (st : Store Validator BlockId Payload) (F : ℕ) {i : BlockId}
    (hi : i ∈ (st.above F).ids) : (st.above F).blk i = st.windowBlk F i := by
  change (st.map.filterMap (aboveSel F)).getD i st.junk = _
  rw [above_getD, if_pos (Finset.mem_filter.mp hi)]

/-- **Releasing the memory below a higher round keeps it the disk's
window there.** -/
theorem Mirrors.above (h : m.Mirrors d F) {F' : ℕ} (hF : F ≤ F') : (m.above F').Mirrors d F' where
  mem i := by
    rw [above_ids, Finset.mem_filter]
    constructor
    · rintro ⟨hi, hr⟩
      rw [h.round hi] at hr
      exact ⟨h.sub hi, hr⟩
    · rintro ⟨hi, hr⟩
      have hm := h.mem_of hi (hF.trans hr)
      exact ⟨hm, by rw [h.round hm]; exact hr⟩
  blk i hi := by
    rw [above_blk _ _ hi]
    have hm := (Finset.mem_filter.mp hi).1
    unfold windowBlk
    dsimp only
    rw [h.blk i hm]
    unfold windowBlk
    dsimp only
    split <;> split <;> simp_all
    omega

omit [LinearOrder BlockId] in
/-- **Validity at the row reads only the references' rounds and authors.** -/
theorem rowValid_congr {q : ℕ} {blk blk' : BlockId → Block Validator BlockId Payload}
    {b : Block Validator BlockId Payload}
    (hr : ∀ j ∈ b.refs, (blk' j).round = (blk j).round)
    (hc : ∀ j ∈ b.refs, (blk' j).creator = (blk j).creator) :
    rowValid q blk b → rowValid q blk' b := fun h =>
  ⟨fun i hi => by rw [hr i hi]; exact h.predecessor i hi,
    fun h0 => by
      have : creators blk' b = creators blk b := Finset.image_congr fun j hj => hc j hj
      rw [this]; exact h.quorum h0,
    fun i hi j hj hij => h.clause i hi j hj (by rw [← hc i hi, ← hc j hj]; exact hij)⟩

/-- **The checks a block passes to be accepted**: its references are
accepted, one round below it, and it is valid at the row. -/
def Checks (q : ℕ) (st : Store Validator BlockId Payload) (id : BlockId)
    (b : Block Validator BlockId Payload) : Prop :=
  b.refs ⊆ st.ids ∧ (∀ j ∈ b.refs, (st.blk j).round + 1 = b.round) ∧
    rowValid q (Function.update st.blk id b) b

instance (q : ℕ) (st : Store Validator BlockId Payload) (id : BlockId)
    (b : Block Validator BlockId Payload) : Decidable (st.Checks q id b) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _))

/-- Reading the update at `id` of a map that agrees on round and author
with another on `b`'s references. -/
theorem update_congr {blk blk' : BlockId → Block Validator BlockId Payload} {id : BlockId}
    {b : Block Validator BlockId Payload}
    (hr : ∀ j ∈ b.refs, (blk' j).round = (blk j).round)
    (hc : ∀ j ∈ b.refs, (blk' j).creator = (blk j).creator) :
    rowValid q (Function.update blk id b) b → rowValid q (Function.update blk' id b) b :=
  rowValid_congr
    (fun j hj => by
      by_cases hji : j = id
      · subst hji; simp
      · rw [Function.update_of_ne hji, Function.update_of_ne hji]; exact hr j hj)
    (fun j hj => by
      by_cases hji : j = id
      · subst hji; simp
      · rw [Function.update_of_ne hji, Function.update_of_ne hji]; exact hc j hj)

/-- **A block passing the checks in memory passes them on disk.** -/
theorem Mirrors.checks_disk (h : m.Mirrors d F) {q : ℕ} {id : BlockId}
    {b : Block Validator BlockId Payload} (hc : m.Checks q id b) : d.Checks q id b :=
  ⟨fun j hj => h.sub (hc.1 hj), fun j hj => by rw [← h.round (hc.1 hj)]; exact hc.2.1 j hj,
    update_congr (fun j hj => (h.round (hc.1 hj)).symm) (fun j hj => (h.creator (hc.1 hj)).symm)
      hc.2.2⟩

/-- **Above `F`, a block passes the checks in memory exactly when on
disk.** -/
theorem Mirrors.checks_iff (h : m.Mirrors d F) {q : ℕ} {id : BlockId}
    {b : Block Validator BlockId Payload} (hF : F < b.round) :
    m.Checks q id b ↔ d.Checks q id b := by
  refine ⟨h.checks_disk, fun hc => ?_⟩
  have hm := h.refs_mem hc.1 hc.2.1 hF
  exact ⟨hm, h.pred_mem hc.1 hc.2.1 hF,
    update_congr (fun j hj => h.round (hm hj)) (fun j hj => h.creator (hm hj)) hc.2.2⟩

/-- **The store a block of round `ρ` is checked against**: the memory `m`
above its lowest round `F`, the disk `d` otherwise. -/
def pick (m d : Store Validator BlockId Payload) (F ρ : ℕ) : Store Validator BlockId Payload :=
  if F < ρ then m else d

theorem Mirrors.checks_pick (h : m.Mirrors d F) {q : ℕ} {id : BlockId}
    {b : Block Validator BlockId Payload} :
    (pick m d F b.round).Checks q id b ↔ d.Checks q id b := by
  unfold pick
  split
  · exact h.checks_iff (by assumption)
  · exact Iff.rfl

theorem mem_atRound {st : Store Validator BlockId Payload} {r : ℕ} {i : BlockId} :
    i ∈ st.atRound r ↔ i ∈ st.ids ∧ (st.blk i).round = r := by
  rw [atRound_eq, mem_blocksAt]; rfl

/-- **The memory holds at each round only blocks the disk holds there.** -/
theorem Mirrors.atRound_sub (h : m.Mirrors d F) (r : ℕ) : m.atRound r ⊆ d.atRound r :=
  fun i hi => by
    rw [mem_atRound] at hi ⊢
    exact ⟨h.sub hi.1, by rw [← h.round hi.1]; exact hi.2⟩

/-- **From `F` up, the memory holds at each round the disk's blocks.** -/
theorem Mirrors.atRound_eq (h : m.Mirrors d F) {r : ℕ} (hr : F ≤ r) :
    m.atRound r = d.atRound r := by
  refine subset_antisymm (h.atRound_sub r) fun i hi => ?_
  rw [mem_atRound] at hi ⊢
  have hm := h.mem_of hi.1 (by rw [hi.2]; exact hr)
  exact ⟨hm, by rw [h.round hm]; exact hi.2⟩

theorem Mirrors.creatorsOf_eq (h : m.Mirrors d F) {S : Finset BlockId} (hS : S ⊆ m.ids) :
    creatorsOf m.blk S = creatorsOf d.blk S :=
  Finset.image_congr fun _ hi => h.creator (hS hi)

theorem Mirrors.authorsAt_sub (h : m.Mirrors d F) (r : ℕ) : m.authorsAt r ⊆ d.authorsAt r := by
  unfold authorsAt
  rw [h.creatorsOf_eq fun i hi => (mem_atRound.mp hi).1]
  exact Finset.image_subset_image (h.atRound_sub r)

theorem Mirrors.authorsAt_eq (h : m.Mirrors d F) {r : ℕ} (hr : F ≤ r) :
    m.authorsAt r = d.authorsAt r := by
  unfold authorsAt
  rw [h.creatorsOf_eq fun i hi => (mem_atRound.mp hi).1, h.atRound_eq hr]

end Store

end Node

end LeanDag
