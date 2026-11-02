import LeanDag.Node.Model.Interface
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Data.Finset.Sort
/-!
# An honest node — its store

`docs/validator.md` §3.1. The accepted blocks, in an ordered map. The
store is closed under references, and every reference sits one round
below its referrer (`stored`, the validity its record carries).
`Store.insert` accepts a block, and `Store.toRecord` and `Store.view`
read the store as a block record and its view.

The store keeps three indexes beside the set of accepted identifiers,
each with the invariant that ties it to that set: the map's keys are
the accepted identifiers (`mem_map`), so membership is decided by a map
lookup (`has`, and the instances `decMem` and `decSubset`); the highest
round (`topRound`, `topRound_eq`); and the accepted identifiers of each
round (`byRound`), read by `atRound` and `authorsAt`, which equal
`blocksAt` and `authorsIn` of the record (`atRound_eq`, `authorsAt_eq`).

`leaderBlocks` reads a slot's leader blocks off `atRound`, and equals
the scheme's `candidatesIn` on the store's view (`leaderBlocks_eq`).
`window st R` is the record of the blocks at rounds `R` and above,
gathered from `byRound`, those at `R` read without references, and
`windowView st R` its view of all its blocks.

A store may keep a block without its references (`strip`, `stripAll`),
holding those references apart (`kept`); they are accepted and one round
below the block (`kept_closed`). The block as accepted (`full`) restores
them, so the blocks as accepted are closed under references too
(`full_refs`, `causal_full`). `Restrips F st st'` says `st'` keeps the
blocks of `st`, as accepted, perhaps more of those below `F` without their
references.
-/

namespace LeanDag

namespace Node

variable {Validator BlockId Payload : Type} [DecidableEq Validator] [LinearOrder BlockId]

section TreeMap

variable {κ β : Type} [LinearOrder κ]

omit [DecidableEq Validator] in
theorem treeMap_getD_insert_ne {t : Std.TreeMap κ β compare} {k a : κ} {fb v : β}
    (h : k ≠ a) : (t.insert k v).getD a fb = t.getD a fb := by
  rw [Std.TreeMap.getD_insert]
  simp [h]

omit [DecidableEq Validator] in
theorem treeMap_contains_insert {t : Std.TreeMap κ β compare} {k a : κ} {v : β} :
    (t.insert k v).contains a = true ↔ a = k ∨ t.contains a = true := by
  rw [Std.TreeMap.contains_insert, Bool.or_eq_true, beq_iff_eq, compare_eq_iff_eq, eq_comm]

end TreeMap

variable (Validator BlockId Payload) in
/-- **The accepted blocks.** -/
structure Store where
  /-- The blocks, by identifier. -/
  map : Std.TreeMap BlockId (Block Validator BlockId Payload) compare
  /-- The accepted identifiers. -/
  ids : Finset BlockId
  /-- What an identifier outside the map denotes. -/
  junk : Block Validator BlockId Payload
  /-- Every reference of an accepted block is accepted. -/
  complete : ∀ i ∈ ids, ∀ j ∈ (map.getD i junk).refs, j ∈ ids
  /-- Every reference sits one round below its referrer. -/
  pred : ∀ i ∈ ids, ∀ j ∈ (map.getD i junk).refs,
    (map.getD j junk).round + 1 = (map.getD i junk).round
  /-- The accepted identifiers are the map's keys. -/
  mem_map : ∀ j, j ∈ ids ↔ map.contains j = true
  /-- The highest round in the store. -/
  topRound : ℕ
  /-- `topRound` is the highest round of an accepted block. -/
  topRound_spec : topRound = ids.sup fun i => (map.getD i junk).round
  /-- The accepted identifiers, by round. -/
  byRound : Std.TreeMap ℕ (Finset BlockId) compare
  /-- `byRound` holds at each round the accepted identifiers of that round. -/
  byRound_spec : ∀ r, byRound.getD r ∅ = ids.filter fun i => (map.getD i junk).round = r
  /-- The references of the blocks kept without them. -/
  kept : Std.TreeMap BlockId (Finset BlockId) compare
  /-- A block kept without its references is accepted and holds none. -/
  kept_spec : ∀ j, kept.contains j = true → j ∈ ids ∧ (map.getD j junk).refs = ∅
  /-- The references kept apart are accepted, one round below their block. -/
  kept_closed : ∀ j R, kept[j]? = some R → ∀ x ∈ R,
    x ∈ ids ∧ (map.getD x junk).round + 1 = (map.getD j junk).round

namespace Store

/-- The empty store. -/
def empty (junk : Block Validator BlockId Payload) : Store Validator BlockId Payload where
  map := ∅
  ids := ∅
  junk := junk
  complete := fun _ h => absurd h (Finset.notMem_empty _)
  pred := fun _ h => absurd h (Finset.notMem_empty _)
  mem_map := fun j => by simp [Std.TreeMap.contains_emptyc]
  topRound := 0
  topRound_spec := by simp
  byRound := ∅
  byRound_spec := fun r => by simp [Std.TreeMap.getD_emptyc]
  kept := ∅
  kept_spec := fun j h => by simp [Std.TreeMap.contains_emptyc] at h
  kept_closed := fun j R h => by simp at h

variable (s : Store Validator BlockId Payload)

/-- What each identifier denotes. -/
def blk (i : BlockId) : Block Validator BlockId Payload := s.map.getD i s.junk

/-- Whether an identifier is accepted, by a map lookup. -/
def has (j : BlockId) : Bool := s.map.contains j

omit [DecidableEq Validator] in
theorem has_iff (j : BlockId) : s.has j = true ↔ j ∈ s.ids := (s.mem_map j).symm

/-- Membership in the accepted identifiers, decided by `has`. -/
instance decMem (j : BlockId) : Decidable (j ∈ s.ids) :=
  decidable_of_iff (s.has j = true) (s.has_iff j)

/-- Inclusion in the accepted identifiers, decided by `has` at each element. -/
instance decSubset (R : Finset BlockId) : Decidable (R ⊆ s.ids) :=
  decidable_of_iff (∀ j ∈ R, j ∈ s.ids) Finset.subset_iff.symm

omit [DecidableEq Validator] in
theorem topRound_eq : s.topRound = s.ids.sup fun i => (s.blk i).round := s.topRound_spec

omit [DecidableEq Validator] in
theorem notMem_byRound {id : BlockId} {r : ℕ} (hnew : id ∉ s.ids) : id ∉ s.byRound.getD r ∅ := by
  rw [s.byRound_spec]
  exact fun h => hnew (Finset.mem_filter.mp h).1

/-- **Accept a block**: new, with its references accepted and one round
below it. -/
def insert (id : BlockId) (b : Block Validator BlockId Payload) (hnew : id ∉ s.ids)
    (hrefs : b.refs ⊆ s.ids) (hpred : ∀ j ∈ b.refs, (s.blk j).round + 1 = b.round) :
    Store Validator BlockId Payload where
  map := s.map.insert id b
  ids := Finset.cons id s.ids hnew
  junk := s.junk
  complete := by
    have hlk : ∀ i, i ≠ id → (s.map.insert id b).getD i s.junk = s.blk i :=
      fun i hi => by simp only [blk, treeMap_getD_insert_ne (Ne.symm hi)]
    intro i hi j hj
    rw [Finset.mem_cons] at hi
    by_cases h : i = id
    · subst h
      simp only [Std.TreeMap.getD_insert_self] at hj
      exact Finset.mem_cons_of_mem (hrefs hj)
    · rw [hlk i h] at hj
      exact Finset.mem_cons_of_mem (s.complete i (hi.resolve_left h) j hj)
  pred := by
    have hlk : ∀ i, i ≠ id → (s.map.insert id b).getD i s.junk = s.blk i :=
      fun i hi => by simp only [blk, treeMap_getD_insert_ne (Ne.symm hi)]
    intro i hi j hj
    rw [Finset.mem_cons] at hi
    by_cases h : i = id
    · subst h
      simp only [Std.TreeMap.getD_insert_self] at hj ⊢
      have hj' : j ≠ i := fun e => hnew (e ▸ hrefs hj)
      rw [hlk j hj']
      exact hpred j hj
    · have hi' := hi.resolve_left h
      rw [hlk i h] at hj ⊢
      have hj' : j ≠ id := fun e => hnew (e ▸ s.complete i hi' j hj)
      rw [hlk j hj']
      exact s.pred i hi' j hj
  mem_map := fun j => by rw [Finset.mem_cons, treeMap_contains_insert, s.mem_map]
  topRound := max b.round s.topRound
  topRound_spec := by
    rw [Finset.sup_cons, Std.TreeMap.getD_insert_self, s.topRound_spec]
    congr 1
    refine Finset.sup_congr rfl fun i hi => ?_
    rw [treeMap_getD_insert_ne (ne_of_mem_of_not_mem hi hnew).symm]
  byRound := s.byRound.insert b.round (Finset.cons id (s.byRound.getD b.round ∅)
    (s.notMem_byRound hnew))
  byRound_spec := fun r => by
    have hlk : ∀ i ∈ s.ids, (s.map.insert id b).getD i s.junk = s.map.getD i s.junk :=
      fun i hi => treeMap_getD_insert_ne (ne_of_mem_of_not_mem hi hnew).symm
    ext i
    rw [Finset.mem_filter, Finset.mem_cons]
    by_cases h : b.round = r
    · subst h
      rw [Std.TreeMap.getD_insert_self, Finset.mem_cons, s.byRound_spec, Finset.mem_filter]
      constructor
      · rintro (rfl | ⟨hi, hr⟩)
        · exact ⟨Or.inl rfl, by rw [Std.TreeMap.getD_insert_self]⟩
        · exact ⟨Or.inr hi, by rw [hlk i hi]; exact hr⟩
      · rintro ⟨rfl | hi, hr⟩
        · exact Or.inl rfl
        · exact Or.inr ⟨hi, by rwa [hlk i hi] at hr⟩
    · rw [treeMap_getD_insert_ne h, s.byRound_spec, Finset.mem_filter]
      constructor
      · rintro ⟨hi, hr⟩
        exact ⟨Or.inr hi, by rw [hlk i hi]; exact hr⟩
      · rintro ⟨rfl | hi, hr⟩
        · rw [Std.TreeMap.getD_insert_self] at hr; exact absurd hr h
        · exact ⟨hi, by rwa [hlk i hi] at hr⟩
  kept := s.kept
  kept_spec := fun j hj => by
    obtain ⟨hj, hr⟩ := s.kept_spec j hj
    refine ⟨Finset.mem_cons_of_mem hj, ?_⟩
    rw [treeMap_getD_insert_ne (ne_of_mem_of_not_mem hj hnew).symm]
    exact hr
  kept_closed := fun j R hR x hx => by
    have hj := (s.kept_spec j (by rw [Std.TreeMap.contains_eq_isSome_getElem?, hR]; rfl)).1
    obtain ⟨hxi, hxr⟩ := s.kept_closed j R hR x hx
    refine ⟨Finset.mem_cons_of_mem hxi, ?_⟩
    rw [treeMap_getD_insert_ne (ne_of_mem_of_not_mem hj hnew).symm,
      treeMap_getD_insert_ne (ne_of_mem_of_not_mem hxi hnew).symm]
    exact hxr

omit [DecidableEq Validator] in
variable {s} in
theorem insert_ids {id : BlockId} {b : Block Validator BlockId Payload} {hnew : id ∉ s.ids}
    {hrefs : b.refs ⊆ s.ids} {hpred : ∀ j ∈ b.refs, (s.blk j).round + 1 = b.round} :
    (s.insert id b hnew hrefs hpred).ids = Insert.insert id s.ids :=
  Finset.cons_eq_insert id s.ids hnew

omit [DecidableEq Validator] in
variable {s} in
theorem mem_insert_self {id : BlockId} {b : Block Validator BlockId Payload} {hnew : id ∉ s.ids}
    {hrefs : b.refs ⊆ s.ids} {hpred : ∀ j ∈ b.refs, (s.blk j).round + 1 = b.round} :
    id ∈ (s.insert id b hnew hrefs hpred).ids :=
  Finset.mem_cons_self (h := hnew)

omit [DecidableEq Validator] in
variable {s} in
theorem mem_insert_of_mem {id j : BlockId} {b : Block Validator BlockId Payload} {hnew : id ∉ s.ids}
    {hrefs : b.refs ⊆ s.ids} {hpred : ∀ j ∈ b.refs, (s.blk j).round + 1 = b.round}
    (hj : j ∈ s.ids) : j ∈ (s.insert id b hnew hrefs hpred).ids :=
  Finset.mem_cons_of_mem (hb := hnew) hj

/-- **A block as accepted**: as stored, with its references restored if the
store keeps it without them. -/
def full (j : BlockId) : Block Validator BlockId Payload :=
  match s.kept[j]? with
  | some R => { s.blk j with refs := R }
  | none => s.blk j

omit [DecidableEq Validator] in
theorem full_fields (j : BlockId) : (s.full j).round = (s.blk j).round ∧
    (s.full j).creator = (s.blk j).creator ∧ (s.full j).payload = (s.blk j).payload := by
  unfold full; split <;> exact ⟨rfl, rfl, rfl⟩

omit [DecidableEq Validator] in
theorem full_eta (i : BlockId) : { s.blk i with refs := (s.full i).refs } = s.full i := by
  unfold full; split <;> rfl

omit [DecidableEq Validator] in
theorem full_of_kept_none {j : BlockId} (h : s.kept[j]? = none) : s.full j = s.blk j := by
  unfold full; rw [h]

omit [DecidableEq Validator] in
theorem kept_none_of_notMem {j : BlockId} (hj : j ∉ s.ids) : s.kept[j]? = none := by
  rcases h : s.kept[j]? with _ | R
  · rfl
  · exact absurd (s.kept_spec j (by rw [Std.TreeMap.contains_eq_isSome_getElem?, h]; rfl)).1 hj

omit [DecidableEq Validator] in
variable {s} in
theorem full_insert {id : BlockId} {b : Block Validator BlockId Payload} {hnew : id ∉ s.ids}
    {hrefs : b.refs ⊆ s.ids} {hpred : ∀ j ∈ b.refs, (s.blk j).round + 1 = b.round} (j : BlockId) :
    (s.insert id b hnew hrefs hpred).full j = if j = id then b else s.full j := by
  have hlk : (s.insert id b hnew hrefs hpred).blk j = if j = id then b else s.blk j := by
    change (s.map.insert id b).getD j s.junk = _
    split
    · subst j; exact Std.TreeMap.getD_insert_self
    · rename_i hne; exact treeMap_getD_insert_ne (Ne.symm hne)
  have hk : (s.insert id b hnew hrefs hpred).kept = s.kept := rfl
  by_cases hji : j = id
  · subst hji
    rw [if_pos rfl, full_of_kept_none _ (by rw [hk]; exact kept_none_of_notMem s hnew), hlk,
      if_pos rfl]
  · rw [if_neg hji]
    unfold full
    rw [hk, hlk, if_neg hji]

omit [DecidableEq Validator] in
/-- **The references of a block as accepted are accepted**, one round below
it. -/
theorem full_refs (j : BlockId) (hj : j ∈ s.ids) :
    ∀ x ∈ (s.full j).refs, x ∈ s.ids ∧ (s.blk x).round + 1 = (s.blk j).round := by
  unfold full
  split
  · rename_i R hR
    exact s.kept_closed j R hR
  · exact fun x hx => ⟨s.complete j hj x hx, s.pred j hj x hx⟩

omit [DecidableEq Validator] in
/-- A block's stored references are among its references as accepted. -/
theorem refs_sub_full (j : BlockId) : (s.blk j).refs ⊆ (s.full j).refs := by
  unfold full
  split
  · rename_i R hR
    have := (s.kept_spec j (by rw [Std.TreeMap.contains_eq_isSome_getElem?, hR]; rfl)).2
    change (s.blk j).refs = ∅ at this
    rw [this]; exact Finset.empty_subset _
  · exact subset_rfl

omit [DecidableEq Validator] in
/-- **The blocks as accepted are closed under references**, each one round
below its referrer. -/
theorem causal_full : CausalStructure s.full s.ids where
  complete i hi j hj := (s.full_refs i hi j hj).1
  refs_round i hi j hj := by
    rw [(s.full_fields j).1, (s.full_fields i).1]; exact (s.full_refs i hi j hj).2

/-- **Keep the block `j` without its references**, its references apart. -/
def strip (j : BlockId) : Store Validator BlockId Payload :=
  if hj : j ∈ s.ids then
    have hround : ∀ i, ((s.map.insert j { s.blk j with refs := ∅ }).getD i s.junk).round =
        (s.blk i).round := fun i => by
      by_cases h : i = j
      · subst h; rw [Std.TreeMap.getD_insert_self]
      · rw [treeMap_getD_insert_ne (Ne.symm h)]; rfl
    have hrefs : ∀ i, i ≠ j → (s.map.insert j { s.blk j with refs := ∅ }).getD i s.junk =
        s.blk i := fun i h => treeMap_getD_insert_ne (Ne.symm h)
    { map := s.map.insert j { s.blk j with refs := ∅ }
      ids := s.ids
      junk := s.junk
      complete := fun i hi k hk => by
        by_cases h : i = j
        · subst h; rw [Std.TreeMap.getD_insert_self] at hk; exact absurd hk (Finset.notMem_empty k)
        · rw [hrefs i h] at hk; exact s.complete i hi k hk
      pred := fun i hi k hk => by
        rw [hround, hround]
        by_cases h : i = j
        · subst h; rw [Std.TreeMap.getD_insert_self] at hk; exact absurd hk (Finset.notMem_empty k)
        · rw [hrefs i h] at hk; exact s.pred i hi k hk
      mem_map := fun k => by
        rw [treeMap_contains_insert, ← s.mem_map]
        exact ⟨Or.inr, fun h => h.elim (fun e => e ▸ hj) id⟩
      topRound := s.topRound
      topRound_spec := by
        rw [s.topRound_spec]
        exact Finset.sup_congr rfl fun i _ => (hround i).symm
      byRound := s.byRound
      byRound_spec := fun r => by
        rw [s.byRound_spec]
        exact Finset.filter_congr fun i _ => by rw [hround]; rfl
      kept := s.kept.insert j (s.full j).refs
      kept_spec := fun i hi => by
        rw [treeMap_contains_insert] at hi
        by_cases h : i = j
        · subst h; exact ⟨hj, by rw [Std.TreeMap.getD_insert_self]⟩
        · obtain ⟨hi', hr⟩ := s.kept_spec i (hi.resolve_left h)
          exact ⟨hi', by rw [hrefs i h]; exact hr⟩
      kept_closed := fun i R hR x hx => by
        rw [hround, hround]
        rw [Std.TreeMap.getElem?_insert] at hR
        split at hR
        · rename_i he
          have hij : j = i := compare_eq_iff_eq.mp he
          subst hij
          rw [Option.some.injEq] at hR
          subst hR
          exact s.full_refs j hj x hx
        · exact s.kept_closed i R hR x hx }
  else s

omit [DecidableEq Validator] in
theorem strip_ids (j : BlockId) : (s.strip j).ids = s.ids := by
  unfold strip; split <;> rfl

omit [DecidableEq Validator] in
theorem strip_blk (j i : BlockId) :
    (s.strip j).blk i = if i = j ∧ j ∈ s.ids then { s.blk j with refs := ∅ } else s.blk i := by
  unfold strip
  split
  · rename_i hj
    change (s.map.insert j _).getD i s.junk = _
    by_cases h : i = j
    · subst h; rw [Std.TreeMap.getD_insert_self, if_pos ⟨rfl, hj⟩]
    · rw [treeMap_getD_insert_ne (Ne.symm h), if_neg (fun h' => h h'.1)]; rfl
  · rename_i hj
    rw [if_neg (fun h' => hj h'.2)]

omit [DecidableEq Validator] in
/-- **Stripping keeps every block as accepted.** -/
theorem full_strip (j i : BlockId) : (s.strip j).full i = s.full i := by
  by_cases hj : j ∈ s.ids
  · have hk : (s.strip j).kept = s.kept.insert j (s.full j).refs := by
      unfold strip; rw [dif_pos hj]
    unfold full
    rw [hk, Std.TreeMap.getElem?_insert, strip_blk]
    by_cases h : i = j
    · subst h
      simp only [show compare i i = Ordering.eq from compare_eq_iff_eq.mpr rfl, if_true,
        and_self, hj]
      exact s.full_eta i
    · have hc : ¬ compare j i = Ordering.eq := fun e => h (compare_eq_iff_eq.mp e).symm
      simp only [hc, if_false, h, false_and]
  · have : s.strip j = s := by unfold strip; rw [dif_neg hj]
    rw [this]

omit [DecidableEq Validator] in
/-- Stripping keeps the round, author and payload of every block. -/
theorem strip_fields (j i : BlockId) : ((s.strip j).blk i).round = (s.blk i).round ∧
    ((s.strip j).blk i).creator = (s.blk i).creator ∧
      ((s.strip j).blk i).payload = (s.blk i).payload := by
  rw [strip_blk]; split
  · rename_i h; rw [h.1]; exact ⟨rfl, rfl, rfl⟩
  · exact ⟨rfl, rfl, rfl⟩

/-- **The store as a block record**, at `stored` and no honest set. -/
def toRecord : BlockRecord Validator BlockId Payload (stored Validator BlockId Payload) ∅ where
  ids := s.ids
  block := s.blk
  complete := s.complete
  valid := fun i hi => ⟨s.pred i hi, fun _ => Nat.zero_le _, trivial⟩
  no_equivocation := fun _ _ _ _ h => absurd h (Finset.notMem_empty _)

/-- **The node's view**: everything it accepted. -/
def view : s.toRecord.View where
  ids := s.ids
  subset_ids := subset_rfl
  complete := s.complete

/-- The accepted identifiers of round `r`, read off `byRound`. -/
def atRound (r : ℕ) : Finset BlockId := s.byRound.getD r ∅

theorem atRound_eq (r : ℕ) : s.atRound r = blocksAt s.toRecord r := s.byRound_spec r

/-- The authors of the accepted blocks of round `r`. -/
def authorsAt (r : ℕ) : Finset Validator := creatorsOf s.blk (s.atRound r)

theorem authorsAt_eq (r : ℕ) : s.authorsAt r = authorsIn s.toRecord s.ids r := by
  rw [authorsAt, atRound_eq]; rfl

/-- **The leader blocks of slot `k`**: the accepted blocks of the slot's
round whose author is the slot's leader, read off `atRound`. -/
def leaderBlocks [S : Slots Validator] (k : ℕ) : Finset BlockId :=
  (s.atRound (S.slotRound k)).filter fun b => (s.blk b).creator = S.leader k

theorem leaderBlocks_eq [S : Slots Validator] (k : ℕ) :
    s.leaderBlocks k = Scheme.candidatesIn s.toRecord s.view k := by
  ext x
  rw [leaderBlocks, Finset.mem_filter, atRound_eq, mem_blocksAt]
  simp only [Scheme.candidatesIn, Finset.mem_filter]
  exact ⟨fun ⟨⟨h₁, h₂⟩, h₃⟩ => ⟨h₁, h₃, h₂⟩, fun ⟨h₁, h₃, h₂⟩ => ⟨⟨h₁, h₂⟩, h₃⟩⟩

omit [DecidableEq Validator] in
/-- A block not kept without its references after a strip was not before,
and is stored alike. -/
theorem strip_unkept (j i : BlockId) (h : (s.strip j).kept[i]? = none) :
    s.kept[i]? = none ∧ (s.strip j).blk i = s.blk i := by
  by_cases hj : j ∈ s.ids
  · have hk : (s.strip j).kept = s.kept.insert j (s.full j).refs := by
      unfold strip; rw [dif_pos hj]
    rw [hk, Std.TreeMap.getElem?_insert] at h
    by_cases hij : i = j
    · subst hij
      simp [show compare i i = Ordering.eq from compare_eq_iff_eq.mpr rfl] at h
    · have hc : ¬ compare j i = Ordering.eq := fun e => hij (compare_eq_iff_eq.mp e).symm
      simp only [hc, if_false] at h
      exact ⟨h, by rw [strip_blk, if_neg fun h' => hij h'.1]⟩
  · have : s.strip j = s := by unfold strip; rw [dif_neg hj]
    rw [this] at h ⊢
    exact ⟨h, rfl⟩

/-- **Keep the blocks of `l` without their references.** -/
def stripAll (l : List BlockId) : Store Validator BlockId Payload :=
  l.foldl (fun st j => st.strip j) s

/-- The blocks of the rounds `F, …, F' − 1`. -/
def roundsFrom (F F' : ℕ) : List BlockId :=
  (List.range' F (F' - F)).flatMap fun r => (s.atRound r).sort (· ≤ ·)

omit [DecidableEq Validator] in
theorem stripAll_cases : ∀ (l : List BlockId) (st : Store Validator BlockId Payload),
    (st.stripAll l).ids = st.ids ∧ (∀ i, (st.stripAll l).full i = st.full i) ∧
      ∀ i, ((st.stripAll l).blk i).round = (st.blk i).round ∧
        ((st.stripAll l).blk i).creator = (st.blk i).creator ∧
        ((st.stripAll l).blk i).payload = (st.blk i).payload ∧
        (i ∉ l → (st.stripAll l).blk i = st.blk i) ∧
        ((st.stripAll l).kept[i]? = none → st.kept[i]? = none ∧ (st.stripAll l).blk i = st.blk i)
  | [], st => ⟨rfl, fun _ => rfl, fun _ => ⟨rfl, rfl, rfl, fun _ => rfl, fun h => ⟨h, rfl⟩⟩⟩
  | j :: l, st => by
    obtain ⟨h₁, h₂, h₃⟩ := stripAll_cases l (st.strip j)
    refine ⟨h₁.trans (st.strip_ids j), fun i => (h₂ i).trans (st.full_strip j i), fun i => ?_⟩
    obtain ⟨r₁, c₁, p₁, e₁, k₁⟩ := h₃ i
    obtain ⟨r₂, c₂, p₂⟩ := st.strip_fields j i
    refine ⟨r₁.trans r₂, c₁.trans c₂, p₁.trans p₂, fun hi => ?_, fun hk => ?_⟩
    · rw [List.mem_cons, not_or] at hi
      change ((st.strip j).stripAll l).blk i = st.blk i
      rw [e₁ hi.2, strip_blk, if_neg fun h => hi.1 h.1]
    · obtain ⟨hk', hb⟩ := k₁ hk
      obtain ⟨hk'', hb'⟩ := st.strip_unkept j i hk'
      exact ⟨hk'', hb.trans hb'⟩

omit [DecidableEq Validator] in
/-- A block newly kept without its references was stripped. -/
theorem stripAll_kept : ∀ (l : List BlockId) (st : Store Validator BlockId Payload) (i : BlockId),
    (st.stripAll l).kept[i]? ≠ none → st.kept[i]? = none → i ∈ l
  | [], st, i, h, h₀ => absurd h₀ h
  | j :: l, st, i, h, h₀ => by
    by_cases hij : i = j
    · exact hij ▸ List.mem_cons_self
    · refine List.mem_cons_of_mem _ (stripAll_kept l (st.strip j) i h ?_)
      by_cases hj : j ∈ st.ids
      · have hk : (st.strip j).kept = st.kept.insert j (st.full j).refs := by
          unfold strip; rw [dif_pos hj]
        rw [hk, Std.TreeMap.getElem?_insert]
        have hc : ¬ compare j i = Ordering.eq := fun e => hij (compare_eq_iff_eq.mp e).symm
        simp only [hc, if_false]
        exact h₀
      · have : st.strip j = st := by unfold strip; rw [dif_neg hj]
        rw [this]; exact h₀

omit [DecidableEq Validator] in
theorem mem_roundsFrom {F F' : ℕ} {i : BlockId} :
    i ∈ s.roundsFrom F F' ↔ i ∈ s.ids ∧ F ≤ (s.blk i).round ∧ (s.blk i).round < F' := by
  simp only [roundsFrom, List.mem_flatMap, List.mem_range'_1, Finset.mem_sort]
  constructor
  · rintro ⟨r, hr, hi⟩
    change i ∈ s.byRound.getD r ∅ at hi
    rw [s.byRound_spec, Finset.mem_filter] at hi
    change i ∈ s.ids ∧ (s.blk i).round = r at hi
    exact ⟨hi.1, by omega, by omega⟩
  · rintro ⟨hi, h₁, h₂⟩
    refine ⟨(s.blk i).round, by omega, ?_⟩
    change i ∈ s.byRound.getD _ ∅
    rw [s.byRound_spec, Finset.mem_filter]
    exact ⟨hi, rfl⟩

/-- **`st'` keeps the blocks of `st` below `F`, perhaps without their
references**: the same blocks, as accepted, at the same rounds, authors and
payloads, and from `F` up as stored. -/
structure Restrips (F : ℕ) (st st' : Store Validator BlockId Payload) : Prop where
  ids : st'.ids = st.ids
  junk : st'.junk = st.junk
  topRound : st'.topRound = st.topRound
  full : ∀ i, st'.full i = st.full i
  fields : ∀ i, (st'.blk i).round = (st.blk i).round ∧ (st'.blk i).creator = (st.blk i).creator ∧
    (st'.blk i).payload = (st.blk i).payload
  above : ∀ i, F ≤ (st.blk i).round → st'.blk i = st.blk i
  unkept : ∀ i, st'.kept[i]? = none → st.kept[i]? = none ∧ st'.blk i = st.blk i
  low : ∀ i, st'.kept[i]? ≠ none → st.kept[i]? = none → (st.blk i).round < F

omit [DecidableEq Validator] in
theorem Restrips.refl (F : ℕ) : Restrips F s s :=
  ⟨rfl, rfl, rfl, fun _ => rfl, fun _ => ⟨rfl, rfl, rfl⟩, fun _ _ => rfl, fun _ h => ⟨h, rfl⟩,
    fun _ h h' => absurd h' h⟩

omit [DecidableEq Validator] in
theorem Restrips.trans {F F' : ℕ} {a b c : Store Validator BlockId Payload} (h₁ : Restrips F a b)
    (h₂ : Restrips F' b c) (hF : F ≤ F') : Restrips F' a c where
  ids := h₂.ids.trans h₁.ids
  junk := h₂.junk.trans h₁.junk
  topRound := h₂.topRound.trans h₁.topRound
  full i := (h₂.full i).trans (h₁.full i)
  fields i := ⟨(h₂.fields i).1.trans (h₁.fields i).1, (h₂.fields i).2.1.trans (h₁.fields i).2.1,
    (h₂.fields i).2.2.trans (h₁.fields i).2.2⟩
  above i hi := (h₂.above i (by rw [(h₁.fields i).1]; exact hi)).trans (h₁.above i (by omega))
  unkept i hi := ⟨(h₁.unkept i (h₂.unkept i hi).1).1,
    (h₂.unkept i hi).2.trans (h₁.unkept i (h₂.unkept i hi).1).2⟩
  low i hi h₀ := by
    by_cases hb : b.kept[i]? = none
    · have := h₂.low i hi hb
      rw [(h₁.fields i).1] at this
      exact this
    · have := h₁.low i hb h₀; omega

omit [DecidableEq Validator] in
theorem Restrips.atRound {F : ℕ} {st st' : Store Validator BlockId Payload} (h : Restrips F st st')
    (r : ℕ) : st'.atRound r = st.atRound r := by
  change st'.byRound.getD r ∅ = st.byRound.getD r ∅
  rw [st'.byRound_spec, st.byRound_spec, h.ids]
  exact Finset.filter_congr fun i _ => by
    change (st'.blk i).round = r ↔ (st.blk i).round = r
    rw [(h.fields i).1]

omit [DecidableEq Validator] in
/-- **Keeping blocks below `F` without their references.** -/
theorem restrips_stripAll {F : ℕ} {l : List BlockId} (hl : ∀ j ∈ l, (s.blk j).round < F) :
    Restrips F s (s.stripAll l) := by
  obtain ⟨hids, hfull, hb⟩ := stripAll_cases l s
  have hjt : ∀ (l : List BlockId) (st : Store Validator BlockId Payload),
      (st.stripAll l).junk = st.junk ∧ (st.stripAll l).topRound = st.topRound := by
    intro l
    induction l with
    | nil => intro st; exact ⟨rfl, rfl⟩
    | cons j l ih =>
      intro st
      obtain ⟨h₁, h₂⟩ := ih (st.strip j)
      refine ⟨h₁.trans ?_, h₂.trans ?_⟩ <;> (unfold strip; split <;> rfl)
  exact ⟨hids, (hjt l s).1, (hjt l s).2, hfull, fun i => ⟨(hb i).1, (hb i).2.1, (hb i).2.2.1⟩,
    fun i hi => (hb i).2.2.2.1 fun hil => by have := hl i hil; omega, fun i hi => (hb i).2.2.2.2 hi,
    fun i hi h₀ => hl i (stripAll_kept l s i hi h₀)⟩

omit [DecidableEq Validator] in
variable {s} in
/-- Inserting a block keeps the blocks kept without their references below a
round. -/
theorem low_insert {F : ℕ} (hlow : ∀ j, s.kept[j]? ≠ none → (s.blk j).round < F) {id : BlockId}
    {b : Block Validator BlockId Payload} {hnew hrefs hpred} :
    ∀ j, (s.insert id b hnew hrefs hpred).kept[j]? ≠ none →
      ((s.insert id b hnew hrefs hpred).blk j).round < F := by
  intro j hj
  have hj' : s.kept[j]? ≠ none := hj
  have hjid : j ≠ id := fun e => hnew (by
    rw [← e]
    exact (s.kept_spec j (by
      rw [Std.TreeMap.contains_eq_isSome_getElem?]; exact Option.isSome_iff_ne_none.mpr hj')).1)
  have : (s.insert id b hnew hrefs hpred).blk j = s.blk j := by
    change (s.map.insert id b).getD j s.junk = _
    exact treeMap_getD_insert_ne (Ne.symm hjid)
  rw [this]
  exact hlow j hj'

omit [DecidableEq Validator] in
/-- Keeping blocks below `F` without their references keeps every block so
kept below `F`. -/
theorem Restrips.low_of {st st' : Store Validator BlockId Payload} {F₀ F : ℕ}
    (h : Restrips F st st') (hlow : ∀ j, st.kept[j]? ≠ none → (st.blk j).round < F₀)
    (hF : F₀ ≤ F) : ∀ j, st'.kept[j]? ≠ none → (st'.blk j).round < F := by
  intro j hj
  rw [(h.fields j).1]
  by_cases h₀ : st.kept[j]? = none
  · exact h.low j hj h₀
  · have := hlow j h₀; omega

omit [DecidableEq Validator] in
/-- The rounds `R … topRound`, each read off `byRound`, hold disjoint sets. -/
theorem atRound_disjoint (R : ℕ) :
    ((Finset.Ico R (s.topRound + 1) : Finset ℕ) : Set ℕ).PairwiseDisjoint s.atRound := by
  intro r₁ _ r₂ _ hne
  change Disjoint (s.byRound.getD r₁ ∅) (s.byRound.getD r₂ ∅)
  rw [s.byRound_spec, s.byRound_spec]
  exact Finset.disjoint_filter.mpr fun _ _ h₁ h₂ => hne (h₁.symm.trans h₂)

/-- The accepted identifiers at rounds `R` and above, gathered from
`byRound` at the rounds `R … topRound`. -/
def windowIds (R : ℕ) : Finset BlockId :=
  (Finset.Ico R (s.topRound + 1)).disjiUnion s.atRound (s.atRound_disjoint R)

omit [DecidableEq Validator] in
theorem mem_windowIds {R : ℕ} {i : BlockId} :
    i ∈ s.windowIds R ↔ i ∈ s.ids ∧ R ≤ (s.blk i).round := by
  rw [windowIds, Finset.mem_disjiUnion]
  constructor
  · rintro ⟨r, hr, hi⟩
    change i ∈ s.byRound.getD r ∅ at hi
    rw [s.byRound_spec, Finset.mem_filter] at hi
    rw [Finset.mem_Ico] at hr
    exact ⟨hi.1, hi.2 ▸ hr.1⟩
  · rintro ⟨hi, hR⟩
    refine ⟨(s.blk i).round, Finset.mem_Ico.mpr ⟨hR, Nat.lt_succ_of_le ?_⟩, ?_⟩
    · rw [topRound_eq]
      exact Finset.le_sup (f := fun i => (s.blk i).round) hi
    · change i ∈ s.byRound.getD _ ∅
      rw [s.byRound_spec, Finset.mem_filter]
      exact ⟨hi, rfl⟩

/-- The block map of the window at `R`: a block at or below round `R`
without its references, any other as stored. -/
def windowBlk (R : ℕ) (i : BlockId) : Block Validator BlockId Payload :=
  let b := s.blk i
  if b.round ≤ R then { b with refs := ∅ } else b

omit [DecidableEq Validator] in
theorem windowBlk_round (R : ℕ) (i : BlockId) : (s.windowBlk R i).round = (s.blk i).round := by
  unfold windowBlk
  dsimp only
  split <;> rfl

omit [DecidableEq Validator] in
theorem refs_windowBlk {R : ℕ} {i j : BlockId} (hj : j ∈ (s.windowBlk R i).refs) :
    R < (s.blk i).round ∧ j ∈ (s.blk i).refs := by
  unfold windowBlk at hj
  dsimp only at hj
  split at hj
  · exact absurd hj (Finset.notMem_empty j)
  · exact ⟨by omega, hj⟩

/-- **The window of the store at round `R`**: its blocks at rounds `R`
and above, those at `R` without references, as a block record at
`stored`. A reference of a block above `R` lies one round below it,
hence at `R` or above. -/
def window (R : ℕ) :
    BlockRecord Validator BlockId Payload (stored Validator BlockId Payload) ∅ where
  ids := s.windowIds R
  block := s.windowBlk R
  complete := fun i hi j hj => by
    obtain ⟨hi, -⟩ := s.mem_windowIds.mp hi
    obtain ⟨hlt, hj⟩ := s.refs_windowBlk hj
    have h := s.pred i hi j hj
    change (s.blk j).round + 1 = (s.blk i).round at h
    exact s.mem_windowIds.mpr ⟨s.complete i hi j hj, by omega⟩
  valid := fun i hi => ⟨fun j hj => by
      rw [windowBlk_round, windowBlk_round]
      exact s.pred i (s.mem_windowIds.mp hi).1 j (s.refs_windowBlk hj).2,
    fun _ => Nat.zero_le _, trivial⟩
  no_equivocation := fun _ _ _ _ h => absurd h (Finset.notMem_empty _)

/-- **The view of the window**: all its blocks. -/
def windowView (R : ℕ) : (s.window R).View where
  ids := s.windowIds R
  subset_ids := subset_rfl
  complete := (s.window R).complete

end Store

end Node

end LeanDag
