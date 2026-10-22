import LeanDag.Node.Model.Interface
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

end Store

end Node

end LeanDag
