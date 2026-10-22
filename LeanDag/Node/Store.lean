import LeanDag.Node.Model.Interface
/-!
# An honest node — its store

`docs/validator.md` §3.1. The accepted blocks, in an ordered map. The
store is closed under references, and every reference sits one round
below its referrer (`stored`, the validity its record carries).
`Store.insert` accepts a block, and `Store.toRecord` and `Store.view`
read the store as a block record and its view.
-/

namespace LeanDag

namespace Node

variable {Validator BlockId Payload : Type} [DecidableEq Validator] [LinearOrder BlockId]

section TreeMap

variable {β : Type}

omit [DecidableEq Validator] in
theorem treeMap_getD_insert_ne {t : Std.TreeMap BlockId β compare} {k a : BlockId} {fb v : β}
    (h : k ≠ a) : (t.insert k v).getD a fb = t.getD a fb := by
  rw [Std.TreeMap.getD_insert]
  simp [h]

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

namespace Store

/-- The empty store. -/
def empty (junk : Block Validator BlockId Payload) : Store Validator BlockId Payload where
  map := ∅
  ids := ∅
  junk := junk
  complete := fun _ h => absurd h (Finset.notMem_empty _)
  pred := fun _ h => absurd h (Finset.notMem_empty _)

variable (s : Store Validator BlockId Payload)

/-- What each identifier denotes. -/
def blk (i : BlockId) : Block Validator BlockId Payload := s.map.getD i s.junk

/-- **Accept a block**: new, with its references accepted and one round
below it. -/
def insert (id : BlockId) (b : Block Validator BlockId Payload) (hnew : id ∉ s.ids)
    (hrefs : b.refs ⊆ s.ids) (hpred : ∀ j ∈ b.refs, (s.blk j).round + 1 = b.round) :
    Store Validator BlockId Payload where
  map := s.map.insert id b
  ids := Insert.insert id s.ids
  junk := s.junk
  complete := by
    have hlk : ∀ i, i ≠ id → (s.map.insert id b).getD i s.junk = s.blk i :=
      fun i hi => by simp only [blk, treeMap_getD_insert_ne (Ne.symm hi)]
    intro i hi j hj
    by_cases h : i = id
    · subst h
      simp only [Std.TreeMap.getD_insert_self] at hj
      exact Finset.mem_insert_of_mem (hrefs hj)
    · rw [hlk i h] at hj
      exact Finset.mem_insert_of_mem (s.complete i ((Finset.mem_insert.mp hi).resolve_left h) j hj)
  pred := by
    have hlk : ∀ i, i ≠ id → (s.map.insert id b).getD i s.junk = s.blk i :=
      fun i hi => by simp only [blk, treeMap_getD_insert_ne (Ne.symm hi)]
    intro i hi j hj
    by_cases h : i = id
    · subst h
      simp only [Std.TreeMap.getD_insert_self] at hj ⊢
      have hj' : j ≠ i := fun e => hnew (e ▸ hrefs hj)
      rw [hlk j hj']
      exact hpred j hj
    · have hi' := (Finset.mem_insert.mp hi).resolve_left h
      rw [hlk i h] at hj ⊢
      have hj' : j ≠ id := fun e => hnew (e ▸ s.complete i hi' j hj)
      rw [hlk j hj']
      exact s.pred i hi' j hj

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

/-- The highest round in the store. -/
def topRound : ℕ := s.ids.sup fun i => (s.blk i).round

end Store

end Node

end LeanDag
