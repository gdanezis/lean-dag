import LeanDag.Node.Model.Interface
/-!
# An honest node — its store

`docs/validator.md` §3.1. The accepted blocks: an identifier set and a
block map, closed under references and valid at the row. `Store.insert`
adds a new block whose references are present and which is valid under
the extended map; `Store.toRecord` reads the store as a block record, which is what the decider and the vote rule take, and
`Store.view` as its view.

Definitions only.
-/

namespace LeanDag

namespace Node

variable {Validator BlockId Payload : Type} [Fintype Validator] [DecidableEq Validator]
variable [LinearOrder BlockId]

variable (Validator BlockId Payload) in
/-- **The accepted blocks** at quorum `q`, closed under references and
valid. `blk` is total, with junk outside `ids`. -/
structure Store (q : ℕ) where
  /-- The accepted identifiers. -/
  ids : Finset BlockId
  /-- What each identifier denotes. -/
  blk : BlockId → Block Validator BlockId Payload
  /-- Every reference of an accepted block is accepted. -/
  complete : ∀ i ∈ ids, ∀ j ∈ (blk i).refs, j ∈ ids
  /-- Every accepted block is valid at the row. -/
  valid : ∀ i ∈ ids, rowValid q blk (blk i)

namespace Store

variable {q : ℕ}

/-- The empty store, its block map constantly `junk`. -/
def empty (junk : Block Validator BlockId Payload) : Store Validator BlockId Payload q where
  ids := ∅
  blk := fun _ => junk
  complete := fun _ h => absurd h (Finset.notMem_empty _)
  valid := fun _ h => absurd h (Finset.notMem_empty _)

variable (s : Store Validator BlockId Payload q)

/-- **Accept a block**: new, its references accepted, and valid under the
extended map. -/
def insert (id : BlockId) (b : Block Validator BlockId Payload) (hnew : id ∉ s.ids)
    (hrefs : b.refs ⊆ s.ids) (hv : rowValid q (Function.update s.blk id b) b) :
    Store Validator BlockId Payload q where
  ids := Insert.insert id s.ids
  blk := Function.update s.blk id b
  complete := by
    intro i hi j hj
    by_cases h : i = id
    · subst h
      rw [Function.update_self] at hj
      exact Finset.mem_insert_of_mem (hrefs hj)
    · rw [Function.update_of_ne h] at hj
      exact Finset.mem_insert_of_mem (s.complete i ((Finset.mem_insert.mp hi).resolve_left h) j hj)
  valid := by
    have hag : ∀ j ∈ s.ids, Function.update s.blk id b j = s.blk j := fun j hj =>
      Function.update_of_ne (fun h : j = id => hnew (h ▸ hj)) _ _
    intro i hi
    by_cases h : i = id
    · subst h
      rw [Function.update_self]
      exact hv
    · have hi' := (Finset.mem_insert.mp hi).resolve_left h
      rw [Function.update_of_ne h]
      exact Validity.Mechanised.reads s.blk _ s.ids (s.blk i) s.complete (s.complete i hi')
        hag (s.valid i hi')

/-- **The store as a block record**, at the row's validity and no honest
set. -/
def toRecord : BlockRecord Validator BlockId Payload (rowValid q) ∅ where
  ids := s.ids
  block := s.blk
  complete := s.complete
  valid := s.valid
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
