import Mathlib.Data.Finset.Basic
/-!
# First-occurrence deduplication by a key

The filter a linearizer applies when it keeps a persistent set `H` of
what it has delivered: walk a list left to right, emit an element iff
its key is not yet in `H`, and add the key. `dedupFrom` threads the set
(`seen`); `dedupBy` starts it empty.

This is **not** Mathlib's `List.dedup`, which keeps the *last*
occurrence of each element: keeping the last occurrence is not stable
under extending the list, and a delivered sequence must be.

**Definitions only**; the lemmas live in `Common/DedupLemmas.lean`.
-/

namespace LeanDag

variable {α κ : Type*} [DecidableEq κ]

/-- Walk `l` left to right with delivered keys `seen` (the paper's `H`):
an element whose key is in `seen` is dropped; any other is emitted and
its key added to `seen` for the rest of the walk. -/
def dedupFrom (key : α → κ) : List α → Finset κ → List α
  | [], _ => []
  | a :: as, seen =>
      if key a ∈ seen then dedupFrom key as seen
      else a :: dedupFrom key as (insert (key a) seen)

/-- The first occurrence of each key, in the order of `l`: the walk
started from `H = ∅`. -/
def dedupBy (key : α → κ) (l : List α) : List α :=
  dedupFrom key l ∅

end LeanDag
