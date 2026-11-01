import LeanDag.Node.Sync.Model.Net
/-!
# Sync by causal streams — time

`docs/sync.md` §7. Events carry times, nondecreasing along the trace
(`TimeMono`). A node detects an author at an event when the author is
detected after it and not before (`DetectsAt`). At each event a node
reports, to every other node, a pair of twins of each author it detects
there (`reports`): the pairs a stream exposes against the disk, the pairs
the disk then shows (`shownPairs`, `exposedPairs`), and a pair it is
given. Under synchrony from the start the reports of an honest node reach
every other honest node within `Δ` (`ReportsDelivered`), so a detection
by an honest node yields a report of twins of the author at every other
honest node within `Δ` (`ReportsWithin`). A node builds a block at an
event when the event is its build of the block and puts it on its disk
(`BuiltAt`); every block of an honest author is built by that author
(`Authentic`).

Definitions only.
-/

namespace LeanDag

namespace Node

namespace Sync

variable {Validator BlockId Payload : Type} [DecidableEq Validator] [LinearOrder BlockId]
variable (blk : BlockId → Block Validator BlockId Payload)
variable (ev : Payload → Finset (BlockId × BlockId)) [Fintype Validator] (f : ℕ)

/-- **Times are nondecreasing** along the trace. -/
def TimeMono (tr : Trace Validator BlockId) (time : ℕ → ℕ) : Prop :=
  ∀ i j, i ≤ j → j < tr.length → time i ≤ time j

/-- **`v` detects `X` at event `i`**: `X` is detected after the event and
not before. -/
def DetectsAt (tr : Trace Validator BlockId) (i : ℕ) (v X : Validator) : Prop :=
  X ∉ (stateBefore blk ev f tr i v).detected ∧ X ∈ (stateBefore blk ev f tr (i + 1) v).detected

/-- **The twin pairs a set of blocks shows**: the twins in it, and the
twins its blocks carry evidence of. -/
def shownPairs (S : Finset BlockId) : Finset (BlockId × BlockId) :=
  ((S ×ˢ S).filter fun p => Twins blk p.1 p.2) ∪
    S.biUnion fun i => (ev (blk i).payload).filter fun p => Twins blk p.1 p.2

/-- **The twin pairs a stream exposes against `S`**: a streamed block
outside `S` with its twin in `S`. -/
def exposedPairs (S : Finset BlockId) (L : List BlockId) : Finset (BlockId × BlockId) :=
  (L.toFinset ×ˢ S).filter fun p => p.1 ∉ S ∧ Twins blk p.1 p.2

/-- **The reports of an event**: the twin pairs, of authors not detected
before it, that the event exposes, that the disk then shows, or that it
reports. -/
def reports (me : Validator) (s : State Validator BlockId) (inp : Input Validator BlockId) :
    Finset (BlockId × BlockId) :=
  let cand : Finset (BlockId × BlockId) := match inp with
    | .announce _ _ => ∅
    | .chunk _ L => exposedPairs blk s.disk L ∪ shownPairs blk ev (step blk ev f me s inp).disk
    | .build _ => shownPairs blk ev (step blk ev f me s inp).disk
    | .report i j => {(i, j)}
  cand.filter fun p => Twins blk p.1 p.2 ∧ (blk p.1).creator ∉ s.detected

/-- **Reports are delivered within `Δ`**: a report of an honest node at
event `i` reaches every other honest node at an event by `time i + Δ`. -/
def ReportsDelivered (H : Finset Validator) (tr : Trace Validator BlockId) (time : ℕ → ℕ)
    (Δ : ℕ) : Prop :=
  ∀ i v inp, tr[i]? = some (v, inp) → v ∈ H →
    ∀ p ∈ reports blk ev f v (stateBefore blk ev f tr i v) inp, ∀ w ∈ H, w ≠ v →
      ∃ k, tr[k]? = some (w, .report p.1 p.2) ∧ time k ≤ time i + Δ

/-- **Reports within `Δ`**: when an honest node detects `X` at event `i`,
every other honest node is given a report of twins of `X` at an event by
`time i + Δ`. -/
def ReportsWithin (H : Finset Validator) (tr : Trace Validator BlockId) (time : ℕ → ℕ)
    (Δ : ℕ) : Prop :=
  ∀ i v X, v ∈ H → DetectsAt blk ev f tr i v X → ∀ w ∈ H, w ≠ v →
    ∃ k a b, tr[k]? = some (w, .report a b) ∧ Twins blk a b ∧ (blk a).creator = X ∧
      time k ≤ time i + Δ

/-- **`v` builds `x` at event `i`**: the event is `v`'s build of `x`, and
puts `x` on `v`'s disk. -/
def BuiltAt (tr : Trace Validator BlockId) (i : ℕ) (v : Validator) (x : BlockId) : Prop :=
  tr[i]? = some (v, .build x) ∧ x ∉ (stateBefore blk ev f tr i v).disk ∧
    x ∈ (stateBefore blk ev f tr (i + 1) v).disk

/-- **Honest blocks are authentic**: a block of an honest author is built
by that author in the trace. -/
def Authentic (H : Finset Validator) (tr : Trace Validator BlockId) : Prop :=
  ∀ c, (blk c).creator ∈ H → ∃ i, BuiltAt blk ev f tr i (blk c).creator c

end Sync

end Node

end LeanDag
