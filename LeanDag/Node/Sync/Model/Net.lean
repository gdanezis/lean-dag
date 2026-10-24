import LeanDag.Node.Sync.Model.Check
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
/-!
# Sync by causal streams — the node and the network

`docs/sync.md` §3. A node keeps one sync for each other node `u`: its
target is the highest block that `u` announced, that the node does not
hold, and whose history passes the checks (`State.target`, `Admits`). A
piece of `u`'s stream is taken in by `absorb`, keeping only blocks of the
target's history. The authors it exposes, and the authors the disk
catches (`caught`), are detected, and their targets dropped; so are the
authors of reported twins. The node's own blocks pass the checks and are
built on its disk (`step`).

Pending blocks are the targets (`pending`): a streamed block that is not
ready on arrival is dropped, and the next pass asks for what is missing
(`pass`).

A trace lists the events, each a node and its input (`Trace`,
`stateBefore`). The blocks honest nodes receive from nodes outside `H`
before event `i` number `fromOutside`, and `RateBounded` caps those an
honest node receives from one outside node at one time.

Definitions only.
-/

namespace LeanDag

namespace Node

namespace Sync

variable {Validator BlockId Payload : Type} [DecidableEq Validator] [LinearOrder BlockId]
variable (blk : BlockId → Block Validator BlockId Payload)

variable (Validator BlockId) in
/-- **An input to a node.** -/
inductive Input where
  /-- `u` announces its latest block `t`. -/
  | announce (u : Validator) (t : BlockId)
  /-- A piece of `u`'s stream. -/
  | chunk (u : Validator) (L : List BlockId)
  /-- The node builds the block `x`. -/
  | build (x : BlockId)
  /-- A report that `i` and `j` are twins. -/
  | report (i j : BlockId)

variable (Validator BlockId) in
/-- **A node's state.** -/
structure State where
  /-- The blocks the node holds. -/
  disk : Finset BlockId
  /-- The authors it has detected equivocating. -/
  detected : Finset Validator
  /-- For each node, the target of its sync, if any. -/
  target : Validator → Option BlockId

/-- The state before start. -/
def State.init : State Validator BlockId := ⟨∅, ∅, fun _ => none⟩

/-- **`t` is above the target `cur`.** -/
def above (cur : Option BlockId) (t : BlockId) : Bool :=
  cur.all fun c => decide ((blk c).round < (blk t).round)

variable (ev : Payload → Finset (BlockId × BlockId)) [Fintype Validator] (f : ℕ)

/-- **Settle a state** on the disk `S` and the detected authors `D`: the
targets of detected authors and the targets held are dropped. -/
def settle (s : State Validator BlockId) (S : Finset BlockId) (D : Finset Validator) :
    State Validator BlockId :=
  ⟨S, D, fun a => if a ∈ D then none else (s.target a).filter fun c => decide (c ∉ S)⟩

variable (me : Validator)

/-- **The node's transition function.** An announced block of another
node not detected, by that node, not held, above its target and admitted,
becomes the target. A piece of a stream is taken in, keeping only blocks
of the target's history; the authors it exposes and the authors the disk
catches are detected. A block the node builds is its own, ready and
passing the checks. A report of twins detects their author. -/
def step (s : State Validator BlockId) : Input Validator BlockId → State Validator BlockId
  | .announce u t =>
    if u ≠ me ∧ u ∉ s.detected ∧ (blk t).creator = u ∧ t ∉ s.disk ∧ above blk (s.target u) t ∧
        Admits blk ev f t
    then { s with target := Function.update s.target u (some t) }
    else s
  | .chunk u L =>
    let L' := L.filter fun i => (s.target u).any fun t => decide (i ∈ historyFrom blk t)
    let S := absorb blk s.disk L'
    settle s S (s.detected ∪ exposes blk s.disk L' ∪ caught blk ev S)
  | .build x =>
    if (blk x).creator = me ∧ Ready blk s.disk x ∧ Checks blk ev f x then
      settle s (insert x s.disk) (s.detected ∪ caught blk ev (insert x s.disk))
    else s
  | .report i j =>
    if Twins blk i j then settle s s.disk (insert (blk i).creator s.detected) else s

/-- **Run a node** over its inputs. -/
def run (s : State Validator BlockId) (ins : List (Input Validator BlockId)) :
    State Validator BlockId :=
  ins.foldl (step blk ev f me) s

/-- **The pending blocks**: the nodes with a target. -/
def pending (s : State Validator BlockId) : Finset Validator :=
  Finset.univ.filter fun a => (s.target a).isSome

variable (Validator BlockId) in
/-- **A trace**: the events in order, each a node and its input. -/
abbrev Trace := List (Validator × Input Validator BlockId)

/-- The inputs of `v` in a trace. -/
def inputsOf (tr : Trace Validator BlockId) (v : Validator) : List (Input Validator BlockId) :=
  tr.filterMap fun e => if e.1 = v then some e.2 else none

/-- **The state of `v` before event `i`.** -/
def stateBefore (tr : Trace Validator BlockId) (i : ℕ) (v : Validator) : State Validator BlockId :=
  run blk ev f v State.init (inputsOf (tr.take i) v)

/-- **Honest nodes stream what they hold**: a piece of an honest node's
stream to an honest node holds blocks on the sender's disk. -/
def Faithful (H : Finset Validator) (tr : Trace Validator BlockId) : Prop :=
  ∀ i v u L, tr[i]? = some (v, .chunk u L) → v ∈ H → u ∈ H →
    ∀ x ∈ L, x ∈ (stateBefore blk ev f tr i u).disk

/-- The blocks of event `j` that `w` receives from `u`. -/
def chunkBlocks (tr : Trace Validator BlockId) (j : ℕ) (w u : Validator) : Finset BlockId :=
  match tr[j]? with
  | some (v, .chunk u' L) => if v = w ∧ u' = u then L.toFinset else ∅
  | _ => ∅

/-- The length of the piece of `u`'s stream that `w` receives at event
`j`. -/
def chunkLen (tr : Trace Validator BlockId) (j : ℕ) (w u : Validator) : ℕ :=
  match tr[j]? with
  | some (v, .chunk u' L) => if v = w ∧ u' = u then L.length else 0
  | _ => 0

/-- **The blocks honest nodes receive from outside `H`** before event
`i`. -/
def fromOutside (H : Finset Validator) (tr : Trace Validator BlockId)
    (i : ℕ) : ℕ :=
  ∑ j ∈ Finset.range i, ∑ w ∈ H, ∑ u ∈ Hᶜ, chunkLen tr j w u

/-- **Rate-bounded streams**: at each time, an honest node receives at
most `k` blocks from each node outside `H`. -/
def RateBounded (H : Finset Validator) (tr : Trace Validator BlockId)
    (time : ℕ → ℕ) (k : ℕ) : Prop :=
  ∀ τ, ∀ w ∈ H, ∀ u ∈ Hᶜ,
    ∑ j ∈ (Finset.range tr.length).filter (time · = τ), chunkLen tr j w u ≤ k

end Sync

end Node

end LeanDag
