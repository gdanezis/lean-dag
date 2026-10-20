import LeanDag.Node.Model.Step
import LeanDag.Node.Vote
import Mathlib.Data.Finset.Sort
/-!
# Four honest nodes at the Mysticeti row

Four nodes, `n = 4`, `f = 1`, at the Mysticeti row with one leader per
round, over a network that delivers every block a tick after it is sent
and fires each timer when it expires. Each node builds as soon as it
holds the round's leader block and three authors, and all four commit
the same slots. With node `3` down, the others wait out the timer at its
rounds and skip its slots. The nodes certify their decisions, and
garbage collection keeps each store a few rounds deep however long the
run.
-/

namespace LeanDagTest

namespace Node

open LeanDag LeanDag.Node

/-- A hash of a block, standing in for the environment's. -/
def idOf (b : Block (Fin 4) ℕ Unit) : ℕ :=
  (hash (b.round, b.creator.val, b.refs.sort (· ≤ ·))).toNat

/-- The Mysticeti row at `n = 4`, `f = 1`, for node `me`. -/
def cfg (me : Fin 4) : Config (Fin 4) ℕ Unit where
  p := Scheme.Params.mysticeti 4 1
  f := 1
  c := 0
  q := 3
  me := me
  per := 1
  m := 1
  per_pos := Nat.one_pos
  m_pos := Nat.one_pos
  elect := fun k => ⟨k % 4, Nat.mod_lt _ (by omega)⟩
  elect_block := Slots.one_hblock _
  timeout := fun _ => 10
  σ := boundedSel
  idOf := idOf
  lag := 2
  ahead := 8
  limit := none
  payload := fun _ => ()
  extend := fun h e => (hash (h, e.1, e.2)).toNat
  root := 0

/-- A network of four nodes: their states, the inputs in flight with the
time each arrives, ordered by it, and the commits each node output. -/
structure Net where
  states : Fin 4 → State (Fin 4) ℕ Unit
  queue : List (ℕ × Fin 4 × Input (Fin 4) ℕ Unit)
  commits : Fin 4 → List (ℕ × Option ℕ)

/-- Put an input in flight, behind those arriving no later. -/
def enqueue (e : ℕ × Fin 4 × Input (Fin 4) ℕ Unit) :
    List (ℕ × Fin 4 × Input (Fin 4) ℕ Unit) → List (ℕ × Fin 4 × Input (Fin 4) ℕ Unit)
  | [] => [e]
  | x :: xs => if e.1 < x.1 then e :: x :: xs else x :: enqueue e xs

/-- The inputs a node's outputs at time `t` send: each broadcast block
and each proposal to every other node a tick later, and each timer back
to the node when it expires. -/
def sends (t : ℕ) (src : Fin 4) (out : List (Output (Fin 4) ℕ Unit)) :
    List (ℕ × Fin 4 × Input (Fin 4) ℕ Unit) :=
  out.flatMap fun
    | .broadcast id b =>
      ((List.finRange 4).filter (· ≠ src)).map fun d => (t + 1, d, .deliver id b)
    | .propose k h =>
      ((List.finRange 4).filter (· ≠ src)).map fun d => (t + 1, d, .proposal src k h)
    | .setTimer r after => [(t + after, src, .timer r)]
    | _ => []

/-- The commits among a node's outputs. -/
def commitsOf (out : List (Output (Fin 4) ℕ Unit)) : List (ℕ × Option ℕ) :=
  out.filterMap fun
    | .commit k d => some (k, d)
    | _ => none

/-- Process at most `fuel` inputs in order of arrival; the nodes in
`down` never act. -/
def run (down : List (Fin 4)) : ℕ → Net → Net
  | 0, net => net
  | fuel + 1, net =>
    match net.queue with
    | [] => net
    | (t, d, i) :: rest =>
      if d ∈ down then run down fuel { net with queue := rest } else
      let r := step (cfg d) (net.states d) i
      run down fuel
        { states := Function.update net.states d r.1
          queue := (sends t d r.2).foldl (fun q e => enqueue e q) rest
          commits := Function.update net.commits d (net.commits d ++ commitsOf r.2) }

/-- All four nodes started at time `0`. -/
def net0 : Net :=
  { states := fun d => State.init (cfg d)
    queue := (List.finRange 4).map fun d => (0, d, .start)
    commits := fun _ => [] }

/-- The highest round each node built. -/
def tops (net : Net) : List (Option ℕ) := (List.finRange 4).map fun d => (net.states d).top

/-- The slots each node committed or skipped, in order. -/
def slotsOut (net : Net) : List (List ℕ) :=
  (List.finRange 4).map fun d => (net.commits d).map Prod.fst

/-- **Any two nodes' decisions are prefix-comparable.** -/
def agree (net : Net) : Bool :=
  (List.finRange 4).all fun d => (List.finRange 4).all fun e =>
    (net.commits d).isPrefixOf (net.commits e) || (net.commits e).isPrefixOf (net.commits d)

/-- The configuration is admissible. -/
example : (cfg 0).Admissible := by decide

/-! ## Everyone up -/

/-- The network after `100` inputs, everyone up. -/
def up : Net := run [] 100 net0

/-- Every decision is a commit, and any two nodes' decisions agree. -/
def allCommit (net : Net) : Bool :=
  agree net && (List.finRange 4).all fun d => (net.commits d).all fun e => e.2.isSome

/-- info: [some 6, some 5, some 5, some 6] -/
#guard_msgs in
#eval tops up

/-- info: [[0, 1, 2, 3], [0, 1, 2], [0, 1, 2], [0, 1, 2, 3]] -/
#guard_msgs in
#eval slotsOut up

/-- info: true -/
#guard_msgs in
#eval allCommit up

/-! ## Node `3` down

Node `3` leads slot `3`. The others build round `4` only when the timer
of round `3` fires, skip slot `3`, and commit the slots around it. -/

/-- The network after `170` inputs, node `3` down. -/
def down3 : Net := run [3] 170 net0

/-- info: [some 8, some 8, some 8, none] -/
#guard_msgs in
#eval tops down3

/--
info: [(0, true), (1, true), (2, true), (3, false), (4, true), (5, true), (6, true), (7, false)]
-/
#guard_msgs in
#eval (down3.commits 0).map fun e => (e.1, e.2.isSome)

/-- info: [8, 8, 8, 0] -/
#guard_msgs in
#eval (List.finRange 4).map fun d => (down3.commits d).length

/-- info: true -/
#guard_msgs in
#eval agree down3

/-! ## A long run, node `3` down

Over `252` rounds every fourth slot, node `3`'s, is skipped, and each
store holds nine to fifteen blocks, its horizon two to four rounds below
its top. -/

/-- The network after `5300` inputs, node `3` down. -/
def long3 : Net := run [3] 5300 net0

/-- info: ([some 252, some 252, some 252, none], 252, 63, true) -/
#guard_msgs in
#eval (tops long3, (long3.commits 0).length, ((long3.commits 0).filter (·.2.isNone)).length,
  agree long3)

/-- info: [(12, 249), (15, 248), (9, 250)] -/
#guard_msgs in
#eval [0, 1, 2].map fun d : Fin 4 => ((long3.states d).store.ids.card, (long3.states d).store.base)

end Node

end LeanDagTest
