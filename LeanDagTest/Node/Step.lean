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
rounds and skip its slots, over a short run and over a long one. With
node `3` down and node `2` crashing for a while, losing what is sent to
it, the others stall without a quorum; once node `2` restarts, the
resent blocks bring it the history it lost and the chain restarts.
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
  xp := ⟨fun _ => ∅, fun _ => ∅⟩
  payload := fun _ _ _ => ()

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

/-- The inputs a node's outputs at time `t` send: each broadcast block to
every other node, each request and each answer to its peer, a tick
later, and each timer back to the node when it expires. -/
def sends (t : ℕ) (src : Fin 4) (out : List (Output (Fin 4) ℕ Unit)) :
    List (ℕ × Fin 4 × Input (Fin 4) ℕ Unit) :=
  out.flatMap fun
    | .broadcast id b =>
      ((List.finRange 4).filter (· ≠ src)).map fun d => (t + 1, d, .deliver src id b)
    | .setTimer r after => [(t + after, src, .timer r)]
    | .sync peer r fr ids => [(t + 1, peer, .syncRequest src r fr ids)]
    | .stream peer L => [(t + 1, peer, .stream src L)]
    | _ => []

/-- The commits among a node's outputs. -/
def commitsOf (out : List (Output (Fin 4) ℕ Unit)) : List (ℕ × Option ℕ) :=
  out.filterMap fun
    | .commit k d => some (k, d)
    | _ => none

/-- Process at most `fuel` inputs in order of arrival; a node down at an
input's time loses it. -/
def run (down : ℕ → Fin 4 → Bool) : ℕ → Net → Net
  | 0, net => net
  | fuel + 1, net =>
    match net.queue with
    | [] => net
    | (t, d, i) :: rest =>
      if down t d then run down fuel { net with queue := rest } else
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
def up : Net := run (fun _ _ => false) 100 net0

/-- Every decision is a commit, and any two nodes' decisions agree. -/
def allCommit (net : Net) : Bool :=
  agree net && (List.finRange 4).all fun d => (net.commits d).all fun e => e.2.isSome

/-- info: [some 8, some 8, some 8, some 8] -/
#guard_msgs in
#eval tops up

/-- info: [[0, 1, 2, 3, 4, 5], [0, 1, 2, 3, 4, 5], [0, 1, 2, 3, 4, 5], [0, 1, 2, 3, 4, 5]] -/
#guard_msgs in
#eval slotsOut up

/-- info: true -/
#guard_msgs in
#eval allCommit up

/-! ## Node `3` down

Node `3` leads slot `3`. The others build round `4` only when the timer
of round `3` fires, skip slot `3`, and commit the slots around it. -/

/-- The network after `170` inputs, node `3` down. -/
def down3 : Net := run (fun _ d => d = 3) 170 net0

/-- info: [some 12, some 12, some 12, none] -/
#guard_msgs in
#eval tops down3

/--
info: [(0, true), (1, true), (2, true), (3, false), (4, true), (5, true), (6, true), (7, false), (8, true), (9, true),
  (10, true), (11, false)]
-/
#guard_msgs in
#eval (down3.commits 0).map fun e => (e.1, e.2.isSome)

/-- info: [12, 12, 12, 0] -/
#guard_msgs in
#eval (List.finRange 4).map fun d => (down3.commits d).length

/-- info: true -/
#guard_msgs in
#eval agree down3

/-! ## A long run, node `3` down

Over `392` slots every fourth slot, node `3`'s, is skipped, and each
disk holds one block of each of the three nodes up at each round, less
those still in flight. -/

/-- The network after `5300` inputs, node `3` down. -/
def long3 : Net := run (fun _ d => d = 3) 5300 net0

/-- info: ([some 392, some 392, some 392, none], 392, 98, true) -/
#guard_msgs in
#eval (tops long3, (long3.commits 0).length, ((long3.commits 0).filter (·.2.isNone)).length,
  agree long3)

/-- info: [1179, 1179, 1179] -/
#guard_msgs in
#eval [0, 1, 2].map fun d : Fin 4 => (long3.states d).disk.ids.card

/-! ## Node `3` down, node `2` crashing

Node `2` is down from time `20` and restarts at `60`, losing what is sent
to it meanwhile. Without it nodes `0` and `1` lack a quorum and stall,
resending their top blocks each timeout. Once node `2` restarts it
receives them, syncs the blocks it lost, builds the rounds it missed,
and the three go on deciding. -/

/-- Node `3` down; node `2` down from `20` on. -/
def gone2 (t : ℕ) (d : Fin 4) : Bool := d = 3 || (d = 2 && 20 ≤ t)

/-- Node `3` down; node `2` down from `20` to `60`. -/
def crash2 (t : ℕ) (d : Fin 4) : Bool := d = 3 || (d = 2 && 20 ≤ t && t < 60)

/-- The network after `400` inputs, node `2` never back. -/
def stalled : Net := run gone2 400 net0

/-- The network after `400` inputs, node `2` restarting at `60`. -/
def restarted : Net :=
  run crash2 400 { net0 with queue := net0.queue ++ [(60, 2, .restart)] }

/-- info: ([some 5, some 5, some 4, none], [4, 4, 4, 0], true) -/
#guard_msgs in
#eval (tops stalled, (List.finRange 4).map fun d => (stalled.commits d).length, agree stalled)

/-- info: ([some 28, some 28, some 28, none], [28, 28, 28, 0], true) -/
#guard_msgs in
#eval (tops restarted, (List.finRange 4).map fun d => (restarted.commits d).length,
  agree restarted)

end Node

end LeanDagTest
