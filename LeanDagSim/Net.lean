import LeanDag.Node.Model.Step
import LeanDag.Node.Vote
import Mathlib.Data.Finset.Sort
/-!
# A simulated network of honest nodes

`docs/validator.md` §6. `n` nodes run one row of the scheme over a
network with a seeded schedule: before GST a message takes up to
`preMax` ticks, after it between `delayMin` and `delayMax`, and a timer
fires when it expires. A crashed node acts on nothing from its crash
time on. An equivocator is two copies of the honest program with the
same identity and different payloads, each sending to half the nodes,
so its twins are valid blocks; it acts on nothing from `byzUntil` on. A node's request for blocks goes to every
other node, and an answer to the node that asked. `simulate` runs the schedule and reports
what each honest node reached and committed, whether their decisions
agree, and whether every honest block is valid under the blocks
broadcast.
-/

namespace LeanDagSim

open LeanDag LeanDag.Node

/-- A row of the table by name, at `n`, `f` and `c`: its parameters and
its quorum. -/
def row? (name : String) (n f c : ℕ) : Option (Scheme.Params × ℕ) :=
  match name with
  | "cordial-miners" => some (Scheme.Params.cordialMinersPS n f, n - f)
  | "mysticeti" => some (Scheme.Params.mysticeti n f, n - f)
  | "blue-bottle" => some (Scheme.Params.blueBottlePS n f, n - f)
  | "orcaella" => some (Scheme.Params.orcaella n f c, n - f - c)
  | "nemo-nemo" => some (Scheme.Params.nemoNemo n c, n - c)
  | "hybrid-mysticeti" => some (Scheme.Params.hybridMysticeti n f c, n - f - c)
  | _ => none

/-- The rows the simulator knows. -/
def rows : List String :=
  ["cordial-miners", "mysticeti", "blue-bottle", "orcaella", "nemo-nemo", "hybrid-mysticeti"]

/-- **A scenario.** Times are in ticks. -/
structure Scenario where
  row : String := "mysticeti"
  n : ℕ := 4
  f : ℕ := 1
  c : ℕ := 0
  seed : ℕ := 1
  /-- The simulated time to run to. -/
  horizon : ℕ := 500
  /-- At most this many inputs are processed. -/
  fuel : ℕ := 10000000
  gst : ℕ := 0
  preMax : ℕ := 20
  delayMin : ℕ := 1
  delayMax : ℕ := 3
  timeout : ℕ := 10
  lag : ℕ := 2
  /-- Crashed nodes, with the time each crashes. -/
  crash : List (ℕ × ℕ) := []
  /-- Equivocating nodes. -/
  byz : List ℕ := []
  /-- The time from which equivocators act on nothing. A copy of the
  honest program drops blocks that claim its identity, so neither copy of
  an equivocator accepts blocks built on its twin; it stops building, and
  its pending blocks grow. -/
  byzUntil : ℕ := 200
  deriving Repr

/-- A block's identifier: a hash of its content. -/
def idOf {n : ℕ} (b : Block (Fin n) ℕ ℕ) : ℕ :=
  (hash (b.round, b.creator.val, b.refs.sort (· ≤ ·), b.payload)).toNat

/-- The configuration of node `me`, its payload `twin` at every round. -/
def cfgFor (sc : Scenario) (p : Scheme.Params) (q : ℕ) {n : ℕ} (hn : 0 < n) (me : Fin n)
    (twin : ℕ) : Config (Fin n) ℕ ℕ where
  p := p
  f := sc.f
  c := sc.c
  q := q
  me := me
  per := 1
  m := 1
  per_pos := Nat.one_pos
  m_pos := Nat.one_pos
  elect := fun k => ⟨k % n, Nat.mod_lt _ hn⟩
  elect_block := Slots.one_hblock _
  timeout := fun _ => sc.timeout
  σ := boundedSel
  idOf := idOf
  lag := sc.lag
  budget := 0
  payload := fun _ => twin

/-- An agent: a node, and which copy of it (`0` unless it equivocates). -/
structure Agent (n : ℕ) where
  node : Fin n
  twin : ℕ

/-- **What a simulation reports.** -/
structure Report where
  /-- The row was admissible at `n`, `f`, `c` and its quorum. -/
  admissible : Bool
  /-- The highest round each honest node built. -/
  tops : List (Option ℕ)
  /-- The decisions each honest node output, in order. -/
  commits : List (List (ℕ × Option ℕ))
  /-- Any two honest nodes' decisions are prefix-comparable. -/
  agree : Bool
  /-- Every honest block is valid at the row under the blocks broadcast. -/
  valid : Bool
  /-- The largest store any honest node held. -/
  maxStore : ℕ
  /-- The inputs processed. -/
  events : ℕ
  /-- The simulated time reached. -/
  time : ℕ

/-- Put an input in flight, behind those arriving no later. -/
def enqueue {α : Type} (e : ℕ × α) : List (ℕ × α) → List (ℕ × α)
  | [] => [e]
  | x :: xs => if e.1 < x.1 then e :: x :: xs else x :: enqueue e xs

section Run

variable {n : ℕ} (sc : Scenario) (p : Scheme.Params) (q : ℕ) (hn : 0 < n)

/-- The simulation's state: each agent's state, the inputs in flight, the
seed, each agent's decisions, the blocks broadcast by honest agents, all
blocks broadcast, the largest honest store, and the inputs processed. -/
structure World (n : ℕ) where
  agents : Array (Agent n)
  states : Array (State (Fin n) ℕ ℕ)
  queue : List (ℕ × ℕ × Input (Fin n) ℕ ℕ)
  gen : StdGen
  decisions : Array (List (ℕ × Option ℕ))
  honest : List (ℕ × Block (Fin n) ℕ ℕ)
  blocks : Std.TreeMap ℕ (Block (Fin n) ℕ ℕ) compare
  maxStore : ℕ
  events : ℕ
  time : ℕ

/-- Whether node `v` has crashed by time `t`. -/
def crashed (v t : ℕ) : Bool := sc.crash.any fun e => e.1 = v ∧ e.2 ≤ t

/-- Whether agent `a` receives what agent `src` broadcasts. -/
def receives (a src : Agent n) : Bool :=
  a.node ≠ src.node &&
    (!(sc.byz.contains src.node.val) || (src.twin = 0) == (a.node.val < n / 2))

/-- A message delay at time `t`. -/
def delay (t : ℕ) (g : StdGen) : ℕ × StdGen :=
  if t < sc.gst then randNat g 1 (max 1 sc.preMax) else randNat g sc.delayMin sc.delayMax

/-- The inputs an agent's outputs at time `t` send. -/
def sends (agents : Array (Agent n)) (src : ℕ) (t : ℕ) (out : List (Output (Fin n) ℕ ℕ))
    (g : StdGen) : List (ℕ × ℕ × Input (Fin n) ℕ ℕ) × StdGen :=
  out.foldl (fun (acc : List (ℕ × ℕ × Input (Fin n) ℕ ℕ) × StdGen) o =>
    match o with
    | .broadcast id b =>
      (List.range agents.size).foldl (fun (acc : List (ℕ × ℕ × Input (Fin n) ℕ ℕ) × StdGen) d =>
        match agents[src]?, agents[d]? with
        | some s, some a =>
          if receives sc a s then
            let (dt, g') := delay sc t acc.2
            ((t + dt, d, .deliver id b) :: acc.1, g')
          else acc
        | _, _ => acc) acc
    | .setTimer r after => ((t + after, src, .timer r) :: acc.1, acc.2)
    | .fetch ids =>
      (List.range agents.size).foldl (fun (acc : List (ℕ × ℕ × Input (Fin n) ℕ ℕ) × StdGen) d =>
        match agents[src]?, agents[d]? with
        | some s, some a =>
          if a.node ≠ s.node then
            let (dt, g') := delay sc t acc.2
            ((t + dt, d, .fetchRequest s.node ids) :: acc.1, g')
          else acc
        | _, _ => acc) acc
    | .send peer id b =>
      (List.range agents.size).foldl (fun (acc : List (ℕ × ℕ × Input (Fin n) ℕ ℕ) × StdGen) d =>
        match agents[d]? with
        | some a =>
          if a.node = peer then
            let (dt, g') := delay sc t acc.2
            ((t + dt, d, .deliver id b) :: acc.1, g')
          else acc
        | none => acc) acc
    | _ => acc) ([], g)

/-- Process at most `fuel` inputs, in order of arrival, up to the horizon. -/
def loop : ℕ → World n → World n
  | 0, w => w
  | fuel + 1, w =>
    match w.queue with
    | [] => w
    | (t, d, i) :: rest =>
      if t > sc.horizon then { w with time := t } else
      match w.agents[d]?, w.states[d]? with
      | some a, some st =>
        if crashed sc a.node.val t || (sc.byz.contains a.node.val && sc.byzUntil ≤ t) then
          loop fuel { w with queue := rest, time := t } else
        let cfg := cfgFor sc p q hn a.node a.twin
        let r := step cfg st i
        let (msgs, g) := sends sc w.agents d t r.2 w.gen
        let isHonest := !(sc.byz.contains a.node.val)
        let bcast := r.2.filterMap fun
          | .broadcast id b => some (id, b)
          | _ => none
        let decs := r.2.filterMap fun
          | .commit k x => some (k, x)
          | _ => none
        loop fuel
          { agents := w.agents
            states := w.states.set! d r.1
            queue := msgs.foldl (fun q e => enqueue e q) rest
            gen := g
            decisions := w.decisions.modify d (· ++ decs)
            honest := if isHonest then w.honest ++ bcast else w.honest
            blocks := bcast.foldl (fun m e => m.insert e.1 e.2) w.blocks
            maxStore := if isHonest then max w.maxStore r.1.store.ids.card else w.maxStore
            events := w.events + 1
            time := t }
      | _, _ => loop fuel { w with queue := rest }

end Run

/-- Any two lists prefix-comparable. -/
def comparable {α : Type} [BEq α] (ls : List (List α)) : Bool :=
  ls.all fun a => ls.all fun b => a.isPrefixOf b || b.isPrefixOf a

/-- **Run a scenario.** -/
def simulate (sc : Scenario) : Report :=
  let empty : Report := ⟨false, [], [], true, true, 0, 0, 0⟩
  match row? sc.row sc.n sc.f sc.c with
  | none => empty
  | some (p, q) =>
    if hn : 0 < sc.n then
      let n := sc.n
      let honestAgents : List (Agent n) := (List.finRange n).map fun v => ⟨v, 0⟩
      let twins : List (Agent n) := (List.finRange n).filterMap fun v =>
        if sc.byz.contains v.val then some ⟨v, 1⟩ else none
      let agents := (honestAgents ++ twins).toArray
      let cfg0 := cfgFor sc p q hn ⟨0, hn⟩ 0
      if ¬ cfg0.Admissible then empty else
      let w0 : World n :=
        { agents := agents
          states := agents.map fun a => State.init (cfgFor sc p q hn a.node a.twin)
          queue := (List.range agents.size).map fun d => (0, d, .start)
          gen := mkStdGen sc.seed
          decisions := agents.map fun _ => []
          honest := []
          blocks := ∅
          maxStore := 0
          events := 0
          time := 0 }
      let w := loop sc p q hn sc.fuel w0
      let honestIdx := (List.range n).filter fun v => !(sc.byz.contains v)
      let decs := honestIdx.map fun v => w.decisions[v]?.getD []
      let junk : Block (Fin n) ℕ ℕ := ⟨0, ⟨0, hn⟩, ∅, 0⟩
      let valid := w.honest.all fun e =>
        decide (rowValid q (fun i => w.blocks.getD i junk) e.2)
      { admissible := true
        tops := honestIdx.map fun v => (w.states[v]?.map (·.top)).getD none
        commits := decs
        agree := comparable decs
        valid := valid
        maxStore := w.maxStore
        events := w.events
        time := w.time }
    else empty

end LeanDagSim
