import LeanDag.Node.Model.Step
import LeanDag.Node.Vote
import Mathlib.Data.Finset.Sort
/-!
# A simulated network of honest nodes

`docs/validator.md` §6. `n` nodes run one row of the scheme over a
network with a seeded schedule: before GST a message takes up to
`preMax` ticks, after it between `delayMin` and `delayMax`, and a timer
fires when it expires. A crashed node acts on nothing from its crash
time on; a recovering node acts on nothing while it is down, then
restarts, keeping only what it persisted, asks its peers for their bases,
and either skips to a round its store holds a quorum at or bootstraps
from the bases. An equivocator is two copies of the honest program with
the same identity and different payloads, each sending to half the
nodes, so its twins are valid blocks; it acts on nothing from `byzUntil`
on. A node's request for blocks goes to every other node, and an answer
to the node that asked. `simulate` runs the schedule and reports what
each honest node reached and committed, whether their decisions agree,
whether every honest block above round `0` is valid under the blocks the
nodes made, and how many skips and bootstraps the honest nodes made.
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
  /-- Recovering nodes `(v, down, up)`: node `v` is down from `down` and
  restarts at `up`. -/
  recover : List (ℕ × ℕ × ℕ) := []
  /-- Equivocating nodes. -/
  byz : List ℕ := []
  /-- The time from which equivocators act on nothing. A copy of the
  honest program drops blocks that claim its identity, so neither copy of
  an equivocator accepts blocks built on its twin; it stops building, and
  its pending blocks grow. -/
  byzUntil : ℕ := 200
  /-- A withholding attack `(z, v, R)`: node `z` holds back its round-`R`
  block `x`, sends its round-`R + 1` block, which references `x`, to `v`
  alone, reveals `x` to the others `revealAfter` ticks later, and never
  answers `v`'s requests for `x`. -/
  withhold : Option (ℕ × ℕ × ℕ) := none
  revealAfter : ℕ := 6
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
  /-- Two honest nodes that decide a slot decide it alike. -/
  agree : Bool
  /-- Any two honest nodes' decisions are prefix-comparable. -/
  prefixes : Bool
  /-- Every honest block above round `0` is valid at the row under the
  blocks the nodes made. -/
  valid : Bool
  /-- The skips the honest nodes made: a recovering node resuming at a
  round above its top. -/
  skips : ℕ
  /-- The bootstraps the honest nodes made. -/
  boots : ℕ
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
seed, each agent's decisions, the honest agents' own blocks, all agents'
own blocks, the largest honest store, the inputs processed, and the
honest agents' skips and bootstraps. -/
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
  /-- The withheld block, once built. -/
  withheld : Option (ℕ × Block (Fin n) ℕ ℕ)
  skips : ℕ
  boots : ℕ

/-- Whether node `v` has crashed by time `t`. -/
def crashed (v t : ℕ) : Bool :=
  sc.crash.any (fun e => e.1 = v ∧ e.2 ≤ t) ||
    sc.recover.any fun e => e.1 = v ∧ e.2.1 ≤ t ∧ t < e.2.2

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
    | .requestBase =>
      (List.range agents.size).foldl (fun (acc : List (ℕ × ℕ × Input (Fin n) ℕ ℕ) × StdGen) d =>
        match agents[src]?, agents[d]? with
        | some s, some a =>
          if a.node ≠ s.node then
            let (dt, g') := delay sc t acc.2
            ((t + dt, d, .baseRequest s.node) :: acc.1, g')
          else acc
        | _, _ => acc) acc
    | .propose k ds =>
      (List.range agents.size).foldl (fun (acc : List (ℕ × ℕ × Input (Fin n) ℕ ℕ) × StdGen) d =>
        match agents[src]?, agents[d]? with
        | some s, some a =>
          if receives sc a s then
            let (dt, g') := delay sc t acc.2
            ((t + dt, d, .proposal s.node k ds) :: acc.1, g')
          else acc
        | _, _ => acc) acc
    | .serveCert peer c =>
      (List.range agents.size).foldl (fun (acc : List (ℕ × ℕ × Input (Fin n) ℕ ℕ) × StdGen) d =>
        match agents[src]?, agents[d]? with
        | some s, some a =>
          if a.node = peer then
            let (dt, g') := delay sc t acc.2
            ((t + dt, d, .certOffer s.node c) :: acc.1, g')
          else acc
        | _, _ => acc) acc
    | .serveBase peer G bs =>
      (List.range agents.size).foldl (fun (acc : List (ℕ × ℕ × Input (Fin n) ℕ ℕ) × StdGen) d =>
        match agents[src]?, agents[d]? with
        | some s, some a =>
          if a.node = peer then
            let (dt, g') := delay sc t acc.2
            ((t + dt, d, .baseOffer s.node G bs) :: acc.1, g')
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

/-- **The withholding attack**, applied to agent `src`'s outputs at time
`t`: the outputs it keeps, the deliveries it adds, and the withheld
block. -/
def withholding (agents : Array (Agent n)) (src t : ℕ) (out : List (Output (Fin n) ℕ ℕ))
    (wh : Option (ℕ × Block (Fin n) ℕ ℕ)) :
    List (Output (Fin n) ℕ ℕ) × List (ℕ × ℕ × Input (Fin n) ℕ ℕ) × Option (ℕ × Block (Fin n) ℕ ℕ) :=
  match sc.withhold, agents[src]? with
  | some (z, v, R), some a =>
    if a.node.val ≠ z then (out, [], wh) else
    out.foldl (fun (acc : List (Output (Fin n) ℕ ℕ) × List (ℕ × ℕ × Input (Fin n) ℕ ℕ) ×
        Option (ℕ × Block (Fin n) ℕ ℕ)) o =>
      match o with
      | .broadcast id b =>
        if b.round = R then (acc.1, acc.2.1, some (id, b))
        else if b.round = R + 1 then
          let toV := (List.range agents.size).filterMap fun d =>
            match agents[d]? with
            | some a' => if a'.node.val = v then some (t + 1, d, .deliver id b) else none
            | none => none
          let reveal := match acc.2.2 with
            | some (xid, x) => (List.range agents.size).filterMap fun d =>
                match agents[d]? with
                | some a' =>
                  if a'.node.val ≠ v ∧ a'.node.val ≠ z then
                    some (t + sc.revealAfter, d, .deliver xid x)
                  else none
                | none => none
            | none => []
          (acc.1, acc.2.1 ++ toV ++ reveal, acc.2.2)
        else (acc.1 ++ [o], acc.2.1, acc.2.2)
      | .send peer id _ =>
        if peer.val = v ∧ (acc.2.2.map (·.1)) = some id then acc
        else (acc.1 ++ [o], acc.2.1, acc.2.2)
      | _ => (acc.1 ++ [o], acc.2.1, acc.2.2)) ([], [], wh)
  | _, _ => (out, [], wh)

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
        let (out, extra, wh) := withholding sc w.agents d t r.2 w.withheld
        let (msgs, g) := sends sc w.agents d t out w.gen
        let msgs := extra ++ msgs
        let isHonest := !(sc.byz.contains a.node.val)
        let own := r.2.filterMap fun
          | .persist id b => some (id, b)
          | _ => none
        let skip := st.recovering && !r.1.recovering
        let boot := match i with
          | .baseOffer .. => st.recovering && r.1.offers.isEmpty
          | _ => false
        let decs := r.2.filterMap fun
          | .commit k x => some (k, x)
          | _ => none
        loop fuel
          { agents := w.agents
            states := w.states.set! d r.1
            queue := msgs.foldl (fun q e => enqueue e q) rest
            gen := g
            decisions := w.decisions.modify d (· ++ decs)
            honest := if isHonest then w.honest ++ own else w.honest
            blocks := own.foldl (fun m e => m.insert e.1 e.2) w.blocks
            maxStore := if isHonest then max w.maxStore r.1.store.ids.card else w.maxStore
            events := w.events + 1
            time := t
            withheld := wh
            skips := if isHonest && skip then w.skips + 1 else w.skips
            boots := if isHonest && boot then w.boots + 1 else w.boots }
      | _, _ => loop fuel { w with queue := rest }

end Run

/-- Any two lists prefix-comparable. -/
def comparable {α : Type} [BEq α] (ls : List (List α)) : Bool :=
  ls.all fun a => ls.all fun b => a.isPrefixOf b || b.isPrefixOf a

/-- Any two lists of decisions agree at every slot both decide. -/
def agreeAt (ls : List (List (ℕ × Option ℕ))) : Bool :=
  ls.all fun a => ls.all fun b => a.all fun x => b.all fun y => x.1 != y.1 || x.2 == y.2

/-- **Run a scenario.** -/
def simulate (sc : Scenario) : Report :=
  let empty : Report := ⟨false, [], [], true, true, true, 0, 0, 0, 0, 0⟩
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
          queue := sc.recover.foldl (fun q e => enqueue (e.2.2, e.1, .restart) q)
            ((List.range agents.size).map fun d => (0, d, .start))
          gen := mkStdGen sc.seed
          decisions := agents.map fun _ => []
          honest := []
          blocks := ∅
          maxStore := 0
          events := 0
          time := 0
          withheld := none
          skips := 0
          boots := 0 }
      let w := loop sc p q hn sc.fuel w0
      let honestIdx := (List.range n).filter fun v => !(sc.byz.contains v)
      let decs := honestIdx.map fun v => w.decisions[v]?.getD []
      let junk : Block (Fin n) ℕ ℕ := ⟨0, ⟨0, hn⟩, ∅, 0⟩
      let valid := w.honest.all fun e =>
        e.2.round == 0 || decide (rowValid q (fun i => w.blocks.getD i junk) e.2)
      { admissible := true
        tops := honestIdx.map fun v => (w.states[v]?.map (·.top)).getD none
        commits := decs
        agree := agreeAt decs
        prefixes := comparable decs
        valid := valid
        skips := w.skips
        boots := w.boots
        maxStore := w.maxStore
        events := w.events
        time := w.time }
    else empty

end LeanDagSim
