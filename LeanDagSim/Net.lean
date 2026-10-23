import LeanDag.Node.Model.Step
import LeanDag.Node.Vote
import Mathlib.Data.Finset.Sort
/-!
# A simulated network of honest nodes

`docs/validator.md` §6. `n` nodes run one row of the scheme over a
network with a seeded schedule: before GST a message takes up to
`preMax` ticks, after it between `delayMin` and `delayMax`, and a timer
fires when it expires. A crashed node acts on nothing from its crash
time on. A node with an outage is down for a while: it loses what
arrives meanwhile and the timers it set before, and then restarts from
its state. An equivocator is two copies of the honest program with the
same identity and different payloads, each sending to half the nodes, so
its twins are valid blocks; it acts on nothing from `byzUntil` on. A
node's request for blocks goes to the peer it names, and an answer to
the node that asked. `simulate` runs the schedule and reports what each
honest node reached and committed, whether their decisions agree, and
whether every honest block above round `0` is valid under the blocks the
nodes made. An attacker (`Scenario.adv`) runs the honest program and
mounts `Scenario.attacks`; the network checks signatures
(`Scenario.verify`), which is what the claims about traces assume of
authentication.
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

/-- **An attack** a Byzantine node of `Scenario.adv` mounts, besides running
the honest program. -/
inductive Attack where
  /-- With each block, broadcast one with no references, one referencing
  a block that does not exist, and one under an identifier that is not its
  hash. -/
  | invalidBlocks
  /-- With each block, broadcast a block in the next node's name. -/
  | forgedAuthor
  /-- Instead of each block, send each other node its own twin of it,
  with its own payload; its later blocks reference the block itself. -/
  | twinSplit
  deriving Repr, DecidableEq

/-- **A scenario.** Times are in ticks. -/
structure Scenario where
  row : String := "mysticeti"
  n : ℕ := 4
  f : ℕ := 1
  c : ℕ := 0
  seed : ℕ := 1
  /-- The simulated time to run to. -/
  horizon : ℕ := 500
  /-- Rounds between slot rounds. -/
  per : ℕ := 1
  /-- At most this many inputs are processed. -/
  fuel : ℕ := 10000000
  gst : ℕ := 0
  preMax : ℕ := 20
  delayMin : ℕ := 1
  delayMax : ℕ := 3
  timeout : ℕ := 10
  /-- Crashed nodes, with the time each crashes. -/
  crash : List (ℕ × ℕ) := []
  /-- Outages `(v, a, b)`: node `v` is down from `a` until `b`, and
  restarts at `b`. -/
  outages : List (ℕ × ℕ × ℕ) := []
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
  /-- Byzantine nodes that run the honest program and mount `attacks`. -/
  adv : List ℕ := []
  /-- The attacks the nodes of `adv` mount. -/
  attacks : List Attack := []
  /-- Whether the network checks signatures: a block in an honest author's
  name is one that author made. -/
  verify : Bool := true
  /-- Slow nodes: every message to or from one takes at least `slowDelay`
  ticks past GST, and before `slowUntil` if set. -/
  slow : List ℕ := []
  slowDelay : ℕ := 0
  slowUntil : Option ℕ := none
  /-- The leader schedule, cycled, if not round robin. -/
  leaders : List ℕ := []
  deriving Repr

/-- Whether node `v` is honest: neither an equivocator nor an attacker. -/
def Scenario.honest (sc : Scenario) (v : ℕ) : Bool :=
  !(sc.byz.contains v) && !(sc.adv.contains v)

/-- A block's identifier: a hash of its content. -/
def idOf {n : ℕ} (b : Block (Fin n) ℕ ℕ) : ℕ :=
  (hash (b.round, b.creator.val, b.refs.sort (· ≤ ·), b.payload)).toNat % 2 ^ 62

/-- The configuration of node `me`, its payload `twin` at every round. -/
def cfgFor (sc : Scenario) (p : Scheme.Params) (q : ℕ) {n : ℕ} (hn : 0 < n) (me : Fin n)
    (twin : ℕ) : Config (Fin n) ℕ ℕ where
  p := p
  f := sc.f
  c := sc.c
  q := q
  me := me
  per := max sc.per 1
  m := 1
  per_pos := Nat.lt_of_lt_of_le Nat.one_pos (le_max_right _ _)
  m_pos := Nat.one_pos
  elect := fun k =>
    if sc.leaders.isEmpty then ⟨k % n, Nat.mod_lt _ hn⟩
    else ⟨sc.leaders.getD (k % sc.leaders.length) 0 % n, Nat.mod_lt _ hn⟩
  elect_block := Slots.one_hblock _
  timeout := fun _ => sc.timeout
  σ := boundedSel
  idOf := idOf
  payload := fun _ => twin

/-- An agent: a node, and which copy of it (`0` unless it equivocates). -/
structure Agent (n : ℕ) where
  node : Fin n
  twin : ℕ

/-- **Timing measurements** of the honest nodes, for the liveness
conditions (`docs/validator.md` §5): when each built each round,
decided each slot and accepted each block of another honest author, the
honest blocks delivered and kept neither on its disk nor pending, and
the fetches asked for. -/
structure Stats where
  /-- Each honest node's own blocks: the node, the round and the time. -/
  built : List (ℕ × ℕ × ℕ) := []
  /-- Each honest node's decisions: the node, the slot and the time. -/
  decided : List (ℕ × ℕ × ℕ) := []
  /-- The blocks of other honest authors each honest node accepted: the
  node, the round and the time. -/
  accepted : List (ℕ × ℕ × ℕ) := []
  /-- Honest-authored blocks delivered to an honest node, new, that it
  neither put on its disk nor kept pending. -/
  notKept : ℕ := 0
  /-- The fetches honest nodes asked for, and the identifiers in them. -/
  fetches : ℕ := 0
  fetched : ℕ := 0
  deriving Inhabited

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
  /-- The inputs the signature checks dropped. -/
  dropped : ℕ
  /-- The largest disk any honest node held. -/
  maxDisk : ℕ
  /-- The most pending blocks any honest node held. -/
  maxPending : ℕ
  /-- The inputs processed. -/
  events : ℕ
  /-- The simulated time reached. -/
  time : ℕ
  /-- The timing measurements. -/
  stats : Stats := {}
  /-- Each honest node's final state, in brief: top, own block, next
  undecided slot, the authors its disk holds at the top and the two
  rounds above, its pending blocks (author, round, references missing,
  payload), the timers fired, whether it can build and its references
  reach, and the blocks in its memory, from which round, and on disk. -/
  final : List String := []

/-- The key of an input in flight: its arrival time, then the order in
which it was sent, so inputs arriving together keep that order. -/
def queueKey (t seq : ℕ) : ℕ := t * 2 ^ 32 + seq

/-- The arrival time of a key. -/
def keyTime (k : ℕ) : ℕ := k / 2 ^ 32

/-- Put inputs in flight, numbered from `seq` on. -/
def enqueueAll {α : Type} (q : Std.TreeMap ℕ α compare) (seq : ℕ) (es : List (ℕ × α)) :
    Std.TreeMap ℕ α compare × ℕ :=
  es.foldl (fun acc e => (acc.1.insert (queueKey e.1 acc.2) e.2, acc.2 + 1)) (q, seq)

section Run

variable {n : ℕ} (sc : Scenario) (p : Scheme.Params) (q : ℕ) (hn : 0 < n)

/-- The simulation's state: each agent's state, the inputs in flight, the
seed, each agent's decisions (the latest first), the honest agents' own
blocks, the blocks each agent made or sent in its own name under their
hash, every block broadcast or sent under its hash, the largest honest
disk, and the inputs processed. -/
structure World (n : ℕ) where
  agents : Array (Agent n)
  states : Array (State (Fin n) ℕ ℕ)
  /-- The inputs in flight, by `queueKey`: the agent and the input. -/
  queue : Std.TreeMap ℕ (ℕ × Input (Fin n) ℕ ℕ) compare
  /-- The number of inputs put in flight so far. -/
  seq : ℕ
  gen : StdGen
  decisions : Array (List (ℕ × Option ℕ))
  honest : List (ℕ × Block (Fin n) ℕ ℕ)
  blocks : Std.TreeMap ℕ (Block (Fin n) ℕ ℕ) compare
  seen : Std.TreeMap ℕ (Block (Fin n) ℕ ℕ) compare
  maxDisk : ℕ
  maxPending : ℕ
  events : ℕ
  time : ℕ
  /-- The withheld block, once built. -/
  withheld : Option (ℕ × Block (Fin n) ℕ ℕ)
  /-- The inputs the signature checks dropped. -/
  dropped : ℕ
  /-- The timing measurements. -/
  stats : Stats

/-- Whether node `v` is down at time `t`: crashed by then, or in an
outage. -/
def isDown (v t : ℕ) : Bool :=
  sc.crash.any (fun e => e.1 = v ∧ e.2 ≤ t) ||
    sc.outages.any fun e => e.1 = v ∧ e.2.1 ≤ t ∧ t < e.2.2

/-- Whether node `v` loses a timer it sets at `t` to fire at `t'`: an
outage of `v` begins after `t` and by `t'`. -/
def timerLost (v t t' : ℕ) : Bool :=
  sc.outages.any fun e => e.1 = v ∧ t < e.2.1 ∧ e.2.1 ≤ t'

/-- Whether agent `a` receives what agent `src` broadcasts. -/
def receives (a src : Agent n) : Bool :=
  a.node ≠ src.node &&
    (!(sc.byz.contains src.node.val) || (src.twin = 0) == (a.node.val < n / 2))

/-- A message delay at time `t`. -/
def delay (t : ℕ) (g : StdGen) : ℕ × StdGen :=
  if t < sc.gst then randNat g 1 (max 1 sc.preMax) else randNat g sc.delayMin sc.delayMax

/-- A message delay at time `t` from node `src` to node `dst`, slow if
either is. -/
def delayAt (src dst t : ℕ) (g : StdGen) : ℕ × StdGen :=
  let (dt, g') := delay sc t g
  if sc.gst ≤ t && (sc.slowUntil.all (t < ·)) && (sc.slow.contains src || sc.slow.contains dst) then
    (max dt sc.slowDelay, g')
  else (dt, g')

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
            let (dt, g') := delayAt sc s.node.val a.node.val t acc.2
            ((t + dt, d, .deliver id b) :: acc.1, g')
          else acc
        | _, _ => acc) acc
    | .setTimer r after =>
      if (agents[src]?.map fun s => timerLost sc s.node.val t (t + after)).getD false then acc
      else ((t + after, src, .timer r) :: acc.1, acc.2)
    | .fetch peer r ids =>
      (List.range agents.size).foldl (fun (acc : List (ℕ × ℕ × Input (Fin n) ℕ ℕ) × StdGen) d =>
        match agents[src]?, agents[d]? with
        | some s, some a =>
          if a.node = peer then
            let (dt, g') := delayAt sc s.node.val a.node.val t acc.2
            ((t + dt, d, .fetchRequest s.node r ids) :: acc.1, g')
          else acc
        | _, _ => acc) acc
    | .send peer id b =>
      (List.range agents.size).foldl (fun (acc : List (ℕ × ℕ × Input (Fin n) ℕ ℕ) × StdGen) d =>
        match agents[d]? with
        | some a =>
          if a.node = peer then
            let (dt, g') := delayAt sc ((agents[src]?.map (·.node.val)).getD src) a.node.val t acc.2
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

/-- Two blocks alike. -/
def sameBlock (b c : Block (Fin n) ℕ ℕ) : Bool :=
  b.round == c.round && b.creator == c.creator && decide (b.refs = c.refs) && b.payload == c.payload

/-- **A block passes the signature check**: an honest author made it. -/
def authentic (w : World n) (id : ℕ) (b : Block (Fin n) ℕ ℕ) : Bool :=
  !(sc.honest b.creator.val) || (w.blocks.get? id).any (sameBlock b)

/-- **The signature check** on an input: a block in an honest author's
name is one it made. -/
def checked (w : World n) : Input (Fin n) ℕ ℕ → Option (Input (Fin n) ℕ ℕ)
  | .deliver id b => if authentic sc w id b then some (.deliver id b) else none
  | i => some i

/-- **An attacker's outputs**: the honest program's outputs, changed by
the attacks. -/
def attacked (out : List (Output (Fin n) ℕ ℕ)) : List (Output (Fin n) ℕ ℕ) :=
  let has (x : Attack) := sc.attacks.contains x
  out.flatMap fun (o : Output (Fin n) ℕ ℕ) => match o with
    | .broadcast _ b =>
      let junk : List (Output (Fin n) ℕ ℕ) := if has .invalidBlocks then
          let b₁ : Block (Fin n) ℕ ℕ := { b with refs := ∅, payload := 1 }
          let b₂ : Block (Fin n) ℕ ℕ := { b with refs := {123456789}, payload := 2 }
          let b₃ : Block (Fin n) ℕ ℕ := { b with payload := 3 }
          [.broadcast (idOf b₁) b₁, .broadcast (idOf b₂) b₂, .broadcast (idOf b₃ + 1) b₃]
        else []
      let forged : List (Output (Fin n) ℕ ℕ) := if has .forgedAuthor then
          let v : Fin n := ⟨(b.creator.val + 1) % n, Nat.mod_lt _ (Fin.pos b.creator)⟩
          let b₄ : Block (Fin n) ℕ ℕ := { b with creator := v, payload := 4 }
          [.broadcast (idOf b₄) b₄]
        else []
      if has .twinSplit then
        ((List.finRange n).filterMap fun v =>
          if v = b.creator then none else
          let bv : Block (Fin n) ℕ ℕ := { b with payload := 200 + v.val }
          some (.send v (idOf bv) bv)) ++ junk ++ forged
      else o :: junk ++ forged
    | o => [o]

/-- Process at most `fuel` inputs, in order of arrival, up to the horizon. -/
def loop : ℕ → World n → World n
  | 0, w => w
  | fuel + 1, w =>
    match w.queue.minEntry? with
    | none => w
    | some (key, (d, i)) =>
      let t := keyTime key
      let rest := w.queue.erase key
      if t > sc.horizon then { w with time := t } else
      match w.agents[d]?, w.states[d]? with
      | some a, some st =>
        if isDown sc a.node.val t || (sc.byz.contains a.node.val && sc.byzUntil ≤ t) then
          loop fuel { w with queue := rest, time := t } else
        match (if sc.verify then checked sc w i else some i) with
        | none => loop fuel { w with queue := rest, time := t, dropped := w.dropped + 1 }
        | some i =>
        let cfg := cfgFor sc p q hn a.node a.twin
        let r := step cfg st i
        let out := if sc.adv.contains a.node.val then attacked sc r.2 else r.2
        let (out, extra, wh) := withholding sc w.agents d t out w.withheld
        let (msgs, g) := sends sc w.agents d t out w.gen
        let msgs := extra ++ msgs
        let isHonest := sc.honest a.node.val
        let own := r.2.filterMap fun
          | .persist id b => some (id, b)
          | _ => none
        let sent := out.filterMap fun
          | .broadcast id b => if id = idOf b ∧ b.creator = a.node then some (id, b) else none
          | .send _ id b => if id = idOf b ∧ b.creator = a.node then some (id, b) else none
          | _ => none
        let seen := out.filterMap fun
          | .broadcast id b => if id = idOf b then some (id, b) else none
          | .send _ id b => if id = idOf b then some (id, b) else none
          | _ => none
        let decs := r.2.filterMap fun
          | .commit k x => some (k, x)
          | _ => none
        let ss := w.stats
        let ss : Stats := if isHonest then
            let fs := r.2.filterMap fun | .fetch _ _ ids => some ids.length | _ => none
            let ss := { ss with
              built := own.map (fun e => (a.node.val, e.2.round, t)) ++ ss.built
              decided := decs.map (fun e => (a.node.val, e.1, t)) ++ ss.decided
              accepted := ((((match i with | .deliver id _ => [id] | _ => []) ++
                  st.pending.map Prod.fst).filter fun j =>
                    r.1.disk.map.contains j && !st.disk.map.contains j).filterMap fun j =>
                  let b := r.1.disk.blk j
                  if sc.honest b.creator.val ∧ b.creator ≠ a.node then some (a.node.val, b.round, t)
                  else none) ++ ss.accepted
              fetches := ss.fetches + fs.length
              fetched := ss.fetched + fs.foldl (· + ·) 0 }
            match i with
            | .deliver id b =>
              if sc.honest b.creator.val ∧ b.creator ≠ a.node ∧ id = idOf b ∧
                  !st.disk.map.contains id ∧ id ∉ st.pending.map Prod.fst ∧
                  !r.1.disk.map.contains id ∧ id ∉ r.1.pending.map Prod.fst then
                { ss with notKept := ss.notKept + 1 }
              else ss
            | _ => ss
          else ss
        let (queue, seq) := enqueueAll rest w.seq msgs
        loop fuel
          { agents := w.agents
            states := w.states.set! d r.1
            queue := queue
            seq := seq
            gen := g
            decisions := w.decisions.modify d (decs.reverse ++ ·)
            honest := if isHonest then own ++ w.honest else w.honest
            blocks := (own ++ sent).foldl (fun m e => m.insert e.1 e.2) w.blocks
            seen := (own ++ seen).foldl (fun m e => m.insert e.1 e.2) w.seen
            maxDisk := if isHonest then max w.maxDisk r.1.disk.map.size else w.maxDisk
            maxPending := if isHonest then max w.maxPending r.1.pending.length else w.maxPending
            events := w.events + 1
            time := t
            withheld := wh
            dropped := w.dropped
            stats := ss }
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
  let empty : Report := ⟨false, [], [], true, true, true, 0, 0, 0, 0, 0, {}, []⟩
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
      let q0 := enqueueAll ∅ 0 ((List.range agents.size).map (fun d => (0, d, .start)) ++
        sc.outages.flatMap fun e => ((List.range agents.size).filter fun d =>
          (agents[d]?.map (·.node.val)) = some e.1).map fun d => (e.2.2, d, .restart))
      let w0 : World n :=
        { agents := agents
          states := agents.map fun a => State.init (cfgFor sc p q hn a.node a.twin)
          queue := q0.1
          seq := q0.2
          gen := mkStdGen sc.seed
          decisions := agents.map fun _ => []
          honest := []
          blocks := ∅
          seen := ∅
          maxDisk := 0
          maxPending := 0
          events := 0
          time := 0
          withheld := none
          dropped := 0
          stats := {} }
      let w := loop sc p q hn sc.fuel w0
      let honestIdx := (List.range n).filter sc.honest
      let decs := honestIdx.map fun v => (w.decisions[v]?.getD []).reverse
      let junk : Block (Fin n) ℕ ℕ := ⟨0, ⟨0, hn⟩, ∅, 0⟩
      let valid := w.honest.all fun e =>
        e.2.round == 0 || decide (rowValid q (fun i => w.seen.getD i junk) e.2)
      { admissible := true
        tops := honestIdx.map fun v => (w.states[v]?.map (·.top)).getD none
        final := honestIdx.map fun v => match w.states[v]? with
          | some st =>
            let t := st.top.getD 0
            let auth (r : ℕ) := (authorsIn st.disk.toRecord st.disk.ids r).card
            let cf := cfgFor sc p q hn ⟨v % n, Nat.mod_lt _ hn⟩ 0
            let pend := st.pending.map fun e => (e.2.creator.val, e.2.round,
              (e.2.refs.filter fun j => j ∉ st.disk.ids).card, e.2.payload)
            let reach := reachReady cf st.memory (refsAt cf st.memory t st.own) t
            s!"node {v}: top {st.top} own {st.own.isSome} " ++
              s!"lo {st.lo} authors {auth t}/{auth (t + 1)}/{auth (t + 2)} " ++
              s!"pending {pend} fired {st.fired.sort (· ≤ ·)} " ++
              s!"builds {(tryBuild cf st).isSome} reach {reach} " ++
              s!"memory {st.memory.ids.card} from {st.floor} disk {st.disk.ids.card}"
          | none => s!"node {v}: none"
        commits := decs
        agree := agreeAt decs
        prefixes := comparable decs
        valid := valid
        dropped := w.dropped
        maxDisk := w.maxDisk
        maxPending := w.maxPending
        events := w.events
        time := w.time
        stats := w.stats }
    else empty

/-- **Recovery from an outage** of node `v` ending at `b`: the highest
round an honest node built by `b`, the first time from `b` on that `v`
built above it, and the first time from `b` on that any honest node
decided a slot. -/
def recovery (r : Report) (v b : ℕ) : ℕ × Option ℕ × Option ℕ :=
  let R := (r.stats.built.filter (·.2.2 ≤ b)).foldl (fun m e => max m e.2.1) 0
  let above := (r.stats.built.filter fun e => e.1 = v ∧ R < e.2.1 ∧ b ≤ e.2.2).map (·.2.2)
  let decs := (r.stats.decided.filter fun e => b ≤ e.2.2).map (·.2.2)
  (R, above.min?, decs.min?)

end LeanDagSim
