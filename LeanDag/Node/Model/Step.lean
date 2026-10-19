import LeanDag.Node.Store
import Mathlib.Data.Finset.Sort
/-!
# An honest node — its transition function

`docs/validator.md` §3. `step cfg s i` is the node's response to the
input `i` in the state `s`: the new state and the outputs.

* **Receipt** (`deliver`): a block whose identifier is its hash, not the
  node's own, and new, waits in `pending` until its references are
  accepted; it is then accepted if it satisfies `rowValid q`, and
  dropped otherwise (`flush`).
* **Building** (`tryBuild`): round `r + 1` once the store holds `q`
  authors of round `r` and either the round's timer fired or the block
  would reach every leader block of a slot whose wave is at a vote round
  (`reachReady`) and certify one at a decision round (`certReady`). The
  block references one accepted block per author of round `r`, the
  node's own for itself and the least identifier otherwise; it is
  persisted, then broadcast, then the round's timer is set.
* **Deciding** (`decideStep`): `tryDecide` from the next undecided slot
  to the last slot whose decision round the store holds.

* **Fetching** (`walkLevel`, `missing`, `answer`): after a delivery, the missing part
  of the delivered block's history, walked through the pending blocks, is
  asked of every peer, once on account of each block that needs it; a
  request is answered with the blocks the store holds.
* **Collecting** (`collect`): the horizon rises to `Λ` below the lesser
  of the decided frontier and the node's round, and what lies below it is
  dropped.

* **Restarting** (`State.recover`): a crash keeps the store, the next
  slot and the top, and loses what is pending, the timers and the
  requests; the downtime counts as the top round's timer firing.
  `State.persisted` is what the node writes, and `resume` rebuilds a
  state from it.
* **Jumping** (`tryJump`, `jumpFills`): after a restart, a node two
  rounds or more behind the store's top fills the rounds in between with
  blocks of its own, each the references of another author's line plus
  its own block of the round below, persists them and sends one jump
  message; a receiver derives the same blocks from its own store and
  accepts them as it accepts delivered ones (`jumpIn`).

Rate limiting and bootstrap are not yet implemented: their inputs leave
the state unchanged.

Definitions only.
-/

namespace LeanDag

namespace Node

variable {Validator BlockId Payload : Type} [Fintype Validator] [DecidableEq Validator]
variable [LinearOrder BlockId]

variable (Validator BlockId Payload) in
/-- **A node's state.** -/
structure State where
  /-- The accepted blocks. -/
  store : Store Validator BlockId Payload
  /-- Blocks received whose references are not all accepted. -/
  pending : List (BlockId × Block Validator BlockId Payload)
  /-- The highest round the node built, once started. -/
  top : Option ℕ
  /-- The node's block at `top`. -/
  own : Option BlockId
  /-- The rounds whose timer fired. -/
  fired : Finset ℕ
  /-- The next undecided slot. -/
  lo : ℕ
  /-- The blocks asked for, each with the block whose history needed it
  and its own round. -/
  requested : List (BlockId × BlockId × ℕ)
  /-- Restarted, and not yet jumped. -/
  recovering : Bool

variable (cfg : Config Validator BlockId Payload)

/-- The node's genesis block. -/
def Config.genesis : Block Validator BlockId Payload := ⟨0, cfg.me, ∅, cfg.payload 0⟩

/-- The state before start. -/
def State.init : State Validator BlockId Payload :=
  ⟨Store.empty cfg.genesis, [], none, none, ∅, 0, [], false⟩

/-- **Accept a block**: below the horizon it is dropped; at the horizon it
is kept without its references, as the cut keeps it; above, it is kept if
it is new, its references are accepted, and it is valid at the row. -/
def accept (s : Store Validator BlockId Payload) (id : BlockId)
    (b : Block Validator BlockId Payload) : Store Validator BlockId Payload :=
  if h : id ∉ s.ids ∧ s.base ≤ b.round ∧ (s.base < b.round → b.refs ⊆ s.ids) ∧
      (s.base < b.round → ∀ j ∈ b.refs, (s.blk j).round + 1 = b.round) ∧
      (s.base < b.round → rowValid cfg.q (Function.update s.blk id b) b) then
    s.insert id b h.1 h.2.1 h.2.2.1 h.2.2.2.1
  else s

/-- A pending block is ready when it is at or below the horizon or its
references are accepted. -/
def ready (s : Store Validator BlockId Payload) (b : Block Validator BlockId Payload) : Bool :=
  decide (b.round ≤ s.base) || decide (b.refs ⊆ s.ids)

/-- **Accept what the pending blocks allow**, in passes, at most `fuel`. -/
def flush : ℕ → Store Validator BlockId Payload → List (BlockId × Block Validator BlockId Payload) →
    Store Validator BlockId Payload × List (BlockId × Block Validator BlockId Payload)
  | 0, s, pend => (s, pend)
  | fuel + 1, s, pend =>
    let split := pend.partition fun e => ready s e.2
    if split.1.isEmpty then (s, pend)
    else flush fuel (split.1.foldl (fun s e => accept cfg s e.1 e.2) s) split.2

/-- **The references of the node's next block**, above its block `o` at
round `r`: one accepted block per author of round `r`, `o` for the node
itself and the least identifier otherwise. -/
def refsFor (s : Store Validator BlockId Payload) (r : ℕ) (o : BlockId) : Finset BlockId :=
  let R := blocksAt s.toRecord r
  (creatorsOf s.blk R).image fun a =>
    if a = cfg.me then o else (Scheme.leastOf (R.filter fun i => (s.blk i).creator = a)).getD o

/-- **The reach test** for a block at round `r + 1` referencing `refs`:
for each slot whose wave has `r + 1` at or below its vote round, the
block reaches one of the slot's leader blocks. A leader block `m` rounds
below a reference lies within `m` steps of it, so the search stops
there. -/
def reachReady (s : Store Validator BlockId Payload) (refs : Finset BlockId) (r : ℕ) : Bool :=
  letI := cfg.slots
  (List.range cfg.p.voteOffset).all fun m =>
    if m ≤ r then
      (cfg.slotsAt (r - m)).all fun k =>
        decide (∃ L ∈ Scheme.candidatesIn s.toRecord s.view k,
          ∃ c ∈ refs, L ∈ historyUptoFrom s.blk m c)
    else true

/-- **The certificate test** for a block at round `r + 1` referencing
`refs`: where votes are certified a round later, for each slot whose
decision round is `r + 1`, the block carries `certThreshold` votes for
one of the slot's leader blocks. -/
def certReady (s : Store Validator BlockId Payload) (refs : Finset BlockId) (r : ℕ) : Bool :=
  letI := cfg.slots
  if cfg.p.voteIsCert then true
  else if cfg.p.voteOffset ≤ r then
    (cfg.slotsAt (r - cfg.p.voteOffset)).all fun k =>
      decide (∃ L ∈ Scheme.candidatesIn s.toRecord s.view k,
        cfg.p.certThreshold ≤
          (creatorsOf s.blk (refs.filter fun b => cfg.σ.Votes s.toRecord b L)).card)
  else true

/-- **Build the next round**, if the build rule allows it. -/
def tryBuild (s : State Validator BlockId Payload) :
    Option (State Validator BlockId Payload × List (Output Validator BlockId Payload)) :=
  match s.top, s.own with
  | some r, some o =>
    let refs := refsFor cfg s.store r o
    if cfg.q ≤ (authorsIn s.store.toRecord s.store.ids r).card ∧
        (r ∈ s.fired ∨ (reachReady cfg s.store refs r ∧ certReady cfg s.store refs r)) then
      let b : Block Validator BlockId Payload := ⟨r + 1, cfg.me, refs, cfg.payload (r + 1)⟩
      let id := cfg.idOf b
      if h : id ∉ s.store.ids ∧ s.store.base ≤ b.round ∧
          (s.store.base < b.round → b.refs ⊆ s.store.ids) ∧
          (s.store.base < b.round → ∀ j ∈ b.refs, (s.store.blk j).round + 1 = b.round) ∧
          rowValid cfg.q (Function.update s.store.blk id b) b then
        let st := s.store.insert id b h.1 h.2.1 h.2.2.1 h.2.2.2.1
        some ({ s with store := st, top := some (r + 1), own := some id },
          [.persist id b, .broadcast id b, .setTimer (r + 1) (cfg.timeout (r + 1))])
      else none
    else none
  | _, _ => none

/-- **Build while the rule allows**, at most `fuel` rounds. -/
def progress : ℕ → State Validator BlockId Payload →
    State Validator BlockId Payload × List (Output Validator BlockId Payload)
  | 0, s => (s, [])
  | fuel + 1, s =>
    match tryBuild cfg s with
    | some (s', out) => let r := progress fuel s'; (r.1, out ++ r.2)
    | none => (s, [])

/-- **The reference by `v`** of a block, the least if there are several. -/
def refBy (s : Store Validator BlockId Payload) (b : Block Validator BlockId Payload)
    (v : Validator) : Option BlockId :=
  Scheme.leastOf (b.refs.filter fun j => (s.blk j).creator = v)

/-- **A line**: from `j`, `d` rounds down along references by `j`'s
author, each above round `lo`; lowest first. -/
def lineDown (s : Store Validator BlockId Payload) (lo : ℕ) : ℕ → BlockId → Option (List BlockId)
  | 0, j => if j ∈ s.ids ∧ lo < (s.blk j).round then some [j] else none
  | d + 1, j =>
    if j ∈ s.ids ∧ lo < (s.blk j).round then
      ((refBy s (s.blk j) (s.blk j).creator).bind (lineDown s lo d)).map (· ++ [j])
    else none

/-- **The filled blocks along a line**, lowest first: each by `v1`, at its
line block's round, with that block's references and payload and the
filled block below, `prev` at the bottom. -/
def fillUp (idOf : Block Validator BlockId Payload → BlockId)
    (blk : BlockId → Block Validator BlockId Payload) (v1 : Validator) :
    BlockId → List BlockId → List (BlockId × Block Validator BlockId Payload)
  | _, [] => []
  | prev, l :: ls =>
    let b : Block Validator BlockId Payload :=
      ⟨(blk l).round, v1, insert prev (blk l).refs, (blk l).payload⟩
    (idOf b, b) :: fillUp idOf blk v1 (idOf b) ls

/-- **The blocks a jump message denotes** on a store (`docs/validator.md`
§3.5): `v1` resumes after its block `B1` along the line of `B2`, one
filled block per round in between; if the store holds `B1` at or above
its horizon, and the line above it. -/
def jumpFills (idOf : Block Validator BlockId Payload → BlockId) (s : Store Validator BlockId Payload)
    (v1 : Validator) (B1 B2 : BlockId) : Option (List (BlockId × Block Validator BlockId Payload)) :=
  if B1 ∈ s.ids ∧ (s.blk B1).creator = v1 ∧ s.base ≤ (s.blk B1).round ∧
      (s.blk B1).round < (s.blk B2).round then
    (lineDown s (s.blk B1).round ((s.blk B2).round - (s.blk B1).round - 1) B2).map
      (fillUp idOf s.blk v1 B1)
  else none

/-- **Accept blocks in turn**, each new, above the horizon, with its
references accepted one round below, and valid at the row; nothing if
one is not. -/
def insertAll (st : Store Validator BlockId Payload) :
    List (BlockId × Block Validator BlockId Payload) → Option (Store Validator BlockId Payload)
  | [] => some st
  | e :: l =>
    if h : e.1 ∉ st.ids ∧ st.base < e.2.round ∧ e.2.refs ⊆ st.ids ∧
        (∀ j ∈ e.2.refs, (st.blk j).round + 1 = e.2.round) ∧
        rowValid cfg.q (Function.update st.blk e.1 e.2) e.2 then
      insertAll (st.insert e.1 e.2 h.1 h.2.1.le (fun _ => h.2.2.1) (fun _ => h.2.2.2.1)) l
    else none

/-- **Jump over the downtime** (`docs/validator.md` §3.5): once
restarted, when the store's top round lies two rounds or more above the
node's top, the node fills each round in between along the line of the
least block there by another author, persists the filled blocks, and
sends the jump message; its top is then the last filled block, whose
round's timer counts as fired. -/
def tryJump (s : State Validator BlockId Payload) :
    Option (State Validator BlockId Payload × List (Output Validator BlockId Payload)) :=
  match s.recovering, s.top, s.own with
  | true, some r0, some B1 =>
    let R := s.store.topRound
    match Scheme.leastOf ((blocksAt s.store.toRecord R).filter fun i =>
        (s.store.blk i).creator ≠ cfg.me) with
    | some B2 =>
      if r0 + 2 ≤ R ∧ (s.store.blk B1).round = r0 then
        match jumpFills cfg.idOf s.store cfg.me B1 B2 with
        | some F =>
          match insertAll cfg s.store F, F.getLast? with
          | some st, some e =>
            let s' := { s with store := st, top := some e.2.round, own := some e.1 }
            some ({ s' with fired := insert e.2.round s.fired, recovering := false },
              F.map (fun e => .persist e.1 e.2) ++ [.jump cfg.me B1 (s.store.blk B2).creator B2])
          | _, _ => none
        | none => none
      else none
    | none => none
  | _, _, _ => none

/-- **The blocks a received jump message gives**: those it denotes on the
store, if it names another node and `B2`'s author, less those stored or
pending. -/
def jumpIn (s : State Validator BlockId Payload) (v1 : Validator) (B1 : BlockId) (v2 : Validator)
    (B2 : BlockId) : List (BlockId × Block Validator BlockId Payload) :=
  if v1 ≠ cfg.me ∧ B2 ∈ s.store.ids ∧ (s.store.blk B2).creator = v2 then
    ((jumpFills cfg.idOf s.store v1 B1 B2).getD []).filter fun e =>
      decide (e.1 ∉ s.store.ids) && decide (e.1 ∉ s.pending.map Prod.fst)
  else []

/-- The number of slots whose decision round is at most `R`. -/
def decidable (R : ℕ) : ℕ :=
  if R + 1 < cfg.p.waveLength then 0 else cfg.m * ((R + 1 - cfg.p.waveLength) / cfg.per + 1)

/-- **Decide**: `tryDecide` from the next undecided slot to the last slot
whose decision round the store holds, and output what it decides. -/
def decideStep (s : State Validator BlockId Payload) :
    State Validator BlockId Payload × List (Output Validator BlockId Payload) :=
  letI := cfg.slots
  let N := decidable cfg s.store.topRound
  if s.lo < N then
    let ds := Scheme.tryDecide cfg.p cfg.σ s.store.toRecord
      s.store.view s.lo (N - 1)
    ({ s with lo := s.lo + ds.length }, ds.map fun e => .commit e.1 e.2)
  else (s, [])

/-- The references of a pending block, each with the round below it. -/
def expand (s : State Validator BlockId Payload) (j : BlockId) : List (BlockId × ℕ) :=
  match s.pending.find? (fun e => decide (e.1 = j)) with
  | some (_, c) => (c.refs.sort (· ≤ ·)).map fun k => (k, c.round - 1)
  | none => []

/-- **One level of the walk**, from a front, the identifiers met already,
and the missing blocks found so far: the front's blocks at or above the
horizon, neither accepted nor met already, are missing if no pending
block has their identifier, and their references form the next front
otherwise. -/
def walkLevel (s : State Validator BlockId Payload)
    (w : List (BlockId × ℕ) × List BlockId × List (BlockId × ℕ)) :
    List (BlockId × ℕ) × List BlockId × List (BlockId × ℕ) :=
  let front := (w.1.filter fun x =>
    decide (s.store.base ≤ x.2) && decide (x.1 ∉ s.store.ids) && decide (x.1 ∉ w.2.1)).dedup
  let split := front.partition fun x => decide (x.1 ∈ s.pending.map Prod.fst)
  (split.1.flatMap fun x => expand s x.1, w.2.1 ++ front.map Prod.fst, w.2.2 ++ split.2)

/-- **The blocks to ask for**, after the block `b` with identifier `id`
arrived: the missing part of its history, walked through the pending
blocks, less those already asked for on `b`'s account. Asking again on
account of a new block is what lets an honest block's author answer
what a Byzantine block's author would not. -/
def missing (s : State Validator BlockId Payload) (id : BlockId)
    (b : Block Validator BlockId Payload) : List (BlockId × ℕ) :=
  ((walkLevel s)^[s.pending.length + 2]
    ((b.refs.sort (· ≤ ·)).map fun j => (j, b.round - 1), [], [])).2.2.filter
    fun x => decide ((x.1, id) ∉ s.requested.map fun e => (e.1, e.2.1))

/-- **Answer a request**: send the peer each block asked for that the
store holds. -/
def answer (s : State Validator BlockId Payload) (peer : Validator) (ids : List BlockId) :
    List (Output Validator BlockId Payload) :=
  (ids.filter fun j => decide (j ∈ s.store.ids)).map fun j =>
    .send peer j (s.store.map.getD j s.store.junk)

/-- **Raise the horizon** (`docs/validator.md` §3.4) to `Λ` below the
lesser of the decided frontier, the round of the first undecided slot,
and the node's own round; drop what lies below it. -/
def collect (s : State Validator BlockId Payload) :
    State Validator BlockId Payload × List (Output Validator BlockId Payload) :=
  match s.top with
  | some t =>
    let G := min (cfg.per * (s.lo / cfg.m)) t - cfg.lag
    if h : s.store.base < G then
      let st := s.store.prune G h.le
      let pend := s.pending.filter fun e => G ≤ e.2.round
      let req := s.requested.filter fun x => G ≤ x.2.2
      ({ s with store := st, pending := pend, fired := s.fired.filter (G ≤ ·), requested := req },
        [.prune G])
    else (s, [])
  | none => (s, [])

/-- **Build, decide, collect, then accept what that allows**: a block
built or a horizon raised can make a pending block ready, so this ends
by flushing, and no pending block is left ready. -/
def advance (s : State Validator BlockId Payload) :
    State Validator BlockId Payload × List (Output Validator BlockId Payload) :=
  let b := progress cfg (s.store.topRound + 2) s
  let d := decideStep cfg b.1
  let g := collect cfg d.1
  let fl := flush cfg (g.1.pending.length + 1) g.1.store g.1.pending
  ({ g.1 with store := fl.1, pending := fl.2 }, b.2 ++ d.2 ++ g.2)

/-- **Jump if it can, then advance**, after a change to the state. -/
def settle (s : State Validator BlockId Payload) :
    State Validator BlockId Payload × List (Output Validator BlockId Payload) :=
  match tryJump cfg s with
  | some (s', out) => let r := advance cfg s'; (r.1, out ++ r.2)
  | none => advance cfg s

/-- **What the node persists**: its accepted blocks, the horizon, the next
undecided slot and its own top block. -/
def State.persisted (s : State Validator BlockId Payload) : Persisted Validator BlockId Payload :=
  ⟨(s.store.ids.sort (· ≤ ·)).map fun j => (j, s.store.map.getD j s.store.junk), s.store.base,
    s.lo, s.own⟩

/-- **The state after a crash and restart**: the store, the next slot and
the top kept; nothing pending or asked for; the top round's timer fired,
since the node was away; recovering. -/
def State.recover (s : State Validator BlockId Payload) : State Validator BlockId Payload :=
  let s' := { s with pending := [], fired := (s.top.map fun t => {t}).getD ∅ }
  { s' with requested := [], recovering := true }

/-- **Resume from what was persisted**: the store rebuilt from the window
at the horizon, if the window is closed under references one round below
and lies at or above the horizon; the top read off the own block; and
the rest as `State.recover` sets it. -/
def resume (ps : Persisted Validator BlockId Payload) : Option (State Validator BlockId Payload) :=
  let map : Std.TreeMap BlockId (Block Validator BlockId Payload) compare :=
    Std.TreeMap.ofList ps.window
  let ids := (ps.window.map Prod.fst).toFinset
  if h : (∀ i ∈ ids, ∀ j ∈ (lookup map cfg.genesis ps.horizon i).refs, j ∈ ids) ∧
      (∀ i ∈ ids, ∀ j ∈ (lookup map cfg.genesis ps.horizon i).refs,
        (lookup map cfg.genesis ps.horizon j).round + 1 =
          (lookup map cfg.genesis ps.horizon i).round) ∧
      ∀ i ∈ ids, ps.horizon ≤ (lookup map cfg.genesis ps.horizon i).round then
    let st : Store Validator BlockId Payload := ⟨map, ids, cfg.genesis, ps.horizon, h.1, h.2.1, h.2.2⟩
    let top := ps.own.map fun o => (st.blk o).round
    some ⟨st, [], top, ps.own, (top.map fun t => {t}).getD ∅, ps.lo, [], true⟩
  else none

/-- **The node's transition function.** -/
def step (s : State Validator BlockId Payload) :
    Input Validator BlockId Payload →
      State Validator BlockId Payload × List (Output Validator BlockId Payload)
  | .start =>
    if s.top = none ∧ cfg.Admissible then
      let b := cfg.genesis
      let id := cfg.idOf b
      if h : id ∉ s.store.ids ∧ s.store.base ≤ b.round ∧
          rowValid cfg.q (Function.update s.store.blk id b) b then
        let st := s.store.insert id b h.1 h.2.1 (fun _ => Finset.empty_subset _)
          (fun _ j hj => absurd hj (Finset.notMem_empty j))
        let s₀ := { s with store := st, top := some 0, own := some id }
        let r := settle cfg { s₀ with recovering := false }
        (r.1, [.persist id b, .broadcast id b, .setTimer 0 (cfg.timeout 0)] ++ r.2)
      else (s, [])
    else (s, [])
  | .deliver id b =>
    if id = cfg.idOf b ∧ b.creator ≠ cfg.me ∧ s.store.base ≤ b.round ∧ id ∉ s.store.ids ∧
        id ∉ s.pending.map Prod.fst then
      let fl := flush cfg (s.pending.length + 1) s.store ((id, b) :: s.pending)
      let s₁ := { s with store := fl.1, pending := fl.2 }
      let miss := missing s₁ id b
      let req := s₁.requested ++ miss.map fun x => (x.1, id, x.2)
      let r := settle cfg { s₁ with requested := req }
      (r.1, (if miss.isEmpty then [] else [.fetch (miss.map Prod.fst)]) ++ r.2)
    else (s, [])
  | .timer r => settle cfg { s with fired := insert r s.fired }
  | .jump v1 B1 v2 B2 =>
    let F := jumpIn cfg s v1 B1 v2 B2
    if F.isEmpty then (s, [])
    else
      let fl := flush cfg (s.pending.length + F.length + 1) s.store (F ++ s.pending)
      settle cfg { s with store := fl.1, pending := fl.2 }
  | .fetchRequest peer ids => (s, answer s peer ids)
  | .restart => settle cfg s.recover
  | _ => (s, [])

end Node

end LeanDag
