import LeanDag.Node.Memory
import Mathlib.Data.Finset.Sort
/-!
# An honest node — its transition function

`docs/validator.md` §3. `step cfg s i` is the node's response to the
input `i` in the state `s`: the new state and the outputs.

* **Memory and disk** (`State.memory`, `State.disk`, `keep`, `release`):
  every accepted block is kept on disk, and in memory if its round is
  the floor or above, without references at the floor. The node builds,
  decides and arms its timers on the memory, and answers requests and
  resends from the disk. When it builds or decides, it releases the
  memory below the lowest round it reads, the round of its next
  undecided slot and `voteOffset` below its top (`floorOf`).
* **Receipt** (`deliver`): a block whose identifier is its hash, not the
  node's own, and not on disk, waits in `pending` until its references
  are accepted and it satisfies `rowValid q`, checked in memory if its
  round is above the floor and on disk otherwise, and is then accepted
  (`ready`, `flush`).
* **Building** (`tryBuild`): round `r + 1`, above the node's top `r`,
  once the memory holds `q` authors of round `r` and either the round's
  timer fired, or the memory holds round-`r + 1` blocks of `f + 1`
  authors, so a node other than a Byzantine one built the round
  (`behind`), or the block would reach every leader block of a slot
  whose wave is at a vote round (`reachReady`) and certify one at a
  decision round (`certReady`). A node behind thus builds each round
  below the highest block it holds without waiting its timers. The block
  references one accepted block per author of round `r`, the node's own
  for itself when it built there, which is the self-parent rule of an
  honest node, and the least identifier otherwise; where these fail the
  tests and the references of a held round-`r + 1` block of another
  author pass them, it takes those, with its own block for itself
  (`refsAt`). It is persisted, then broadcast, and the retry timer is
  set: the timer of the round below it, for twice that round's timeout.
* **Timers** (`arm`): the timer of the node's top round is set once the
  memory holds `q` authors of that round, so a node that gets ahead of a
  quorum does not start waiting before the quorum is there. After a
  restart it is set again if it was (`rearm`).
* **Deciding** (`decideStep`): `tryDecide` from the next undecided slot
  to the last slot at a round the disk holds, on the memory's window at
  the round of that slot (`Store.window`); the decisions are kept
  (`State.decided`), the latest first.
* **Fetching** (`walkLevel`, `missing`, `answer`): after a delivery, the
  missing part of the delivered block's history, walked through the
  pending blocks, is asked of its author, with the asker's round `r`; a
  request is answered with the blocks asked for that the disk holds and
  their histories, less the blocks a node at round `r` holds whatever it
  built on (`coreThreshold`, `pruned`).
* **Resending** (`resend`): when the retry timer, or the top round's,
  fires and the node does not build, and when it restarts, the node
  broadcasts its top block again, sets the retry timer again, and asks
  again for the missing histories of its pending blocks (`refetch`). A
  node with a quorum of its round builds within its timeout and the time
  the quorum takes to arrive, before the retry timer fires, so it resends
  only when it is stuck. A crash loses the messages sent to a node while
  it is down, and the requests and answers sent to it; resending lets a
  peer that lost blocks fetch them again, and the node itself ask again
  for what it lost.
* **Settling** (`settle`, `quiesce`): after each change to its state,
  the node builds, decides and accepts what that allows, in passes,
  until a pass changes none of its top, its pending blocks and its next
  undecided slot.

Definitions only.
-/

namespace LeanDag

namespace Node

variable {Validator BlockId Payload : Type} [Fintype Validator] [DecidableEq Validator]
variable [LinearOrder BlockId]

variable (Validator BlockId Payload) in
/-- **A node's state.** -/
structure State where
  /-- The accepted blocks, on disk: what the node answers requests from. -/
  disk : Store Validator BlockId Payload
  /-- The accepted blocks from round `floor` up, those at `floor` without
  references, in memory: what the node computes on. -/
  memory : Store Validator BlockId Payload
  /-- The lowest round in memory. -/
  floor : ℕ
  /-- The memory holds the disk's blocks from `floor` up. -/
  mirrors : memory.Mirrors disk floor
  /-- Blocks received whose references are not all accepted. -/
  pending : List (BlockId × Block Validator BlockId Payload)
  /-- The highest round the node built, once started. -/
  top : Option ℕ
  /-- The node's block at `top`. -/
  own : Option BlockId
  /-- The rounds whose timer fired; each timer drops the rounds below the
  top, which the node no longer reads. -/
  fired : Finset ℕ
  /-- The next undecided slot. -/
  lo : ℕ
  /-- The decisions the node output, the latest first. -/
  decided : List (ℕ × Option BlockId)
  /-- The round whose timer is set. -/
  armed : Option ℕ

variable (cfg : Config Validator BlockId Payload)

/-- The node's genesis block. -/
def Config.genesis : Block Validator BlockId Payload := ⟨0, cfg.me, ∅, cfg.payload 0⟩

/-- The state before start. -/
def State.init : State Validator BlockId Payload :=
  ⟨Store.empty cfg.genesis, Store.empty cfg.genesis, 0, Store.Mirrors.empty, [], none, none, ∅, 0,
    [], none⟩

/-- **Keep a block**: on disk, and in memory if its round is the floor or
above. -/
def keep (s : State Validator BlockId Payload) (id : BlockId) (b : Block Validator BlockId Payload)
    (hnew : id ∉ s.disk.ids) (hrefs : b.refs ⊆ s.disk.ids)
    (hpred : ∀ j ∈ b.refs, (s.disk.blk j).round + 1 = b.round) : State Validator BlockId Payload :=
  { s with
    disk := s.disk.insert id b hnew hrefs hpred
    memory := s.memory.put s.floor id b (s.mirrors.notMem hnew) (s.mirrors.refs_mem hrefs hpred)
      (s.mirrors.pred_mem hrefs hpred)
    mirrors := s.mirrors.put hnew hrefs hpred }

/-- **A pending block is ready** when its references are accepted, one
round below it, and it is valid at the row: checked in memory if its
round is above the floor, on disk otherwise. -/
def ready (s : State Validator BlockId Payload) (e : BlockId × Block Validator BlockId Payload) :
    Bool :=
  decide ((Store.pick s.memory s.disk s.floor e.2.round).Checks cfg.q e.1 e.2)

/-- **Accept a block**: it is kept if it is new and ready. -/
def accept (s : State Validator BlockId Payload) (id : BlockId)
    (b : Block Validator BlockId Payload) : State Validator BlockId Payload :=
  if h : id ∉ s.disk.ids ∧ (Store.pick s.memory s.disk s.floor b.round).Checks cfg.q id b then
    keep s id b h.1 (s.mirrors.checks_pick.mp h.2).1 (s.mirrors.checks_pick.mp h.2).2.1
  else s

/-- **Accept what the pending blocks allow**, in passes, at most `fuel`. -/
def flush : ℕ → State Validator BlockId Payload → State Validator BlockId Payload
  | 0, s => s
  | fuel + 1, s =>
    let split := s.pending.partition fun e => ready cfg s e
    if split.1.isEmpty then s
    else flush fuel { split.1.foldl (fun s e => accept cfg s e.1 e.2) s with pending := split.2 }

/-- **The references of the node's next block**, above round `r`: one
accepted block per author of round `r`, the node's own block `o` there
for itself if it built one, and the least identifier otherwise. -/
def refsFor (s : Store Validator BlockId Payload) (r : ℕ) (o : Option BlockId) : Finset BlockId :=
  let R := s.atRound r
  (creatorsOf s.blk R).biUnion fun a =>
    if a = cfg.me ∧ o.isSome then o.toFinset
    else (Scheme.leastOf (R.filter fun i => (s.blk i).creator = a)).toFinset

/-- **The reach test** for a block at round `r + 1` referencing `refs`:
for each slot whose wave has `r + 1` at or below its vote round, the
block reaches one of the slot's leader blocks (`Store.leaderBlocks`). A
leader block `m` rounds below a reference lies within `m` steps of it,
so the search stops there. -/
def reachReady (s : Store Validator BlockId Payload) (refs : Finset BlockId) (r : ℕ) : Bool :=
  letI := cfg.slots
  (List.range cfg.p.voteOffset).all fun m =>
    if m ≤ r then
      (cfg.slotsAt (r - m)).all fun k =>
        decide (∃ L ∈ s.leaderBlocks k,
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
      decide (∃ L ∈ s.leaderBlocks k,
        cfg.p.certThreshold ≤
          (creatorsOf s.blk (refs.filter fun b => cfg.σ.Votes s.toRecord b L)).card)
  else true

/-- **The references a held round-`r + 1` block `c` lends**: `c`'s, with
the node's own block `o` put in for itself. -/
def lent (s : Store Validator BlockId Payload) (c : BlockId) (o : Option BlockId) :
    Finset BlockId :=
  ((s.blk c).refs.filter fun j => (s.blk j).creator ≠ cfg.me) ∪ o.toFinset

/-- **References `R` the node can build on above round `r`**: they are
accepted and one round below the block they make, which is valid at the
row. -/
def buildable (s : Store Validator BlockId Payload) (r : ℕ) (R : Finset BlockId) : Bool :=
  let b : Block Validator BlockId Payload := ⟨r + 1, cfg.me, R, cfg.payload (r + 1)⟩
  decide (s.Checks cfg.q (cfg.idOf b) b)

/-- **The references of the node's next block**, above round `r`: those of
`refsFor` if they pass the reach and certificate tests; else those lent
by the first held round-`r + 1` block of another author that pass them
and can be built on; else those of `refsFor`. A node behind then reaches
what a peer reached. -/
def refsAt (s : Store Validator BlockId Payload) (r : ℕ) (o : Option BlockId) :
    Finset BlockId :=
  let ready := fun R => reachReady cfg s R r && certReady cfg s R r
  let own := refsFor cfg s r o
  if ready own then own
  else ((((s.atRound (r + 1)).sort (· ≤ ·)).filter fun c =>
      decide ((s.blk c).creator ≠ cfg.me)).map (lent cfg s · o) |>.find? fun R =>
        ready R && buildable cfg s r R).getD own

/-- **The node is behind round `r + 1`**: its store holds round-`r + 1`
blocks of `f + 1` authors, so a node other than a Byzantine one built the
round. -/
def behind (st : Store Validator BlockId Payload) (r : ℕ) : Prop :=
  cfg.f + 1 ≤ (st.authorsAt (r + 1)).card

instance (st : Store Validator BlockId Payload) (r : ℕ) : Decidable (behind cfg st r) :=
  inferInstanceAs (Decidable (_ ≤ _))

/-- **The lowest round the node reads**: the round of its next undecided
slot, and `voteOffset` below its top. -/
def floorOf (s : State Validator BlockId Payload) : ℕ :=
  min (cfg.slots.slotRound s.lo) (s.top.getD 0 - cfg.p.voteOffset)

/-- **Release the memory below the lowest round the node reads.** -/
def release (s : State Validator BlockId Payload) : State Validator BlockId Payload :=
  if h : s.floor < floorOf cfg s then
    { s with
      memory := s.memory.above (floorOf cfg s)
      floor := floorOf cfg s
      mirrors := s.mirrors.above h.le }
  else s

/-- **Build the next round**, if the build rule allows it, and release the
memory below the lowest round the node then reads. -/
def tryBuild (s : State Validator BlockId Payload) :
    Option (State Validator BlockId Payload × List (Output Validator BlockId Payload)) :=
  match s.top with
  | some r =>
    let refs := refsAt cfg s.memory r s.own
    if cfg.q ≤ (s.memory.authorsAt r).card ∧ (r ∈ s.fired ∨ behind cfg s.memory r ∨
        (reachReady cfg s.memory refs r ∧ certReady cfg s.memory refs r)) then
      let b : Block Validator BlockId Payload := ⟨r + 1, cfg.me, refs, cfg.payload (r + 1)⟩
      let id := cfg.idOf b
      if h : id ∉ s.disk.ids ∧ s.memory.Checks cfg.q id b then
        let s' := keep s id b h.1 (s.mirrors.checks_disk h.2).1 (s.mirrors.checks_disk h.2).2.1
        some (release cfg { s' with top := some (r + 1), own := some id },
          [.persist id b, .broadcast id b, .setTimer r (2 * cfg.timeout r)])
      else none
    else none
  | none => none

/-- **Build while the rule allows**, at most `fuel` rounds. -/
def progress : ℕ → State Validator BlockId Payload →
    State Validator BlockId Payload × List (Output Validator BlockId Payload)
  | 0, s => (s, [])
  | fuel + 1, s =>
    match tryBuild cfg s with
    | some (s', out) => let r := progress fuel s'; (r.1, out ++ r.2)
    | none => (s, [])

/-- **The outputs that build some blocks**: for each, persist, broadcast,
then set the retry timer, which resends (`resend`). -/
def built (bs : List (BlockId × Block Validator BlockId Payload)) :
    List (Output Validator BlockId Payload) :=
  bs.flatMap fun e =>
    [.persist e.1 e.2, .broadcast e.1 e.2,
      .setTimer (e.2.round - 1) (2 * cfg.timeout (e.2.round - 1))]

/-- The references of a pending block. -/
def expand (s : State Validator BlockId Payload) (j : BlockId) : List BlockId :=
  match s.pending.find? (fun e => decide (e.1 = j)) with
  | some (_, c) => c.refs.sort (· ≤ ·)
  | none => []

/-- **One level of the walk**, from a front, the identifiers met already,
and the missing blocks found so far: the front's blocks neither accepted
nor met already are missing if no pending block has their identifier,
and their references form the next front otherwise. -/
def walkLevel (s : State Validator BlockId Payload)
    (w : List BlockId × List BlockId × List BlockId) :
    List BlockId × List BlockId × List BlockId :=
  let front := (w.1.filter fun x => decide (x ∉ s.disk.ids) && decide (x ∉ w.2.1)).dedup
  let split := front.partition fun x => decide (x ∈ s.pending.map Prod.fst)
  (split.1.flatMap fun x => expand s x, w.2.1 ++ front, w.2.2 ++ split.2)

/-- The slots below the slot rounds up to `R`: the slots `tryDecide` may
reach on a store whose top round is `R`. -/
def decidable (R : ℕ) : ℕ := cfg.m * (R / cfg.per + 1)

/-- **Decide**: `tryDecide` from the next undecided slot to the last slot
at a round the disk holds, on the memory's window at the round of the
first slot, if the memory holds that round; output and keep what it
decides, if anything, and release the memory below the lowest round the
node then reads. -/
def decideStep (s : State Validator BlockId Payload) :
    State Validator BlockId Payload × List (Output Validator BlockId Payload) :=
  letI := cfg.slots
  let N := decidable cfg s.disk.topRound
  let R := cfg.slots.slotRound s.lo
  let ds := Scheme.tryDecide cfg.p cfg.σ (s.memory.window R) (s.memory.windowView R) s.lo (N - 1)
  if s.lo < N ∧ s.floor ≤ R ∧ ds ≠ [] then
    (release cfg { s with lo := s.lo + ds.length, decided := ds.reverse ++ s.decided },
      ds.map fun e => .commit e.1 e.2)
  else (s, [])

/-- **The blocks to ask for**, after the block `b` arrived: the missing
part of its history, walked through the pending blocks. Asking on account
of each block delivered is what lets an honest block's author answer
what a Byzantine block's author would not. -/
def missing (s : State Validator BlockId Payload) (b : Block Validator BlockId Payload) :
    List BlockId :=
  ((walkLevel s)^[s.pending.length + 2] (b.refs.sort (· ≤ ·), [], [])).2.2

/-- **The authors a block must have reached to lie in every view at round
`r`**: `n − q + f + 1`. A node at round `r` built on blocks of `q`
distinct authors of round `r − 1`; a block reached by round-`(r − 1)`
blocks of this many authors is reached by one of an honest author among
them, which has one block there. -/
def coreThreshold : ℕ := Fintype.card Validator - cfg.q + cfg.f + 1

/-- **One level of the core sweep**: each reference of a block of the
level receives the authors that reach the block. -/
def coreLevel (st : Store Validator BlockId Payload) (lvl : List (BlockId × Finset Validator)) :
    List (BlockId × Finset Validator) :=
  (lvl.foldl (fun (m : Std.TreeMap BlockId (Finset Validator) compare) e =>
      ((st.blk e.1).refs.sort (· ≤ ·)).foldl (fun m j => m.insert j (m.getD j ∅ ∪ e.2)) m)
    ∅).toList

/-- **The core sweep** from a level down, at most `fuel` levels, stopping at
a level whose blocks all reach the threshold: each block met, with
authors of round-`(r − 1)` blocks that reach it. -/
def coreFrom (st : Store Validator BlockId Payload) :
    ℕ → List (BlockId × Finset Validator) → Std.TreeMap BlockId (Finset Validator) compare →
      Std.TreeMap BlockId (Finset Validator) compare
  | 0, _, acc => acc
  | fuel + 1, lvl, acc =>
    let acc := lvl.foldl (fun m e => m.insert e.1 e.2) acc
    if lvl.all fun e => decide (coreThreshold cfg ≤ e.2.card) then acc
    else coreFrom st fuel (coreLevel st lvl) acc

/-- **Authors reaching each block from round `r − 1`**, as far as the
sweep goes; nothing at `r = 0`. -/
def coreSets (st : Store Validator BlockId Payload) (r : ℕ) :
    Std.TreeMap BlockId (Finset Validator) compare :=
  if r = 0 then ∅
  else coreFrom cfg st r (((st.atRound (r - 1)).sort (· ≤ ·)).map
    fun c => (c, {(st.blk c).creator})) ∅

/-- **The store read through core sets**: a block keeps only its
references whose recorded set falls short of `coreThreshold`. -/
def prunedBy (st : Store Validator BlockId Payload)
    (core : Std.TreeMap BlockId (Finset Validator) compare) (x : BlockId) :
    Block Validator BlockId Payload :=
  { st.blk x with
    refs := (st.blk x).refs.filter fun i => ¬ coreThreshold cfg ≤ (core.getD i ∅).card }

/-- **The store read for an answer to a node at round `r`**: a block keeps
only its references that round-`(r − 1)` blocks of fewer than
`coreThreshold` authors reach. -/
def pruned (st : Store Validator BlockId Payload) (r : ℕ) : BlockId →
    Block Validator BlockId Payload :=
  prunedBy cfg st (coreSets cfg st r)

/-- **The blocks a request from a node at round `r` is answered with**:
each block asked for that the disk holds, then their histories on disk
through blocks the asker need not hold. -/
def answerIds (s : State Validator BlockId Payload) (r : ℕ) (ids : List BlockId) :
    List BlockId :=
  let held := ids.filter fun j => decide (j ∈ s.disk.ids)
  let core := coreSets cfg s.disk r
  (held ++ held.flatMap fun j =>
    ((historyUptoFrom (prunedBy cfg s.disk core) ((s.disk.blk j).round + 1) j).filter fun x =>
      decide (x ∈ s.disk.ids)).sort (· ≤ ·)).dedup

/-- **Answer a request** from a node at round `r`: send the peer the
blocks of `answerIds`. -/
def answer (s : State Validator BlockId Payload) (peer : Validator) (r : ℕ) (ids : List BlockId) :
    List (Output Validator BlockId Payload) :=
  (answerIds cfg s r ids).map fun j => .send peer j (s.disk.blk j)

/-- **Ask again for the pending blocks' histories**: for each pending
block, the missing part of its history, of its author. -/
def refetch (s : State Validator BlockId Payload) : List (Output Validator BlockId Payload) :=
  s.pending.filterMap fun e =>
    let miss := missing s e.2
    if miss.isEmpty then none else some (.fetch e.2.creator (s.top.getD 0) miss)

/-- **Send the node's top block again**: broadcast its block at its top
round and set the retry timer again, then ask again for the pending
blocks' histories. -/
def resend (s : State Validator BlockId Payload) : List (Output Validator BlockId Payload) :=
  (match s.top, s.own with
    | some r, some id =>
      [.broadcast id (s.disk.blk id), .setTimer (r - 1) (2 * cfg.timeout (r - 1))]
    | _, _ => []) ++ refetch s

/-- **Set the top round's timer again**, after a restart, if it was set. -/
def rearm (s : State Validator BlockId Payload) : List (Output Validator BlockId Payload) :=
  match s.top with
  | some r => if s.armed = some r then [.setTimer r (cfg.timeout r)] else []
  | none => []

/-- **Arm the top round's timer**, once the memory holds `q` authors of
the node's top round and the timer is not set yet. -/
def arm (s : State Validator BlockId Payload) :
    State Validator BlockId Payload × List (Output Validator BlockId Payload) :=
  match s.top with
  | some r =>
    if s.armed ≠ some r ∧ cfg.q ≤ (s.memory.authorsAt r).card then
      ({ s with armed := some r }, [.setTimer r (cfg.timeout r)])
    else (s, [])
  | none => (s, [])

/-- **Build, decide, then accept what that allows**: a block built can
make a pending block ready, so this ends by flushing, and no pending
block is left ready. -/
def pass (s : State Validator BlockId Payload) :
    State Validator BlockId Payload × List (Output Validator BlockId Payload) :=
  let b := progress cfg (s.disk.topRound + 2) s
  let d := decideStep cfg b.1
  (flush cfg (d.1.pending.length + 1) d.1, b.2 ++ d.2)

/-- **A pass, then arming the top round's timer.** -/
def advance (s : State Validator BlockId Payload) :
    State Validator BlockId Payload × List (Output Validator BlockId Payload) :=
  let p := pass cfg s
  let a := arm cfg p.1
  (a.1, p.2 ++ a.2)

/-- **Advance until a pass changes nothing the next would read**: the
top, the pending blocks and the next undecided slot; at most `fuel`
passes. -/
def quiesce : ℕ → State Validator BlockId Payload →
    State Validator BlockId Payload × List (Output Validator BlockId Payload)
  | 0, s => (s, [])
  | fuel + 1, s =>
    let r := advance cfg s
    if r.1.top = s.top ∧ r.1.pending.length = s.pending.length ∧ r.1.lo = s.lo then r
    else let r' := quiesce fuel r.1; (r'.1, r.2 ++ r'.2)

/-- The highest round of a pending block, `0` without one. -/
def pendingTop (s : State Validator BlockId Payload) : ℕ :=
  (s.pending.map (·.2.round)).foldr max 0

/-- **The passes a settle takes at most**: each but the last raises the
top or the next undecided slot, or leaves fewer blocks pending, within
bounds the state fixes. -/
def passes (s : State Validator BlockId Payload) : ℕ :=
  let B := max (s.top.getD 0) (max s.disk.topRound (pendingTop s)) + 1
  let L := max s.lo (decidable cfg B)
  s.pending.length + 2 * B + 2 * L + 1

/-- **Advance until nothing changes**, after a change to the state. -/
def settle (s : State Validator BlockId Payload) :
    State Validator BlockId Payload × List (Output Validator BlockId Payload) :=
  quiesce cfg (passes cfg s) s

/-- **The fired rounds after the timer of round `r`**: `r`, and those not
below the top. -/
def fire (s : State Validator BlockId Payload) (r : ℕ) : Finset ℕ :=
  insert r (s.fired.filter (s.top.getD 0 ≤ ·))

/-- **The node's transition function.** -/
def step (s : State Validator BlockId Payload) :
    Input Validator BlockId Payload →
      State Validator BlockId Payload × List (Output Validator BlockId Payload)
  | .start =>
    if s.top = none ∧ cfg.Admissible then
      let b := cfg.genesis
      let id := cfg.idOf b
      if h : id ∉ s.disk.ids ∧ rowValid cfg.q (Function.update s.disk.blk id b) b then
        let s' := keep s id b h.1 (fun _ hj => absurd hj (Finset.notMem_empty _))
          (fun j hj => absurd hj (Finset.notMem_empty j))
        let r := settle cfg { s' with top := some 0, own := some id }
        (r.1, [.persist id b, .broadcast id b, .setTimer 0 (2 * cfg.timeout 0)] ++ r.2)
      else (s, [])
    else (s, [])
  | .deliver id b =>
    if id = cfg.idOf b ∧ b.creator ≠ cfg.me ∧ id ∉ s.disk.ids ∧
        id ∉ s.pending.map Prod.fst then
      let s₁ := flush cfg (s.pending.length + 1) { s with pending := (id, b) :: s.pending }
      let miss := missing s₁ b
      let r := settle cfg s₁
      (r.1, (if miss.isEmpty then [] else [.fetch b.creator (s.top.getD 0) miss]) ++ r.2)
    else (s, [])
  | .timer r =>
    let res := settle cfg { s with fired := fire s r }
    if res.1.top = s.top ∧ (s.top = some r ∨ s.top = some (r + 1)) then
      (res.1, res.2 ++ resend cfg res.1)
    else res
  | .fetchRequest peer r ids => (s, answer cfg s peer r ids)
  | .restart => (s, resend cfg s ++ rearm cfg s)

end Node

end LeanDag
