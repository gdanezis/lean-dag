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
* **Receipt** (`deliver`, `stream`): a block a peer sends in its own
  name, under its hash, not on disk, from a peer not detected, is
  accepted if its references are accepted and it satisfies `rowValid q E`,
  checked in memory if its round is above the floor and on disk otherwise
  (`ready`, `accept`). Otherwise, if it names `q` references unless it is
  at round `0`, it becomes the block of the sync with that peer if it lies
  above the sync's block, and the node asks the peer for its history
  (`syncs`, `request`).
* **Conviction** (`evidenceOf`, `accept`): accepting a block of an author
  whose block of that round the disk holds gives evidence of the author,
  the two blocks; the evidence an accepted block carries is kept too
  (`evidence`), and the authors the evidence names are convicted
  (`detected`). The syncs with convicted peers and the syncs whose block
  is held are dropped (`tidy`), and the requests of convicted peers are
  not answered.
* **Building** (`tryBuild`): round `r + 1`, above the node's top `r`,
  once the memory holds `q` authors of round `r` and either the round's
  timer fired, or the memory holds round-`r + 1` blocks of `f + 1`
  authors, so a node other than a Byzantine one built the round
  (`behind`), or the block would reach every leader block of a slot
  whose wave is at a vote round (`reachReady`) and certify one at a
  decision round (`certReady`). A node behind thus builds each round
  below the highest block it holds without waiting its timers. The block
  references one accepted block per author of round `r` that it does not
  leave out, the node's own for itself when it built there and the least
  identifier otherwise; it leaves out the authors its evidence names and
  those a round-`r` block it holds exposes (`excluded`, `refsFor`). Where
  these fail the tests, or cannot be built on, it takes the references of
  a held round-`r + 1` block of another author (`lent`, `refsAt`). Its
  payload carries the node's evidence against the authors it does not
  reference, and the authors it then exposes (`payloadFor`). It is
  persisted, then broadcast, and the retry timer is set: the timer of the
  round below it, for twice that round's timeout.
* **The jump** (`jumpRound`): a node that restarted, until it builds or
  a timer fires (`State.recovering`), builds above the highest round `r`
  above its top at which the memory holds `q` authors and is behind,
  with no block of its own among the references, once no sync's block
  lies above round `r + 1` and the references pass the reach and
  certificate tests. Without such a round it builds above its top, once
  no sync's block lies above the round it builds.
* **Timers** (`arm`): the timer of the node's top round is set once the
  memory holds `q` authors of that round, so a node that gets ahead of a
  quorum does not start waiting before the quorum is there. After a
  restart it is set again if it was (`rearm`).
* **Deciding** (`decideStep`): `tryDecide` from the next undecided slot
  to the last slot at a round the disk holds, on the memory's window at
  the round of that slot (`Store.window`); the decisions are kept
  (`State.decided`), the latest first.
* **Syncing** (`request`, `streamOf`, `inHistory`, `absorb`): a request
  names the sync's block, the node's frontier (for each author the least
  round at which its disk holds no block of it, `0` for a detected author,
  `frontierOf`), and the identifiers asked for by name. It is answered with
  the blocks of the disk in the block's history that are the block, asked
  for, or at or above their author's frontier, in order of round. Of a
  stream piece the node takes the blocks in the history of the sync's
  block, each accepted if it is ready on arrival; the references still
  missing are asked for by name in the next request (`missingIn`).
* **Resending** (`resend`): when the retry timer, or the top round's,
  fires and the node does not build, and when it restarts, before it
  settles, the node broadcasts its top block again, sets the retry timer
  again, asks every peer for its block of its top round (`ask`), and asks
  again in every sync (`resync`). A peer not convicted answers with its
  own block of that round (`ownAt`). A node with a quorum of
  its round builds within its timeout and the time the quorum takes to
  arrive, before the retry timer fires, so it resends only when it is
  stuck. A crash loses the messages sent to a node while it is down, and
  the requests and streams sent to it; resending lets a peer that lost
  blocks sync them again, and the node itself ask again for what it lost.
* **Settling** (`settle`, `quiesce`): after each change to its state,
  the node builds, decides and accepts the syncs' blocks that this makes
  ready, in passes, until a pass changes none of its top, its syncs and
  its next undecided slot (`flushSyncs`).

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
  /-- The syncs with peers, at most one each: the peer, its block the
  node lacks, and the identifiers asked for by name. -/
  syncs : List (Validator × (BlockId × Block Validator BlockId Payload) × List BlockId)
  /-- The authors the node convicted: whose twins it accepted, or whom the
  evidence of a block it accepted names. -/
  detected : Finset Validator
  /-- The evidence the node holds: an author with two of its blocks. -/
  evidence : Finset (Validator × BlockId × BlockId)
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
  /-- Restarted, and since neither built nor had a timer fire. -/
  recovering : Bool

variable (cfg : Config Validator BlockId Payload)

/-- The node's genesis block. -/
def Config.genesis : Block Validator BlockId Payload := ⟨0, cfg.me, ∅, cfg.payload 0 ∅ ∅⟩

/-- The state before start. -/
def State.init : State Validator BlockId Payload :=
  ⟨Store.empty cfg.genesis, Store.empty cfg.genesis, 0, Store.Mirrors.empty, [], ∅, ∅, none,
    none, ∅, 0, [], none, false⟩

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

/-- **A block is ready** when its references are accepted, one round below
it, and it is valid at the row: checked in memory if its round is above
the floor, on disk otherwise. -/
def ready (s : State Validator BlockId Payload) (e : BlockId × Block Validator BlockId Payload) :
    Bool :=
  decide ((Store.pick s.memory s.disk s.floor e.2.round).Checks cfg.q cfg.xp e.1 e.2)

/-- **The twin of a block on a store**: the least block of its author at its
round. -/
def twinOf (st : Store Validator BlockId Payload) (b : Block Validator BlockId Payload) :
    Option BlockId :=
  Scheme.leastOf ((st.atRound b.round).filter fun i => (st.blk i).creator = b.creator)

/-- **The evidence accepting the block `b` under `id` gives**: its author
with its twin on the store, and the evidence `b` carries that names an
author. -/
def evidenceOf (st : Store Validator BlockId Payload) (id : BlockId)
    (b : Block Validator BlockId Payload) : Finset (Validator × BlockId × BlockId) :=
  ((twinOf st b).map fun i => (b.creator, i, id)).toFinset ∪
    (cfg.xp.ev b.payload).filter fun e => e.2.1 ≠ e.2.2

/-- **Accept a block**: it is kept if it is new and ready; the node keeps
the evidence it gives and convicts the authors that evidence names. -/
def accept (s : State Validator BlockId Payload) (id : BlockId)
    (b : Block Validator BlockId Payload) : State Validator BlockId Payload :=
  if h : id ∉ s.disk.ids ∧
      (Store.pick s.memory s.disk s.floor b.round).Checks cfg.q cfg.xp id b then
    let s' := keep s id b h.1 (s.mirrors.checks_pick.mp h.2).1 (s.mirrors.checks_pick.mp h.2).2.1
    let E := evidenceOf cfg s.disk id b
    { s' with detected := s'.detected ∪ named E, evidence := s'.evidence ∪ E }
  else s

/-- **Drop the syncs done**: those whose block is held, and those with a
detected peer. -/
def tidy (s : State Validator BlockId Payload) : State Validator BlockId Payload :=
  { s with syncs := s.syncs.filter fun e => decide (e.2.1.1 ∉ s.disk.ids ∧ e.1 ∉ s.detected) }

/-- **The authors the node's next block above round `r` leaves out**: those
its evidence `E` names, and those a round-`r` block of the store exposes. -/
def excluded (s : Store Validator BlockId Payload) (r : ℕ)
    (E : Finset (Validator × BlockId × BlockId)) : Finset Validator :=
  named E ∪ (s.atRound r).biUnion fun i => cfg.xp.ex (s.blk i).payload

/-- **The references of the node's next block**, above round `r`: one
accepted block per author of round `r` not left out, the node's own block
`o` there for itself if it built one, and the least identifier otherwise. -/
def refsFor (s : Store Validator BlockId Payload) (r : ℕ) (o : Option BlockId)
    (E : Finset (Validator × BlockId × BlockId)) : Finset BlockId :=
  let R := s.atRound r
  (creatorsOf s.blk R \ excluded cfg s r E).biUnion fun a =>
    if a = cfg.me ∧ o.isSome then o.toFinset
    else (Scheme.leastOf (R.filter fun i => (s.blk i).creator = a)).toFinset

/-- **The payload of the node's block above round `r` on the references
`R`**: the evidence `E` against the authors it does not reference, and the
authors that evidence names and the references expose. -/
def payloadFor (s : Store Validator BlockId Payload) (r : ℕ) (R : Finset BlockId)
    (E : Finset (Validator × BlockId × BlockId)) : Payload :=
  let E' := E.filter fun e => e.1 ∉ creatorsOf s.blk R
  cfg.payload (r + 1) E' (named E' ∪ R.biUnion fun j => cfg.xp.ex (s.blk j).payload)

/-- **The node's block above round `r` on the references `R`.** -/
def blockOn (s : Store Validator BlockId Payload) (r : ℕ) (R : Finset BlockId)
    (E : Finset (Validator × BlockId × BlockId)) : Block Validator BlockId Payload :=
  ⟨r + 1, cfg.me, R, payloadFor cfg s r R E⟩

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

/-- **The references a held round-`r + 1` block `c` lends**: `c`'s. -/
def lent (s : Store Validator BlockId Payload) (c : BlockId) : Finset BlockId := (s.blk c).refs

/-- **References `R` the node can build on above round `r`**, with the
evidence `E`: they are accepted and one round below the block they make,
which is valid at the row. -/
def buildable (s : Store Validator BlockId Payload) (r : ℕ) (R : Finset BlockId)
    (E : Finset (Validator × BlockId × BlockId)) : Bool :=
  decide (s.Checks cfg.q cfg.xp (cfg.idOf (blockOn cfg s r R E)) (blockOn cfg s r R E))

/-- **The references lent by the held round-`r + 1` blocks of other
authors**, in order of identifier. -/
def lents (s : Store Validator BlockId Payload) (r : ℕ) : List (Finset BlockId) :=
  (((s.atRound (r + 1)).sort (· ≤ ·)).filter fun c =>
    decide ((s.blk c).creator ≠ cfg.me)).map (lent s ·)

/-- **The references of the node's next block**, above round `r`, with the
evidence `E`: those of `refsFor` if they pass the reach and certificate
tests and can be built on; else the first lent ones that pass the tests
and can be built on; else those of `refsFor` if they can be built on; else
the first lent ones that can be built on; else those of `refsFor`. A node
behind then reaches what a peer reached, and a node that leaves out
too many authors builds on what a peer built on. -/
def refsAt (s : Store Validator BlockId Payload) (r : ℕ) (o : Option BlockId)
    (E : Finset (Validator × BlockId × BlockId)) : Finset BlockId :=
  let ready := fun R => reachReady cfg s R r && certReady cfg s R r
  let ok := fun R => buildable cfg s r R E
  let own := refsFor cfg s r o E
  if ready own && ok own then own
  else match (lents cfg s r).find? fun R => ready R && ok R with
    | some R => R
    | none => if ok own then own else ((lents cfg s r).find? ok).getD own

/-- **The node is behind round `r + 1`**: the store `st` holds round-`r + 1`
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

/-- The highest round of a sync's block, `0` without one. -/
def syncTop (s : State Validator BlockId Payload) : ℕ :=
  (s.syncs.map (·.2.1.2.round)).foldr max 0

/-- **The round a recovering node builds above**: the highest round above
`t` at which the store `st` holds `q` authors and is behind, or `t`. -/
def jumpRound (st : Store Validator BlockId Payload) (t : ℕ) : ℕ :=
  ((List.range (st.topRound + 1)).filter fun r =>
    decide (t < r ∧ cfg.q ≤ (st.authorsAt r).card ∧ behind cfg st r)).foldr max t

/-- **Build the round above `r`**, referencing the node's own block `o`
there, if the build rule allows it, and release the memory below the
lowest round the node then reads. -/
def buildAbove (s : State Validator BlockId Payload) (r : ℕ) (o : Option BlockId) :
    Option (State Validator BlockId Payload × List (Output Validator BlockId Payload)) :=
  let refs := refsAt cfg s.memory r o s.evidence
  if cfg.q ≤ (s.memory.authorsAt r).card ∧ (r ∈ s.fired ∨ behind cfg s.memory r ∨
      (reachReady cfg s.memory refs r ∧ certReady cfg s.memory refs r)) then
    let b := blockOn cfg s.memory r refs s.evidence
    let id := cfg.idOf b
    if h : id ∉ s.disk.ids ∧ s.memory.Checks cfg.q cfg.xp id b then
      let s' := keep s id b h.1 (s.mirrors.checks_disk h.2).1 (s.mirrors.checks_disk h.2).2.1
      some (release cfg { s' with top := some (r + 1), own := some id, recovering := false },
        [.persist id b, .broadcast id b, .setTimer r (2 * cfg.timeout r)])
    else none
  else none

/-- **Build the next round**: above the node's top, referencing its own
block there; while recovering, above `jumpRound` with no own reference if
that round is above the top, and in either case only once no sync's block
lies above the round built. -/
def tryBuild (s : State Validator BlockId Payload) :
    Option (State Validator BlockId Payload × List (Output Validator BlockId Payload)) :=
  match s.top with
  | some t =>
    if s.recovering then
      let r := jumpRound cfg s.memory t
      if t < r then
        if syncTop s ≤ r + 1 ∧
            reachReady cfg s.memory (refsAt cfg s.memory r none s.evidence) r = true ∧
            certReady cfg s.memory (refsAt cfg s.memory r none s.evidence) r = true then
          buildAbove cfg s r none
        else none
      else if syncTop s ≤ t + 1 then buildAbove cfg s t s.own else none
    else buildAbove cfg s t s.own
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

/-- The slots below the slot rounds up to `R`: the slots `tryDecide` may
reach on a disk whose top round is `R`. -/
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

/-- **The frontier of a store for an author**: the least round at which it
holds no block of the author. -/
def gapOf (st : Store Validator BlockId Payload) (a : Validator) : ℕ :=
  ((List.range (st.topRound + 1)).find? fun r => decide (a ∉ st.authorsAt r)).getD
    (st.topRound + 1)

/-- **The frontier a request carries**: for each author, the least round
at which the disk holds no block of it, and `0` for a detected author. -/
def frontierOf (s : State Validator BlockId Payload) (a : Validator) : ℕ :=
  if a ∈ s.detected then 0 else gapOf s.disk a

/-- **One level of the stream's walk**: the front's blocks on the store,
not met already, that the stream carries, and their references next. -/
def streamLevel (st : Store Validator BlockId Payload) (carries : BlockId → Bool)
    (w : List BlockId × List BlockId) : List BlockId × List BlockId :=
  let front := (w.1.filter fun x => decide (x ∈ st.ids) && carries x && decide (x ∉ w.2)).dedup
  (front.flatMap fun x => (st.blk x).refs.sort (· ≤ ·), w.2 ++ front)

/-- **The stream for a request**: the blocks of the store in the history
of `t` that are `t`, asked for by name, or at or above their author's
frontier, reached through such blocks, in order of round. -/
def streamOf (st : Store Validator BlockId Payload) (t : BlockId) (fr : Validator → ℕ)
    (ids : List BlockId) : List (BlockId × Block Validator BlockId Payload) :=
  let carries := fun i =>
    decide (i = t ∨ i ∈ ids ∨ fr (st.blk i).creator ≤ (st.blk i).round)
  let found := ((streamLevel st carries)^[(st.blk t).round + 1] ([t], [])).2
  (found.map fun i => (i, st.blk i)).mergeSort fun x y => decide (x.2.round ≤ y.2.round)

/-- **One level of the walk through a stream piece**: the front's
identifiers the piece holds, not met already, and their references next. -/
def pieceLevel (L : List (BlockId × Block Validator BlockId Payload))
    (w : List BlockId × List BlockId) : List BlockId × List BlockId :=
  let front := (w.1.filter fun x => decide (x ∈ L.map Prod.fst) && decide (x ∉ w.2)).dedup
  (front.flatMap fun x => ((L.find? fun e => decide (e.1 = x)).map fun e =>
    e.2.refs.sort (· ≤ ·)).getD [], w.2 ++ front)

/-- **The part of a stream piece in the history of the block `t`**: its
blocks reached from `t` through its blocks, identified by their hash and
not the node's own, in order of round. -/
def inHistory (t : BlockId × Block Validator BlockId Payload)
    (L : List (BlockId × Block Validator BlockId Payload)) :
    List (BlockId × Block Validator BlockId Payload) :=
  let found := ((pieceLevel L)^[L.length + 1] ([t.1], [])).2
  (L.filter fun e => decide (e.1 = cfg.idOf e.2) && decide (e.2.creator ≠ cfg.me) &&
    decide (e.1 ∈ found)).mergeSort fun x y => decide (x.2.round ≤ y.2.round)

/-- **The identifiers to ask for by name** after a stream piece: the
references of its blocks that the disk does not hold. -/
def missingIn (s : State Validator BlockId Payload)
    (L : List (BlockId × Block Validator BlockId Payload)) : List BlockId :=
  ((L.flatMap fun e => e.2.refs.sort (· ≤ ·)).filter fun j => decide (j ∉ s.disk.ids)).dedup

/-- **Take a stream piece in**: its blocks, in order, each accepted if it
is new and ready. -/
def absorb (s : State Validator BlockId Payload)
    (L : List (BlockId × Block Validator BlockId Payload)) : State Validator BlockId Payload :=
  L.foldl (fun s e => accept cfg s e.1 e.2) s

/-- **Accept the syncs' blocks that are ready**, and drop the syncs done, in
passes, at most `fuel`. -/
def flushSyncs : ℕ → State Validator BlockId Payload → State Validator BlockId Payload
  | 0, s => s
  | fuel + 1, s =>
    let split := s.syncs.partition fun e => ready cfg s e.2.1
    if split.1.isEmpty then s
    else flushSyncs fuel (tidy (absorb cfg s (split.1.map (·.2.1))))

/-- **The request of a sync**. -/
def request (s : State Validator BlockId Payload)
    (e : Validator × (BlockId × Block Validator BlockId Payload) × List BlockId) :
    Output Validator BlockId Payload :=
  .sync e.1 e.2.1.1 (frontierOf s) e.2.2

/-- **Ask again** in every sync. -/
def resync (s : State Validator BlockId Payload) : List (Output Validator BlockId Payload) :=
  s.syncs.map (request s)

/-- **Send the node's top block again**: broadcast its block at its top
round, set the retry timer again and ask every peer for its block of that
round, then ask again in every sync. -/
def resend (s : State Validator BlockId Payload) : List (Output Validator BlockId Payload) :=
  (match s.top, s.own with
    | some r, some id =>
      [.broadcast id (s.disk.blk id), .setTimer (r - 1) (2 * cfg.timeout (r - 1)), .ask r]
    | _, _ => []) ++ resync s

/-- **The node's own block of round `r`** on its disk. -/
def ownAt (s : State Validator BlockId Payload) (r : ℕ) : Option BlockId :=
  Scheme.leastOf ((s.disk.atRound r).filter fun i => (s.disk.blk i).creator = cfg.me)

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

/-- **Build, decide, then accept the syncs' blocks that are ready**: a
block built can make one ready. -/
def pass (s : State Validator BlockId Payload) :
    State Validator BlockId Payload × List (Output Validator BlockId Payload) :=
  let b := progress cfg (s.disk.topRound + 2) s
  let d := decideStep cfg b.1
  (flushSyncs cfg (d.1.syncs.length + 1) d.1, b.2 ++ d.2)

/-- **A pass, then arming the top round's timer.** -/
def advance (s : State Validator BlockId Payload) :
    State Validator BlockId Payload × List (Output Validator BlockId Payload) :=
  let p := pass cfg s
  let a := arm cfg p.1
  (a.1, p.2 ++ a.2)

/-- **Advance until a pass changes nothing the next would read**: the
top, the syncs and the next undecided slot; at most `fuel` passes. -/
def quiesce : ℕ → State Validator BlockId Payload →
    State Validator BlockId Payload × List (Output Validator BlockId Payload)
  | 0, s => (s, [])
  | fuel + 1, s =>
    let r := advance cfg s
    if r.1.top = s.top ∧ r.1.syncs.length = s.syncs.length ∧ r.1.lo = s.lo then r
    else let r' := quiesce fuel r.1; (r'.1, r.2 ++ r'.2)

/-- **The passes a settle takes at most**: each but the last raises the
top or the next undecided slot, or leaves fewer syncs, within bounds the
state fixes. -/
def passes (s : State Validator BlockId Payload) : ℕ :=
  let B := max (s.top.getD 0) (max s.disk.topRound (syncTop s)) + 1
  let L := max s.lo (decidable cfg B)
  s.syncs.length + 2 * B + 2 * L + 1

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
      if h : id ∉ s.disk.ids ∧ rowValid cfg.q cfg.xp (Function.update s.disk.blk id b) b then
        let s' := keep s id b h.1 (fun _ hj => absurd hj (Finset.notMem_empty _))
          (fun j hj => absurd hj (Finset.notMem_empty j))
        let r := settle cfg { s' with top := some 0, own := some id, recovering := false }
        (r.1, [.persist id b, .broadcast id b, .setTimer 0 (2 * cfg.timeout 0)] ++ r.2)
      else (s, [])
    else (s, [])
  | .deliver u id b =>
    if id = cfg.idOf b ∧ b.creator = u ∧ u ≠ cfg.me ∧ u ∉ s.detected ∧ id ∉ s.disk.ids then
      if ready cfg s (id, b) then settle cfg (tidy (accept cfg s id b))
      else if (0 < b.round → cfg.q ≤ b.refs.card) ∧ (s.syncs.find? fun e => decide (e.1 = u)).all
          (fun e => decide (e.2.1.2.round < b.round)) then
        let e := (u, (id, b), ([] : List BlockId))
        let s₁ := { s with syncs := e :: s.syncs.filter fun e => decide (e.1 ≠ u) }
        let r := settle cfg s₁
        (r.1, request s₁ e :: r.2)
      else (s, [])
    else (s, [])
  | .stream u L =>
    match s.syncs.find? fun e => decide (e.1 = u) with
    | none => (s, [])
    | some e =>
      let L' := inHistory cfg e.2.1 L
      let s₁ := tidy (absorb cfg s L')
      match s₁.syncs.find? fun e => decide (e.1 = u) with
      | none => settle cfg s₁
      | some e₁ =>
        let asked := (e₁.2.2 ++ missingIn s₁ (e₁.2.1 :: L')).dedup
        let e₂ := (u, e₁.2.1, asked)
        let s₂ := { s₁ with syncs := s₁.syncs.map fun x => if x.1 = u then e₂ else x }
        let r := settle cfg s₂
        let moved := s₂.disk.ids.card ≠ s.disk.ids.card ∨ asked.length ≠ e₁.2.2.length
        (r.1, (if moved then [request s₂ e₂] else []) ++ r.2)
  | .timer r =>
    let res := settle cfg { s with fired := fire s r, recovering := false }
    if res.1.top = s.top ∧ (s.top = some r ∨ s.top = some (r + 1)) then
      (res.1, res.2 ++ resend cfg res.1)
    else res
  | .syncRequest peer t fr ids =>
    let L := streamOf s.disk t fr ids
    (s, if peer ∈ s.detected ∨ L.isEmpty then [] else [.stream peer L])
  | .ask peer r =>
    (s, if peer ∈ s.detected then [] else match ownAt cfg s r with
      | some i => [.send peer i (s.disk.blk i)]
      | none => [])
  | .restart =>
    let r := settle cfg { s with recovering := true }
    (r.1, resend cfg s ++ rearm cfg s ++ r.2)

end Node

end LeanDag
