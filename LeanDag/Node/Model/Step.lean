import LeanDag.Node.Store
import Mathlib.Data.Finset.Sort
/-!
# An honest node — its transition function

`docs/validator.md` §3. `step cfg s i` is the node's response to the
input `i` in the state `s`: the new state and the outputs.

* **Receipt** (`deliver`): a block whose identifier is its hash, not the
  node's own, and new, waits in `pending` until its references are
  accepted and it satisfies `rowValid q`, or until the horizon reaches
  it, and is then accepted (`flush`).
* **Building** (`tryBuild`): round `r + 1`, above the node's top `r`,
  once the store holds `q` authors of round `r` and either the round's
  timer fired or the block would reach every leader block of a slot
  whose wave is at a vote round (`reachReady`) and certify one at a
  decision round (`certReady`). The block references one accepted block
  per author of round `r`, the node's own for itself when it built
  there, which is the self-parent rule of an honest node, and the least
  identifier otherwise; where these fail the tests and the references
  of a held round-`r + 1` block of another author pass them, it takes
  those, with its own block for itself (`refsAt`). It is persisted, then
  broadcast, then the round's timer is set.
* **Exclusion** (`twinned`, `State.exposed`, `evidence`, `usable`): a
  node given two blocks of one author at one round holds that author
  exposed; it references a block of an exposed author only if a held
  block one round above, by an author not exposed, references it, and
  counts toward its quorum only the authors of blocks it may reference;
  the first time, it relays both blocks to every peer, so its peers
  exclude the author too.
* **Deciding** (`decideStep`): `tryDecide` from the next undecided slot
  to the last slot at a round the store holds; the decisions are kept
  (`State.decided`), the latest first.
* **Checkpoints** (`proposeAt`, `record`, `certify`): at each multiple
  of `m` slots above the height last proposed and the certificate's that
  the decided frontier reaches, the node signs and sends a proposal of
  the head of the chain of its decisions below it (`Config.headOf`),
  extending the head it last proposed by the decisions since. It keeps
  its peers' proposals, one per signer and height above its
  certificate's height, and above `lo + ahead` only each signer's
  latest; its own it reads off its decisions (`ownHead`). The node and
  peers making `q` distinct signers of the head of its decisions at a
  height it has proposed make a certificate; the node keeps the highest,
  and serves it with the decisions it certifies.
* **Announcing** (`collect`, `confirms`, `confirm`): a node that raises
  its horizon announces its certificate to every peer. A node given a
  certificate above its own, of `q` distinct signers, at a multiple of
  `m` it has decided and of the head of its decisions there, keeps it; announced one at a
  height it has not decided, it asks the sender for the decisions
  certified from its next undecided slot up.
* **Adopting** (`adoptable`, `adopt`): served a certificate above its
  next undecided slot with decisions from that slot or below,
  whose chain extends its own to the certificate's head, it outputs
  those from that slot and moves its next slot to the certificate's
  height. Its horizon then rises with its peers', so it takes the blocks
  at their horizon as they did.

* **Fetching** (`walkLevel`, `missing`, `answer`): after a delivery, the missing part
  of the delivered block's history, walked through the pending blocks, is
  asked of its author, with the node's horizon, once on account of each
  block that needs it; a request is answered with the blocks asked for
  that the store holds and their histories above the asker's horizon.
* **Collecting** (`collect`): the horizon rises to `Λ` below the lesser
  of the round of the last slot decided and certified and the node's
  round, and what lies below it is dropped.
* **Settling** (`settle`, `quiesce`): after each change to its state,
  peers' proposals included, the node builds, decides, collects and
  accepts what that allows, in passes, until a pass changes none of its
  top, its horizon, its pending blocks, its next undecided slot and its
  certificate's height.

* **Restarting** (`State.recover`): a crash keeps the store, the next
  slot and the top, and loses what is pending, the timers and the
  requests; the downtime counts as the top round's timer firing.
  `State.persisted` is what the node writes, and `resume` rebuilds a
  state from it.
* **Resuming** (`tryResume`, `resumeAt`, `caughtUp`): a recovering node
  whose store holds blocks of `q` authors it may reference at a round
  above its top, two above if it built at its top, moves its top there
  without a block of its own, and builds from there. A recovering node
  that builds a block once some peer offered it a horizon, at most `f`
  horizons offered lie above the block's round, and at most `f` authors
  of blocks it holds or has pending lie more than one round above it, no
  longer recovers.
* **Stalling** (`stalledAt`, `stallsTwice`, `timerState`, `timerOut`): a
  node still at round `r` when `r`'s timer fires sets the timer again. A
  node for which the round of the last slot it has decided and its
  certificate certifies lies more than `Λ` above its top `r`, at two
  firings of `r`'s timer, recovers again, as after a restart, and asks
  for bases.
* **Bootstrap** (`jumpRound`, `docs/validator.md` §3.6): a restarted node
  asks its peers for their bases, again whenever a delivered block, kept
  or not, lies `Λ + 2` rounds above the one it last asked on, when the
  timer of its top round fires (`timerAsks`), and when a peer it holds no
  base of asks for its base; a peer answers with its horizon and its
  certificate, and sends the blocks of its store as blocks. The node
  keeps each peer's horizon, and takes certificates and blocks as any
  node does. Once a peer's horizon lies above its top and at or below
  the round of the last slot its certificate certifies, its top moves to
  the highest such horizon without a block of its own, and its horizon
  follows (`horizonAt`), taking the blocks there without their
  references.

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
  /-- Restarted, and not yet resumed. -/
  recovering : Bool
  /-- The horizons offered since the restart, one per peer. -/
  offers : List (Validator × ℕ)
  /-- The round of the delivered block on whose account the node last
  asked for the bases. -/
  asked : ℕ
  /-- The decisions the node output, the latest first. -/
  decided : List (ℕ × Option BlockId)
  /-- The height the node last proposed. -/
  lastProposed : ℕ
  /-- The head of the chain of its decisions below that height. -/
  chain : BlockId
  /-- The proposals kept, the node's own included: the signer, the height
  and the head. -/
  props : List (Validator × ℕ × BlockId)
  /-- The highest certificate the node holds. -/
  cert : Option (Cert Validator BlockId)
  /-- The authors the node was given two blocks of at one round. -/
  exposed : Finset Validator
  /-- The round at whose timer the node last found itself stalled. -/
  stalled : Option ℕ

variable (cfg : Config Validator BlockId Payload)

/-- The node's genesis block. -/
def Config.genesis : Block Validator BlockId Payload := ⟨0, cfg.me, ∅, cfg.payload 0⟩

/-- The state before start. -/
def State.init : State Validator BlockId Payload :=
  ⟨Store.empty cfg.genesis, [], none, none, ∅, 0, [], false, [], 0, [], 0, cfg.root, [], none,
    ∅, none⟩

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

/-- A pending block is ready when it is at or below the horizon, or its
references are accepted, one round below it, and it is valid at the row.
A block above the horizon that is not valid waits for the horizon to
reach it, as one whose references are missing does. -/
def ready (s : Store Validator BlockId Payload) (e : BlockId × Block Validator BlockId Payload) :
    Bool :=
  decide (e.2.round ≤ s.base) || decide (e.2.refs ⊆ s.ids ∧
    (∀ j ∈ e.2.refs, (s.blk j).round + 1 = e.2.round) ∧
    rowValid cfg.q (Function.update s.blk e.1 e.2) e.2)

/-- **Accept what the pending blocks allow**, in passes, at most `fuel`. -/
def flush : ℕ → Store Validator BlockId Payload → List (BlockId × Block Validator BlockId Payload) →
    Store Validator BlockId Payload × List (BlockId × Block Validator BlockId Payload)
  | 0, s, pend => (s, pend)
  | fuel + 1, s, pend =>
    let split := pend.partition fun e => ready cfg s e
    if split.1.isEmpty then (s, pend)
    else flush fuel (split.1.foldl (fun s e => accept cfg s e.1 e.2) s) split.2

/-- **Whether the node may reference the block `i`**, holding the authors
`X` exposed (`docs/validator.md` §3.10): `i`'s author lies outside `X`,
or a held block one round above, by an author outside `X`, references
`i`. -/
def usable (s : Store Validator BlockId Payload) (X : Finset Validator) (i : BlockId) : Bool :=
  decide ((s.blk i).creator ∉ X) ||
    decide (((blocksAt s.toRecord ((s.blk i).round + 1)).filter fun c =>
      (s.blk c).creator ∉ X ∧ i ∈ (s.blk c).refs).Nonempty)

/-- The authors of the held round-`r` blocks the node may reference,
holding the authors `X` exposed. -/
def usableAuthors (s : Store Validator BlockId Payload) (X : Finset Validator) (r : ℕ) :
    Finset Validator :=
  creatorsOf s.blk ((blocksAt s.toRecord r).filter fun i => usable s X i)

/-- **The references of the node's next block**, above round `r`: one
accepted block per author of round `r` among those it may reference,
holding `X` exposed, the node's own block `o` there for itself if it
built one, and the least identifier otherwise. -/
def refsFor (s : Store Validator BlockId Payload) (r : ℕ) (o : Option BlockId)
    (X : Finset Validator) : Finset BlockId :=
  let R := (blocksAt s.toRecord r).filter fun i => usable s X i
  (creatorsOf s.blk R).biUnion fun a =>
    if a = cfg.me ∧ o.isSome then o.toFinset
    else (Scheme.leastOf (R.filter fun i => (s.blk i).creator = a)).toFinset

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

/-- **The references a held round-`r + 1` block `c` lends**: `c`'s that
the node may reference, holding `X` exposed, with the node's own block
`o` put in for itself. -/
def lent (s : Store Validator BlockId Payload) (c : BlockId) (o : Option BlockId)
    (X : Finset Validator) : Finset BlockId :=
  ((s.blk c).refs.filter fun j => (s.blk j).creator ≠ cfg.me ∧ usable s X j = true) ∪
    o.toFinset

/-- **References `R` the node can build on above round `r`**: the block
they make is new, and valid at the row. -/
def buildable (s : Store Validator BlockId Payload) (r : ℕ) (R : Finset BlockId) : Bool :=
  let b : Block Validator BlockId Payload := ⟨r + 1, cfg.me, R, cfg.payload (r + 1)⟩
  decide (cfg.idOf b ∉ s.ids ∧ s.base ≤ b.round ∧ (s.base < b.round → b.refs ⊆ s.ids) ∧
    (s.base < b.round → ∀ j ∈ b.refs, (s.blk j).round + 1 = b.round) ∧
    rowValid cfg.q (Function.update s.blk (cfg.idOf b) b) b)

/-- **The references of the node's next block**, above round `r`, each
one the node may reference, holding `X` exposed: those of `refsFor` if they pass the reach and
certificate tests; else those lent by the first held round-`r + 1` block
of another author that pass them and can be built on; else those of
`refsFor`. A node behind then reaches what a peer reached. -/
def refsAt (s : Store Validator BlockId Payload) (r : ℕ) (o : Option BlockId)
    (X : Finset Validator) : Finset BlockId :=
  let ready := fun R => reachReady cfg s R r && certReady cfg s R r
  let own := refsFor cfg s r o X
  if ready own then own
  else ((((blocksAt s.toRecord (r + 1)).sort (· ≤ ·)).filter fun c =>
      decide ((s.blk c).creator ≠ cfg.me)).map (lent cfg s · o X) |>.find? fun R =>
        ready R && buildable cfg s r R).getD own

/-- **The authors of blocks the node holds or has pending above round
`t + 1`.** -/
def aheadOf (s : State Validator BlockId Payload) (t : ℕ) : Finset Validator :=
  (s.store.ids.filter fun i => t + 1 < (s.store.blk i).round).image
      (fun i => (s.store.blk i).creator) ∪
    ((s.pending.filter fun e => decide (t + 1 < e.2.round)).map (·.2.creator)).toFinset

/-- **Whether the node has caught up at round `t`**: some peer offered it
a horizon, at most `f` of the horizons offered lie above `t`, and at
most `f` authors of blocks it holds or has pending lie above `t + 1`. -/
def caughtUp (s : State Validator BlockId Payload) (t : ℕ) : Bool :=
  !s.offers.isEmpty && decide ((s.offers.filter fun o => t < o.2).length ≤ cfg.f) &&
    decide ((aheadOf s t).card ≤ cfg.f)

/-- **Build the next round**, if the build rule allows it; a recovering
node that catches up there no longer recovers. -/
def tryBuild (s : State Validator BlockId Payload) :
    Option (State Validator BlockId Payload × List (Output Validator BlockId Payload)) :=
  match s.top with
  | some r =>
    let refs := refsAt cfg s.store r s.own s.exposed
    if cfg.q ≤ (usableAuthors s.store s.exposed r).card ∧
        (r ∈ s.fired ∨ (reachReady cfg s.store refs r ∧ certReady cfg s.store refs r)) then
      let b : Block Validator BlockId Payload := ⟨r + 1, cfg.me, refs, cfg.payload (r + 1)⟩
      let id := cfg.idOf b
      if h : id ∉ s.store.ids ∧ s.store.base ≤ b.round ∧
          (s.store.base < b.round → b.refs ⊆ s.store.ids) ∧
          (s.store.base < b.round → ∀ j ∈ b.refs, (s.store.blk j).round + 1 = b.round) ∧
          rowValid cfg.q (Function.update s.store.blk id b) b then
        let st := s.store.insert id b h.1 h.2.1 h.2.2.1 h.2.2.2.1
        let s₁ := { s with store := st, top := some (r + 1), own := some id }
        let s₂ := { s₁ with recovering := s.recovering && !caughtUp cfg s (r + 1) }
        some (s₂,
          [.persist id b, .broadcast id b, .setTimer (r + 1) (cfg.timeout (r + 1))])
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
then set the timer of its round. -/
def built (bs : List (BlockId × Block Validator BlockId Payload)) :
    List (Output Validator BlockId Payload) :=
  bs.flatMap fun e =>
    [.persist e.1 e.2, .broadcast e.1 e.2, .setTimer e.2.round (cfg.timeout e.2.round)]

/-- **The store as a list**: its identifiers in order, each with its
block as kept. -/
def Store.window (st : Store Validator BlockId Payload) :
    List (BlockId × Block Validator BlockId Payload) :=
  (st.ids.sort (· ≤ ·)).map fun j => (j, st.map.getD j st.junk)

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

/-- **A twin of a delivered block** the node holds: a stored or pending
block of the block's author at its round, with its content. -/
def twinOf (s : State Validator BlockId Payload) (b : Block Validator BlockId Payload) :
    Option (BlockId × Block Validator BlockId Payload) :=
  match (s.store.ids.sort (· ≤ ·)).find? fun j =>
      decide ((s.store.blk j).creator = b.creator ∧ (s.store.blk j).round = b.round) with
  | some j => some (j, s.store.map.getD j s.store.junk)
  | none => s.pending.find? fun e => decide (e.2.creator = b.creator ∧ e.2.round = b.round)

/-- **Whether a delivery shows its author equivocating**: the node holds
another block of the block's author at its round. -/
def twinned (s : State Validator BlockId Payload) (b : Block Validator BlockId Payload) : Bool :=
  (twinOf s b).isSome

/-- **The evidence a delivery relays**: both blocks, when it first shows
its author equivocating. -/
def evidence (s : State Validator BlockId Payload) (id : BlockId)
    (b : Block Validator BlockId Payload) : List (Output Validator BlockId Payload) :=
  match twinOf s b with
  | some e => if b.creator ∈ s.exposed then [] else [.relay id b, .relay e.1 e.2]
  | none => []

/-- The height of the node's certificate, `0` without one. -/
def State.certHeight (s : State Validator BlockId Payload) : ℕ :=
  (s.cert.map Cert.height).getD 0

/-- The proposals above the height of the certificate `c`, taken as `0` without one. -/
def above (c : Option (Cert Validator BlockId)) (ps : List (Validator × ℕ × BlockId)) :
    List (Validator × ℕ × BlockId) :=
  ps.filter fun x => (c.map Cert.height).getD 0 < x.2.1

/-- The number of slots at rounds at most `R`. -/
def decidable (R : ℕ) : ℕ := cfg.m * (R / cfg.per + 1)

/-- **The head the node signs at height `k`**: the head of the chain of
its first `k` decisions. -/
def ownHead (s : State Validator BlockId Payload) (k : ℕ) : BlockId :=
  cfg.headOf (s.decided.reverse.take k)

/-- **Certify**: the certificate the node holds once it has proposed the
head `h` at height `k`, a multiple of `m` it has reached, the head of its
own decisions there, and the peers' proposals it keeps add signers of
`h` at `k` to `q` distinct signers with itself, if `k` lies above its
certificate's height. -/
def certify (s : State Validator BlockId Payload) (k : ℕ) (h : BlockId) :
    Option (Cert Validator BlockId) :=
  let signers := (cfg.me :: (s.props.filter fun x => decide (x.2 = (k, h))).map Prod.fst).dedup
  if cfg.q ≤ signers.length ∧ s.certHeight < k ∧ cfg.m ∣ k ∧ k ≤ s.lastProposed ∧
      h = ownHead cfg s k then
    some ⟨k, h, signers⟩
  else s.cert

/-- **Certify at `k`**: keep the certificate `certify` gives, and only the
proposals above it. -/
def certifyAt (s : State Validator BlockId Payload) (k : ℕ) (h : BlockId) :
    State Validator BlockId Payload :=
  let c := certify cfg s k h
  { s with props := above c s.props, cert := c }

/-- **Record a peer's proposal**, then certify: one proposal kept per
signer and height, the signer's others above `lo + ahead` dropped if this
one lies there too, and none at or below the certificate's height. -/
def record (s : State Validator BlockId Payload) (v : Validator) (k : ℕ) (h : BlockId) :
    State Validator BlockId Payload :=
  let w := s.lo + cfg.ahead
  let ps := (v, k, h) :: s.props.filter fun x => x.1 ≠ v ∨ x.2.1 ≠ k ∧ (k ≤ w ∨ x.2.1 ≤ w)
  certifyAt cfg { s with props := ps } k h

/-- **The next height to propose**: the least multiple of `m` above both
the height last proposed and the certificate's height. -/
def nextHeight (s : State Validator BlockId Payload) : ℕ :=
  cfg.m * (max s.lastProposed s.certHeight / cfg.m + 1)

/-- **Propose once**: if the decided frontier reaches the next height `k`,
extend the head last proposed by the decisions of slots `lastProposed …
k − 1`, the latest `lo − lastProposed` kept, sign the head at `k`, and
certify there. -/
def proposeNext (s : State Validator BlockId Payload) :
    Option (State Validator BlockId Payload × Output Validator BlockId Payload) :=
  let k := nextHeight cfg s
  if k ≤ s.lo then
    let h := ((s.decided.take (s.lo - s.lastProposed)).reverse.take (k - s.lastProposed)).foldl
      cfg.extend s.chain
    some (certifyAt cfg { s with lastProposed := k, chain := h } k h, .propose k h)
  else none

/-- Propose at most `fuel` times. -/
def proposeFrom : ℕ → State Validator BlockId Payload →
    State Validator BlockId Payload × List (Output Validator BlockId Payload)
  | 0, s => (s, [])
  | fuel + 1, s =>
    match proposeNext cfg s with
    | some (s₁, o) => let r := proposeFrom fuel s₁; (r.1, o :: r.2)
    | none => (s, [])

/-- **Propose** at every height the decided frontier reaches. -/
def proposeAt (s : State Validator BlockId Payload) :
    State Validator BlockId Payload × List (Output Validator BlockId Payload) :=
  proposeFrom cfg (s.lo + 1) s

/-- **Decide**: `tryDecide` from the next undecided slot to the last slot
at a round the store holds; output and keep what it decides; then
propose. -/
def decideStep (s : State Validator BlockId Payload) :
    State Validator BlockId Payload × List (Output Validator BlockId Payload) :=
  letI := cfg.slots
  let N := decidable cfg s.store.topRound
  if s.lo < N then
    let ds := Scheme.tryDecide cfg.p cfg.σ s.store.toRecord
      s.store.view s.lo (N - 1)
    let r := proposeAt cfg { s with lo := s.lo + ds.length, decided := ds.reverse ++ s.decided }
    (r.1, ds.map (fun e => .commit e.1 e.2) ++ r.2)
  else proposeAt cfg s

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

/-- **The blocks a request is answered with**: each block asked for that
the store holds, then their histories in the store at or above the
asker's horizon `G`, searched no deeper than `G`. -/
def answerIds (s : State Validator BlockId Payload) (G : ℕ) (ids : List BlockId) : List BlockId :=
  let held := ids.filter fun j => decide (j ∈ s.store.ids)
  (held ++ held.flatMap fun j =>
    ((historyUptoFrom s.store.blk ((s.store.blk j).round + 1 - G) j).filter fun x =>
      decide (x ∈ s.store.ids ∧ G ≤ (s.store.blk x).round)).sort (· ≤ ·)).dedup

/-- **Answer a request**: send the peer the blocks of `answerIds`. A
missing history then arrives in one round trip, whatever its depth. -/
def answer (s : State Validator BlockId Payload) (peer : Validator) (G : ℕ)
    (ids : List BlockId) : List (Output Validator BlockId Payload) :=
  (answerIds s G ids).map fun j => .send peer j (s.store.map.getD j s.store.junk)

/-- **The horizon a node at top `t` raises to**: `Λ` below the lesser of
the round of the last slot both decided and certified and `t`; for a
recovering node, `Λ` below that round, but not above `t`. -/
def horizonAt (s : State Validator BlockId Payload) (t : ℕ) : ℕ :=
  let F := cfg.per * ((min s.lo s.certHeight - 1) / cfg.m)
  if s.recovering then min (F - cfg.lag) t else min F t - cfg.lag

/-- **Raise the horizon** (`docs/validator.md` §3.4) to `horizonAt`;
drop what lies below it, and announce the certificate. -/
def collect (s : State Validator BlockId Payload) :
    State Validator BlockId Payload × List (Output Validator BlockId Payload) :=
  match s.top with
  | some t =>
    let G := horizonAt cfg s t
    if h : s.store.base < G then
      let st := s.store.prune G h.le
      let pend := s.pending.filter fun e => G ≤ e.2.round
      let req := s.requested.filter fun x => G ≤ x.2.2
      let s₁ := { s with store := st, pending := pend, fired := s.fired.filter (G ≤ ·) }
      ({ s₁ with requested := req },
        .prune G :: s.cert.toList.map .announce)
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

/-- **The highest round at or above `t` at which the store holds blocks
of `q` authors the node may reference, holding `X` exposed**, if any. -/
def quorumRound (st : Store Validator BlockId Payload) (X : Finset Validator) (t : ℕ) :
    Option ℕ :=
  ((List.range (st.topRound + 1)).filter fun R =>
    decide (t ≤ R) && decide (cfg.q ≤ (usableAuthors st X R).card) &&
      decide (0 < (authorsIn st.toRecord st.ids R).card)).max?

/-- **The round a recovering node jumps to**: the highest horizon a peer
offered above its top `t`, at or below the round of the last slot it has
decided and its certificate certifies. -/
def jumpRound (s : State Validator BlockId Payload) (t : ℕ) : Option ℕ :=
  if 0 < min s.lo s.certHeight then
    ((s.offers.map Prod.snd).filter fun G =>
      decide (t < G ∧ G ≤ cfg.slots.slotRound (min s.lo s.certHeight - 1))).max?
  else none

/-- **Resume at a quorum**: the highest round above the top `t`, two above
if the node built at `t`, at which the store holds `q` authors it may
reference; the top moves there, with no block of its own, that round's
timer counts as fired, and the node no longer recovers. -/
def resumeAt (s : State Validator BlockId Payload) (t : ℕ) : Option (State Validator BlockId Payload) :=
  match quorumRound cfg s.store s.exposed (t + 1) with
  | some R =>
    if s.own = none ∨ t + 2 ≤ R then
      let s' := { s with top := some R, own := none }
      some { s' with fired := insert R s.fired, recovering := false }
    else none
  | none => none

/-- **Resume after a restart** (`docs/validator.md` §3.5, §3.6): a
recovering node whose jump round lies above its top moves its top there,
with no block of its own, and that round's timer counts as fired; it
still recovers. Otherwise it resumes at a quorum (`resumeAt`). -/
def tryResume (s : State Validator BlockId Payload) : Option (State Validator BlockId Payload) :=
  match s.recovering, s.top with
  | true, some t =>
    match jumpRound cfg s t with
    | some J => some { s with top := some J, own := none, fired := insert J s.fired }
    | none => resumeAt cfg s t
  | _, _ => none

/-- **Advance until a pass changes nothing the next would read**: the top,
the horizon, the pending blocks, the next undecided slot and the
certificate's height; at most `fuel` passes. -/
def quiesce : ℕ → State Validator BlockId Payload →
    State Validator BlockId Payload × List (Output Validator BlockId Payload)
  | 0, s => (s, [])
  | fuel + 1, s =>
    let r := advance cfg s
    if r.1.top = s.top ∧ r.1.store.base = s.store.base ∧ r.1.pending.length = s.pending.length ∧
        r.1.lo = s.lo ∧ r.1.certHeight = s.certHeight then r
    else let r' := quiesce fuel r.1; (r'.1, r.2 ++ r'.2)

/-- The highest round of a pending block, `0` without one. -/
def pendingTop (s : State Validator BlockId Payload) : ℕ :=
  (s.pending.map (·.2.round)).foldr max 0

/-- **The passes a settle takes at most**: each but the last raises the
top, the horizon, the next undecided slot or the certificate's height, or
leaves fewer blocks pending, within bounds the state fixes. -/
def passes (s : State Validator BlockId Payload) : ℕ :=
  let B := max (s.top.getD 0) (max s.store.topRound (pendingTop s)) + 1
  let L := max s.lo (decidable cfg B)
  s.pending.length + 2 * B + 2 * L + 1

/-- **Resume if it can, then advance until nothing changes**, after a
change to the state. -/
def settle (s : State Validator BlockId Payload) :
    State Validator BlockId Payload × List (Output Validator BlockId Payload) :=
  match tryResume cfg s with
  | some s' => quiesce cfg (passes cfg s') s'
  | none => quiesce cfg (passes cfg s) s

/-- **What the node persists**: its accepted blocks, the horizon, the next
undecided slot, its top round and its own block there, its decisions,
the height it last proposed and the head there, and its certificate. -/
def State.persisted (s : State Validator BlockId Payload) : Persisted Validator BlockId Payload :=
  ⟨s.store.window, s.store.base, s.lo, s.top, s.own, s.decided, s.lastProposed, s.chain, s.cert⟩

/-- **The state after a crash and restart**: the store, the next slot,
the top, the decisions and the certificate kept; nothing pending, asked
for, proposed by peers, offered, exposed or stalled; the top round's
timer fired, since the node was away; recovering. -/
def State.recover (s : State Validator BlockId Payload) : State Validator BlockId Payload :=
  let s' := { s with pending := [], fired := (s.top.map fun t => {t}).getD ∅ }
  let s'' := { s' with requested := [], recovering := true, offers := [], asked := 0 }
  { s'' with props := [], exposed := ∅, stalled := none }

/-- **Resume from what was persisted**: the store rebuilt from the window
at the horizon, if the window is closed under references one round below
and lies at or above the horizon; the top and the own block as
persisted, with the decisions and the certificate; and the rest as
`State.recover` sets it. -/
def resume (ps : Persisted Validator BlockId Payload) : Option (State Validator BlockId Payload) :=
  let map : Std.TreeMap BlockId (Block Validator BlockId Payload) compare :=
    Std.TreeMap.ofList ps.window
  let ids := (ps.window.map Prod.fst).toFinset
  if h : (∀ i ∈ ids, ∀ j ∈ (lookup map cfg.genesis ps.horizon i).refs, j ∈ ids) ∧
      (∀ i ∈ ids, ∀ j ∈ (lookup map cfg.genesis ps.horizon i).refs,
        (lookup map cfg.genesis ps.horizon j).round + 1 =
          (lookup map cfg.genesis ps.horizon i).round) ∧
      ∀ i ∈ ids, ps.horizon ≤ (lookup map cfg.genesis ps.horizon i).round then
    let st : Store Validator BlockId Payload :=
      ⟨map, ids, cfg.genesis, ps.horizon, h.1, h.2.1, h.2.2⟩
    some ⟨st, [], ps.top, ps.own, (ps.top.map fun t => {t}).getD ∅, ps.lo, [], true, [], 0,
      ps.decided, ps.lastProposed, ps.chain, [], ps.cert, ∅, none⟩
  else none

/-- **Serve certified decisions** from slot `lo` up: the node's
certificate, if above `lo`, with the decisions of slots `lo … height − 1`. -/
def serveFrom (s : State Validator BlockId Payload) (peer : Validator) (lo : ℕ) :
    List (Output Validator BlockId Payload) :=
  match s.cert with
  | some c =>
    if lo < c.height ∧ c.height ≤ s.lo then
      [.serveCert peer c ((s.decided.drop (s.lo - c.height)).take (c.height - lo)).reverse]
    else []
  | none => []

/-- **Decisions the node can adopt**: a certificate of `q` distinct
signers at a multiple of `m` above its next undecided slot, served with
the decisions of the slots from there to its height, in order, whose
chain extends the node's own to the certificate's head. -/
def adoptable (s : State Validator BlockId Payload) (c : Cert Validator BlockId)
    (ds : List (ℕ × Option BlockId)) : Bool :=
  decide (cfg.q ≤ c.signers.length) && decide c.signers.Nodup &&
    decide (s.lo < c.height ∧ cfg.m ∣ c.height) &&
    decide (ds.map Prod.fst = List.range' s.lo (c.height - s.lo)) &&
    decide (((s.decided.take (s.lo - s.lastProposed)).reverse ++ ds).foldl cfg.extend s.chain =
      c.head)

/-- **Adopt certified decisions**: output and keep them, move the next
slot to the certificate's height, keep the certificate if higher and
only the proposals above the certificate held, then settle. -/
def adopt (s : State Validator BlockId Payload) (c : Cert Validator BlockId)
    (ds : List (ℕ × Option BlockId)) :
    State Validator BlockId Payload × List (Output Validator BlockId Payload) :=
  let ct := if s.certHeight < c.height then some c else s.cert
  let s₁ := { s with decided := ds.reverse ++ s.decided, lo := c.height, cert := ct }
  let r := settle cfg { s₁ with props := above ct s.props }
  (r.1, ds.map (fun e => .commit e.1 e.2) ++ r.2)

/-- **A certificate the node can confirm**: `q` distinct signers, above
its certificate's height and at or below its next undecided slot, at a
multiple of `m`, of the head of its own decisions there. -/
def confirms (s : State Validator BlockId Payload) (c : Cert Validator BlockId) : Bool :=
  decide (cfg.q ≤ c.signers.length) && decide c.signers.Nodup && decide (s.certHeight < c.height) &&
    decide (c.height ≤ s.lo) && decide (cfg.m ∣ c.height) && decide (c.head = ownHead cfg s c.height)

/-- **Confirm a certificate**: keep it, and only the proposals above it,
then settle. -/
def confirm (s : State Validator BlockId Payload) (c : Cert Validator BlockId) :
    State Validator BlockId Payload × List (Output Validator BlockId Payload) :=
  settle cfg { s with cert := some c, props := above (some c) s.props }

/-- **Whether the node is stalled at round `r`**: it does not recover, its
top is `r`, and the round of the last slot it has decided and its
certificate certifies lies more than `Λ` above `r`. -/
def stalledAt (s : State Validator BlockId Payload) (r : ℕ) : Bool :=
  !s.recovering && decide (s.top = some r ∧ 0 < min s.lo s.certHeight ∧
    r + cfg.lag < cfg.slots.slotRound (min s.lo s.certHeight - 1))

/-- **Whether the timer of round `r` finds the node stalled there a second
time**: it is stalled at `r`, and was at an earlier firing of the timer. -/
def stallsTwice (s : State Validator BlockId Payload) (r : ℕ) : Bool :=
  stalledAt cfg s r && decide (s.stalled = some r)

/-- **Whether the timer of round `r` makes the node ask for bases**: it
recovers at `r`, or the timer finds it stalled there a second time. -/
def timerAsks (s : State Validator BlockId Payload) (r : ℕ) : Bool :=
  s.recovering && decide (s.top = some r) || stallsTwice cfg s r

/-- **The state the timer of round `r` leaves before settling**: the
round's timer fired; a node stalled at `r` notes it, and recovers if the
timer finds it stalled there a second time. -/
def timerState (s : State Validator BlockId Payload) (r : ℕ) : State Validator BlockId Payload :=
  { s with
    fired := insert r s.fired
    recovering := s.recovering || stallsTwice cfg s r
    asked := if stallsTwice cfg s r then r else s.asked
    stalled := if stalledAt cfg s r then some r else s.stalled }

/-- **What the timer of round `r` sends before settling**: a node still at
`r` sets the timer again, and asks for bases if `timerAsks`. -/
def timerOut (s : State Validator BlockId Payload) (r : ℕ) :
    List (Output Validator BlockId Payload) :=
  (if s.top = some r then [.setTimer r (cfg.timeout r)] else []) ++
    if timerAsks cfg s r then [.requestBase] else []

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
      let X := if twinned s b then insert b.creator s.exposed else s.exposed
      let s₀ := { s with store := fl.1, pending := fl.2 }
      let s₁ := { s₀ with exposed := X }
      let miss := missing s₁ id b
      let req := s₁.requested ++ miss.map fun x => (x.1, id, x.2)
      let ask := s.recovering ∧ s.asked + cfg.lag + 2 ≤ b.round
      let top := if ask then b.round else s.asked
      let r := settle cfg { s₁ with requested := req, asked := top }
      (r.1, evidence s id b ++
        (if miss.isEmpty then [] else [.fetch b.creator s.store.base (miss.map Prod.fst)]) ++
        (if ask then [.requestBase] else []) ++ r.2)
    else if id = cfg.idOf b ∧ b.creator ≠ cfg.me ∧ s.recovering ∧
        s.asked + cfg.lag + 2 ≤ b.round then
      ({ s with asked := b.round, recovering := true }, [.requestBase])
    else (s, [])
  | .timer r =>
    let x := settle cfg (timerState cfg s r)
    (x.1, timerOut cfg s r ++ x.2)
  | .fetchRequest peer G ids => (s, answer s peer G ids)
  | .restart => let r := settle cfg s.recover; (r.1, .requestBase :: r.2)
  | .baseRequest peer =>
    (s, .serveBase peer s.store.base :: s.cert.toList.map (fun c =>
      .serveCert peer c (s.decided.drop (s.lo - c.height)).reverse) ++
      s.store.window.map (fun e => .send peer e.1 e.2) ++
      if s.recovering ∧ peer ≠ cfg.me ∧ peer ∉ s.offers.map Prod.fst then [.requestBase] else [])
  | .baseOffer peer G =>
    if s.recovering ∧ peer ≠ cfg.me then
      settle cfg { s with offers := (peer, G) :: s.offers.filter fun o => o.1 ≠ peer }
    else (s, [])
  | .certOffer peer c ds =>
    let ds' := ds.filter fun e => s.lo ≤ e.1
    if peer ≠ cfg.me ∧ adoptable cfg s c ds' then adopt cfg s c ds'
    else if peer ≠ cfg.me ∧ confirms cfg s c then confirm cfg s c
    else (s, [])
  | .decisionRequest peer lo => (s, if peer ≠ cfg.me then serveFrom s peer lo else [])
  | .proposal peer k h =>
    if peer ≠ cfg.me then settle cfg (record cfg s peer k h)
    else (s, [])
  | .announced peer c =>
    if peer = cfg.me then (s, [])
    else if confirms cfg s c then confirm cfg s c
    else if cfg.q ≤ c.signers.length ∧ s.lo < c.height then (s, [.requestDecisions peer s.lo])
    else (s, [])

end Node

end LeanDag
