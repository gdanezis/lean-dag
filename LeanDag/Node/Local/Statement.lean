import LeanDag.Node.Model.Run
import LeanDag.Node.Vote
/-!
# An honest node, one node at a time — statement

`docs/validator.md` §4, V1 and V2. Over any sequence of inputs from the
initial state:

* **one block per round**: the node's own blocks, those it persists, lie
  at strictly increasing rounds (`OneEach`), each its own and identified
  by its hash (`Authored`); it broadcasts each block it persists, and
  only blocks it persists (`Sends`);
* **its decisions**: the node keeps the decisions it outputs, the latest
  first, which are slots `0 … lo − 1` (`Decisions`);
* **its syncs**: the node holds at most `n − 1` syncs, one for each other
  node at most (`SyncsBound`);
* **valid blocks**: each of its own blocks references only blocks it
  knew, delivered with their hash, or its own, and is valid at
  the row under every block map agreeing with what it knew (`ValidOut`);
* **decisions are the scheme's on the view**: at the bounded vote, a
  decision step of a node whose memory holds the round of its next
  undecided slot decides what `tryDecide` decides on any record and view
  holding the disk's blocks, read alike (`DecidesOnView`);
* **its requests and streams keep to the cut** (D15): a request carries a
  frontier at or above the node's cut, a stream holds, besides the
  requested block and the blocks asked for by name, only blocks at or
  above their author's frontier, and of a stream piece the node reads only
  blocks at or above its cut (`Horizon`).

Statements only; the proofs are `Proof.lean`.
-/

namespace LeanDag

namespace Node

namespace Local

/-- **One block per round**: the node's own blocks lie at strictly
increasing rounds. -/
def OneEach : Prop :=
  ∀ (Validator BlockId Payload : Type) [Fintype Validator] [DecidableEq Validator]
    [LinearOrder BlockId] (cfg : Config Validator BlockId Payload)
    (is : List (Input Validator BlockId Payload)),
    let B := persists (run cfg (State.init cfg) is).2
    (B.map fun e => e.2.round).Pairwise (· < ·)

/-- **Its own blocks**: each block the node persists is authored by it and
identified by its hash. -/
def Authored : Prop :=
  ∀ (Validator BlockId Payload : Type) [Fintype Validator] [DecidableEq Validator]
    [LinearOrder BlockId] (cfg : Config Validator BlockId Payload)
    (is : List (Input Validator BlockId Payload)),
    ∀ e ∈ persists (run cfg (State.init cfg) is).2, e.1 = cfg.idOf e.2 ∧ e.2.creator = cfg.me

/-- **It sends its own blocks**: the node broadcasts each block it
persists, and only blocks it persists. -/
def Sends : Prop :=
  ∀ (Validator BlockId Payload : Type) [Fintype Validator] [DecidableEq Validator]
    [LinearOrder BlockId] (cfg : Config Validator BlockId Payload)
    (is : List (Input Validator BlockId Payload)),
    let out := (run cfg (State.init cfg) is).2
    (∀ e ∈ persists out, e ∈ broadcasts out) ∧ ∀ e ∈ broadcasts out, e ∈ persists out

/-- **Its decisions**: the node keeps the decisions it outputs, the latest
first, which are slots `0 … lo − 1`. -/
def Decisions : Prop :=
  ∀ (Validator BlockId Payload : Type) [Fintype Validator] [DecidableEq Validator]
    [LinearOrder BlockId] (cfg : Config Validator BlockId Payload)
    (is : List (Input Validator BlockId Payload)),
    let r := run cfg (State.init cfg) is
    r.1.decided.reverse = commitsOf r.2 ∧ (commitsOf r.2).map Prod.fst = List.range r.1.lo

/-- **Its syncs**: the node holds at most `n − 1` syncs. -/
def SyncsBound : Prop :=
  ∀ (Validator BlockId Payload : Type) [Fintype Validator] [DecidableEq Validator]
    [LinearOrder BlockId] (cfg : Config Validator BlockId Payload)
    (is : List (Input Validator BlockId Payload)),
    (run cfg (State.init cfg) is).1.syncs.length ≤ Fintype.card Validator - 1

/-- **Valid blocks**: each of the node's own blocks references only blocks
it knew, and is valid at the row under every block map agreeing with
what it knew. -/
def ValidOut : Prop :=
  ∀ (Validator BlockId Payload : Type) [Fintype Validator] [DecidableEq Validator]
    [LinearOrder BlockId] (cfg : Config Validator BlockId Payload)
    (is : List (Input Validator BlockId Payload)),
    let B := persists (run cfg (State.init cfg) is).2
    let K := delivered cfg is ++ B
    ∀ e ∈ B, (∀ j ∈ e.2.refs, j ∈ K.map Prod.fst) ∧
      ∀ blk : BlockId → Block Validator BlockId Payload, (∀ x ∈ K, blk x.1 = x.2) →
        rowValid cfg.q cfg.xp blk e.2

/-- **Decisions are the scheme's on the view**: at the bounded vote, a
decision step of a node whose memory holds the round of its next
undecided slot decides what `tryDecide` decides on any record and view
holding the disk's blocks, read alike. -/
def DecidesOnView : Prop :=
  ∀ (Validator BlockId Payload : Type) [Fintype Validator] [DecidableEq Validator]
    [LinearOrder BlockId] (cfg : Config Validator BlockId Payload)
    (s : State Validator BlockId Payload) (P : Validity Validator BlockId Payload) [P.Mechanised]
    (H : Finset Validator) (U : BlockRecord Validator BlockId Payload P H) (V : U.View),
    cfg.σ = boundedSel → cfg.Admissible → s.floor ≤ cfg.slots.slotRound s.lo →
    (∀ i, i ∈ V.ids ↔ i ∈ s.disk.ids) → (∀ i ∈ s.disk.ids, U.block i = s.disk.blk i) →
    let N := decidable cfg s.disk.topRound
    commitsOf (decideStep cfg s).2 =
      if s.lo < N then Scheme.tryDecide (S := cfg.slots) cfg.p boundedSel U V s.lo (N - 1)
      else []

/-- **Its requests and streams keep to the cut** (D15): every request a step
sends carries a frontier at or above the node's cut before the step, every
stream it sends in answer to a request holds, besides the requested block
and the blocks asked for by name, only blocks at or above their author's
frontier, and the part of a stream piece the node reads lies at or above
its cut. -/
def Horizon : Prop :=
  ∀ (Validator BlockId Payload : Type) [Fintype Validator] [DecidableEq Validator]
    [LinearOrder BlockId] (cfg : Config Validator BlockId Payload)
    (s : State Validator BlockId Payload) (inp : Input Validator BlockId Payload),
    (∀ peer t fr ids, Output.sync peer t fr ids ∈ (Node.step cfg s inp).2 →
      ∀ a, cutOf cfg s ≤ fr a) ∧
    (∀ peer t fr ids, inp = .syncRequest peer t fr ids →
      ∀ u L, Output.stream u L ∈ (Node.step cfg s inp).2 →
        ∀ e ∈ L, e.1 = t ∨ e.1 ∈ ids ∨ fr e.2.creator ≤ e.2.round) ∧
    ∀ t L, ∀ e ∈ inHistory cfg t (aboveCut cfg s L), cutOf cfg s ≤ e.2.round

/-- One node at a time. -/
def Statement : Prop :=
  OneEach ∧ Authored ∧ Sends ∧ Decisions ∧ SyncsBound ∧ ValidOut ∧ DecidesOnView ∧ Horizon

end Local

end Node

end LeanDag
