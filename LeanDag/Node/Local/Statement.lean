import LeanDag.Node.Model.Run
import LeanDag.Node.Vote
/-!
# An honest node, one node at a time — statement

`docs/validator.md` §4, V1, V2 and V4. Over any sequence of inputs from the
initial state:

* **each step's outputs**, from any state a run reaches, are its
  requests and answers, then at most one jump, its filled blocks each
  persisted and then the message, then its built blocks, each persisted,
  then broadcast, then its round's timer set, then its decisions, then at
  most one horizon (`Shape`);
* **one block per round**: the node's own blocks, those it persists, lie
  at rounds `0, 1, 2, …`, in order (`OneEach`), each its own and
  identified by its hash (`Authored`);
* **valid blocks**: each of its own blocks references only blocks it
  knew, delivered with their hash, given by a jump message, or its own,
  and is valid at the row under every block map agreeing with what it
  knew (`ValidOut`);
* **decisions read only the view, from the horizon up**: at the bounded
  vote, with the horizon at or below the next undecided slot's round, a
  decision step outputs what `tryDecide` decides on any record and view
  holding the store's blocks from the horizon up (`DecidesOnView`); a
  pruned store decides as the view it is a cut of.

Statements only; the proofs are `Proof.lean`.
-/

namespace LeanDag

namespace Node

namespace Local

/-- **Each step's outputs**, from any state a run reaches: requests and
answers, then at most one jump, then built blocks, then decisions, then
at most one horizon. -/
def Shape : Prop :=
  ∀ (Validator BlockId Payload : Type) [Fintype Validator] [DecidableEq Validator]
    [LinearOrder BlockId] (cfg : Config Validator BlockId Payload)
    (is : List (Input Validator BlockId Payload)) (i : Input Validator BlockId Payload),
    ∃ (xs js : List (Output Validator BlockId Payload))
      (bs : List (BlockId × Block Validator BlockId Payload))
      (ds : List (ℕ × Option BlockId)) (gs : List ℕ), (∀ o ∈ xs, o.isFetch) ∧
      (js = [] ∨ ∃ fs B1 v2 B2, js = jumped fs cfg.me B1 v2 B2) ∧ gs.length ≤ 1 ∧
      (step cfg (run cfg (State.init cfg) is).1 i).2 =
        xs ++ js ++ built cfg bs ++ ds.map (fun e => .commit e.1 e.2) ++ gs.map .prune

/-- **One block per round**: the node's own blocks lie at rounds
`0, 1, 2, …`, in order. -/
def OneEach : Prop :=
  ∀ (Validator BlockId Payload : Type) [Fintype Validator] [DecidableEq Validator]
    [LinearOrder BlockId] (cfg : Config Validator BlockId Payload)
    (is : List (Input Validator BlockId Payload)),
    let B := persists (run cfg (State.init cfg) is).2
    B.map (fun e => e.2.round) = List.range B.length

/-- **Its own blocks**: each block the node persists is authored by it and
identified by its hash. -/
def Authored : Prop :=
  ∀ (Validator BlockId Payload : Type) [Fintype Validator] [DecidableEq Validator]
    [LinearOrder BlockId] (cfg : Config Validator BlockId Payload)
    (is : List (Input Validator BlockId Payload)),
    ∀ e ∈ persists (run cfg (State.init cfg) is).2, e.1 = cfg.idOf e.2 ∧ e.2.creator = cfg.me

/-- **Valid blocks**: each of the node's own blocks references only blocks
it knew, and is valid at the row under every block map agreeing with
what it knew. -/
def ValidOut : Prop :=
  ∀ (Validator BlockId Payload : Type) [Fintype Validator] [DecidableEq Validator]
    [LinearOrder BlockId] (cfg : Config Validator BlockId Payload)
    (is : List (Input Validator BlockId Payload)),
    let B := persists (run cfg (State.init cfg) is).2
    let K := delivered cfg is ++ derived cfg (State.init cfg) is ++ B
    ∀ e ∈ B, (∀ j ∈ e.2.refs, j ∈ K.map Prod.fst) ∧
      ∀ blk : BlockId → Block Validator BlockId Payload, (∀ x ∈ K, blk x.1 = x.2) →
        rowValid cfg.q blk e.2

/-- **Decisions read only the view, from the horizon up**: at the bounded
vote, with the horizon at or below the next undecided slot's round, a
decision step outputs what `tryDecide` decides on any record and view
holding the store's blocks from the horizon up, read at the horizon. -/
def DecidesOnView : Prop :=
  ∀ (Validator BlockId Payload : Type) [Fintype Validator] [DecidableEq Validator]
    [LinearOrder BlockId] (cfg : Config Validator BlockId Payload)
    (s : State Validator BlockId Payload) (P : Validity Validator BlockId Payload) [P.Mechanised]
    (H : Finset Validator) (U : BlockRecord Validator BlockId Payload P H) (V : U.View),
    cfg.σ = boundedSel → cfg.Admissible → s.store.base ≤ cfg.per * (s.lo / cfg.m) →
    (∀ i, i ∈ V.ids ∧ s.store.base ≤ (U.block i).round ↔ i ∈ s.store.ids) →
    (∀ i ∈ s.store.ids, atBase s.store.base (U.block i) = s.store.blk i) →
    let N := decidable cfg s.store.topRound
    (decideStep cfg s).2 =
      if s.lo < N then
        (Scheme.tryDecide (S := cfg.slots) cfg.p boundedSel U V s.lo (N - 1)).map
          fun e => .commit e.1 e.2
      else []

/-- One node at a time. -/
def Statement : Prop := Shape ∧ OneEach ∧ Authored ∧ ValidOut ∧ DecidesOnView

end Local

end Node

end LeanDag
