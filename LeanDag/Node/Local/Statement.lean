import LeanDag.Node.Model.Run
import LeanDag.Node.Vote
/-!
# An honest node, one node at a time — statement

`docs/validator.md` §4, V1, V2 and V4, and certification. Over any sequence of inputs from the
initial state:

* **one block per round**: the node's own blocks, those it persists, lie
  at strictly increasing rounds (`OneEach`), each its own and identified
  by its hash (`Authored`); the blocks it broadcasts are those it
  persists (`Sends`);
* **its decisions**: the node keeps the decisions it outputs, the latest
  first, which are slots `0 … lo − 1`, and every proposal it signs at a
  height `k` is the head of the chain of its first `k` decisions
  (`Decisions`);
* **valid blocks**: each of its own blocks references only blocks it
  knew, delivered or offered with their hash, or its own, and is valid at
  the row under every block map agreeing with what it knew (`ValidOut`);
* **decisions read only the view, from the horizon up**: at the bounded
  vote, with the horizon at or below the next undecided slot's round, a
  decision step decides what `tryDecide` decides on any record and view
  holding the store's blocks from the horizon up (`DecidesOnView`); a
  pruned store decides as the view it is a cut of;
* **certifying what it decides**: without a restart, a node whose
  decisions reach a multiple of `m` certifies it once `q − 1` other
  signers' proposals of the same head reached it in time (`Certifies`);
* **the proposals it keeps**: of each signer at most
  `lo + ahead − certHeight + 1`, and `n` times that in all (`Bounded`).

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

/-- **It sends its own blocks**: the blocks the node broadcasts are those
it persists. -/
def Sends : Prop :=
  ∀ (Validator BlockId Payload : Type) [Fintype Validator] [DecidableEq Validator]
    [LinearOrder BlockId] (cfg : Config Validator BlockId Payload)
    (is : List (Input Validator BlockId Payload)),
    broadcasts (run cfg (State.init cfg) is).2 = persists (run cfg (State.init cfg) is).2

/-- **Its decisions**: the node keeps the decisions it outputs, the latest
first, which are slots `0 … lo − 1`, and every proposal it signs at a
height `k` is the head of the chain of its first `k` decisions. -/
def Decisions : Prop :=
  ∀ (Validator BlockId Payload : Type) [Fintype Validator] [DecidableEq Validator]
    [LinearOrder BlockId] (cfg : Config Validator BlockId Payload)
    (is : List (Input Validator BlockId Payload)),
    let r := run cfg (State.init cfg) is
    r.1.decided.reverse = commitsOf r.2 ∧ (commitsOf r.2).map Prod.fst = List.range r.1.lo ∧
      ∀ k h, Output.propose k h ∈ r.2 → k ≤ (commitsOf r.2).length ∧
        h = cfg.headOf ((commitsOf r.2).take k)

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
        rowValid cfg.q blk e.2

/-- **Decisions read only the view, from the horizon up**: at the bounded
vote, with the horizon at or below the next undecided slot's round, a
decision step decides what `tryDecide` decides on any record and view
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
    commitsOf (decideStep cfg s).2 =
      if s.lo < N then Scheme.tryDecide (S := cfg.slots) cfg.p boundedSel U V s.lo (N - 1)
      else []

/-- **Certifying what it decides**: over inputs without a restart, a node
whose decisions reach a positive multiple `k` of `m` holds a certificate
at `k` or above, once proposals at `k` of the head of its first `k`
decisions reached it from `q − 1` distinct other signers, each while `k`
lay at most `ahead` above its next undecided slot, and none of them sent
another head at `k` after. -/
def Certifies : Prop :=
  ∀ (Validator BlockId Payload : Type) [Fintype Validator] [DecidableEq Validator]
    [LinearOrder BlockId] (cfg : Config Validator BlockId Payload)
    (is : List (Input Validator BlockId Payload)) (k : ℕ) (S : Finset Validator),
    let r := run cfg (State.init cfg) is
    let h := cfg.headOf ((commitsOf r.2).take k)
    (∀ i ∈ is, i ≠ .restart) → 0 < k → cfg.m ∣ k → k ≤ (commitsOf r.2).length →
    cfg.me ∉ S → cfg.q ≤ S.card + 1 →
    (∀ u ∈ S, ∃ is₁ is₂, is = is₁ ++ .proposal u k h :: is₂ ∧
      k ≤ (run cfg (State.init cfg) is₁).1.lo + cfg.ahead ∧
      ∀ h', .proposal u k h' ∈ is₂ → h' = h) →
    k ≤ r.1.certHeight

/-- **The proposals it keeps**: over any inputs, the node keeps at most
`lo + ahead − certHeight + 1` proposals of each signer, and `n` times that
in all. -/
def Bounded : Prop :=
  ∀ (Validator BlockId Payload : Type) [Fintype Validator] [DecidableEq Validator]
    [LinearOrder BlockId] (cfg : Config Validator BlockId Payload)
    (is : List (Input Validator BlockId Payload)),
    let s := (run cfg (State.init cfg) is).1
    (∀ v, (s.props.filter fun x => x.1 = v).length ≤ s.lo + cfg.ahead - s.certHeight + 1) ∧
      s.props.length ≤ Fintype.card Validator * (s.lo + cfg.ahead - s.certHeight + 1)

/-- One node at a time. -/
def Statement : Prop :=
  OneEach ∧ Authored ∧ Sends ∧ Decisions ∧ ValidOut ∧ DecidesOnView ∧ Certifies ∧ Bounded

end Local

end Node

end LeanDag
