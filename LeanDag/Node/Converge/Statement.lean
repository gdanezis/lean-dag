import LeanDag.Node.Model.Trace
/-!
# Fetching makes the honest nodes converge — statement

`docs/validator.md` §3.7. Over a trace of honest nodes `H` and an
adversary, assume:

* **delivery** (`Delivered`): every message an honest node sends another
  reaches it later in the trace, so the trace is causal and the network
  has caught up;
* **timely authentication** (`TimelyAuthentic`): a block delivered to an
  honest node with an honest author's identity and its hash was
  broadcast by that author earlier in the trace;
* **the hash** (`HashInjective`): no two different blocks delivered to or
  broadcast by honest nodes have one identifier;
* no honest node raises its horizon.

Then **every block an honest node broadcast, with its history, is in
every honest node's store at the end** (`Converges`).

Statements only; the proofs are `Proof.lean`.
-/

namespace LeanDag

namespace Node

namespace Converge

variable {Validator BlockId Payload : Type} [Fintype Validator] [DecidableEq Validator]
variable [LinearOrder BlockId]

/-- **Delivery**: every message an honest node sends another reaches it
later in the trace. -/
def Delivered (cfg : Config Validator BlockId Payload) (H : Finset Validator)
    (tr : Trace Validator BlockId Payload) : Prop :=
  ∀ i u inp, tr[i]? = some (u, inp) → u ∈ H → ∀ m, Sends u (outputsAt cfg tr i) m → m.1 ∈ H →
    ∃ j, i < j ∧ tr[j]? = some m

/-- **Timely authentication**: a block delivered to an honest node with an
honest author's identity and its hash was broadcast by that author
earlier. -/
def TimelyAuthentic (cfg : Config Validator BlockId Payload) (H : Finset Validator)
    (tr : Trace Validator BlockId Payload) : Prop :=
  ∀ j v id b, tr[j]? = some (v, .deliver id b) → v ∈ H → b.creator ∈ H → id = cfg.idOf b →
    ∃ i < j, (tr[i]?.map Prod.fst) = some b.creator ∧ (id, b) ∈ broadcasts (outputsAt cfg tr i)

/-- The blocks delivered to honest nodes with their hash, and those honest
nodes broadcast. -/
def knownIn (cfg : Config Validator BlockId Payload) (H : Finset Validator)
    (tr : Trace Validator BlockId Payload) : Set (BlockId × Block Validator BlockId Payload) :=
  {x | (∃ (j : ℕ) (v : Validator), tr[j]? = some (v, Input.deliver x.1 x.2) ∧ v ∈ H ∧
      x.1 = cfg.idOf x.2) ∨
    ∃ (i : ℕ) (u : Validator), (tr[i]?.map Prod.fst) = some u ∧ u ∈ H ∧
      x ∈ broadcasts (outputsAt cfg tr i)}

/-- **The hash** is injective on the blocks honest nodes knew. -/
def HashInjective (cfg : Config Validator BlockId Payload) (H : Finset Validator)
    (tr : Trace Validator BlockId Payload) : Prop :=
  ∀ x ∈ knownIn cfg H tr, ∀ y ∈ knownIn cfg H tr, cfg.idOf x.2 = cfg.idOf y.2 → x.2 = y.2

/-- **Every block an honest node broadcast, with its history, is in every
honest node's store at the end.** -/
def Converges : Prop :=
  ∀ (Validator BlockId Payload : Type) [Fintype Validator] [DecidableEq Validator]
    [LinearOrder BlockId] (cfg : Config Validator BlockId Payload) (H : Finset Validator)
    (tr : Trace Validator BlockId Payload),
    Delivered cfg H tr → TimelyAuthentic cfg H tr → HashInjective cfg H tr →
    (∀ v ∈ H, (stateBefore cfg tr tr.length v).store.base = 0) →
    ∀ i u, (tr[i]?.map Prod.fst) = some u → u ∈ H → ∀ e ∈ broadcasts (outputsAt cfg tr i),
      ∀ y ∈ historyFrom (stateBefore cfg tr tr.length u).store.blk e.1, ∀ v ∈ H,
        y ∈ (stateBefore cfg tr tr.length v).store.ids

/-- Fetching makes the honest nodes converge. -/
def Statement : Prop := Converges

end Converge

end Node

end LeanDag
