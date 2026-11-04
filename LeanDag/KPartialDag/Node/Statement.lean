import LeanDag.KPartialDag.Model.Node
/-!
# What a node reads — statement

`docs/kpartial.md` §5. A node holds a set `H` of blocks of the record, not
closed under histories:

* **local** (`Local`): the indirect test and the fetch test read on `H` are
  the same on every record whose blocks agree on `H`, so the node computes
  them from what it holds;
* **fetchable** (`Fetchable`): a node holding the record's available
  sub-DAG below an anchor has fetched it;
* **sound** (`Sound`): a decision the node takes on what it holds is a
  decision of the commit rule on every view holding `H`;
* **agreement** (`Agrees`): at `K ≥ 3`, two nodes decide each slot alike.

Statements only; the proofs are `Proof.lean`.
-/

namespace LeanDag

namespace KPartialDag

namespace Node

/-- **The node's tests read only what it holds**: on two records whose
blocks agree on `H`, the indirect test and the fetch test read on `H` hold
alike. -/
def Local : Prop :=
  ∀ (Validator BlockId Payload : Type) [Fintype Validator] [DecidableEq Validator]
    [Faults Validator] [DecidableEq BlockId] (U U' : KRecord Validator BlockId Payload) (K : ℕ)
    (H : Finset BlockId) (A L : BlockId) (r : ℕ), (∀ i ∈ H, U.block i = U'.block i) →
    (LinkedIn U K H A L r ↔ LinkedIn U' K H A L r) ∧ (FetchedIn U K H A ↔ FetchedIn U' K H A)

/-- **Holding the available sub-DAG fetches it.** -/
def Fetchable : Prop :=
  ∀ (Validator BlockId Payload : Type) [Fintype Validator] [DecidableEq Validator]
    [Faults Validator] [DecidableEq BlockId] (U : KRecord Validator BlockId Payload) (K : ℕ)
    (H : Finset BlockId) (A : BlockId), (∀ z ∈ Avail U K A, z ∈ H) → FetchedIn U K H A

/-- **A node's decision is the commit rule's** on every view holding what the
node holds. -/
def Sound : Prop :=
  ∀ (Validator BlockId Payload : Type) [Fintype Validator] [DecidableEq Validator]
    [Faults Validator] [DecidableEq BlockId] [S : Slots Validator] (K : ℕ)
    (U : KRecord Validator BlockId Payload) (H : Finset BlockId) (V : U.View) (k : ℕ)
    (v : Option BlockId), H ⊆ U.ids → H ⊆ V.ids → NodeDecided U K H k v →
    (kRule K).Decided (S := S) U V k v

/-- **Two nodes decide each slot alike**, at `K ≥ 3`. -/
def Agrees : Prop :=
  ∀ (Validator BlockId Payload : Type) [Fintype Validator] [DecidableEq Validator]
    [Faults Validator] [DecidableEq BlockId] [Slots Validator] (K : ℕ)
    (U : KRecord Validator BlockId Payload) (H₁ H₂ : Finset BlockId) (k : ℕ)
    (v₁ v₂ : Option BlockId), 3 ≤ K → H₁ ⊆ U.ids → H₂ ⊆ U.ids →
    NodeDecided U K H₁ k v₁ → NodeDecided U K H₂ k v₂ → v₁ = v₂

/-- What a node reads. -/
def Statement : Prop := Local ∧ Fetchable ∧ Sound ∧ Agrees

end Node

end KPartialDag

end LeanDag
