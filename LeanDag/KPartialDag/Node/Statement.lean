import LeanDag.KPartialDag.Model.Node
/-!
# What a node reads — statement

`docs/kpartial.md` §5. A node holds a set `H` of blocks of the record, not
closed under histories:

* **local** (`Local`): the indirect test and the fetch test read on `H` are
  the same on every record whose blocks agree on `H`, so the node computes
  them from what it holds;
* **fetchable** (`Fetchable`): a node holding the record's available
  sub-DAG below an anchor, down to `K` rounds below `ρ`, has fetched it down
  to `ρ`;
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
    (H : Finset BlockId) (A L : BlockId) (r ρ : ℕ), (∀ i ∈ H, U.block i = U'.block i) →
    (LinkedIn U K H A L r ↔ LinkedIn U' K H A L r) ∧
      (FetchedIn U K H A ρ ↔ FetchedIn U' K H A ρ)

/-- **Holding the available sub-DAG down to `K` rounds below `ρ` fetches it
down to `ρ`**, for an anchor of the record at or above round `ρ`. -/
def Fetchable : Prop :=
  ∀ (Validator BlockId Payload : Type) [Fintype Validator] [DecidableEq Validator]
    [Faults Validator] [DecidableEq BlockId] (U : KRecord Validator BlockId Payload) (K : ℕ)
    (H : Finset BlockId) (A : BlockId) (ρ : ℕ), A ∈ U.ids → ρ ≤ (U.block A).round →
    (∀ z ∈ Avail U K A, ρ ≤ (U.block z).round + K → z ∈ H) → FetchedIn U K H A ρ

/-- **A node's decision is the commit rule's** on every view holding what the
node holds. -/
def Sound : Prop :=
  ∀ (Validator BlockId Payload : Type) [Fintype Validator] [DecidableEq Validator]
    [Faults Validator] [DecidableEq BlockId] [S : Slots Validator]
    (U : KRecord Validator BlockId Payload) (K : ℕ) (H : Finset BlockId) (V : U.View) (k : ℕ)
    (v : Option BlockId), H ⊆ U.ids → H ⊆ V.ids → NodeDecided U K H k v →
    (kRule K).Decided (S := S) U V k v

/-- **Two nodes decide each slot alike**, at `K ≥ 3`. -/
def Agrees : Prop :=
  ∀ (Validator BlockId Payload : Type) [Fintype Validator] [DecidableEq Validator]
    [Faults Validator] [DecidableEq BlockId] [Slots Validator]
    (U : KRecord Validator BlockId Payload) (K : ℕ) (H₁ H₂ : Finset BlockId) (k : ℕ)
    (v₁ v₂ : Option BlockId), 3 ≤ K → H₁ ⊆ U.ids → H₂ ⊆ U.ids →
    NodeDecided U K H₁ k v₁ → NodeDecided U K H₂ k v₂ → v₁ = v₂

/-- What a node reads. -/
def Statement : Prop := Local ∧ Fetchable ∧ Sound ∧ Agrees

end Node

end KPartialDag

end LeanDag
