import LeanDag.KPartialDag.Model.Node
/-!
# What a node reads — statement

`docs/kpartial.md` §5, Theorem 3: a node's tests read only what it holds,
holding the sub-DAG to depth `K` fetches it, and a node's decisions are
decisions of the commit rule and agree across nodes.

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
    [Faults Validator] [Crashes Validator] [LinearOrder BlockId] (p : Scheme.Params)
    (U U' : KRecord Validator BlockId Payload) (K : ℕ) (H : Finset BlockId) (A L : BlockId)
    (r ρ : ℕ), (∀ i ∈ H, U.block i = U'.block i) →
    (LinkedIn p U K H A L r ↔ LinkedIn p U' K H A L r) ∧
      (FetchedIn U K H A ρ ↔ FetchedIn U' K H A ρ)

/-- **Holding the available sub-DAG down to `K` rounds below `ρ` fetches it
down to `ρ`**, for an anchor of the record at or above round `ρ`. -/
def Fetchable : Prop :=
  ∀ (Validator BlockId Payload : Type) [Fintype Validator] [DecidableEq Validator]
    [Faults Validator] [Crashes Validator]
    [LinearOrder BlockId] (U : KRecord Validator BlockId Payload) (K : ℕ)
    (H : Finset BlockId) (A : BlockId) (ρ : ℕ), A ∈ U.ids → ρ ≤ (U.block A).round →
    (∀ z ∈ Avail U K A, ρ ≤ (U.block z).round + K → z ∈ H) → FetchedIn U K H A ρ

/-- **A node's decision is the commit rule's**, at a row, on every view
holding what the node holds. -/
def Sound : Prop :=
  ∀ (Validator BlockId Payload : Type) [Fintype Validator] [DecidableEq Validator]
    [Faults Validator] [Crashes Validator]
    [LinearOrder BlockId] [S : Slots Validator] (p : Scheme.Params)
    (U : KRecord Validator BlockId Payload) (K : ℕ) (H : Finset BlockId) (V : U.View) (k : ℕ)
    (v : Option BlockId), Row Validator p → H ⊆ U.ids → H ⊆ V.ids → NodeDecided p U K H k v →
    (kRule p K).Decided (S := S) U V k v

/-- **Two nodes decide each slot alike**, at a row and its depth. -/
def Agrees : Prop :=
  ∀ (Validator BlockId Payload : Type) [Fintype Validator] [DecidableEq Validator]
    [Faults Validator] [Crashes Validator]
    [LinearOrder BlockId] [Slots Validator] (p : Scheme.Params)
    (U : KRecord Validator BlockId Payload) (K : ℕ) (H₁ H₂ : Finset BlockId) (k : ℕ)
    (v₁ v₂ : Option BlockId), Row Validator p → kDepth Validator p ≤ K → H₁ ⊆ U.ids → H₂ ⊆ U.ids →
    NodeDecided p U K H₁ k v₁ → NodeDecided p U K H₂ k v₂ → v₁ = v₂

/-- What a node reads. -/
def Statement : Prop := Local ∧ Fetchable ∧ Sound ∧ Agrees

end Node

end KPartialDag

end LeanDag
