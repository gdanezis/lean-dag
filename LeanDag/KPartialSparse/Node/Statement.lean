import LeanDag.KPartialSparse.Model.Node
/-!
# Sparse K-partial DAG — what a node reads, statement

`docs/kpartial-sparse.md` §5, Theorem 3: a node's tests read only what it
holds, holding what the anchor points bring fetches the sub-DAG, fetching
down to a round reads at most `K` rounds below it, a node's
decisions are decisions of the commit rule and agree across nodes, and
correct nodes that check claims on what they hold meet the rule's claim
disciplines.

Statements only; the proofs are `Proof.lean`.
-/

namespace LeanDag

namespace KPartialSparse

namespace Node

open KPartialDag Scheme

/-- **The node's tests read only what it holds**: on two records whose blocks
agree on `H`, and which give the references of those blocks the same rounds,
the link and the fetch test read on `H` hold alike. -/
def Local : Prop :=
  ∀ (Validator BlockId Payload : Type) [Fintype Validator] [DecidableEq Validator]
    [Faults Validator] [Crashes Validator] [Leaders Validator] [LinearOrder BlockId]
    [ClaimFormat BlockId Payload] (p : Params) (U U' : SRecord Validator BlockId Payload) (K : ℕ)
    (H : Finset BlockId) (A L : BlockId) (r ρ : ℕ), (∀ i ∈ H, U.block i = U'.block i) →
    (∀ i ∈ H, ∀ j ∈ (U.block i).refs, (U'.block j).round = (U.block j).round) →
    (LinkedIn p U K H A L r ↔ LinkedIn p U' K H A L r) ∧ (FetchedIn U K H A ρ ↔ FetchedIn U' K H A ρ)

/-- **Holding what the anchor points bring fetches the sub-DAG** down to any
round. -/
def Fetchable : Prop :=
  ∀ (Validator BlockId Payload : Type) [Fintype Validator] [DecidableEq Validator]
    [Faults Validator] [Crashes Validator] [Leaders Validator] [LinearOrder BlockId]
    (U : SRecord Validator BlockId Payload) (K : ℕ) (H : Finset BlockId) (A : BlockId) (ρ : ℕ),
    (∀ y d, Anchored U K A y d → window U d y ⊆ H) → FetchedIn U K H A ρ

/-- **Fetching reads at most `K` rounds below**: holding the record's blocks
from round `ρ − K` up to the anchor's round fetches the sub-DAG below the anchor
down to round `ρ`. -/
def Bounded : Prop :=
  ∀ (Validator BlockId Payload : Type) [Fintype Validator] [DecidableEq Validator]
    [Faults Validator] [Crashes Validator] [Leaders Validator] [LinearOrder BlockId]
    (U : SRecord Validator BlockId Payload) (K : ℕ) (H : Finset BlockId) (A : BlockId) (ρ : ℕ),
    A ∈ U.ids → ρ ≤ (U.block A).round →
    (∀ b ∈ U.ids, ρ - K ≤ (U.block b).round → (U.block b).round ≤ (U.block A).round → b ∈ H) →
    FetchedIn U K H A ρ

/-- **A node's decision is the commit rule's**, on every view holding what the
node holds. -/
def Sound : Prop :=
  ∀ (Validator BlockId Payload : Type) [Fintype Validator] [DecidableEq Validator]
    [Faults Validator] [Crashes Validator] [Leaders Validator] [LinearOrder BlockId]
    [ClaimFormat BlockId Payload] [S : Slots Validator] (p : Params)
    (U : SRecord Validator BlockId Payload) (K : ℕ) (H : Finset BlockId) (V : U.View) (k : ℕ)
    (v : Option BlockId), H ⊆ U.ids → H ⊆ V.ids → NodeDecided p U K H k v →
    (sRule p K).Decided (S := S) U V k v

/-- **Two nodes decide each slot alike**, at a row and the depth the sub-DAG
needs, on a disciplined schedule and record. -/
def Agrees : Prop :=
  ∀ (Validator BlockId Payload : Type) [Fintype Validator] [DecidableEq Validator]
    [Faults Validator] [Crashes Validator] [Leaders Validator] [LinearOrder BlockId]
    [ClaimFormat BlockId Payload] [S : Slots Validator] (p : Params)
    (U : SRecord Validator BlockId Payload) (K : ℕ) (H₁ H₂ : Finset BlockId) (k : ℕ)
    (v₁ v₂ : Option BlockId), Row Validator p → Deep Validator K →
    Disciplined K p.certThreshold S U → H₁ ⊆ U.ids → H₂ ⊆ U.ids →
    NodeDecided p U K H₁ k v₁ → NodeDecided p U K H₂ k v₂ → v₁ = v₂

/-- **Claims are checked on what a node holds**: backing reads only what is
held, and correct authors that check claims on what they hold check and claim
truthfully on the record. -/
def Checked : Prop :=
  ∀ (Validator BlockId Payload : Type) [Fintype Validator] [DecidableEq Validator]
    [Faults Validator] [Crashes Validator] [Leaders Validator] [LinearOrder BlockId]
    [ClaimFormat BlockId Payload] (U U' : SRecord Validator BlockId Payload) (K t : ℕ)
    (H : Finset BlockId) (L : BlockId),
    ((∀ i ∈ H, U.block i = U'.block i) → (Backs U t H L ↔ Backs U' t H L)) ∧
      (BuildsChecked U K t → Checks U K t ∧ Truthful U t)

/-- What a node reads. -/
def Statement : Prop := Local ∧ Fetchable ∧ Bounded ∧ Sound ∧ Agrees ∧ Checked

end Node

end KPartialSparse

end LeanDag
