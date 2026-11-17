import LeanDag.KPartialSparse.Model.Node
/-!
# Sparse K-partial DAG — what a node reads, statement

`docs/kpartial-sparse.md` §5, Theorem 3: a node's tests read only what it
holds, holding what the anchor points bring fetches the sub-DAG, a node's
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
agree on `H`, the link and the fetch test read on `H` hold alike. -/
def Local : Prop :=
  ∀ (Validator BlockId Payload : Type) [Fintype Validator] [DecidableEq Validator]
    [Faults Validator] [Crashes Validator] [Leaders Validator] [LinearOrder BlockId]
    [ClaimFormat BlockId Payload] (p : Params) (U U' : SRecord Validator BlockId Payload) (K : ℕ)
    (H : Finset BlockId) (A L : BlockId) (r ρ : ℕ), (∀ i ∈ H, U.block i = U'.block i) →
    (LinkedIn p U K H A L r ↔ LinkedIn p U' K H A L r) ∧ (FetchedIn U K H A ρ ↔ FetchedIn U' K H A ρ)

/-- **Holding what the anchor points bring fetches the sub-DAG** down to any
round. -/
def Fetchable : Prop :=
  ∀ (Validator BlockId Payload : Type) [Fintype Validator] [DecidableEq Validator]
    [Faults Validator] [Crashes Validator] [Leaders Validator] [LinearOrder BlockId]
    (U : SRecord Validator BlockId Payload) (K : ℕ) (H : Finset BlockId) (A : BlockId) (ρ : ℕ),
    (∀ y d, Anchored U K A y d → historyUpto U d y ⊆ H) → FetchedIn U K H A ρ

/-- **A node's decision is the commit rule's**, on every view holding what the
node holds. -/
def Sound : Prop :=
  ∀ (Validator BlockId Payload : Type) [Fintype Validator] [DecidableEq Validator]
    [Faults Validator] [Crashes Validator] [Leaders Validator] [LinearOrder BlockId]
    [ClaimFormat BlockId Payload] [S : Slots Validator] (p : Params)
    (U : SRecord Validator BlockId Payload) (K : ℕ) (H : Finset BlockId) (V : U.View) (k : ℕ)
    (v : Option BlockId), H ⊆ U.ids → H ⊆ V.ids → NodeDecided p U K H k v →
    (sRule p K).Decided (S := S) U V k v

/-- **Two nodes decide each slot alike**, at a row, under the spreading
condition, at `K ≥ 6`, on a disciplined schedule and record. -/
def Agrees : Prop :=
  ∀ (Validator BlockId Payload : Type) [Fintype Validator] [DecidableEq Validator]
    [Faults Validator] [Crashes Validator] [Leaders Validator] [LinearOrder BlockId]
    [ClaimFormat BlockId Payload] [S : Slots Validator] (p : Params)
    (U : SRecord Validator BlockId Payload) (K : ℕ) (H₁ H₂ : Finset BlockId) (k : ℕ)
    (v₁ v₂ : Option BlockId), Row Validator p → Spread Validator → 6 ≤ K →
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
def Statement : Prop := Local ∧ Fetchable ∧ Sound ∧ Agrees ∧ Checked

end Node

end KPartialSparse

end LeanDag
