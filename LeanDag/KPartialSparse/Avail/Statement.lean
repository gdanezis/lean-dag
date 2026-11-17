import LeanDag.KPartialSparse.Model.Substrate
/-!
# Sparse K-partial DAG — the available sub-DAG, statement

`docs/kpartial-sparse.md` §3: below a leader block, a claim from a quorum of
authors two rounds above some block lies in the available sub-DAG
(`Linked`), and every claim in the available sub-DAG names a certified block
(`Backed`).

Statements only; the proofs are `Proof.lean`.
-/

namespace LeanDag

namespace KPartialSparse

open KPartialDag

namespace Avail

/-- **A quorum's claim is in the sub-DAG**: under the spreading condition, at
`K ≥ 6`, with honest chains, if blocks of `cm` distinct authors at round
`ρ + 2` claim `L` and `n + f < q + cm`, then below a leader block at round
`ρ + 3` or above the sub-DAG holds a claim for `L` at round `ρ + 2`. -/
def Linked : Prop :=
  ∀ (Validator BlockId Payload : Type) [Fintype Validator] [DecidableEq Validator]
    [Faults Validator] [Crashes Validator] [Leaders Validator]
    [LinearOrder BlockId] [ClaimFormat BlockId Payload] (U : SRecord Validator BlockId Payload)
    (K cm ρ : ℕ) (A L : BlockId),
    Spread Validator → 6 ≤ K → Chains U → A ∈ U.ids →
    (U.block A).creator ∈ Leaders.leaders (U.block A).round → ρ + 3 ≤ (U.block A).round →
    Fintype.card Validator + Faults.f Validator < kQuorum Validator + cm →
    cm ≤ (creatorsOf U.block (claimersOf U L (ρ + 2))).card →
    ∃ C ∈ Avail U K A, (U.block C).round = ρ + 2 ∧ L ∈ claimsOf U C

/-- **Claims in the sub-DAG are backed**: at `K ≥ 1`, when correct authors
check the claims of what they reference, below a block a correct author
references every claim of the sub-DAG names a certified block. -/
def Backed : Prop :=
  ∀ (Validator BlockId Payload : Type) [Fintype Validator] [DecidableEq Validator]
    [Faults Validator] [Crashes Validator] [Leaders Validator]
    [LinearOrder BlockId] [ClaimFormat BlockId Payload] (U : SRecord Validator BlockId Payload)
    (K t : ℕ) (A : BlockId), 1 ≤ K → Checks U K t →
    (∃ z ∈ U.ids, (U.block z).creator ∈ (Correct : Finset Validator) ∧ A ∈ (U.block z).refs) →
    ∀ X ∈ Avail U K A, ∀ L ∈ claimsOf U X, Certified U t L

/-- The available sub-DAG of a sparse K-partial DAG. -/
def Statement : Prop := Linked ∧ Backed

end Avail

end KPartialSparse

end LeanDag
