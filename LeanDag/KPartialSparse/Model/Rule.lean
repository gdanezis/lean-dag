import LeanDag.KPartialSparse.Model.Substrate
import LeanDag.Common.Anchored
import LeanDag.Common.Rules
import LeanDag.Scheme.Model.Params
/-!
# Sparse K-partial DAG — the commit rule

`docs/kpartial-sparse.md` §4. The three-round rows of the scheme with claims
for certificates (`Row`), truthful claims (`Truthful`), what the rule asks of
the schedule and the record (`Disciplined`), the link by a claim in the
available sub-DAG (`ClaimLinked`), and the commit rule (`sRule`).
-/

namespace LeanDag

namespace KPartialSparse

open KPartialDag Scheme

variable {Validator : Type*} [Fintype Validator] [DecidableEq Validator] [F : Faults Validator]
variable [Cr : Crashes Validator] [Ld : Leaders Validator]
variable {BlockId : Type*} [LinearOrder BlockId] {Payload : Type*} [ClaimFormat BlockId Payload]

variable (Validator) in
/-- **A three-round row of the scheme with claims for certificates**: two
certificate thresholds, a certificate and a skip threshold, and the quorum and
a commit threshold each exceed `n + f`; the link is one claim. -/
def Row (p : Params) : Prop :=
  p.voteIsCert = false ∧ p.waveLength = 3 ∧ p.linkSize = 1 ∧
    Fintype.card Validator + F.f < 2 * p.certThreshold ∧
    Fintype.card Validator + F.f < p.certThreshold + p.skipThreshold ∧
    Fintype.card Validator + F.f < kQuorum Validator + p.commitThreshold

/-- **Truthful claims**: a correct author claims only blocks certified at
threshold `t`. -/
def Truthful (U : SRecord Validator BlockId Payload) (t : ℕ) : Prop :=
  ∀ C ∈ U.ids, (U.block C).creator ∈ (Correct : Finset Validator) →
    ∀ L ∈ claimsOf U C, Certified U t L

/-- **What the rule asks of the schedule and the record**: every slot's leader
leads its round on the substrate, correct authors keep chains, check the
claims of what they reference to depth `K`, and claim truthfully. -/
def Disciplined (K t : ℕ) (S : Slots Validator) (U : SRecord Validator BlockId Payload) : Prop :=
  (∀ k, S.leader k ∈ Ld.leaders (S.slotRound k)) ∧ Chains U ∧ Checks U K t ∧ Truthful U t

/-- **The link by a claim**: the available sub-DAG below `A` holds a claim
for `L` two rounds above round `r`. -/
def ClaimLinked (U : SRecord Validator BlockId Payload) (K : ℕ) (A L : BlockId) (r : ℕ) : Prop :=
  ∃ C ∈ Avail U K A, (U.block C).round = r + 2 ∧ L ∈ claimsOf U C

/-- **The commit rule on a sparse K-partial DAG** at a three-round row: commit
by claims from `commitThreshold` authors two rounds above, skip by blame, one
rung linked by a claim in the available sub-DAG, twins broken by the least
identifier, and an anchor a certified block. -/
def sRule (p : Params) (K : ℕ) :
    AnchoredRule Validator BlockId Payload (fun blk b => SValid Validator BlockId Payload blk b)
      Correct where
  waveAt := fun _ => 2
  Commit := fun U V L r _ => HoldsAtLeast U V p.commitThreshold (claimersOf U L (r + 2))
  decCommit := fun _ _ _ _ _ => inferInstance
  Skip := fun U V S k => blameSkip (S := S) p.skipThreshold U V k
  rungs := 1
  Link := fun _ U A L S k => ClaimLinked U K A L (S.slotRound k)
  tie := fun _ L L' => L < L'
  Anchor := fun U A => Certified U p.certThreshold A

end KPartialSparse

end LeanDag
