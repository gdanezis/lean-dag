import LeanDag.KPartialSparse.Model.Substrate
import LeanDag.Common.Anchored
import LeanDag.Common.Rules
import LeanDag.Scheme.Model.Params
/-!
# Sparse K-partial DAG — the commit rule

`docs/kpartial-sparse.md` §4. The rows of the scheme the substrate runs, a
claim standing for a certificate in a three-round row (`Row`), a row's
certificates (`Certifies`, `certsFor`), truthful claims (`Truthful`), what
the rule asks of the schedule and the record (`Disciplined`), the link by
certificates in the available sub-DAG (`CertLinked`), and the commit rule
(`sRule`).
-/

namespace LeanDag

namespace KPartialSparse

open KPartialDag Scheme

variable {Validator : Type*} [Fintype Validator] [DecidableEq Validator] [F : Faults Validator]
variable [Cr : Crashes Validator] [Ld : Leaders Validator]
variable {BlockId : Type*} [LinearOrder BlockId] {Payload : Type*} [ClaimFormat BlockId Payload]

variable (Validator) in
/-- **A row of the scheme on the sparse substrate**: a three-round row whose
certificate is a claim, where two certificate thresholds, a certificate and
a skip threshold, and the quorum and a commit threshold each exceed `n + f`,
with a link of one claim; or a two-round row, whose certificate is a vote,
at the scheme's two-round inequalities at the quorum `n − f − c`. -/
def Row (p : Params) : Prop :=
  (p.voteIsCert = false ∧ p.waveLength = 3 ∧ p.linkSize = 1 ∧
      Fintype.card Validator + F.f < 2 * p.certThreshold ∧
      Fintype.card Validator + F.f < p.certThreshold + p.skipThreshold ∧
      Fintype.card Validator + F.f < kQuorum Validator + p.commitThreshold) ∨
    (p.voteIsCert = true ∧ p.waveLength = 2 ∧
      p.TwoRound (Fintype.card Validator) F.f (kQuorum Validator))

/-- **The round of a round-`r` block's certificates**: one round above when a
vote is its own certificate, two otherwise. -/
def certRound (p : Params) (r : ℕ) : ℕ := if p.voteIsCert then r + 1 else r + 2

/-- **`C` certifies the round-`r` block `L`**: a vote for it one round above,
when a vote is its own certificate, and otherwise a claim for it two rounds
above. -/
def Certifies (p : Params) (U : SRecord Validator BlockId Payload) (C L : BlockId) (r : ℕ) :
    Prop :=
  if p.voteIsCert then (U.block C).round = r + 1 ∧ L ∈ (U.block C).refs
  else (U.block C).round = r + 2 ∧ L ∈ claimsOf U C

/-- **The certificates of a round-`r` block `L`**: its votes one round above,
or its claimers two rounds above. -/
def certsFor (p : Params) (U : SRecord Validator BlockId Payload) (L : BlockId) (r : ℕ) :
    Finset BlockId :=
  if p.voteIsCert then votesFor U L (r + 1) else claimersOf U L (r + 2)

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

/-- **The link by certificates**: the available sub-DAG below `A` holds
certificates for the round-`r` block `L` from `linkSize` distinct authors. -/
def CertLinked (p : Params) (U : SRecord Validator BlockId Payload) (K : ℕ) (A L : BlockId)
    (r : ℕ) : Prop :=
  ∃ X : Finset BlockId, (∀ C ∈ X, C ∈ U.ids ∧ C ∈ Avail U K A ∧ Certifies p U C L r) ∧
    p.linkSize ≤ (creatorsOf U.block X).card

/-- **The commit rule on a sparse K-partial DAG** at a row of the scheme:
commit by certificates from `commitThreshold` authors, skip by blame, one
rung linked by certificates in the available sub-DAG, twins broken by the
least identifier, and an anchor a certified block when certificates are
claims. -/
def sRule (p : Params) (K : ℕ) :
    AnchoredRule Validator BlockId Payload (fun blk b => SValid Validator BlockId Payload blk b)
      Correct where
  waveAt := fun _ => p.waveLength - 1
  Commit := fun U V L r _ => HoldsAtLeast U V p.commitThreshold (certsFor p U L r)
  decCommit := fun _ _ _ _ _ => inferInstance
  Skip := fun U V S k => blameSkip (S := S) p.skipThreshold U V k
  rungs := 1
  Link := fun _ U A L S k => CertLinked p U K A L (S.slotRound k)
  tie := fun _ L L' => L < L'
  Anchor := fun U A => p.voteIsCert = true ∨ Certified U p.certThreshold A

end KPartialSparse

end LeanDag
