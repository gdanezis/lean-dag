import LeanDag.KPartialDag.Model.Substrate
import LeanDag.Common.Anchored
import LeanDag.Common.Rules
import LeanDag.Scheme.Model.Params
/-!
# K-partial DAG — the commit rule's tests

`docs/kpartial.md` §2. The rows of the scheme the substrate runs (`Row`,
`LiveRow`), a row's certificates (`certsFor`, `Certifies`), the direct tests
(`DirectCommit`, `DirectSkip`), the indirect test read on the available
sub-DAG (`AvailLinked`), blocks with votes of `f + 1` authors (`Voted`), and
the commit rule (`kRule`).
-/

namespace LeanDag

namespace KPartialDag

open Scheme

variable {Validator : Type*} [Fintype Validator] [DecidableEq Validator] [F : Faults Validator]
variable {BlockId : Type*} [LinearOrder BlockId] {Payload : Type*}

variable (Validator) in
/-- **A row of the scheme the substrate runs**: a vote one round above the
slot, at the substrate's `n − f` references a block, either as its own
certificate at a wave of two, meeting the two-round inequalities with a link
of `f + 1` authors or more, or certified one round later at a wave of
three, meeting the three-round inequalities with a link of one certificate. -/
def Row (p : Params) : Prop :=
  (p.voteIsCert = true ∧ p.waveLength = 2 ∧ F.f + 1 ≤ p.linkSize ∧
      p.TwoRound (Fintype.card Validator) F.f (quorumCard Validator)) ∨
    (p.voteIsCert = false ∧ p.waveLength = 3 ∧ p.linkSize = 1 ∧
      p.ThreeRound (Fintype.card Validator) F.f (quorumCard Validator))

variable (Validator) in
/-- **A row is live on the substrate**: its commit and certificate thresholds
are at most a quorum. -/
def LiveRow (p : Params) : Prop :=
  p.commitThreshold ≤ quorumCard Validator ∧ p.certThreshold ≤ quorumCard Validator

/-- **The certificates of a round-`r` block `L`** at the decision round
`r + (w − 1)`: the votes for `L`, when a vote is its own certificate, and
otherwise the blocks carrying votes for `L` from `certThreshold` distinct
authors. -/
def certsFor (p : Params) (U : KRecord Validator BlockId Payload) (L : BlockId) (r : ℕ) :
    Finset BlockId :=
  if p.voteIsCert then votesFor U L (r + (p.waveLength - 1))
  else certificatesAt U (IsVote U) p.certThreshold L (r + (p.waveLength - 1))

/-- **`C` certifies the round-`r` block `L`**: it lies at the decision round
and is a vote for `L`, when a vote is its own certificate, and otherwise
carries votes for `L` from `certThreshold` distinct authors. -/
def Certifies (p : Params) (U : KRecord Validator BlockId Payload) (C L : BlockId) (r : ℕ) :
    Prop :=
  (U.block C).round = r + (p.waveLength - 1) ∧
    if p.voteIsCert then IsVote U C L else CarriesVotes U (IsVote U) p.certThreshold C L

/-- **`L` is directly committed**: certificates for it from `commitThreshold`
distinct authors. -/
def DirectCommit (p : Params) (U : KRecord Validator BlockId Payload) (L : BlockId) (r : ℕ) :
    Prop :=
  p.commitThreshold ≤ (creatorsOf U.block (certsFor p U L r)).card

/-- **`L` is directly skipped**: `skipThreshold` distinct authors with a block
at the round above that does not reference it. -/
def DirectSkip (p : Params) (U : KRecord Validator BlockId Payload) (L : BlockId) (r : ℕ) :
    Prop :=
  p.skipThreshold ≤ (blames U L (r + 1)).card

/-- **The indirect test**: the available sub-DAG below the anchor `A` holds
certificates for `L` from `linkSize` distinct authors, each with its
references, which carry its votes, when votes are certified apart. -/
def AvailLinked (p : Params) (U : KRecord Validator BlockId Payload) (K : ℕ) (A L : BlockId)
    (r : ℕ) : Prop :=
  ∃ X ⊆ certsFor p U L r, (∀ C ∈ X, C ∈ Avail U K A ∧
    (p.voteIsCert = false → ∀ j ∈ (U.block C).refs, j ∈ Avail U K A)) ∧
    p.linkSize ≤ (creatorsOf U.block X).card

/-- **`A` is voted for**: blocks of `f + 1` distinct authors one round above
reference it. -/
def Voted (U : KRecord Validator BlockId Payload) (A : BlockId) : Prop :=
  F.f + 1 ≤ (creatorsOf U.block (votesFor U A ((U.block A).round + 1))).card

/-- **The commit rule on a K-partial DAG** at a row of the scheme: the
scheme's direct commit and slot skip read on a view, at the row's wave, with
one rung, linked through the available sub-DAG below the anchor, and twins
broken by the least identifier. -/
def kRule (p : Params) (K : ℕ) :
    AnchoredRule Validator BlockId Payload (KValid Validator BlockId Payload) Correct where
  waveAt := fun _ => p.waveLength - 1
  Commit := fun U V L r _ => HoldsAtLeast U V p.commitThreshold (certsFor p U L r)
  decCommit := fun _ _ _ _ _ => inferInstance
  Skip := fun U V S k => blameSkip (S := S) p.skipThreshold U V k
  rungs := 1
  Link := fun _ U A L S k => AvailLinked p U K A L (S.slotRound k)
  tie := fun _ L L' => L < L'

end KPartialDag

end LeanDag
