import LeanDag.Scheme.Model.Local
import LeanDag.Scheme.Model.LeastSel
import LeanDag.Scheme.Model.VotedBlock
import LeanDag.Properties.Band
import LeanDag.Properties.Agree
import LeanDag.Properties.Candidate
import LeanDag.Properties.Commit
import LeanDag.Properties.Optional.Quorate
import LeanDag.Properties.Optional.SelfParent
import LeanDag.Properties.Arcs.Headline
/-!
# The family's properties — statement

`docs/scheme.md` §9.1. The decider's carrier `schemeRule p σ Hon` shows
the properties the mechanisms read, for the whole family:

* the least vote and the scheme's own vote are **local**;
* at a local vote, a wave of at least two, and positive link and
  certificate thresholds, the carrier is **banded**, at every row;
* its commits name **candidates**, and its indirect rule is a property
  (**`Indirect`**), at every row and vote;
* its universes are **quorate** when validity asks `q` distinct authors
  of a block's references and `q` is a reliability's quorum, and its
  reliable validators **do not equivocate** when they lie in `Hon`;
* at a local vote and every row meeting its inequalities, the carrier is
  **safe** across every stack of mechanisms (`Properties.Safe`).

Statements only; the proofs are `Proof.lean`.
-/

namespace LeanDag

namespace Scheme

namespace Family

open LeanDag.Properties

/-- **The least vote is local.** -/
def LeastLocal : Prop :=
  ∀ (Validator BlockId Payload : Type) [Fintype Validator] [DecidableEq Validator]
    [LinearOrder BlockId] (P : Validity Validator BlockId Payload) [P.Mechanised]
    (honest : Finset Validator), (leastSel : VoteSel Validator BlockId Payload P honest).Local

/-- **The scheme's vote is local**, for every parent order listing every
parent: a vote-selection rule whose vote is `votedBlock` is local. -/
def VotedBlockLocal : Prop :=
  ∀ (Validator BlockId Payload : Type) [Fintype Validator] [DecidableEq Validator]
    [LinearOrder BlockId] (P : Validity Validator BlockId Payload) [P.Mechanised]
    (honest : Finset Validator) (ord : BlockId → Finset BlockId → List BlockId),
    (∀ b s x, x ∈ ord b s ↔ x ∈ s) →
    ∀ σ : VoteSel Validator BlockId Payload P honest, σ.sel = votedBlock ord → σ.Local

/-- **The carrier is banded**, at every row with a wave of at least two
and positive link and certificate thresholds, at a local vote. -/
def FamilyBanded : Prop :=
  ∀ (Validator BlockId Payload : Type) [Fintype Validator] [DecidableEq Validator]
    [LinearOrder BlockId] (P : Validity Validator BlockId Payload) [P.Mechanised]
    (honest Hon : Finset Validator) (p : Params)
    (σ : VoteSel Validator BlockId Payload P honest),
    σ.Local → 2 ≤ p.waveLength → 1 ≤ p.linkSize →
    (p.voteIsCert = false → 1 ≤ p.certThreshold) → Banded (schemeRule p σ Hon)

/-- **Commits name candidates, and the indirect rule is a property**, at
every row and vote. -/
def FamilyCandidateIndirect : Prop :=
  ∀ (Validator BlockId Payload : Type) [Fintype Validator] [DecidableEq Validator]
    [LinearOrder BlockId] (P : Validity Validator BlockId Payload) [P.Mechanised]
    (honest Hon : Finset Validator) (p : Params)
    (σ : VoteSel Validator BlockId Payload P honest),
    CommitsCandidate (schemeRule p σ Hon) ∧
    Indirect (schemeRule p σ Hon) (fun S i j => S.slotRound i + (p.waveLength - 1) + 1 ≤
      S.slotRound j)

/-- **Quorate and non-equivocating universes**, from validity and the
invariant. -/
def FamilyQuorateNoEquiv : Prop :=
  ∀ (Validator BlockId Payload : Type) [Fintype Validator] [DecidableEq Validator]
    [LinearOrder BlockId] (P : Validity Validator BlockId Payload) [P.Mechanised]
    (q : ℕ) [P.Quorate q] (honest Hon : Finset Validator) (p : Params)
    (σ : VoteSel Validator BlockId Payload P honest) (rel : Reliability Validator),
    (Fintype.card Validator - rel.slack ≤ q → Quorate (schemeRule p σ Hon) rel) ∧
    (rel.correct ⊆ Hon → NoEquiv (schemeRule p σ Hon) rel)

/-- **Every block references its author's previous block**, on the core's
universes. -/
def FamilySelfParent : Prop :=
  ∀ (Validator BlockId Payload : Type) [Fintype Validator] [DecidableEq Validator]
    [Faults Validator] [LinearOrder BlockId] (Hon : Finset Validator) (p : Params)
    (σ : VoteSel Validator BlockId Payload ValidWrt Correct),
    SelfParent (schemeRule p σ Hon)

/-- **The carrier is safe across every stack of mechanisms**, at every row
meeting its inequalities, at a local vote, on records with quorum `q`
where validators outside `Hon`, at most `f`, may equivocate. -/
def FamilySafe : Prop :=
  ∀ (Validator BlockId Payload : Type) [Fintype Validator] [DecidableEq Validator]
    [LinearOrder BlockId] (P : Validity Validator BlockId Payload) [P.Mechanised]
    (q : ℕ) [P.Quorate q] (honest Hon : Finset Validator) (f : ℕ) (p : Params)
    (σ : VoteSel Validator BlockId Payload P honest),
    σ.Local → Honᶜ.card ≤ f → q ≤ Fintype.card Validator →
    ((p.voteIsCert = true ∧ 2 ≤ p.waveLength ∧ 1 ≤ p.linkSize ∧
        p.TwoRound (Fintype.card Validator) f q) ∨
      (p.voteIsCert = false ∧ 3 ≤ p.waveLength ∧ p.linkSize = 1 ∧
        p.ThreeRound (Fintype.card Validator) f q)) →
    Agree (schemeRule p σ Hon) ∧ Safe (schemeRule p σ Hon)

/-- The family's properties. -/
def Statement : Prop :=
  LeastLocal ∧ VotedBlockLocal ∧ FamilyBanded ∧ FamilyCandidateIndirect ∧
    FamilyQuorateNoEquiv ∧ FamilySelfParent ∧ FamilySafe

end Family

end Scheme

end LeanDag
