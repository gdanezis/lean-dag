import LeanDag.Scheme.Helpers.Band
import LeanDag.Scheme.Helpers.Support
import LeanDag.Scheme.Loop.Proof
import LeanDag.Properties.Agree
import LeanDag.Properties.Candidate
import LeanDag.Properties.Commit
import LeanDag.Properties.Optional.Direct
import LeanDag.Properties.Optional.Skip
import LeanDag.Properties.Optional.Quorate
import LeanDag.Properties.Optional.SelfParent
import LeanDag.Properties.Arcs.Headline
/-!
# The family as a carrier, and the properties it shows

`docs/scheme.md` §9. The decider's carrier `schemeRule p σ Hon` shows the
properties the mechanisms read, for the whole family:

* **`Banded`** at a local vote (`leastSel_local`, `votedBlockSel_local`), a
  wave of at least two and positive link and certificate thresholds, by
  the band laws of `Helpers/Band.lean`; the rule needs nothing of its
  anchors;
* **`CommitsCandidate`**, **`CommitsDirect`** and **`Indirect`** at every
  row and vote; **`SkipsUnsupported`** at a vote round one above the slot;
* **`Quorate`**, **`NoEquiv`** and, on the core's universes,
  **`SelfParent`**, from validity and the invariant;
* **`Agree`** and **`Safe`** at every row meeting its inequalities;
* the support `familySupport` with its three laws (**`Local`**,
  **`Commits`**, **`OfCoverage`**, `Helpers/Support.lean`), and **`Lives`**
  on the core's universes.
-/

namespace LeanDag

namespace Scheme

open LeanDag.Properties

variable {Validator : Type} [Fintype Validator] [DecidableEq Validator]
variable {BlockId : Type} [LinearOrder BlockId] {Payload : Type}
variable {P : Validity Validator BlockId Payload} [P.Mechanised] {honest Hon : Finset Validator}
variable {p : Params} {σ : VoteSel Validator BlockId Payload P honest}

/-- **The carrier is banded**, at every row, at a local vote. -/
theorem banded (hσ : σ.Local) (hw : 2 ≤ p.waveLength) (hl : 1 ≤ p.linkSize)
    (hc : p.voteIsCert = false → 1 ≤ p.certThreshold) : Banded (schemeRule p σ Hon) :=
  AnchoredRule.bandedOn (schemeBandLaws hσ hw hl hc) (J := fun _ _ => True)
    (fun _ _ => trivial) fun _ _ _ => trivial

/-- **A commit names a candidate.** -/
theorem commitsCandidate : CommitsCandidate (schemeRule p σ Hon) :=
  AnchoredRule.commitsCandidateOn

/-- **A direct commit is a verdict.** -/
theorem commitsDirect : CommitsDirect (schemeRule p σ Hon)
    (fun {U} V L r κ => (schemeAnchored p σ).Commit U.val V L r κ) :=
  AnchoredRule.commitsDirectOn

/-- **The indirect rule is a property.** -/
theorem indirect : Indirect (schemeRule p σ Hon)
    (fun S i j => S.slotRound i + (p.waveLength - 1) + 1 ≤ S.slotRound j) :=
  AnchoredRule.indirectOn ((schemeAnchored p σ).linkCongr_of_round
    (fun _ U A L r => p.linkSize ≤ (creatorsOf U.block ((certsAt p σ U L r).filter
      (fun C => C ∈ history U A))).card) fun _ _ _ _ _ _ => rfl)
    fun _ h => AnchoredRule.exists_least_of_lt (fun _ _ => Iff.rfl) h

/-- **A slot every quorum member's block one round up leaves unsupported
is skipped**, at a vote round one above the slot and a skip threshold the
quorum meets. -/
theorem skipsUnsupported (hv : p.voteOffset = 1) :
    SkipsUnsupported (schemeRule p σ Hon) (fun T => p.skipThreshold ≤ T.card) := by
  intro S U V T k hq hpres huns
  refine AnchoredRule.Decided.directSkip (S := S) ?_
  show p.skipThreshold ≤ (heldAuthors U.val V (blamersAt p σ U.val k)).card
  refine le_trans hq (Finset.card_le_card fun v hvT => ?_)
  obtain ⟨c, hcV, hcc, hcr⟩ := hpres v hvT
  have hcU : c ∈ U.val.ids := V.subset_ids hcV
  have hcr' : (U.val.block c).round = S.slotRound k + 1 := hcr
  have hcc' : (U.val.block c).creator = v := hcc
  refine mem_heldAuthors.mpr ⟨c, Finset.mem_filter.mpr ⟨mem_blocksAt.mpr ⟨hcU, by rw [hv]; exact
    hcr'⟩, (sel_none_iff σ hcU hcr').mpr fun j hj hjL => ?_⟩, hcV, hcc'⟩
  exact huns c hcV (show (U.val.block c).creator ∈ T by rw [hcc']; exact hvT) hcr j hjL hj

/-- **The universes are quorate**, when validity's quorum is the
reliability's. -/
theorem quorate {q : ℕ} [P.Quorate q] {rel : Reliability Validator}
    (hq : Fintype.card Validator - rel.slack ≤ q) : Quorate (schemeRule p σ Hon) rel :=
  fun U _ hb hr => le_trans hq (U.val.creators_quorum hb hr)

/-- **A reliable author has one block per round**, when the reliable
validators lie in `Hon`. -/
theorem noEquiv {rel : Reliability Validator} (hsub : rel.correct ⊆ Hon) :
    NoEquiv (schemeRule p σ Hon) rel :=
  fun U b c hb hc hbc heq hr => U.property b hb c hc (hsub hbc) heq hr

/-- **Every block references its author's previous block**, on the core's
universes. -/
theorem selfParent [Faults Validator] {σ : VoteSel Validator BlockId Payload ValidWrt Correct} :
    SelfParent (schemeRule p σ Hon) :=
  fun U b hb hr => (U.val.valid b hb).self_parent hr

/-- **Two views decide alike** at every row meeting its inequalities, on
records with quorum `q` where validators outside `Hon`, at most `f`, may
equivocate. -/
theorem agree {q : ℕ} [P.Quorate q] {f : ℕ} (hHon : Honᶜ.card ≤ f)
    (hq : q ≤ Fintype.card Validator)
    (hfam : (p.voteIsCert = true ∧ 2 ≤ p.waveLength ∧ 1 ≤ p.linkSize ∧
        p.TwoRound (Fintype.card Validator) f q) ∨
      (p.voteIsCert = false ∧ 3 ≤ p.waveLength ∧ p.linkSize = 1 ∧
        p.ThreeRound (Fintype.card Validator) f q)) :
    Agree (schemeRule p σ Hon) :=
  AnchoredRule.agreeOn (Loop.family σ hHon hq hfam).2.2.2 (fun _ _ h => h)

/-- **The carrier is safe across every stack of mechanisms**, at every row
meeting its inequalities, at a local vote. -/
theorem safety {q : ℕ} [P.Quorate q] {f : ℕ} (hσ : σ.Local) (hHon : Honᶜ.card ≤ f)
    (hq : q ≤ Fintype.card Validator)
    (hfam : (p.voteIsCert = true ∧ 2 ≤ p.waveLength ∧ 1 ≤ p.linkSize ∧
        p.TwoRound (Fintype.card Validator) f q) ∨
      (p.voteIsCert = false ∧ 3 ≤ p.waveLength ∧ p.linkSize = 1 ∧
        p.ThreeRound (Fintype.card Validator) f q)) :
    Safe (schemeRule p σ Hon) := by
  obtain ⟨hl, -, hc, -⟩ := Loop.family σ hHon hq hfam
  have hw : 2 ≤ p.waveLength := by rcases hfam with ⟨-, hw, -⟩ | ⟨-, hw, -⟩ <;> omega
  exact Properties.safety (banded hσ hw hl hc) (agree hHon hq hfam) commitsCandidate

/-- **The carrier lives** on the core's universes, at a commit threshold
the correct validators meet: progress and inclusion. -/
theorem lives [F : Faults Validator] {σ : VoteSel Validator BlockId Payload ValidWrt Correct}
    (hsub : (Correct : Finset Validator) ⊆ Hon)
    (hlive : p.commitThreshold ≤ Fintype.card Validator - F.f) :
    Support.Lives (R := schemeRule p σ Hon) (familySupport p σ Hon) (coreReliability Validator) :=
  Support.liveness (familySupport_commits hlive) commitsCandidate selfParent (noEquiv hsub)

end Scheme

end LeanDag
