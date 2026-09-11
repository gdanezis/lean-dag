import LeanDag.Properties.Bounded
import LeanDag.Properties.Sustain
import LeanDag.Properties.Deliver
import LeanDag.Properties.Candidate
import LeanDag.Properties.Band
import LeanDag.Common.Density
/-!
# Support: what a rule's commit counts

`docs/target-properties.md` §11.7. `Support` names the one thing every
*commit* counts: a rule's per-block certification relation and the
wavelength its certifiers sit at. It is a parameter structure, not a
carrier field, since a rule may have more than one shape (a fast path
and a slow path), each earning its own liveness bound; two laws keep a
parameter from being chosen vacuously — `OfCoverage`, the lower bound
that coverage directed at a candidate certifies it, and `Commits`, the
upper bound that certification by a quorum produces a verdict — and
`Local` is `Banded` for the support relation.

`Support.live` asks that every candidate of a reliably-led slot be
certified by the reliable set a wave up, with nothing about how the
certifiers came to reference what they reference: a reactive execution
supplies that from its wait clauses, a timed one from coverage through
`Timed.live_of_coverage`. `Derived/LeaderCommits.lean` and
`Arcs/Liveness.lean` build `LeaderCommits` and cross-mechanism liveness
from these laws, with no per-rule precondition.
-/

namespace LeanDag

namespace Properties

variable {Validator : Type} [Fintype Validator] [DecidableEq Validator]
variable {BlockId : Type} [DecidableEq BlockId] {Payload : Type}
variable {R : DagRule Validator BlockId Payload}

/-- **A rule's support shape**: how far above a candidate its certifiers
sit, and what it means for one of them to certify it. -/
structure Support (R : DagRule Validator BlockId Payload) where
  /-- The wavelength at a candidate's round: certifiers of a candidate proposed at `r` sit
  `waveAt r` rounds above it. Constant for every rule in the tree; a rule whose wavelength
  alternates with the round supplies a function of it. -/
  waveAt : ℕ → ℕ
  /-- `Certifies U c L`: block `c` certifies candidate `L`. -/
  Certifies : R.Universe → BlockId → BlockId → Prop

namespace Support

variable (sp : Support R)

/-- **The reliable set certifies `L` from round `r`**: every `T`-block a
wave above `r` certifies it. -/
def certifiesAt (U : R.Universe) (T : Finset Validator) (r : ℕ) (L : BlockId) : Prop :=
  ∀ v ∈ T, ∀ c, c ∈ R.ids U → (R.block U c).creator = v →
    (R.block U c).round = r + sp.waveAt r → sp.Certifies U c L

end Support

/-- **A `RebasedAbove` is a band from its settling round up to any
ceiling**, at offsets `0` and `G`. What lets a rule discharge `Local`
with the band lemmas it already has for `Banded`. -/
theorem agreeBand_of_rebasedAbove {U U' : R.Universe} {G R₀ : ℕ}
    (h : RebasedAbove R U U' G R₀) (hi lo : ℕ) (hlo : R₀ ≤ lo) :
    AgreeBand R U U' lo hi 0 G where
  mem := fun b hb h1 _ => ((h.mem b).mp ⟨hb, by omega⟩).1
  block := fun b hb hor => by
    have hR : R₀ ≤ (R.block U b).round := by
      rcases hor with ⟨h1, _⟩ | ⟨hb', h1, _⟩
      · omega
      · have := (h.of_mem' hb' (by omega)).2; omega
    exact ⟨by have := h.round b hb hR; omega, h.creator b hb hR⟩
  refs := fun b hb h1 _ => h.refs b hb (by omega)

namespace Support

variable (sp : Support R)

/-! ## The three laws -/

/-- **Law 1 — certification is local.** `Banded` for the support relation:
across any `RebasedAbove`, a certifier whose whole window sits at or
above the settling round certifies the same candidates. -/
def Local : Prop :=
  ∀ {U U' : R.Universe} {G R₀ : ℕ}, RebasedAbove R U U' G R₀ →
    ∀ c L, c ∈ R.ids U → R₀ + sp.waveAt (R.block U L).round ≤ (R.block U c).round →
      L ∈ R.ids U → (R.block U L).round + sp.waveAt (R.block U L).round = (R.block U c).round →
      (sp.Certifies U' c L ↔ sp.Certifies U c L)

/-- **Law 2 — certification commits.** A slot whose every candidate a
reliable quorum certifies, on a populated window a view is caught up
to, is committed within a bound one above it when a quorum member leads
it. `LeaderCommits` with the precondition made explicit; the upper
bound on `Certifies`. -/
def Commits (rel : Reliability Validator) : Prop :=
  ∀ (S : Slots Validator) {U : R.Universe} (V : R.View U) (T : Finset Validator) (k : ℕ),
    rel.IsQuorum T →
    (∀ n, S.slotRound k ≤ n → n ≤ S.slotRound k + sp.waveAt (S.slotRound k) → PopulatedOn R U T n) →
    (∀ L, R.IsCandidate S U k L → sp.certifiesAt U T (S.slotRound k) L) →
    CoversUpto R V (S.slotRound k + sp.waveAt (S.slotRound k)) →
    S.leader k ∈ T →
    ∃ L, DecidedBelow R S (k + 1) V k (some L)

end Support

/-! ## The one-round shape, once

Odontoceti, Nemo and Hybrid commit when a quorum of the round above
references the candidate — certifier and voter are the same block. Two
of the three laws are facts about references alone, proved here once;
each rule owes only `Commits`. -/

/-- **Vote support**: wavelength one, certification is reference. -/
def voteSupport (R : DagRule Validator BlockId Payload) : Support R where
  waveAt := fun _ => 1
  Certifies := fun U c L => L ∈ (R.block U c).refs

/-- **Law 1 for vote support.** A block strictly above the settling
round keeps its references. -/
theorem voteSupport_local : (voteSupport R).Local := by
  intro U U' G R₀ h c L hc hcr _ _
  change R₀ + 1 ≤ (R.block U c).round at hcr
  change L ∈ (R.block U' c).refs ↔ L ∈ (R.block U c).refs
  rw [h.refs c hc (by omega)]

end Properties

end LeanDag
