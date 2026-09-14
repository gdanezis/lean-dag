import LeanDag.Steelhead.Model.Replay
/-!
# The replay — statement

What Algorithm 2's replay and selection do (`steelhead.md` §5), the
paper's Lemma 3 among it. Four claims:

* **SH18a, the selection stays among the candidates** — Algorithm 2
  answers a candidate period whenever the current period is one, so the
  period stays in the candidate set (SH10g's premise for it);
* **SH18b, the selection never worsens the score** — the period chosen
  scores no worse than the current one on the window, whatever the
  hysteresis;
* **SH18c, the evidence is consistent** — in the window's evidence a
  committed candidate is certified, and a skipped one is not, at any
  wave of two rounds or more: the direct predicates the replay reads are
  Mahi-Mahi's, restricted to the window;
* **SH18d, the window's committed candidates** — Lemma 3's count: at a
  round of the window whose boost round and decision round a quorum has
  populated *within the window*, at least `n − f − b` authors are marked
  committed at wave `wa`, the counting lemma MM2 read on the anchor's
  causal history as a record of its own. The replay's asynchronous term
  at that round averages over the `n` candidates, so at least that
  fraction of them decide at the decision round.

SH18d asks the quorum's blocks to lie in the window, not merely in the
DAG: the counting lemma counts certificates among the blocks a record
holds, and the replay reads the anchor's causal history, which holds a
quorum's worth of blocks at every round but not necessarily one quorum's
at two rounds. Under synchrony from below the window every reliable block
lies in every reliable cone, and the hypothesis holds; under asynchrony
it is what the paper's "populated" must mean for the lemma to apply to
the window (§7).

Statements only; the proofs live in `Proof.lean`.
-/

namespace LeanDag

namespace Steelhead

namespace Replay

variable {Validator : Type} [Fintype Validator] [DecidableEq Validator]
  [F : Faults Validator] {BlockId : Type} [LinearOrder BlockId] {Payload : Type}

/-- **SH18a, the selection stays among the candidates.** -/
def SelectionValid : Prop :=
  ∀ (candidates : List ℕ) (scores : ℕ → ℚ) (current : ℕ) (epsilon : ℚ),
    current ∈ candidates → select candidates scores current epsilon ∈ candidates

/-- **SH18b, the selection never worsens the score.** -/
def SelectionNonIncreasing : Prop :=
  ∀ (candidates : List ℕ) (scores : ℕ → ℚ) (current : ℕ) (epsilon : ℚ),
    scores (select candidates scores current epsilon) ≤ scores current

/-- **SH18c, the evidence is consistent.** -/
def EvidenceConsistent (U : BlockUniverse Validator BlockId Payload) : Prop :=
  ∀ (A : BlockId) (I r w : ℕ) (a : Validator),
    2 ≤ w →
    -- a committed candidate is certified ...
    ((ofAnchor U A I).commits r w a = true → (ofAnchor U A I).certified r w a = true) ∧
      -- ... and a skipped one is not
      ((ofAnchor U A I).skips r w a = true → (ofAnchor U A I).certified r w a = false)

/-- **SH18d, the window's committed candidates.** -/
def WindowCount (U : BlockUniverse Validator BlockId Payload) (wa I : ℕ) : Prop :=
  ∀ (A : BlockId) (hA : A ∈ U.ids) (T : Finset Validator) (r : ℕ),
    5 ≤ wa → quorumCard Validator ≤ T.card →
    -- the round lies in the window
    windowBottom U A I ≤ r →
    -- T's blocks at the boost round and at the decision round lie in the anchor's history
    PopulatedOn (U.historyView A hA).toRecord T (r + 3) →
    PopulatedOn (U.historyView A hA).toRecord T (MahiMahi.decisionRoundAt wa r) →
    -- then at least n − f − b authors are marked committed at the round and wave
    Fintype.card Validator - F.f - F.byzantine.card ≤
      (Finset.univ.filter fun a => (ofAnchor U A I).commits r wa a = true).card

/-- The replay, over every fault configuration, block universe, asynchronous wave and interval
the model admits. -/
def Statement : Prop :=
  ∀ (Validator BlockId Payload : Type) [Fintype Validator] [DecidableEq Validator]
    [Faults Validator] [LinearOrder BlockId] (U : BlockUniverse Validator BlockId Payload)
    (wa I : ℕ),
    SelectionValid ∧ SelectionNonIncreasing ∧ EvidenceConsistent U ∧ WindowCount U wa I

end Replay

end Steelhead

end LeanDag
