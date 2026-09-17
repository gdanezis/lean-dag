import LeanDag.Steelhead.Model.Replay
import LeanDag.Steelhead.Model.Coin
/-!
# The replay — statement

What Algorithm 2's replay and selection do (`steelhead.md` §5), the
paper's Lemma 3 among it. Ten claims:

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
  causal history as a record of its own;
* **SH18e, the timings are bounded** — every round's expected decision
  lies at or above the round, its expected commit at or above its
  decision, and both at or below the window's top, so the window's top
  is the penalty an unresolved outcome pays and no more;
* **SH18f, the asynchronous term is bounded by the committed count** —
  Lemma 3's second sentence in the form that is a theorem: at an
  asynchronous round of the window whose committed candidates are not
  skipped, the replay's commit term is at most the mean over the `n`
  candidates of the decision round for the `c_r` committed ones and the
  window's top for the rest; with SH18d, `c_r ≥ n − f − b` bounds the
  term under any scheduling. The bound charges every candidate without
  a direct commit the window's top; the asynchronous rule's own latency
  on the same data is not modelled, and no comparison with it is
  claimed;
* **SH18g, a window commit is a commit on the DAG** — a candidate the
  window marks committed is directly committed on the DAG, so a probe's
  success is a certificate quorum the DAG holds: the adversary can
  suppress the probes' evidence of the synchronous rule, never
  manufacture it. What this does not give is a bound on the synchronous
  term itself: the replay extends the probes' rate to the unprobed
  synchronous slots, and a scheduler that serves the canary rounds'
  leaders alone raises that estimate above what those slots hold;
* **SH18h, Algorithm 2 keeps the range** — with candidates in `[1, K]`,
  the replay's selection answers a period in `[1, K]` at every anchor,
  whether it keeps the current period or picks a candidate: the range
  hypothesis SH10g, SH14b, SH14c and SH15 place on the update rule,
  discharged for the paper's rule; the failover's `1` is the scan's own
  (SH10e) and lies in the range too;
* **SH18i, the replay's commit weight is the rule's commit
  probability** — the adaptive section's "exact in expectation", in the
  part that is a theorem: at a round of the window, the share of the `n`
  candidates the window marks committed is the probability that a
  uniform coin names a directly committed leader on the anchor's causal
  history read as a record of its own, `c_r / n`. The anchor's term is
  the approximation the paper admits, and not claimed;
* **SH18j, a probe exists** — the protocol section's "setting the canary
  odd ensures it is coprime to candidate periods, guaranteeing periodic
  probes": at a canary spacing coprime to a candidate period of at
  least two, a window holding two canary rounds whose decision round it
  retains holds a probe for that candidate, since two consecutive
  multiples of the spacing cannot both be multiples of the period.

SH18d asks the quorum's blocks to lie in the window, not merely in the
DAG: the counting lemma counts certificates among the blocks a record
holds, and the replay reads the anchor's causal history, which holds a
quorum's worth of blocks at every round but not necessarily one quorum's
at two rounds. Under synchrony from below the window every reliable block
lies in every reliable cone, and the hypothesis holds; under asynchrony
it is what the paper's "populated" must mean for the lemma to apply to
the window (§7). SH18e and SH18f ask `2 ≤ ws` and `ws < wa`, the waves
of the `3f + 1` pair, so that a round's decision round lies at or above
it and an asynchronous round is not read as an unprobed synchronous one.
SH18i asks `1 ≤ wa` and SH18j `1 ≤ ws`, so that a round's decision round
lies at or above it: the certificates of a round the window retains then
lie in the window, and a probe's in the range the window resolves.

Statements only; the proofs live in `Proof.lean`.
-/

namespace LeanDag

namespace Steelhead

namespace Replay

open scoped ENNReal

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
    Fintype.card Validator - F.f - F.byzantine.card ≤ committedCount (ofAnchor U A I) r wa

/-- **SH18e, the timings are bounded.** -/
def TimingBounded : Prop :=
  ∀ (E : Evidence Validator) (C : Config Validator) (period r : ℕ),
    2 ≤ C.ws → 2 ≤ C.wa → r ≤ E.top →
    -- a round's expected decision lies at or above the round, its expected commit at or above
    -- its decision, and both at or below the window's top
    (r : ℚ) ≤ (timingAt E C period (probeRate E C period) r).decision ∧
      (timingAt E C period (probeRate E C period) r).decision ≤
        (timingAt E C period (probeRate E C period) r).commit ∧
      (timingAt E C period (probeRate E C period) r).commit ≤ E.top

/-- **SH18f, the asynchronous term is at most the rule's own value.** -/
def AsyncTermBound : Prop :=
  ∀ (E : Evidence Validator) (C : Config Validator) (period r : ℕ),
    2 ≤ C.ws → C.ws < C.wa →
    -- an asynchronous round of the window under the candidate period, decided inside the window
    E.bottom ≤ r → r % period = 0 → r + C.wa - 1 ≤ E.top →
    -- whose committed candidates are not skipped, as the window's are (SH18c)
    (∀ a, E.commits r C.wa a = true → E.skips r C.wa a = false) →
    -- then the replay's commit term at r is at most the mean over the n candidates of the
    -- decision round for the committed ones and the window's top for the rest
    (timingAt E C period (probeRate E C period) r).commit ≤
      ((committedCount E r C.wa * (r + C.wa - 1) +
        (Fintype.card Validator - committedCount E r C.wa) * E.top : ℕ) : ℚ) /
        Fintype.card Validator

/-- **SH18g, a window commit is a commit on the DAG.** -/
def CommitsSound (U : BlockUniverse Validator BlockId Payload) : Prop :=
  ∀ (A : BlockId) (I r w : ℕ) (a : Validator),
    (ofAnchor U A I).commits r w a = true →
    ∃ L ∈ blocksAt U r, (U.block L).creator = a ∧ MahiMahi.DirectCommit U w L r

/-- **SH18h, Algorithm 2 keeps the range.** -/
def UpdateInRange (U : BlockUniverse Validator BlockId Payload) (I : ℕ) : Prop :=
  ∀ (C : Config Validator) (candidates : List ℕ) (epsilon : ℚ) (K k : ℕ) (A : BlockId),
    -- the candidates lie in [1, K], as does the current period
    (∀ c ∈ candidates, 1 ≤ c ∧ c ≤ K) → 1 ≤ k → k ≤ K →
    -- then so does the selection's answer at any anchor
    1 ≤ anchorUpdate U I C candidates epsilon A k ∧ anchorUpdate U I C candidates epsilon A k ≤ K

/-- **SH18i, the replay's commit weight is the rule's commit probability.** -/
def CommitWeightExact (U : BlockUniverse Validator BlockId Payload) (wa I : ℕ) : Prop :=
  ∀ (A : BlockId) (hA : A ∈ U.ids) (r : ℕ),
    -- a wave of at least one round, and the round lies in the window
    1 ≤ wa → windowBottom U A I ≤ r →
    -- then the share of the candidates the window marks committed is the probability that the
    -- coin names a committed leader on the anchor's history read as a record
    (committedCount (ofAnchor U A I) r wa : ℝ≥0∞) / Fintype.card Validator =
      commitProb (U.historyView A hA).toRecord wa r

/-- **SH18j, a probe exists.** -/
def ProbeExists : Prop :=
  ∀ (E : Evidence Validator) (C : Config Validator) (canary period : ℕ),
    -- the canary is on, and its spacing is coprime to the candidate period, which is at least two
    C.canary = some canary → Nat.Coprime canary period → 2 ≤ period → 1 ≤ C.ws →
    -- and the window holds two canary rounds whose decision round it retains
    E.bottom + 2 * canary + C.ws ≤ E.top + 2 →
    -- then the candidate has a probe
    0 < (probeRate E C period).2

/-- The replay, over every fault configuration, block universe, asynchronous wave and interval
the model admits. -/
def Statement : Prop :=
  ∀ (Validator BlockId Payload : Type) [Fintype Validator] [DecidableEq Validator]
    [Faults Validator] [LinearOrder BlockId] (U : BlockUniverse Validator BlockId Payload)
    (wa I : ℕ),
    SelectionValid ∧ SelectionNonIncreasing ∧ EvidenceConsistent U ∧ WindowCount U wa I ∧
      TimingBounded (Validator := Validator) ∧ AsyncTermBound (Validator := Validator) ∧
      CommitsSound U ∧ UpdateInRange U I ∧ CommitWeightExact U wa I ∧
      ProbeExists (Validator := Validator)

end Replay

end Steelhead

end LeanDag
