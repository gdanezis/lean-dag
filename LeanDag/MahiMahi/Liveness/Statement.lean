import LeanDag.MahiMahi.Model.Unpredictable
import LeanDag.Mysticeti.ViewPace
/-!
# Liveness under the clause — statement

What the rule decides with no network hypothesis, under the
unpredictable-leader clause (`mahi-mahi.md` §5–6): MM3a-MM3d give a good
leader's commit, windowed and run-length liveness, and a local commit
from eventual delivery alone; MM2′ says `good` depends only on blocks up
to the decision round. MM3d needs every reliable decision-round block
to certify the candidate, which the counting lemma supplies for the
common-core candidates.

Statements only; the proofs live in `Proof.lean`.
-/

namespace LeanDag

namespace MahiMahi

namespace Liveness

variable {Validator : Type} [Fintype Validator] [DecidableEq Validator]
  [F : Faults Validator] {BlockId : Type} [LinearOrder BlockId] {Payload : Type}
  [S : Slots Validator]

/-- **MM3a, a good leader commits.** -/
def GoodCommits (U : BlockUniverse Validator BlockId Payload) (w : ℕ) : Prop :=
  ∀ k,
    -- the slot's leader is a committed candidate of its round
    S.leader k ∈ good U w k →
    -- then its block is a candidate, decided as committed from the full view
    ∃ L, IsLeaderBlock U k L ∧ Decided w U (View.full U) k (some L)

/-- **MM3b, commits within every window.** -/
def CommitsWithin (U : BlockUniverse Validator BlockId Payload) (w : ℕ) : Prop :=
  ∀ (c N : ℕ),
    -- the single-hit clause, with window c below horizon N
    UnpredictableWithin U w c N →
    -- for every window below the horizon ...
    ∀ k, (mahiMahiAnchored Validator BlockId Payload w).decisionRound (k + c) ≤ N →
      -- ... some slot of it commits
      ∃ k', k ≤ k' ∧ k' < k + c ∧
        ∃ L, IsLeaderBlock U k' L ∧ Decided w U (View.full U) k' (some L)

/-- **MM3c, every slot below a run is decided.** -/
def AllDecidedBelow (U : BlockUniverse Validator BlockId Payload) (w : ℕ) : Prop :=
  ∀ (c d N : ℕ),
    -- a wave has at least one round (what `k < j` for an eligible anchor needs)
    1 ≤ w →
    -- a run of d slots spans eligibility
    (mahiMahiAnchored Validator BlockId Payload w).SpansEligible d →
    -- the run form of the clause
    UnpredictableRunWithin U w c d N →
    -- for every window below the horizon ...
    ∀ k, (mahiMahiAnchored Validator BlockId Payload w).decisionRound (k + c + d - 1) ≤ N →
      -- ... there is a slot b at or past k below which every slot is decided
      ∃ b, k ≤ b ∧ ∀ i, i < b → ∃ v, Decided w U (View.full U) i v

/-- **MM3d, local liveness.** -/
def LocalCommit (U : BlockUniverse Validator BlockId Payload) (w : ℕ) : Prop :=
  ∀ (T : Finset Validator) (N : ℕ) (pc : PaceCore U T N),
    -- T is a quorum (its correctness is the pacing structure's own)
    quorumCard Validator ≤ T.card →
    -- at a wave of at least one round
    1 ≤ w →
    ∀ (k : ℕ) (L : BlockId),
      -- L is slot k's candidate, and its decision round is within the horizon
      IsLeaderBlock U k L → (mahiMahiAnchored Validator BlockId Payload w).decisionRound k ≤ N →
      -- every reliable decision-round block certifies L
      (∀ u ∈ T, ∀ C ∈ U.ids, (U.block C).creator = u →
        (U.block C).round = (mahiMahiAnchored Validator BlockId Payload w).decisionRound k → Certifies U C L) →
      -- then every reliable validator commits L on its own view, by the time
      -- the decision round's reliable blocks have converged
      ∀ v ∈ T, Decided w U
        (pc.viewAt v (max (pc.latest ((mahiMahiAnchored Validator BlockId Payload w).decisionRound k)) pc.gst + pc.delay))
        k (some L)

/-- **MM2′, measurability of `good`.** -/
def GoodMeasurable : Prop :=
  ∀ (U₁ U₂ : BlockUniverse Validator BlockId Payload) (w r : ℕ),
    -- the voting round is at or above the proposal round
    2 ≤ w →
    -- the two universes agree up to the decision round ...
    AgreeUpto U₁ U₂ (decisionRoundAt w r) →
    -- ... so they commit the same candidates there
    goodAt U₁ w r = goodAt U₂ w r

/-- Liveness under the clause, over every fault configuration, schedule,
block universe and wave length the model admits. -/
def Statement : Prop :=
  ∀ (Validator BlockId Payload : Type) [Fintype Validator] [DecidableEq Validator]
    [Faults Validator] [LinearOrder BlockId] [Slots Validator]
    (U : BlockUniverse Validator BlockId Payload) (w : ℕ),
    GoodCommits U w ∧ CommitsWithin U w ∧ AllDecidedBelow U w ∧ LocalCommit U w ∧
      GoodMeasurable (Validator := Validator) (BlockId := BlockId) (Payload := Payload)

end Liveness

end MahiMahi

end LeanDag
