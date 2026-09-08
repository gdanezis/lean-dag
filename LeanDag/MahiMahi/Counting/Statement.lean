import LeanDag.MahiMahi.Model.Good
import LeanDag.Mysticeti.Liveness
/-!
# The counting lemma — statement

What a wave commits with no network hypothesis (`mahi-mahi.md` §4):
`CommonCore` (a correct round-`r` block reached by every later block),
`GoodNonempty` and `GoodCard` (direct commits at `w ≥ 4` and `w ≥ 5`),
and `MultiLeader`. The `w ≥ 5` bound counts only correct references,
since an equivocating author's reference need not vote for a fixed
twin; this yields `2f+1` good leaders under no-equivocation, matching
Cordial Miners, where the paper's `f+1` needs no such restriction.

Statements only; the proofs live in `Proof.lean`.
-/

namespace LeanDag

namespace MahiMahi

namespace Counting

variable {Validator : Type*} [Fintype Validator] [DecidableEq Validator]
  [F : Faults Validator] {BlockId : Type*} [LinearOrder BlockId] {Payload : Type*}
  [S : Slots Validator]

/-- **The common core.** If some block exists at round `r + 2`, a correct
validator's round-`r` block lies in the causal history of every block at
every round `≥ r + 2`. The core's T3c (`CommonCore.lean`) at round `r + 2`,
carried upward through references. -/
def CommonCore (U : BlockUniverse Validator BlockId Payload) : Prop :=
  ∀ (r : ℕ) (c₀ : BlockId),
    -- some block exists two rounds above r (its own quorum of references
    -- is what makes the round-(r+1) author pool large enough to count)
    c₀ ∈ U.ids → (U.block c₀).round = r + 2 →
    -- then there is a round-r block b ...
    ∃ b ∈ U.ids, (U.block b).round = r ∧
      -- ... by a correct validator ...
      (U.block b).creator ∈ (Correct : Finset Validator) ∧
      -- ... in the causal history of EVERY block at round ≥ r + 2
      ∀ c ∈ U.ids, r + 2 ≤ (U.block c).round → Reaches U c b

/-- **MM2 at `w ≥ 4`.** Some correct validator's round-`r` block is
directly committed. The common core of round `r` is reached by every
voting-round block (`r + w − 2 ≥ r + 2`), so every decision-round block
certifies it, and the reliable ones are a quorum. -/
def GoodNonempty (U : BlockUniverse Validator BlockId Payload) (w : ℕ) : Prop :=
  ∀ (T : Finset Validator) (r : ℕ),
    -- at least four rounds: the voting round r + w − 2 is at or above r + 2,
    -- where the common core is reached by everyone
    4 ≤ w →
    -- T is a reliable set: correct, and a quorum
    T ⊆ (Correct : Finset Validator) → quorumCard Validator ≤ T.card →
    -- every member of T has a block at round r + 2 (so the common core
    -- exists) ...
    PopulatedOn U T (r + 2) →
    -- ... and at the decision round r + w − 1 (so the certificates form a
    -- quorum)
    PopulatedOn U T (decisionRoundAt w r) →
    -- then some correct validator's round-r block is directly committed
    (goodAt U w r ∩ (Correct : Finset Validator)).Nonempty

/-- **MM2 at `w ≥ 5`.** `n − f ≤ |good ∩ Correct| + |byzantine|`: every
correct author among the round-`(r+1)` common core's references is
directly committed, since every voting-round block reaches the core and
each reference through it. At `n = 3f+1` this is `f + 1` validators. -/
def GoodCard (U : BlockUniverse Validator BlockId Payload) (w : ℕ) : Prop :=
  ∀ (T : Finset Validator) (r : ℕ),
    -- at least five rounds: the voting round r + w − 2 is at or above r + 3,
    -- where the common core of round r + 1 is reached by everyone
    5 ≤ w →
    -- T is a reliable set: correct, and a quorum
    T ⊆ (Correct : Finset Validator) → quorumCard Validator ≤ T.card →
    -- every member of T has a block at round r + 3 (so the round-(r+1)
    -- common core exists) ...
    PopulatedOn U T (r + 3) →
    -- ... and at the decision round r + w − 1
    PopulatedOn U T (decisionRoundAt w r) →
    -- then n − f ≤ |good ∩ Correct| + |byzantine|: the core's n − f
    -- references have distinct creators, and every correct one is good
    quorumCard Validator ≤
      (goodAt U w r ∩ (Correct : Finset Validator)).card + F.byzantine.card

/-- **MM2b, deterministic commits under multiple leaders.** If `2f + 1`
distinct validators lead slots at round `r` and `w ≥ 5`, one is good,
for every schedule: `f + 1` good validators and `2f + 1` leaders cannot
be disjoint in `3f + 1`. -/
def MultiLeader (U : BlockUniverse Validator BlockId Payload) (w : ℕ) : Prop :=
  ∀ (T : Finset Validator) (r : ℕ),
    -- the hypotheses of GoodCard, verbatim
    5 ≤ w →
    T ⊆ (Correct : Finset Validator) → quorumCard Validator ≤ T.card →
    PopulatedOn U T (r + 3) → PopulatedOn U T (decisionRoundAt w r) →
    -- M is a set of validators each of which leads some slot at round r ...
    ∀ M : Finset Validator, (∀ v ∈ M, ∃ k, S.slotRound k = r ∧ S.leader k = v) →
      -- ... with at least 2f + 1 members (distinct, being a Finset)
      2 * F.f + 1 ≤ M.card →
      -- then one of those slots is led by a good validator
      ∃ k, S.slotRound k = r ∧ S.leader k ∈ good U w k

/-- The counting lemma, over every fault configuration, schedule, block
universe and wave length the model admits. -/
def Statement : Prop :=
  ∀ (Validator BlockId Payload : Type) [Fintype Validator] [DecidableEq Validator]
    [Faults Validator] [LinearOrder BlockId] [Slots Validator]
    (U : BlockUniverse Validator BlockId Payload) (w : ℕ),
    CommonCore U ∧ GoodNonempty U w ∧ GoodCard U w ∧ MultiLeader U w

end Counting

end MahiMahi

end LeanDag
