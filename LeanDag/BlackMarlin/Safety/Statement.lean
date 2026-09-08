import LeanDag.BlackMarlin.Model.Decision
import LeanDag.Common.Schedule
/-!
# Black Marlin — safety of the commit rule, stated

The commit rule of `delivery(r)` never admits two anchors that disagree,
whatever DAG the validators hold (`black-marlin.md` §4, following §5.1
of the paper). BM1 is anchor uniqueness (Lemma 3); BM2 is propagation
(Lemma 5); BM3 is density (Lemma 4); BM4 says a validator's verdict is
a verdict of the universe and it holds the block it committed; BM5 is
chaining (Lemma 6): any two committed anchors, from any two views, are
one block or one lies in the other's causal history; BM6 is the
resulting prefix order; BM7 identifies the arc's anchors with the
core's leader blocks under round-robin. BM1–BM3 are stated on the
universe, where the counting happens; BM4–BM6 on views, where the
protocol runs. None assumes synchrony or any bound beyond
`n ≥ 3f + 1`.

Two readings differ from the paper's text. `Reaches` is reflexive where
the paper's `past` and `strong` exclude their own argument, so BM5
states equality as a separate disjunct; and only the strong causal
history is modelled, not weak references, so BM2, BM5 and BM6 conclude
something stronger than the paper's `past`.

Statements only; the proofs live in `Proof.lean`.
-/

namespace LeanDag

namespace BlackMarlin

namespace Safety

variable {Validator : Type*} [Fintype Validator] [DecidableEq Validator]
  [F : Faults Validator] [Rot : Rotation Validator]
  {BlockId : Type*} [DecidableEq BlockId] {Payload : Type*}

/-- **BM1, anchor uniqueness** (the paper's Lemma 3): two supported anchor
blocks of one round are the same block. Their support quorums share
`n − 2f ≥ f + 1` authors, each supporting both, and a validator
supporting two blocks of one author and round is an equivocator — one
more than the fault bound admits. -/
def AnchorUniqueness (U : BlockUniverse Validator BlockId Payload) : Prop :=
  ∀ (r : ℕ) (L₁ L₂ : BlockId),
    IsAnchor U r L₁ → IsAnchor U r L₂ →
    Supported U L₁ r → Supported U L₂ r → L₁ = L₂

/-- **BM2, propagation** (the paper's Lemma 5): a block supported at round
`r` lies in the causal history of every block of the universe at round
`r + 2` or above, whoever authored it. -/
def Propagation (U : BlockUniverse Validator BlockId Payload) : Prop :=
  ∀ (L : BlockId) (r : ℕ) (c : BlockId),
    Supported U L r → c ∈ U.ids → r + 2 ≤ (U.block c).round → Reaches U c L

/-- **BM3, density** (the paper's Lemma 4): if the universe holds a block
above round `r`, then round `r` carries blocks from a quorum of distinct
authors. A consequence of validity alone, and the reason the rule never
inspects a round that could be sparse. -/
def Density (U : BlockUniverse Validator BlockId Payload) : Prop :=
  ∀ (c : BlockId) (r : ℕ), c ∈ U.ids → r < (U.block c).round →
    quorumCard Validator ≤ (authorsAt U r).card

/-- **BM4, soundness of the view reading**: a validator's verdict is a
verdict of the universe, and the validator holds the block it
committed — the second conjunct following from view closure, since the
link to it is a reference. -/
def ViewSound (U : BlockUniverse Validator BlockId Payload) : Prop :=
  ∀ (V : View Validator BlockId Payload U) (L : BlockId) (r : ℕ),
    CommittedIn U V L r → Committed U L r ∧ L ∈ V.ids

/-- **BM5, chaining** (the paper's Lemma 6): two committed anchors, read
from any two views, are the same block or one lies in the causal history
of the other — by BM1 at equal rounds or a gap of one via the shared
linking block, by BM2 at a gap of two or more. -/
def Chained (U : BlockUniverse Validator BlockId Payload) : Prop :=
  ∀ (V₁ V₂ : View Validator BlockId Payload U) (L₁ L₂ : BlockId) (r₁ r₂ : ℕ),
    CommittedIn U V₁ L₁ r₁ → CommittedIn U V₂ L₂ r₂ →
    L₁ = L₂ ∨ Reaches U L₁ L₂ ∨ Reaches U L₂ L₁

/-- **BM6, prefix**: of two committed anchors, the causal history of the
one at the lower round is contained in that of the one at the higher, so
two validators' deliveries agree wherever both have delivered and
neither can retract. -/
def HistoryPrefix (U : BlockUniverse Validator BlockId Payload) : Prop :=
  ∀ (V₁ V₂ : View Validator BlockId Payload U) (L₁ L₂ : BlockId) (r₁ r₂ : ℕ),
    CommittedIn U V₁ L₁ r₁ → CommittedIn U V₂ L₂ r₂ → r₁ ≤ r₂ →
    history U L₁ ⊆ history U L₂

/-- **BM7, the anchors are the core's candidates**: under the pipelined
round-robin schedule an anchor block of round `r` is a leader block of
slot `r`, and conversely — connecting the round-indexed arc to the
slot-indexed vocabulary elsewhere, and asserting nothing about any
verdict. -/
def AnchorsAreLeaderBlocks (U : BlockUniverse Validator BlockId Payload) : Prop :=
  ∀ (r : ℕ) (L : BlockId),
    IsAnchor U r L ↔
      IsLeaderBlock (S := Slots.uniformSingle 1 Nat.one_pos Rot.anchor) U r L

/-- Safety of the Black Marlin commit rule, over every fault
configuration, anchor rotation and block universe the model admits. -/
def Statement : Prop :=
  ∀ (Validator BlockId Payload : Type) [Fintype Validator] [DecidableEq Validator]
    [Faults Validator] [DecidableEq BlockId] [Rotation Validator]
    (U : BlockUniverse Validator BlockId Payload),
    AnchorUniqueness U ∧ Propagation U ∧ Density U ∧ ViewSound U ∧
      Chained U ∧ HistoryPrefix U ∧ AnchorsAreLeaderBlocks U

end Safety

end BlackMarlin

end LeanDag
