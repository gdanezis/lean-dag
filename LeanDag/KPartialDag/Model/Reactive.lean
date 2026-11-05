import LeanDag.KPartialDag.Model.Live
/-!
# K-partial DAG — reactive nodes in time

`docs/kpartial.md` §11. A timeline gives, for each validator and time, the
blocks it holds with their histories to depth `K` (`held`), and for each
block the time it was built (`built`). A correct node builds above round `r`
once it holds what it waits for (`WaitsFor`): blocks of a quorum of distinct
authors at round `r` (`QuorumIn`), a leader block of every slot at round `r`,
and a certificate for a leader block of every slot at round `r − 1`
(`CertIn`). It also builds once it has held a quorum of round `r` for a
timeout `τ`.

A reactive run (`ReactiveRun`) is a timeline on which correct nodes follow
this rule from round `R` to round `N`, reference the leader blocks and certificates
they hold, and hold every block that another correct node holds at a time
`t ≥ G` by `t + δ`. The blocks of correct nodes from round `R` on are built
at `G + τ` or later.

Definitions only.
-/

namespace LeanDag

namespace KPartialDag

variable {Validator : Type*} [Fintype Validator] [DecidableEq Validator] [F : Faults Validator]
variable {BlockId : Type*} [DecidableEq BlockId] {Payload : Type*}
variable [S : Slots Validator]

/-- **A quorum at round `r` in `H`**: blocks of `H` at round `r` by a quorum of
distinct authors. -/
def QuorumIn (U : KRecord Validator BlockId Payload) (H : Finset BlockId) (r : ℕ) : Prop :=
  quorumCard Validator ≤ (creatorsOf U.block (H.filter fun b => (U.block b).round = r)).card

/-- **A certificate for `L` in `H`**: blocks of `H` at round `r` by a quorum of
distinct authors reference `L`. -/
def CertIn (U : KRecord Validator BlockId Payload) (H : Finset BlockId) (r : ℕ) (L : BlockId) :
    Prop :=
  quorumCard Validator ≤
    (creatorsOf U.block (H.filter fun b => (U.block b).round = r ∧ L ∈ (U.block b).refs)).card

/-- **What a node waits for before building above round `r`**: a quorum at
round `r`, a leader block of every slot at round `r`, and a certificate for a
leader block of every slot at round `r − 1`. -/
def WaitsFor (U : KRecord Validator BlockId Payload) (H : Finset BlockId) (r : ℕ) : Prop :=
  QuorumIn U H r ∧ (∀ k, S.slotRound k = r → ∃ L ∈ H, IsLeaderBlock U k L) ∧
    ∀ k, S.slotRound k + 1 = r → ∃ L, IsLeaderBlock U k L ∧ CertIn U H r L

/-- **A timeline**: the blocks each validator holds at each time, with their
histories to depth `K`, and the time each block was built. -/
structure Timeline (Validator BlockId : Type*) where
  /-- The blocks `v` holds at time `t`. -/
  held : Validator → ℕ → Finset BlockId
  /-- The time a block was built. -/
  built : BlockId → ℕ

/-- **Every correct validator has a block at round `s` built by time `t`.** -/
def BuiltBy (U : KRecord Validator BlockId Payload) (tl : Timeline Validator BlockId)
    (s t : ℕ) : Prop :=
  ∀ v ∈ (Correct : Finset Validator), ∃ b ∈ U.ids, (U.block b).creator = v ∧
    (U.block b).round = s ∧ tl.built b ≤ t

/-- **A reactive run from round `R` to round `N`**, with message delay `δ`
from time `G` and timeout `τ`. -/
structure ReactiveRun (U : KRecord Validator BlockId Payload) (tl : Timeline Validator BlockId)
    (G δ τ R N : ℕ) : Prop where
  /-- Nodes hold blocks of the record. -/
  held_ids : ∀ v t, tl.held v t ⊆ U.ids
  /-- A correct node keeps what it holds. -/
  mono : ∀ v ∈ (Correct : Finset Validator), ∀ t t', t ≤ t' → tl.held v t ⊆ tl.held v t'
  /-- From `G` on, what a correct node holds every correct node holds `δ`
  later. -/
  gossip : ∀ u ∈ (Correct : Finset Validator), ∀ v ∈ (Correct : Finset Validator), ∀ t,
    G ≤ t → tl.held u t ⊆ tl.held v (t + δ)
  /-- A correct node holds the references of the blocks it holds. -/
  closed : ∀ v ∈ (Correct : Finset Validator), ∀ t, ∀ b ∈ tl.held v t,
    (U.block b).refs ⊆ tl.held v t
  /-- A correct author holds its block once built. -/
  own : ∀ b ∈ U.ids, (U.block b).creator ∈ (Correct : Finset Validator) →
    b ∈ tl.held (U.block b).creator (tl.built b)
  /-- A correct node holds a correct block only once it is built. -/
  causal : ∀ v ∈ (Correct : Finset Validator), ∀ t, ∀ b ∈ tl.held v t,
    (U.block b).creator ∈ (Correct : Finset Validator) → tl.built b ≤ t
  /-- Correct blocks from round `R` on are built at `G + τ` or later. -/
  late : ∀ b ∈ U.ids, (U.block b).creator ∈ (Correct : Finset Validator) →
    R ≤ (U.block b).round → G + τ ≤ tl.built b
  /-- Every correct validator has a block at round `R`. -/
  start : ∃ t, BuiltBy U tl R t
  /-- **The wait**: a correct block above round `r ≥ R` is built once its
  author holds what it waits for, or has held a quorum of round `r` for
  `τ`. -/
  waits : ∀ b ∈ U.ids, (U.block b).creator ∈ (Correct : Finset Validator) → ∀ r,
    (U.block b).round = r + 1 → R ≤ r →
    WaitsFor U (tl.held (U.block b).creator (tl.built b)) r ∨
      (τ ≤ tl.built b ∧ QuorumIn U (tl.held (U.block b).creator (tl.built b - τ)) r)
  /-- **No later than the wait**: a correct node that holds what it waits for
  above round `r`, from `R` to below `N`, or has held a quorum of round `r`
  for `τ`, has built its block of round `r + 1`. -/
  prompt : ∀ v ∈ (Correct : Finset Validator), ∀ r t, R ≤ r → r < N →
    (WaitsFor U (tl.held v t) r ∨ (τ ≤ t ∧ QuorumIn U (tl.held v (t - τ)) r)) →
    ∃ b ∈ U.ids, (U.block b).creator = v ∧ (U.block b).round = r + 1 ∧ tl.built b ≤ t
  /-- A correct block references a leader block of each slot one round below
  that its author holds. -/
  votes : ∀ b ∈ U.ids, (U.block b).creator ∈ (Correct : Finset Validator) → ∀ k,
    S.slotRound k + 1 = (U.block b).round →
    (∃ L ∈ tl.held (U.block b).creator (tl.built b), IsLeaderBlock U k L) →
    ∃ L ∈ (U.block b).refs, IsLeaderBlock U k L
  /-- A correct block carries a certificate for a leader block of each slot
  two rounds below for which its author holds one. -/
  certifies : ∀ b ∈ U.ids, (U.block b).creator ∈ (Correct : Finset Validator) → ∀ k,
    S.slotRound k + 2 = (U.block b).round →
    (∃ L, IsLeaderBlock U k L ∧
      CertIn U (tl.held (U.block b).creator (tl.built b)) (S.slotRound k + 1) L) →
    ∃ L, IsLeaderBlock U k L ∧ CarriesVotes U (IsVote U) (quorumCard Validator) b L

end KPartialDag

end LeanDag
