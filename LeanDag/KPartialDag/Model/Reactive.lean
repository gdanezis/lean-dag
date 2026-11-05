import LeanDag.KPartialDag.Model.Live
/-!
# K-partial DAG — reactive nodes in time

`docs/kpartial.md` §11. A timeline gives, for each validator and time, the
blocks it holds (`held`) and the blocks it keeps on disk (`disk`), and for
each block the time it was built (`built`). A correct node builds above
round `r` once it holds what it waits for (`WaitsFor`): blocks of a quorum of
distinct authors at round `r` (`QuorumIn`), a leader block of every slot at
round `r`, and a certificate for a leader block of every slot at round
`r − 1` (`CertIn`), and then, for a grace period `γ`, for blocks of every
validator at round `r` (`AllIn`). It also builds once it has held a quorum
of round `r` for a timeout `τ`. In either case it builds no earlier than a
minimum wait `μ` after it first held a quorum of round `r`. It references a
block of every author whose block of round `r` it holds.

A node behind builds above round `r` at once when it holds blocks of round
`r + 1` by `f + 1` authors other than itself (`BehindIn`): one of them is
correct, so a correct node has built the round. A node builds above the
highest round it can, and may skip rounds.

Before a time `G` correct nodes may crash and restart, all at once too. A
restart loses what a node held, except what it keeps on disk: its highest
block, with the block's references. From `G` on correct nodes are up, keep
what they hold, and pass on the correct blocks they hold within `δ`. A
correct node holds the references of the blocks it holds above a round `R`;
below, history may be lost.

The timeline follows the rules for nodes from round `R` to round `N`
(`NodeRules`) when correct nodes follow these rules there; it follows the
reactive rules (`ReactiveRules`) when, in addition, every correct node has
reached round `R`. It is a reactive run (`ReactiveRun`) when, in addition,
the blocks of correct nodes from round `R` on are built at `G + τ` or later.
A node keeps on disk the last round it built, and builds only above it
(`Persists`); that is all it needs to build at most one block a round. A
node that builds above the blocks of its own on its disk (`BuildsAboveDisk`)
does so, numbering its builds by time.

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

/-- **Behind round `r + 1` in `H`, for `v`**: blocks of `H` at round `r + 1`
by `f + 1` distinct authors other than `v`. -/
def BehindIn (U : KRecord Validator BlockId Payload) (H : Finset BlockId) (v : Validator)
    (r : ℕ) : Prop :=
  F.f + 1 ≤ ((creatorsOf U.block (H.filter fun b => (U.block b).round = r + 1)).erase v).card

/-- **All authors at round `r` in `H`**: a block of every validator at round
`r`. -/
def AllIn (U : KRecord Validator BlockId Payload) (H : Finset BlockId) (r : ℕ) : Prop :=
  ∀ w : Validator, ∃ x ∈ H, (U.block x).round = r ∧ (U.block x).creator = w

/-- **A timeline**: the blocks each validator holds and keeps on disk at each
time, and the time each block was built. -/
structure Timeline (Validator BlockId : Type*) where
  /-- The blocks `v` holds at time `t`. -/
  held : Validator → ℕ → Finset BlockId
  /-- The blocks `v` keeps on disk at time `t`. -/
  disk : Validator → ℕ → Finset BlockId
  /-- The time a block was built. -/
  built : BlockId → ℕ

/-- **Every correct validator has a block at round `s` built by time `t`.** -/
def BuiltBy (U : KRecord Validator BlockId Payload) (tl : Timeline Validator BlockId)
    (s t : ℕ) : Prop :=
  ∀ v ∈ (Correct : Finset Validator), ∃ b ∈ U.ids, (U.block b).creator = v ∧
    (U.block b).round = s ∧ tl.built b ≤ t

/-- **Every correct validator has a block at round `s` or above built by time
`t`.** -/
def ReachedBy (U : KRecord Validator BlockId Payload) (tl : Timeline Validator BlockId)
    (s t : ℕ) : Prop :=
  ∀ v ∈ (Correct : Finset Validator), ∃ b ∈ U.ids, (U.block b).creator = v ∧
    s ≤ (U.block b).round ∧ tl.built b ≤ t

/-- **The rules for nodes from round `R` to round `N`**, with restarts before
`G`, message delay `δ` from `G`, timeout `τ`, grace period `γ` and minimum
wait `μ`. -/
structure NodeRules (U : KRecord Validator BlockId Payload)
    (tl : Timeline Validator BlockId) (G δ τ γ μ R N : ℕ) : Prop where
  /-- Nodes hold blocks of the record. -/
  held_ids : ∀ v t, tl.held v t ⊆ U.ids
  /-- From `G` on, a correct node keeps what it holds. -/
  mono : ∀ v ∈ (Correct : Finset Validator), ∀ t t', G ≤ t → t ≤ t' →
    tl.held v t ⊆ tl.held v t'
  /-- From `G` on, a correct block held by a correct node is held by every
  correct node `δ` later. -/
  delivers : ∀ v ∈ (Correct : Finset Validator), ∀ t, G ≤ t → ∀ b ∈ tl.held v t,
    (U.block b).creator ∈ (Correct : Finset Validator) →
    ∀ w ∈ (Correct : Finset Validator), b ∈ tl.held w (t + δ)
  /-- A correct node holds its block when it builds it. -/
  own : ∀ b ∈ U.ids, (U.block b).creator ∈ (Correct : Finset Validator) →
    b ∈ tl.held (U.block b).creator (tl.built b)
  /-- A correct node holds the references of the blocks it holds above round
  `R`. -/
  closed : ∀ v ∈ (Correct : Finset Validator), ∀ t, ∀ b ∈ tl.held v t, R < (U.block b).round →
    (U.block b).refs ⊆ tl.held v t
  /-- A correct node holds a correct block only once it is built. -/
  causal : ∀ v ∈ (Correct : Finset Validator), ∀ t, ∀ b ∈ tl.held v t,
    (U.block b).creator ∈ (Correct : Finset Validator) → tl.built b ≤ t
  /-- A correct node holds another correct author's block only after it is
  built. -/
  prior : ∀ v ∈ (Correct : Finset Validator), ∀ t, ∀ b ∈ tl.held v t,
    (U.block b).creator ∈ (Correct : Finset Validator) → (U.block b).creator ≠ v →
    tl.built b < t
  /-- A correct node holds what it keeps on disk. -/
  disk_held : ∀ v ∈ (Correct : Finset Validator), ∀ t, tl.disk v t ⊆ tl.held v t
  /-- A correct node keeps on disk a block of its own at least as high as any
  it has built, with the block's references. -/
  stores : ∀ b ∈ U.ids, (U.block b).creator ∈ (Correct : Finset Validator) → ∀ t,
    tl.built b ≤ t → ∃ b' ∈ tl.disk (U.block b).creator t,
      (U.block b').creator = (U.block b).creator ∧ (U.block b).round ≤ (U.block b').round ∧
      (U.block b').refs ⊆ tl.disk (U.block b).creator t
  /-- **The wait**: a correct block above round `r ≥ R` is built once its
  author has held what it waits for for `γ` and still holds it, holds it with
  blocks of every validator at round `r`, has held a quorum of round `r` for
  `τ`, or is behind round `r + 1`. -/
  waits : ∀ b ∈ U.ids, (U.block b).creator ∈ (Correct : Finset Validator) → ∀ r,
    (U.block b).round = r + 1 → R ≤ r →
    (γ ≤ tl.built b ∧ WaitsFor U (tl.held (U.block b).creator (tl.built b - γ)) r ∧
        WaitsFor U (tl.held (U.block b).creator (tl.built b)) r) ∨
      (WaitsFor U (tl.held (U.block b).creator (tl.built b)) r ∧
        AllIn U (tl.held (U.block b).creator (tl.built b)) r) ∨
      (τ ≤ tl.built b ∧ QuorumIn U (tl.held (U.block b).creator (tl.built b - τ)) r) ∨
      BehindIn U (tl.held (U.block b).creator (tl.built b)) (U.block b).creator r
  /-- **No later than the wait**: a correct node that has held a quorum of
  round `r`, from `R` to below `N`, for `μ`, and has held what it waits for
  above `r` for `γ`, holds it with blocks of every validator at round `r`, or
  has held the quorum for `τ`, all since `G`, has built a block above `r`; so
  has a correct node behind round `r + 1` from `G` on. -/
  prompt : ∀ v ∈ (Correct : Finset Validator), ∀ r t, R ≤ r → r < N →
    (G + μ ≤ t ∧ QuorumIn U (tl.held v (t - μ)) r ∧
      ((G + γ ≤ t ∧ WaitsFor U (tl.held v (t - γ)) r) ∨
        (WaitsFor U (tl.held v t) r ∧ AllIn U (tl.held v t) r) ∨
        (G + τ ≤ t ∧ QuorumIn U (tl.held v (t - τ)) r)) ∨
      G ≤ t ∧ BehindIn U (tl.held v t) v r) →
    ∃ b ∈ U.ids, (U.block b).creator = v ∧ r + 1 ≤ (U.block b).round ∧ tl.built b ≤ t
  /-- A correct block references a block of every author whose block of the
  round below its author holds. -/
  covers : ∀ b ∈ U.ids, (U.block b).creator ∈ (Correct : Finset Validator) →
    ∀ x ∈ tl.held (U.block b).creator (tl.built b), (U.block x).round + 1 = (U.block b).round →
    ∃ y ∈ (U.block b).refs, (U.block y).creator = (U.block x).creator
  /-- A correct block carries a certificate for a leader block of each slot
  two rounds below for which its author holds one. -/
  certifies : ∀ b ∈ U.ids, (U.block b).creator ∈ (Correct : Finset Validator) → ∀ k,
    S.slotRound k + 2 = (U.block b).round →
    (∃ L, IsLeaderBlock U k L ∧
      CertIn U (tl.held (U.block b).creator (tl.built b)) (S.slotRound k + 1) L) →
    ∃ L, IsLeaderBlock U k L ∧ CarriesVotes U (IsVote U) (quorumCard Validator) b L

/-- **The reactive rules from round `R` to round `N`**: the rules for nodes,
with every correct validator at round `R` or above. -/
structure ReactiveRules (U : KRecord Validator BlockId Payload)
    (tl : Timeline Validator BlockId) (G δ τ γ μ R N : ℕ) : Prop
    extends NodeRules U tl G δ τ γ μ R N where
  /-- Every correct validator has a block at round `R` or above. -/
  start : ∃ t, ReachedBy U tl R t

/-- **A reactive run from round `R` to round `N`**: the reactive rules, with
the correct blocks from round `R` on built at `G + τ` or later. -/
structure ReactiveRun (U : KRecord Validator BlockId Payload) (tl : Timeline Validator BlockId)
    (G δ τ γ μ R N : ℕ) : Prop extends ReactiveRules U tl G δ τ γ μ R N where
  /-- Correct blocks from round `R` on are built at `G + τ` or later. -/
  late : ∀ b ∈ U.ids, (U.block b).creator ∈ (Correct : Finset Validator) →
    R ≤ (U.block b).round → G + τ ≤ tl.built b

/-- **Persisting the last round built**: the builds of each correct
validator are numbered in order (`order`), and before its `i`-th build it
keeps on disk the lowest round it may build at, one above the last round it
built (`next v i`), which never decreases, across restarts too. It builds
only at or above that round, raises it above the block's round before it
sends the block, and numbers no two builds alike. -/
structure Persists (ids : Finset BlockId) (block : BlockId → Block Validator BlockId Payload)
    (order : BlockId → ℕ) (next : Validator → ℕ → ℕ) : Prop where
  /-- The lowest round to build at never decreases. -/
  grows : ∀ v ∈ (Correct : Finset Validator), ∀ i j, i ≤ j → next v i ≤ next v j
  /-- A correct block is at or above the lowest round its author may build at. -/
  above : ∀ b ∈ ids, (block b).creator ∈ (Correct : Finset Validator) →
    next (block b).creator (order b) ≤ (block b).round
  /-- A correct block's round is below the lowest round before its author's
  next build. -/
  stores : ∀ b ∈ ids, (block b).creator ∈ (Correct : Finset Validator) →
    (block b).round < next (block b).creator (order b + 1)
  /-- No two builds of a correct validator have the same number. -/
  single : ∀ b ∈ ids, ∀ c ∈ ids, (block b).creator ∈ (Correct : Finset Validator) →
    (block b).creator = (block c).creator → order b = order c → b = c

/-- **Building above the disk**: a correct validator keeps on disk a block of
its own as high as any it has built, builds at most one block at a time, and
builds only above the blocks of its own that it kept on disk the time
before. -/
structure BuildsAboveDisk (ids : Finset BlockId) (block : BlockId → Block Validator BlockId Payload)
    (tl : Timeline Validator BlockId) : Prop where
  /-- A correct node keeps on disk a block of its own at least as high as any
  it has built. -/
  stores : ∀ b ∈ ids, (block b).creator ∈ (Correct : Finset Validator) → ∀ t,
    tl.built b ≤ t → ∃ b' ∈ tl.disk (block b).creator t,
      (block b').creator = (block b).creator ∧ (block b).round ≤ (block b').round
  /-- A correct block is above the blocks of its author that its author kept
  on disk the time before. -/
  above : ∀ b ∈ ids, (block b).creator ∈ (Correct : Finset Validator) → 0 < tl.built b →
    ∀ b' ∈ tl.disk (block b).creator (tl.built b - 1),
      (block b').creator = (block b).creator → (block b').round < (block b).round
  /-- A correct validator builds at most one block at a time. -/
  single : ∀ b ∈ ids, ∀ c ∈ ids, (block b).creator ∈ (Correct : Finset Validator) →
    (block b).creator = (block c).creator → tl.built b = tl.built c → b = c

end KPartialDag

end LeanDag
