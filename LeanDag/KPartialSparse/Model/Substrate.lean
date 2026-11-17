import LeanDag.KPartialDag.Model.Substrate
/-!
# Sparse K-partial DAG — the substrate

`docs/kpartial-sparse.md` §1. The leaders of each round (`Leaders`), what a
payload claims certified (`ClaimFormat`), the two block shapes (`Dense`,
`Sparse`) and the substrate's validity and record (`SValid`, `SRecord`),
certification and claims (`Certified`, `claimersOf`), the honest
disciplines (`Chains`, `Checks`), and the available sub-DAG with anchor
points reached in one step or two (`Anchored`, `Avail`).
-/

namespace LeanDag

namespace KPartialSparse

open KPartialDag

variable (Validator) in
/-- **The leaders of each round**, fixed before the run. -/
class Leaders (Validator : Type*) where
  /-- The validators that lead round `r`. -/
  leaders : ℕ → Finset Validator

/-- **What a payload claims certified**: blocks two rounds below. -/
class ClaimFormat (BlockId : Type*) (Payload : Type*) where
  /-- The blocks the payload claims certified. -/
  claims : Payload → Finset BlockId

variable {Validator : Type*} [Fintype Validator] [DecidableEq Validator] [F : Faults Validator]
variable [Cr : Crashes Validator] [Ld : Leaders Validator]
variable {BlockId : Type*} [LinearOrder BlockId] {Payload : Type*}

/-- The references of `b` one round below it. -/
def below1 (blk : BlockId → Block Validator BlockId Payload) (b : Block Validator BlockId Payload) :
    Finset BlockId :=
  b.refs.filter fun i => (blk i).round + 1 = b.round

/-- **A dense block** references blocks of `q` distinct authors one round
below. -/
def Dense (q : ℕ) (blk : BlockId → Block Validator BlockId Payload)
    (b : Block Validator BlockId Payload) : Prop :=
  q ≤ (creatorsOf blk (below1 blk b)).card

/-- **A sparse block** references its author's block one round below and,
besides it, only leader blocks one round below, at least one. -/
def Sparse (blk : BlockId → Block Validator BlockId Payload) (b : Block Validator BlockId Payload) :
    Prop :=
  (∃ s ∈ b.refs, (blk s).creator = b.creator ∧ (blk s).round + 1 = b.round) ∧
    (∀ i ∈ b.refs, (blk i).creator ≠ b.creator →
      (blk i).round + 1 = b.round ∧ (blk i).creator ∈ Ld.leaders (b.round - 1)) ∧
    ∃ i ∈ b.refs, (blk i).round + 1 = b.round ∧ (blk i).creator ∈ Ld.leaders (b.round - 1)

variable (Validator BlockId Payload) in
/-- **The sparse substrate's validity**: references lie below, those of other
authors one round below, at most one per author; a non-genesis block is dense
or sparse, and a leader's block is dense. -/
structure SValid (blk : BlockId → Block Validator BlockId Payload)
    (b : Block Validator BlockId Payload) : Prop where
  /-- References lie below. -/
  below : ∀ i ∈ b.refs, (blk i).round < b.round
  /-- References to other authors lie one round below. -/
  others : ∀ i ∈ b.refs, (blk i).creator ≠ b.creator → (blk i).round + 1 = b.round
  /-- At most one reference per author. -/
  distinct : ∀ i ∈ b.refs, ∀ j ∈ b.refs, (blk i).creator = (blk j).creator → i = j
  /-- A non-genesis block is dense or sparse. -/
  shape : 0 < b.round → Dense (kQuorum Validator) blk b ∨ Sparse blk b
  /-- A leader's block is dense. -/
  leader : 0 < b.round → b.creator ∈ Ld.leaders b.round → Dense (kQuorum Validator) blk b

variable (Validator BlockId Payload) in
/-- **A sparse K-partial DAG**: a record at the sparse validity, whose honest
authors are the correct validators. -/
abbrev SRecord :=
  BlockRecord Validator BlockId Payload (fun blk b => SValid Validator BlockId Payload blk b) Correct

variable [ClaimFormat BlockId Payload]

/-- The blocks `X` claims certified. -/
abbrev claimsOf (U : SRecord Validator BlockId Payload) (X : BlockId) : Finset BlockId :=
  ClaimFormat.claims (U.block X).payload

/-- The round-`ρ` blocks that claim `L` certified. -/
def claimersOf (U : SRecord Validator BlockId Payload) (L : BlockId) (ρ : ℕ) : Finset BlockId :=
  (blocksAt U ρ).filter fun C => L ∈ claimsOf U C

/-- **`L` is certified** at threshold `t`: blocks of `t` distinct authors one
round above reference it. -/
def Certified (U : SRecord Validator BlockId Payload) (t : ℕ) (L : BlockId) : Prop :=
  t ≤ (supporters U L ((U.block L).round + 1)).card

/-- **Honest chains**: a correct author's block references a block of its own
at or above each earlier block of its. -/
def Chains (U : SRecord Validator BlockId Payload) : Prop :=
  ∀ y ∈ U.ids, (U.block y).creator ∈ (Correct : Finset Validator) →
    ∀ x ∈ U.ids, (U.block x).creator = (U.block y).creator → (U.block x).round < (U.block y).round →
      ∃ s ∈ (U.block y).refs, (U.block s).creator = (U.block y).creator ∧
        (U.block x).round ≤ (U.block s).round

/-- **Honest checks**: a correct author references a block only when every
claim in its history to depth `K` names a block certified at threshold `t`. -/
def Checks (U : SRecord Validator BlockId Payload) (K t : ℕ) : Prop :=
  ∀ z ∈ U.ids, (U.block z).creator ∈ (Correct : Finset Validator) → ∀ m ∈ (U.block z).refs,
    ∀ X ∈ historyUpto U K m, ∀ L ∈ claimsOf U X, Certified U t L

/-- **The anchor points below `A`, with the depth of history each brings**: `A`
to depth `K`; a block referenced by blocks of the sub-DAG from `f + c + 1`
distinct authors, to depth `K`; and a block they reach in two steps through
the sub-DAG, to depth `K − 1`. -/
inductive Anchored (U : SRecord Validator BlockId Payload) (K : ℕ) (A : BlockId) :
    BlockId → ℕ → Prop
  | anchor : Anchored U K A A K
  | referenced {x : BlockId} (S : Finset BlockId) (y : BlockId → BlockId) (d : BlockId → ℕ)
      (hy : ∀ z ∈ S, Anchored U K A (y z) (d z))
      (hz : ∀ z ∈ S, z ∈ historyUpto U (d z) (y z))
      (href : ∀ z ∈ S, x ∈ (U.block z).refs)
      (hcard : F.f + Cr.c + 1 ≤ (creatorsOf U.block S).card) : Anchored U K A x K
  | reached {x : BlockId} (S : Finset BlockId) (m : BlockId → BlockId)
      (y : BlockId → BlockId) (d : BlockId → ℕ) (y' : BlockId → BlockId) (d' : BlockId → ℕ)
      (hy : ∀ z ∈ S, Anchored U K A (y z) (d z)) (hz : ∀ z ∈ S, z ∈ historyUpto U (d z) (y z))
      (hy' : ∀ z ∈ S, Anchored U K A (y' z) (d' z))
      (hmz : ∀ z ∈ S, m z ∈ historyUpto U (d' z) (y' z))
      (hm : ∀ z ∈ S, m z ∈ (U.block z).refs) (href : ∀ z ∈ S, x ∈ (U.block (m z)).refs)
      (hcard : F.f + Cr.c + 1 ≤ (creatorsOf U.block S).card) : Anchored U K A x (K - 1)

/-- **The available sub-DAG below `A`**: the history each anchor point
brings. -/
def Avail (U : SRecord Validator BlockId Payload) (K : ℕ) (A : BlockId) : Set BlockId :=
  {z | ∃ y d, Anchored U K A y d ∧ z ∈ historyUpto U d y}

end KPartialSparse

end LeanDag
