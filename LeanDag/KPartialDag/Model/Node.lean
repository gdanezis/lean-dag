import LeanDag.KPartialDag.Model.Rule
/-!
# K-partial DAG — what a node reads

`docs/kpartial.md` §5. A node holds a set `H` of blocks, not closed under
histories. It reads the available sub-DAG below an anchor on `H`: a block is
anchored in `H` when its history to depth `K` is held and it is the anchor,
or blocks of `f + 1` distinct authors of the sub-DAG read so far reference it
(`AnchoredIn`, `AvailIn`). It links a candidate when it holds, in that
sub-DAG, a certificate for it with the certificate's references
(`LinkedIn`). It has fetched the sub-DAG when the anchor's history and the
history of every block that blocks of `f + 1` distinct authors of it
reference are held (`FetchedIn`).

The node decides by the commit rule read on what it holds
(`NodeDecided`): the direct tests count the certificates and blamers it
holds with their references, the indirect commit reads `LinkedIn`, and the
indirect skip needs the sub-DAG below the anchor fetched.

Definitions only.
-/

namespace LeanDag

namespace KPartialDag

variable {Validator : Type*} [Fintype Validator] [DecidableEq Validator] [F : Faults Validator]
variable {BlockId : Type*} [DecidableEq BlockId] {Payload : Type*}

/-- **The blocks anchored below `A`, read on `H`**: those whose history to
depth `K` the node holds, and which are `A`, or which blocks of `f + 1`
distinct authors reference, each `z` in the history to depth `K` of a block
`y z` anchored in `H`. -/
inductive AnchoredIn (U : KRecord Validator BlockId Payload) (K : ℕ) (H : Finset BlockId)
    (A : BlockId) : BlockId → Prop
  | anchor : historyUpto U K A ⊆ H → AnchoredIn U K H A A
  | referenced {x : BlockId} (S : Finset BlockId) (y : BlockId → BlockId)
      (hy : ∀ z ∈ S, AnchoredIn U K H A (y z)) (hz : ∀ z ∈ S, z ∈ historyUpto U K (y z))
      (href : ∀ z ∈ S, x ∈ (U.block z).refs)
      (hcard : F.f + 1 ≤ (creatorsOf U.block S).card)
      (hx : historyUpto U K x ⊆ H) : AnchoredIn U K H A x

/-- **The available sub-DAG below `A`, read on `H`.** -/
def AvailIn (U : KRecord Validator BlockId Payload) (K : ℕ) (H : Finset BlockId) (A : BlockId) :
    Set BlockId :=
  {z | ∃ y, AnchoredIn U K H A y ∧ z ∈ historyUpto U K y}

/-- **The indirect test, read on `H`**: the sub-DAG below `A` read on `H`
holds a round-`(r+2)` block carrying votes for `L` from a quorum, and that
block's references. -/
def LinkedIn (U : KRecord Validator BlockId Payload) (K : ℕ) (H : Finset BlockId)
    (A L : BlockId) (r : ℕ) : Prop :=
  ∃ C ∈ AvailIn U K H A, (U.block C).round = r + 2 ∧
    (∀ j ∈ (U.block C).refs, j ∈ AvailIn U K H A) ∧
    CarriesVotes U (IsVote U) (quorumCard Validator) C L

/-- **The sub-DAG below `A` is fetched into `H`**: `H` holds the history to
depth `K` of `A`, and of every block that blocks of `f + 1` distinct authors
of the sub-DAG read on `H` reference. -/
def FetchedIn (U : KRecord Validator BlockId Payload) (K : ℕ) (H : Finset BlockId)
    (A : BlockId) : Prop :=
  historyUpto U K A ⊆ H ∧ ∀ (S : Finset BlockId) (x : BlockId), (∀ z ∈ S, z ∈ AvailIn U K H A) →
    (∀ z ∈ S, x ∈ (U.block z).refs) → F.f + 1 ≤ (creatorsOf U.block S).card →
    historyUpto U K x ⊆ H

/-- The blocks of `s` the node holds with their references. -/
def heldWithRefs (U : KRecord Validator BlockId Payload) (H : Finset BlockId)
    (s : Finset BlockId) : Finset BlockId :=
  s.filter fun b => b ∈ H ∧ ∀ j ∈ (U.block b).refs, j ∈ H

/-- **The commit rule read on what a node holds.** The direct commit counts
the certificates the node holds with their references, the direct skip the
blamers it holds with theirs; the indirect commit links through `LinkedIn`,
and the indirect skip finds no candidate linked in a fetched sub-DAG. -/
inductive NodeDecided [S : Slots Validator] (U : KRecord Validator BlockId Payload) (K : ℕ)
    (H : Finset BlockId) : ℕ → Option BlockId → Prop
  | directCommit {k : ℕ} {L : BlockId} : IsLeaderBlock U k L →
      quorumCard Validator ≤ (creatorsOf U.block (heldWithRefs U H
        (certificatesAt U (IsVote U) (quorumCard Validator) L (S.slotRound k + 2)))).card →
      NodeDecided U K H k (some L)
  | directSkip {k : ℕ} :
      quorumCard Validator ≤ (creatorsOf U.block (heldWithRefs U H (slotBlamers U k))).card →
      NodeDecided U K H k none
  | indirectCommit {k j : ℕ} {A L : BlockId} :
      k < j → EligibleAt (S := S) 2 k j → NodeDecided U K H j (some A) →
      (∀ m, k < m → m < j → EligibleAt (S := S) 2 k m → NodeDecided U K H m none) →
      IsLeaderBlock U k L → LinkedIn U K H A L (S.slotRound k) → NodeDecided U K H k (some L)
  | indirectSkip {k j : ℕ} {A : BlockId} :
      k < j → EligibleAt (S := S) 2 k j → NodeDecided U K H j (some A) →
      (∀ m, k < m → m < j → EligibleAt (S := S) 2 k m → NodeDecided U K H m none) →
      FetchedIn U K H A → (∀ L, IsLeaderBlock U k L → ¬ LinkedIn U K H A L (S.slotRound k)) →
      NodeDecided U K H k none

end KPartialDag

end LeanDag
