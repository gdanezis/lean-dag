import LeanDag.KPartialDag.Model.Rule
/-!
# K-partial DAG — what a node reads

`docs/kpartial.md` §5. The available sub-DAG and the commit rule's tests as
read on the blocks `H` a node holds (`AvailIn`, `LinkedIn`, `FetchedIn`,
`heldWithRefs`), and the node's decisions at a row (`NodeDecided`).
-/

namespace LeanDag

namespace KPartialDag

variable {Validator : Type*} [Fintype Validator] [DecidableEq Validator] [F : Faults Validator]
variable [Cr : Crashes Validator]
variable {BlockId : Type*} [LinearOrder BlockId] {Payload : Type*}

/-- **The anchor points below `A`, read on `H`**: those whose history to the
depth they bring the node holds, anchored as in `AnchoredBelow` from blocks
read on `H`. -/
inductive AnchoredIn (U : KRecord Validator BlockId Payload) (K : ℕ) (H : Finset BlockId)
    (A : BlockId) : BlockId → ℕ → Prop
  | anchor : historyUpto U K A ⊆ H → AnchoredIn U K H A A K
  | referenced {x : BlockId} (S : Finset BlockId) (y : BlockId → BlockId) (d : BlockId → ℕ)
      (hy : ∀ z ∈ S, AnchoredIn U K H A (y z) (d z))
      (hz : ∀ z ∈ S, z ∈ historyUpto U (d z) (y z))
      (href : ∀ z ∈ S, x ∈ (U.block z).refs)
      (hcard : F.f + Cr.c + 1 ≤ (creatorsOf U.block S).card)
      (hx : historyUpto U K x ⊆ H) : AnchoredIn U K H A x K
  | reached {x : BlockId} (S : Finset BlockId) (m : BlockId → BlockId)
      (y : BlockId → BlockId) (d : BlockId → ℕ) (y' : BlockId → BlockId) (d' : BlockId → ℕ)
      (hy : ∀ z ∈ S, AnchoredIn U K H A (y z) (d z)) (hz : ∀ z ∈ S, z ∈ historyUpto U (d z) (y z))
      (hy' : ∀ z ∈ S, AnchoredIn U K H A (y' z) (d' z))
      (hmz : ∀ z ∈ S, m z ∈ historyUpto U (d' z) (y' z))
      (hm : ∀ z ∈ S, m z ∈ (U.block z).refs) (href : ∀ z ∈ S, x ∈ (U.block (m z)).refs)
      (hcard : F.f + Cr.c + 1 ≤ (creatorsOf U.block S).card) (hc : 1 ≤ Cr.c)
      (hx : historyUpto U (K - 1) x ⊆ H) : AnchoredIn U K H A x (K - 1)

/-- **The available sub-DAG below `A`, read on `H`.** -/
def AvailIn (U : KRecord Validator BlockId Payload) (K : ℕ) (H : Finset BlockId) (A : BlockId) :
    Set BlockId :=
  {z | ∃ y d, AnchoredIn U K H A y d ∧ z ∈ historyUpto U d y}

/-- **The indirect test, read on `H`**: the sub-DAG below `A` read on `H`
holds certificates for `L` from `linkSize` distinct authors, each with its
references when votes are certified apart. -/
def LinkedIn (p : Scheme.Params) (U : KRecord Validator BlockId Payload) (K : ℕ)
    (H : Finset BlockId) (A L : BlockId) (r : ℕ) : Prop :=
  ∃ X : Finset BlockId, (∀ C ∈ X, C ∈ AvailIn U K H A ∧ Certifies p U C L r ∧
    (p.voteIsCert = false → ∀ j ∈ (U.block C).refs, j ∈ AvailIn U K H A)) ∧
    p.linkSize ≤ (creatorsOf U.block X).card

/-- **The sub-DAG below `A` is fetched into `H` down to round `ρ`**: `H`
holds the history to depth `K` of `A`, and of every block that blocks of
`f + c + 1` distinct authors of the sub-DAG read on `H` above round `ρ`
reference, and, when validators may crash for good, the history to depth
`K − 1` of every block that blocks of `f + c + 1` distinct authors of it reach in
two steps through it, above `ρ`. -/
def FetchedIn (U : KRecord Validator BlockId Payload) (K : ℕ) (H : Finset BlockId)
    (A : BlockId) (ρ : ℕ) : Prop :=
  historyUpto U K A ⊆ H ∧ (∀ (S : Finset BlockId) (x : BlockId),
    (∀ z ∈ S, z ∈ AvailIn U K H A ∧ ρ < (U.block z).round) →
    (∀ z ∈ S, x ∈ (U.block z).refs) → F.f + Cr.c + 1 ≤ (creatorsOf U.block S).card →
    historyUpto U K x ⊆ H) ∧ ∀ (S : Finset BlockId) (m : BlockId → BlockId) (x : BlockId),
    (∀ z ∈ S, z ∈ AvailIn U K H A ∧ m z ∈ AvailIn U K H A ∧ ρ < (U.block (m z)).round) →
    (∀ z ∈ S, m z ∈ (U.block z).refs) → (∀ z ∈ S, x ∈ (U.block (m z)).refs) →
    F.f + Cr.c + 1 ≤ (creatorsOf U.block S).card → 1 ≤ Cr.c → historyUpto U (K - 1) x ⊆ H

/-- The blocks of `s` the node holds with their references. -/
def heldWithRefs (U : KRecord Validator BlockId Payload) (H : Finset BlockId)
    (s : Finset BlockId) : Finset BlockId :=
  s.filter fun b => b ∈ H ∧ ∀ j ∈ (U.block b).refs, j ∈ H

/-- **The commit rule read on what a node holds**, at a row `p`. The direct
commit counts the certificates the node holds with their references, the
direct skip the blamers it holds with theirs; the indirect commit links the
least linked candidate through `LinkedIn`, and the indirect skip finds no
candidate linked, both in the sub-DAG fetched down to the round above the
slot's. -/
inductive NodeDecided [S : Slots Validator] (p : Scheme.Params)
    (U : KRecord Validator BlockId Payload) (K : ℕ) (H : Finset BlockId) :
    ℕ → Option BlockId → Prop
  | directCommit {k : ℕ} {L : BlockId} : IsLeaderBlock U k L →
      p.commitThreshold ≤
        (creatorsOf U.block (heldWithRefs U H (certsFor p U L (S.slotRound k)))).card →
      NodeDecided p U K H k (some L)
  | directSkip {k : ℕ} :
      p.skipThreshold ≤ (creatorsOf U.block (heldWithRefs U H (slotBlamers U k))).card →
      NodeDecided p U K H k none
  | indirectCommit {k j : ℕ} {A L : BlockId} :
      k < j → EligibleAt (S := S) (p.waveLength - 1) k j → NodeDecided p U K H j (some A) →
      (∀ m, k < m → m < j → EligibleAt (S := S) (p.waveLength - 1) k m →
        NodeDecided p U K H m none) →
      FetchedIn U K H A (S.slotRound k + 1) → IsLeaderBlock U k L →
      LinkedIn p U K H A L (S.slotRound k) →
      (∀ L', IsLeaderBlock U k L' → L' < L → ¬ LinkedIn p U K H A L' (S.slotRound k)) →
      NodeDecided p U K H k (some L)
  | indirectSkip {k j : ℕ} {A : BlockId} :
      k < j → EligibleAt (S := S) (p.waveLength - 1) k j → NodeDecided p U K H j (some A) →
      (∀ m, k < m → m < j → EligibleAt (S := S) (p.waveLength - 1) k m →
        NodeDecided p U K H m none) →
      FetchedIn U K H A (S.slotRound k + 1) →
      (∀ L, IsLeaderBlock U k L → ¬ LinkedIn p U K H A L (S.slotRound k)) →
      NodeDecided p U K H k none

end KPartialDag

end LeanDag
