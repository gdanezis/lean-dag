import LeanDag.KPartialSparse.Model.Rule
/-!
# Sparse K-partial DAG — what a node reads

`docs/kpartial-sparse.md` §5. The available sub-DAG and the link as read on
the blocks `H` a node holds (`AnchoredIn`, `AvailIn`, `LinkedIn`), the
sub-DAG fetched into `H` down to a round (`FetchedIn`), and the node's
decisions at a row (`NodeDecided`).
-/

namespace LeanDag

namespace KPartialSparse

open KPartialDag Scheme

variable {Validator : Type*} [Fintype Validator] [DecidableEq Validator] [F : Faults Validator]
variable [Cr : Crashes Validator] [Ld : Leaders Validator]
variable {BlockId : Type*} [LinearOrder BlockId] {Payload : Type*}

/-- **The anchor points below `A`, read on `H`**: those whose history to the
depth they bring the node holds, anchored as in `Anchored` from blocks read
on `H`. -/
inductive AnchoredIn (U : SRecord Validator BlockId Payload) (K : ℕ) (H : Finset BlockId)
    (A : BlockId) : BlockId → ℕ → Prop
  | anchor : historyUpto U K A ⊆ H → AnchoredIn U K H A A K
  | reached {x : BlockId} (i : ℕ) (S : Finset BlockId) (m : BlockId → BlockId)
      (y : BlockId → BlockId) (d : BlockId → ℕ) (y' : BlockId → BlockId) (d' : BlockId → ℕ)
      (hy : ∀ z ∈ S, AnchoredIn U K H A (y z) (d z))
      (hz : ∀ z ∈ S, z ∈ historyUpto U (d z) (y z))
      (hy' : ∀ z ∈ S, 0 < i → AnchoredIn U K H A (y' z) (d' z))
      (hmz : ∀ z ∈ S, 0 < i → m z ∈ historyUpto U (d' z) (y' z))
      (hi : i ≤ 1) (hm : ∀ z ∈ S, m z ∈ (U.block z).refs ∧ x ∈ historyUpto U i (m z))
      (hcard : F.f + Cr.c + 1 ≤ (creatorsOf U.block S).card)
      (hx : historyUpto U (K - i) x ⊆ H) : AnchoredIn U K H A x (K - i)

/-- **The available sub-DAG below `A`, read on `H`.** -/
def AvailIn (U : SRecord Validator BlockId Payload) (K : ℕ) (H : Finset BlockId) (A : BlockId) :
    Set BlockId :=
  {z | ∃ y d, AnchoredIn U K H A y d ∧ z ∈ historyUpto U d y}

variable [ClaimFormat BlockId Payload]

/-- **The link, read on `H`**: the sub-DAG below `A` read on `H` holds a claim
for `L` two rounds above round `r`. -/
def LinkedIn (U : SRecord Validator BlockId Payload) (K : ℕ) (H : Finset BlockId) (A L : BlockId)
    (r : ℕ) : Prop :=
  ∃ C ∈ AvailIn U K H A, (U.block C).round = r + 2 ∧ L ∈ claimsOf U C

omit [ClaimFormat BlockId Payload] in
/-- **The sub-DAG below `A` is fetched into `H` down to round `ρ`**: `H` holds
the history to depth `K` of `A`, and the history every anchor point brings
when the blocks of the sub-DAG read on `H` that reach it lie above `ρ`. -/
def FetchedIn (U : SRecord Validator BlockId Payload) (K : ℕ) (H : Finset BlockId) (A : BlockId)
    (ρ : ℕ) : Prop :=
  historyUpto U K A ⊆ H ∧ ∀ (i : ℕ) (S : Finset BlockId) (m : BlockId → BlockId) (x : BlockId),
    i ≤ 1 → (∀ z ∈ S, z ∈ AvailIn U K H A ∧ ρ < (U.block z).round ∧
      (0 < i → m z ∈ AvailIn U K H A) ∧ m z ∈ (U.block z).refs ∧ x ∈ historyUpto U i (m z)) →
    F.f + Cr.c + 1 ≤ (creatorsOf U.block S).card → historyUpto U (K - i) x ⊆ H

/-- **The commit rule read on what a node holds**, at a row `p`. The direct
commit counts the claimers it holds, the direct skip the blamers it holds;
the indirect commit links the least linked candidate through `LinkedIn`, and
the indirect skip finds no candidate linked, both in the sub-DAG fetched down
to the round of the slot's claims. -/
inductive NodeDecided [S : Slots Validator] (p : Params) (U : SRecord Validator BlockId Payload)
    (K : ℕ) (H : Finset BlockId) : ℕ → Option BlockId → Prop
  | directCommit {k : ℕ} {L : BlockId} : IsLeaderBlock U k L →
      p.commitThreshold ≤
        (creatorsOf U.block ((claimersOf U L (S.slotRound k + 2)).filter (· ∈ H))).card →
      NodeDecided p U K H k (some L)
  | directSkip {k : ℕ} :
      p.skipThreshold ≤ (creatorsOf U.block ((slotBlamers U k).filter (· ∈ H))).card →
      NodeDecided p U K H k none
  | indirectCommit {k j : ℕ} {A L : BlockId} :
      k < j → EligibleAt (S := S) 2 k j → NodeDecided p U K H j (some A) →
      (∀ m, k < m → m < j → EligibleAt (S := S) 2 k m → NodeDecided p U K H m none) →
      FetchedIn U K H A (S.slotRound k + 2) → IsLeaderBlock U k L →
      LinkedIn U K H A L (S.slotRound k) →
      (∀ L', IsLeaderBlock U k L' → L' < L → ¬ LinkedIn U K H A L' (S.slotRound k)) →
      NodeDecided p U K H k (some L)
  | indirectSkip {k j : ℕ} {A : BlockId} :
      k < j → EligibleAt (S := S) 2 k j → NodeDecided p U K H j (some A) →
      (∀ m, k < m → m < j → EligibleAt (S := S) 2 k m → NodeDecided p U K H m none) →
      FetchedIn U K H A (S.slotRound k + 2) →
      (∀ L, IsLeaderBlock U k L → ¬ LinkedIn U K H A L (S.slotRound k)) →
      NodeDecided p U K H k none

end KPartialSparse

end LeanDag
