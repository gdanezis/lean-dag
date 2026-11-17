import LeanDag.KPartialSparse.Model.Rule
/-!
# Sparse K-partial DAG — what a node reads

`docs/kpartial-sparse.md` §5. The available sub-DAG and the link as read on
the blocks `H` a node holds (`AnchoredIn`, `AvailIn`, `LinkedIn`), the
sub-DAG fetched into `H` down to a round (`FetchedIn`), a claim backed by
votes a node holds and a block referenceable on what it holds (`Backs`,
`Referenceable`, `BuildsChecked`), and the node's decisions at a row
(`NodeDecided`).
-/

namespace LeanDag

namespace KPartialSparse

open KPartialDag Scheme

variable {Validator : Type*} [Fintype Validator] [DecidableEq Validator] [F : Faults Validator]
variable [Cr : Crashes Validator] [Ld : Leaders Validator]
variable {BlockId : Type*} [LinearOrder BlockId] {Payload : Type*}

/-- **The anchor points below `A`, read on `H`**: those whose window to the
depth they bring the node holds, anchored as in `Anchored` from blocks read
on `H`. -/
inductive AnchoredIn (U : SRecord Validator BlockId Payload) (K : ℕ) (H : Finset BlockId)
    (A : BlockId) : BlockId → ℕ → Prop
  | anchor : window U K A ⊆ H → AnchoredIn U K H A A K
  | reached {x : BlockId} (i : ℕ) (S : Finset BlockId) (m : BlockId → BlockId)
      (y : BlockId → BlockId) (d : BlockId → ℕ) (y' : BlockId → BlockId) (d' : BlockId → ℕ)
      (hy : ∀ z ∈ S, AnchoredIn U K H A (y z) (d z))
      (hz : ∀ z ∈ S, z ∈ window U (d z) (y z))
      (hy' : ∀ z ∈ S, 0 < i → AnchoredIn U K H A (y' z) (d' z))
      (hmz : ∀ z ∈ S, 0 < i → interior U i (m z) ⊆ window U (d' z) (y' z))
      (hi : i ≤ K) (hm : ∀ z ∈ S, m z ∈ (U.block z).refs ∧ x ∈ window U i (m z) ∧
        (U.block (m z)).round + 1 = (U.block z).round)
      (hcard : F.f + Cr.c + 1 ≤ (creatorsOf U.block S).card)
      (hx : window U (K - i) x ⊆ H) : AnchoredIn U K H A x (K - i)

/-- **The available sub-DAG below `A`, read on `H`.** -/
def AvailIn (U : SRecord Validator BlockId Payload) (K : ℕ) (H : Finset BlockId) (A : BlockId) :
    Set BlockId :=
  {z | ∃ y d, AnchoredIn U K H A y d ∧ z ∈ window U d y}

variable [ClaimFormat BlockId Payload]

/-- **The link, read on `H`**: the sub-DAG below `A` read on `H` holds
certificates for the round-`r` block `L` from `linkSize` distinct authors. -/
def LinkedIn (p : Params) (U : SRecord Validator BlockId Payload) (K : ℕ) (H : Finset BlockId)
    (A L : BlockId) (r : ℕ) : Prop :=
  ∃ X : Finset BlockId, (∀ C ∈ X, C ∈ AvailIn U K H A ∧ Certifies p U C L r) ∧
    p.linkSize ≤ (creatorsOf U.block X).card

omit [ClaimFormat BlockId Payload] in
/-- **The sub-DAG below `A` is fetched into `H` down to round `ρ`**: `H` holds
the window to depth `K` of `A`, and the window every anchor point brings
when the blocks of the sub-DAG read on `H` that reach it, through an interior
in the window an anchor point read on `H` brings, lie above `ρ`. -/
def FetchedIn (U : SRecord Validator BlockId Payload) (K : ℕ) (H : Finset BlockId) (A : BlockId)
    (ρ : ℕ) : Prop :=
  window U K A ⊆ H ∧ ∀ (i : ℕ) (S : Finset BlockId) (m : BlockId → BlockId) (x : BlockId),
    i ≤ K → (∀ z ∈ S, z ∈ AvailIn U K H A ∧ ρ < (U.block z).round ∧
      (0 < i → ∃ y d, AnchoredIn U K H A y d ∧ interior U i (m z) ⊆ window U d y) ∧
      m z ∈ (U.block z).refs ∧ x ∈ window U i (m z) ∧
        (U.block (m z)).round + 1 = (U.block z).round) →
    F.f + Cr.c + 1 ≤ (creatorsOf U.block S).card → window U (K - i) x ⊆ H

/-- **`H` backs a claim for `L`** at threshold `t`: it holds `L`, and votes for
`L` one round above it from `t` distinct authors. -/
def Backs (U : SRecord Validator BlockId Payload) (t : ℕ) (H : Finset BlockId) (L : BlockId) :
    Prop :=
  L ∈ H ∧ t ≤ (creatorsOf U.block (H.filter fun b =>
    (U.block b).round = (U.block L).round + 1 ∧ L ∈ (U.block b).refs)).card

/-- **`m` is referenceable on `H`** at threshold `t`: `H` holds the window to depth `K` of `m` and backs every claim in it. -/
abbrev Referenceable (U : SRecord Validator BlockId Payload) (K t : ℕ) (H : Finset BlockId)
    (m : BlockId) : Prop :=
  window U K m ⊆ H ∧ ∀ X ∈ window U K m, ∀ L ∈ claimsOf U X, Backs U t H L

/-- **Correct authors check what they hold**: each correct block was built by a
node holding blocks of the record that back its claims, hold the window to depth `K` of each of its references, and back every claim there. -/
def BuildsChecked (U : SRecord Validator BlockId Payload) (K t : ℕ) : Prop :=
  ∀ z ∈ U.ids, (U.block z).creator ∈ (Correct : Finset Validator) → ∃ H ⊆ U.ids,
    (∀ L ∈ claimsOf U z, Backs U t H L) ∧ ∀ m ∈ (U.block z).refs, window U K m ⊆ H ∧
      ∀ X ∈ window U K m, ∀ L ∈ claimsOf U X, Backs U t H L

/-- **The commit rule read on what a node holds**, at a row `p`. The direct
commit counts the certificates it holds, the direct skip the blamers it
holds; the indirect commit links the least linked candidate through
`LinkedIn`, and the indirect skip finds no candidate linked, both in the
sub-DAG fetched down to the round of the slot's certificates. -/
inductive NodeDecided [S : Slots Validator] (p : Params) (U : SRecord Validator BlockId Payload)
    (K : ℕ) (H : Finset BlockId) : ℕ → Option BlockId → Prop
  | directCommit {k : ℕ} {L : BlockId} : IsLeaderBlock U k L →
      p.commitThreshold ≤
        (creatorsOf U.block ((certsFor p U L (S.slotRound k)).filter (· ∈ H))).card →
      NodeDecided p U K H k (some L)
  | directSkip {k : ℕ} :
      p.skipThreshold ≤ (creatorsOf U.block ((slotBlamers U k).filter (· ∈ H))).card →
      NodeDecided p U K H k none
  | indirectCommit {k j : ℕ} {A L : BlockId} :
      k < j → EligibleAt (S := S) (p.waveLength - 1) k j → NodeDecided p U K H j (some A) →
      (∀ m, k < m → m < j → EligibleAt (S := S) (p.waveLength - 1) k m →
        NodeDecided p U K H m none) →
      FetchedIn U K H A (certRound p (S.slotRound k)) → IsLeaderBlock U k L →
      LinkedIn p U K H A L (S.slotRound k) →
      (∀ L', IsLeaderBlock U k L' → L' < L → ¬ LinkedIn p U K H A L' (S.slotRound k)) →
      NodeDecided p U K H k (some L)
  | indirectSkip {k j : ℕ} {A : BlockId} :
      k < j → EligibleAt (S := S) (p.waveLength - 1) k j → NodeDecided p U K H j (some A) →
      (∀ m, k < m → m < j → EligibleAt (S := S) (p.waveLength - 1) k m →
        NodeDecided p U K H m none) →
      FetchedIn U K H A (certRound p (S.slotRound k)) →
      (∀ L, IsLeaderBlock U k L → ¬ LinkedIn p U K H A L (S.slotRound k)) →
      NodeDecided p U K H k none

end KPartialSparse

end LeanDag
