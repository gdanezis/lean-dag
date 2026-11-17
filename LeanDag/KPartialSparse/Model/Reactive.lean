import LeanDag.KPartialSparse.Model.Live
import LeanDag.KPartialDag.Model.Reactive
/-!
# Sparse K-partial DAG — nodes in time

`docs/kpartial-sparse.md` §7. What a node waits for (`WaitsFor`), being behind
(`BehindIn`), progress over a timeline (`BuiltBy`, `ReachedBy`), the rules
for nodes up from `G`, through crashes and restarts before it (`TimedRules`),
started at a round (`TimedStarted`), and a run after `G + τ` (`TimedRun`),
claims checked by timed nodes (`TimedChecks`), fetching the available sub-DAG
(`Fetches`), and windows kept on disk (`KeepsHistory`). Timelines are those of
`docs/kpartial.md` §11 (`KPartialDag.Timeline`).
-/

namespace LeanDag

namespace KPartialSparse

open KPartialDag (Crashes Timeline)
open scoped KPartialDag

variable {Validator : Type*} [Fintype Validator] [DecidableEq Validator] [F : Faults Validator]
variable [Cr : Crashes Validator] [Ld : Leaders Validator]
variable {BlockId : Type*} [LinearOrder BlockId] {Payload : Type*} [ClaimFormat BlockId Payload]
variable [S : Slots Validator]

omit [ClaimFormat BlockId Payload] S in
/-- **A quorum at round `r` in `H`**: blocks of `H` at round `r` by a quorum of
distinct authors. -/
def QuorumIn (U : SRecord Validator BlockId Payload) (H : Finset BlockId) (r : ℕ) : Prop :=
  kQuorum Validator ≤ (creatorsOf U.block (H.filter fun b => (U.block b).round = r)).card

omit [ClaimFormat BlockId Payload] S in
/-- **Votes for `L` in `H`**: blocks of `H` at round `r` by a quorum of distinct
authors reference `L`. -/
def CertIn (U : SRecord Validator BlockId Payload) (H : Finset BlockId) (r : ℕ) (L : BlockId) :
    Prop :=
  kQuorum Validator ≤
    (creatorsOf U.block (H.filter fun b => (U.block b).round = r ∧ L ∈ (U.block b).refs)).card

omit [ClaimFormat BlockId Payload] in
/-- **What a node waits for before building above round `r`**: a quorum at
round `r`, a leader block of every slot at round `r`, and votes from a quorum
for a leader block of every slot at round `r − 1`. -/
def WaitsFor (U : SRecord Validator BlockId Payload) (H : Finset BlockId) (r : ℕ) : Prop :=
  QuorumIn U H r ∧ (∀ k, S.slotRound k = r → ∃ L ∈ H, IsLeaderBlock U k L) ∧
    ∀ k, S.slotRound k + 1 = r → ∃ L, IsLeaderBlock U k L ∧ CertIn U H r L

omit [ClaimFormat BlockId Payload] S in
/-- **Behind round `r + 1` in `H`, for `v`**: blocks of `H` at round `r + 1`
by `f + c + 1` distinct authors other than `v`. -/
def BehindIn (U : SRecord Validator BlockId Payload) (H : Finset BlockId) (v : Validator)
    (r : ℕ) : Prop :=
  F.f + Cr.c + 1 ≤ ((creatorsOf U.block (H.filter fun b => (U.block b).round = r + 1)).erase v).card

omit [ClaimFormat BlockId Payload] S in
/-- **Every validator of `T` has a block at round `s` built by time `t`.** -/
def BuiltBy (U : SRecord Validator BlockId Payload) (tl : Timeline Validator BlockId)
    (T : Finset Validator) (s t : ℕ) : Prop :=
  ∀ v ∈ T, ∃ b ∈ U.ids, (U.block b).creator = v ∧ (U.block b).round = s ∧ tl.built b ≤ t

omit [ClaimFormat BlockId Payload] S in
/-- **Every validator of `T` has a block at round `s` or above built by time
`t`.** -/
def ReachedBy (U : SRecord Validator BlockId Payload) (tl : Timeline Validator BlockId)
    (T : Finset Validator) (s t : ℕ) : Prop :=
  ∀ v ∈ T, ∃ b ∈ U.ids, (U.block b).creator = v ∧ s ≤ (U.block b).round ∧ tl.built b ≤ t

/-- **The rules for nodes from round `R` to round `N`**, with the nodes of `T`
correct and up from `G` on, message delay `δ` from `G`, timeout `τ` and grace
period `γ`. -/
structure TimedRules (U : SRecord Validator BlockId Payload) (tl : Timeline Validator BlockId)
    (T : Finset Validator) (G δ τ γ R N : ℕ) : Prop where
  /-- The nodes up from `G` on are correct. -/
  stable : T ⊆ (Correct : Finset Validator)
  /-- They are a quorum. -/
  large : kQuorum Validator ≤ T.card
  /-- Nodes hold blocks of the record. -/
  held_ids : ∀ v t, tl.held v t ⊆ U.ids
  /-- From `G` on, a node of `T` keeps what it holds. -/
  mono : ∀ v ∈ T, ∀ t t', G ≤ t → t ≤ t' → tl.held v t ⊆ tl.held v t'
  /-- From `G` on, a correct block held by a node of `T` is held by every node
  of `T` `δ` later. -/
  delivers : ∀ v ∈ T, ∀ t, G ≤ t → ∀ b ∈ tl.held v t,
    (U.block b).creator ∈ (Correct : Finset Validator) → ∀ w ∈ T, b ∈ tl.held w (t + δ)
  /-- A correct node holds the references of the correct blocks it holds. -/
  closed : ∀ v ∈ (Correct : Finset Validator), ∀ t, ∀ b ∈ tl.held v t,
    (U.block b).creator ∈ (Correct : Finset Validator) → (U.block b).refs ⊆ tl.held v t
  /-- **Grounded**: a correct node holding a correct block above round `R`
  holds a quorum at the round below it, as its author did when it built it. -/
  grounded : ∀ v ∈ (Correct : Finset Validator), ∀ t, ∀ b ∈ tl.held v t,
    (U.block b).creator ∈ (Correct : Finset Validator) → R < (U.block b).round →
    QuorumIn U (tl.held v t) ((U.block b).round - 1)
  /-- **Backed**: a correct node holding a correct block holds the votes behind
  each of its claims. -/
  backed : ∀ v ∈ (Correct : Finset Validator), ∀ t, ∀ b ∈ tl.held v t,
    (U.block b).creator ∈ (Correct : Finset Validator) → ∀ L ∈ claimsOf U b,
    CertIn U (tl.held v t) ((U.block L).round + 1) L
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
  /-- A correct node keeps on disk every block it has built. -/
  stores : ∀ b ∈ U.ids, (U.block b).creator ∈ (Correct : Finset Validator) → ∀ t,
    tl.built b ≤ t → b ∈ tl.disk (U.block b).creator t
  /-- **The wait**: a correct block above round `r ≥ R` is built once its
  author has held what it waits for for `γ` and still holds it, has held a
  quorum of round `r` for `τ`, or is behind round `r + 1`. -/
  waits : ∀ b ∈ U.ids, (U.block b).creator ∈ (Correct : Finset Validator) → ∀ r,
    (U.block b).round = r + 1 → R ≤ r →
    (γ ≤ tl.built b ∧ WaitsFor U (tl.held (U.block b).creator (tl.built b - γ)) r ∧
        WaitsFor U (tl.held (U.block b).creator (tl.built b)) r) ∨
      (τ ≤ tl.built b ∧ QuorumIn U (tl.held (U.block b).creator (tl.built b - τ)) r) ∨
      BehindIn U (tl.held (U.block b).creator (tl.built b)) (U.block b).creator r
  /-- **No later than the wait**: a node of `T` that has held what it waits for
  above round `r`, from `R` to below `N`, for `γ`, or a quorum of round `r` for
  `τ`, since `G`, or is behind round `r + 1` from `G` on, has built above
  `r`. -/
  prompt : ∀ v ∈ T, ∀ r t, R ≤ r → r < N →
    (G + γ ≤ t ∧ WaitsFor U (tl.held v (t - γ)) r) ∨
      (G + τ ≤ t ∧ QuorumIn U (tl.held v (t - τ)) r) ∨ (G ≤ t ∧ BehindIn U (tl.held v t) v r) →
    ∃ b ∈ U.ids, (U.block b).creator = v ∧ r + 1 ≤ (U.block b).round ∧ tl.built b ≤ t
  /-- **Votes**: a correct block references a leader block of each slot one
  round below, led by a correct validator, whose leader block its author
  holds. -/
  votes : ∀ b ∈ U.ids, (U.block b).creator ∈ (Correct : Finset Validator) → ∀ k,
    S.leader k ∈ (Correct : Finset Validator) → S.slotRound k + 1 = (U.block b).round →
    (∃ L ∈ tl.held (U.block b).creator (tl.built b), IsLeaderBlock U k L) →
    ∃ L ∈ (U.block b).refs, IsLeaderBlock U k L
  /-- **Leaders cover**: a correct leader's block references every correct block
  one round below that its author holds. -/
  covers : ∀ b ∈ U.ids, (U.block b).creator ∈ (Correct : Finset Validator) →
    (U.block b).creator ∈ Ld.leaders (U.block b).round →
    ∀ x ∈ tl.held (U.block b).creator (tl.built b),
      (U.block x).creator ∈ (Correct : Finset Validator) → (U.block x).round + 1 = (U.block b).round →
        x ∈ (U.block b).refs
  /-- **Chains**: a correct block references a block of its own author at or above
  each block its author built before it. -/
  self_ref : ∀ b ∈ U.ids, (U.block b).creator ∈ (Correct : Finset Validator) → ∀ x ∈ U.ids,
    (U.block x).creator = (U.block b).creator → tl.built x < tl.built b →
    ∃ s ∈ (U.block b).refs, (U.block s).creator = (U.block b).creator ∧
      (U.block x).round ≤ (U.block s).round
  /-- **Claims**: a correct block claims each leader block two rounds below for
  which its author holds votes from a quorum. -/
  claims : ∀ b ∈ U.ids, (U.block b).creator ∈ (Correct : Finset Validator) → ∀ k,
    S.slotRound k + 2 = (U.block b).round → ∀ L, IsLeaderBlock U k L →
    CertIn U (tl.held (U.block b).creator (tl.built b)) (S.slotRound k + 1) L → L ∈ claimsOf U b

/-- **The rules for nodes, started at round `R`**: every validator of `T` has a
block at round `R` or above. -/
structure TimedStarted (U : SRecord Validator BlockId Payload) (tl : Timeline Validator BlockId)
    (T : Finset Validator) (G δ τ γ R N : ℕ) : Prop extends TimedRules U tl T G δ τ γ R N where
  /-- Every validator of `T` has a block at round `R` or above. -/
  start : ∃ t, ReachedBy U tl T R t

/-- **A timed run from round `R` to round `N`**: the rules for nodes, started
at round `R`, with the blocks of `T` from round `R` on built at `G + τ` or
later. -/
structure TimedRun (U : SRecord Validator BlockId Payload) (tl : Timeline Validator BlockId)
    (T : Finset Validator) (G δ τ γ R N : ℕ) : Prop extends TimedStarted U tl T G δ τ γ R N where
  /-- Blocks of `T` from round `R` on are built at `G + τ` or later. -/
  late : ∀ b ∈ U.ids, (U.block b).creator ∈ T → R ≤ (U.block b).round → G + τ ≤ tl.built b

omit S in
/-- **Timed nodes check claims**: a correct node references a block only once it
is referenceable on what the node holds, and claims only what it backs; and a
node holding a correct block holds the evidence its author held: the window
to depth `K` of each reference, with the votes behind every claim there and
behind the block's own claims. -/
structure TimedChecks (U : SRecord Validator BlockId Payload) (tl : Timeline Validator BlockId)
    (K t : ℕ) : Prop where
  /-- A correct block references only blocks referenceable for its author. -/
  refs_checked : ∀ b ∈ U.ids, (U.block b).creator ∈ (Correct : Finset Validator) →
    ∀ m ∈ (U.block b).refs, Referenceable U K t (tl.held (U.block b).creator (tl.built b)) m
  /-- A correct block claims only what its author backs. -/
  claims_backed : ∀ b ∈ U.ids, (U.block b).creator ∈ (Correct : Finset Validator) →
    ∀ L ∈ claimsOf U b, Backs U t (tl.held (U.block b).creator (tl.built b)) L
  /-- A correct node holding a correct block holds its references as
  referenceable. -/
  carries : ∀ v ∈ (Correct : Finset Validator), ∀ s, ∀ b ∈ tl.held v s,
    (U.block b).creator ∈ (Correct : Finset Validator) → ∀ m ∈ (U.block b).refs,
      Referenceable U K t (tl.held v s) m
  /-- A correct node holding a correct block backs its claims. -/
  carries_claims : ∀ v ∈ (Correct : Finset Validator), ∀ s, ∀ b ∈ tl.held v s,
    (U.block b).creator ∈ (Correct : Finset Validator) → ∀ L ∈ claimsOf U b,
      Backs U t (tl.held v s) L

omit [ClaimFormat BlockId Payload] in
/-- **Fetching the available sub-DAG**: from `G` on, a node of `T` that holds a
leader block holds the block's available sub-DAG `Δ` later. -/
def Fetches (U : SRecord Validator BlockId Payload) (tl : Timeline Validator BlockId)
    (T : Finset Validator) (K G Δ : ℕ) : Prop :=
  ∀ v ∈ T, ∀ t, G ≤ t → ∀ j A, IsLeaderBlock U j A → A ∈ tl.held v t →
    ∀ z ∈ Avail U K A, z ∈ tl.held v (t + Δ)

omit [ClaimFormat BlockId Payload] S in
/-- **Keeping windows on disk**: a correct node keeps on disk, from the time it
builds a block on, the window to depth `K` of each of the block's
references. -/
def KeepsHistory (U : SRecord Validator BlockId Payload) (tl : Timeline Validator BlockId)
    (K : ℕ) : Prop :=
  ∀ b ∈ U.ids, (U.block b).creator ∈ (Correct : Finset Validator) → ∀ t, tl.built b ≤ t →
    ∀ y ∈ (U.block b).refs, window U K y ⊆ tl.disk (U.block b).creator t

end KPartialSparse

end LeanDag
