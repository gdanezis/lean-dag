import LeanDag.KPartialSparse.Model.Reactive
import LeanDag.KPartialSparse.Model.Order
/-!
# Sparse K-partial DAG — nodes in time, statement

`docs/kpartial-sparse.md` §7, Theorem 5: nodes that wait for a quorum, the
leaders and the votes behind their claims, with a timeout `τ` and a grace
period `γ`, under message delay `δ` from time `G` and any crashes and restarts
before it, reach every round, catch up within `δ`, build each round within
`δ + τ`, and within `δ + γ` when led by `T`, produce a synchronous run, and
commit a slot led by `T` within `3δ + 2γ`; a run starts after `G + τ` and
resumes after crashes, and the available sub-DAG survives them on disk;
commits resume once crashed nodes recover and stay up; and
nodes that wait for referenceable blocks meet the claim disciplines, while
the wait never blocks a correct block or a claim of `T`.

Statements only; the proofs are `Proof.lean`.
-/

namespace LeanDag

namespace KPartialSparse

namespace Reactive

open KPartialDag (Crashes Timeline LiveRow)
open scoped KPartialDag
open Scheme

/-- **Every round is reached**: on a timed run from round `R` to round `N`,
every validator of `T` has a block at every round from `R` to `N`, or above
it. -/
def Built : Prop :=
  ∀ (Validator BlockId Payload : Type) [Fintype Validator] [DecidableEq Validator]
    [Faults Validator] [Crashes Validator] [Leaders Validator] [LinearOrder BlockId]
    [ClaimFormat BlockId Payload] [Slots Validator] (U : SRecord Validator BlockId Payload)
    (tl : Timeline Validator BlockId) (T : Finset Validator) (G δ τ γ R N : ℕ),
    TimedRun U tl T G δ τ γ R N → ∀ s, R ≤ s → s ≤ N → ∃ t, ReachedBy U tl T s t

/-- **A quorum brings every node of `T` to its round within `δ`**: under the
rules for nodes, once a node of `T` holds at a time `t ≥ G` blocks of a quorum
at round `s`, from `R + 1` to `N`, every validator of `T` has reached round
`s` by `t + δ`. -/
def CatchesUp : Prop :=
  ∀ (Validator BlockId Payload : Type) [Fintype Validator] [DecidableEq Validator]
    [Faults Validator] [Crashes Validator] [Leaders Validator] [LinearOrder BlockId]
    [ClaimFormat BlockId Payload] [Slots Validator] (U : SRecord Validator BlockId Payload)
    (tl : Timeline Validator BlockId) (T : Finset Validator) (G δ τ γ R N : ℕ),
    TimedRules U tl T G δ τ γ R N → ∀ s t (u : Validator), R < s → s ≤ N → G ≤ t → u ∈ T →
      QuorumIn U (tl.held u t) s → ReachedBy U tl T s (t + δ)

/-- **Each round within `δ + τ`**: on a timed run, at `δ < γ ≤ τ`, once every
validator of `T` has reached round `s`, from `R` to below `N`, by `t`, every
validator of `T` has built at round `s + 1` by `t + δ + τ`. -/
def Slow : Prop :=
  ∀ (Validator BlockId Payload : Type) [Fintype Validator] [DecidableEq Validator]
    [Faults Validator] [Crashes Validator] [Leaders Validator] [LinearOrder BlockId]
    [ClaimFormat BlockId Payload] [Slots Validator] (U : SRecord Validator BlockId Payload)
    (tl : Timeline Validator BlockId) (T : Finset Validator) (G δ τ γ R N : ℕ),
    TimedRun U tl T G δ τ γ R N → δ < γ → γ ≤ τ → ∀ s t, R ≤ s → s < N →
      ReachedBy U tl T s t → BuiltBy U tl T (s + 1) (t + δ + τ)

/-- **Rounds led by `T` within `δ + γ`**: on a timed run, at `τ ≥ 2δ` and
`δ < γ ≤ τ`, when the slots at round `s`, from `R + 2` to below `N`, and one
round below have leaders of `T`, once every validator of `T` has built at
round `s` by `t`, every validator of `T` has built at round `s + 1` by
`t + δ + γ`. -/
def Fast : Prop :=
  ∀ (Validator BlockId Payload : Type) [Fintype Validator] [DecidableEq Validator]
    [Faults Validator] [Crashes Validator] [Leaders Validator] [LinearOrder BlockId]
    [ClaimFormat BlockId Payload] [S : Slots Validator] (U : SRecord Validator BlockId Payload)
    (tl : Timeline Validator BlockId) (T : Finset Validator) (G δ τ γ R N : ℕ),
    TimedRun U tl T G δ τ γ R N → 2 * δ ≤ τ → δ < γ → γ ≤ τ → ∀ s t, R + 2 ≤ s → s < N →
      (∀ k, S.slotRound k = s ∨ S.slotRound k + 1 = s → S.leader k ∈ T) →
      BuiltBy U tl T s t → BuiltBy U tl T (s + 1) (t + δ + γ)

/-- **The run is synchronous**: at `τ ≥ 2δ` and `δ < γ ≤ τ`, a timed run from
round `R` to round `N` is synchronous among `T` from round `R + 1` to `N`, so
responsive at every row (Theorem 4, *Weaker*). -/
def Synchronised : Prop :=
  ∀ (Validator BlockId Payload : Type) [Fintype Validator] [DecidableEq Validator]
    [Faults Validator] [Crashes Validator] [Leaders Validator] [LinearOrder BlockId]
    [ClaimFormat BlockId Payload] [Slots Validator] (U : SRecord Validator BlockId Payload)
    (tl : Timeline Validator BlockId) (T : Finset Validator) (G δ τ γ R N : ℕ),
    TimedRun U tl T G δ τ γ R N → 2 * δ ≤ τ → δ < γ → γ ≤ τ → SyncFrom U T (R + 1) N

/-- **A slot led by `T` commits within `3δ + 2γ`**: at a live row, `τ ≥ 2δ` and
`δ < γ ≤ τ`, when every slot from one round below a slot at round `r`, from
`R + 2` to `N − 2`, to one round above it has a leader in `T`, and every
validator of `T` has built at round `r` by `t`, every node of `T` commits the
slot directly on what it holds at `t + 3δ + 2γ`. -/
def Commits : Prop :=
  ∀ (Validator BlockId Payload : Type) [Fintype Validator] [DecidableEq Validator]
    [Faults Validator] [Crashes Validator] [Leaders Validator] [LinearOrder BlockId]
    [ClaimFormat BlockId Payload] [S : Slots Validator] (p : Params)
    (U : SRecord Validator BlockId Payload) (tl : Timeline Validator BlockId)
    (T : Finset Validator) (G δ τ γ R K N : ℕ), LiveRow Validator p →
    TimedRun U tl T G δ τ γ R N → 2 * δ ≤ τ → δ < γ → γ ≤ τ → ∀ k t,
      R + 2 ≤ S.slotRound k → S.slotRound k + 2 ≤ N →
      (∀ j, S.slotRound k ≤ S.slotRound j + 1 → S.slotRound j ≤ S.slotRound k + 1 →
        S.leader j ∈ T) →
      BuiltBy U tl T (S.slotRound k) t → ∀ v ∈ T,
        ∃ L, IsLeaderBlock U k L ∧ NodeDecided p U K (tl.held v (t + 3 * δ + 2 * γ)) k (some L)

/-- **A timed run starts**: under the rules for nodes started at round `R`,
there is a round `R' ≥ R`, either `R` or one above a round that a block of
`T` reached before `G + τ`, such that, if `R' ≤ N`, the timeline is a timed
run from `R'` to `N`, and every validator of `T` has reached `R'` within
`2δ + 2τ` of `G + τ` and of the time all reached `R`. -/
def Starts : Prop :=
  ∀ (Validator BlockId Payload : Type) [Fintype Validator] [DecidableEq Validator]
    [Faults Validator] [Crashes Validator] [Leaders Validator] [LinearOrder BlockId]
    [ClaimFormat BlockId Payload] [Slots Validator] (U : SRecord Validator BlockId Payload)
    (tl : Timeline Validator BlockId) (T : Finset Validator) (G δ τ γ R N : ℕ),
    TimedStarted U tl T G δ τ γ R N → ∃ R', R ≤ R' ∧
      (R' = R ∨ ∃ x ∈ U.ids, (U.block x).creator ∈ T ∧
        (U.block x).round + 1 = R' ∧ tl.built x < G + τ) ∧
      (R' ≤ N → TimedRun U tl T G δ τ γ R' N ∧
        ∀ t₀, ReachedBy U tl T R t₀ → ReachedBy U tl T R' (max t₀ (G + τ) + 2 * δ + 2 * τ))

/-- **Operations resume**: under the rules for nodes from round `R` to round
`N`, with any crashes and restarts before `G`, once a validator of `T` has
built above round `R` by `G`, there is a round `R' > R` such that, if
`R' ≤ N`, the timeline is a timed run from `R'` to `N`, and every validator of
`T` has reached `R'` by `G + 3δ + 3τ`. -/
def Resumes : Prop :=
  ∀ (Validator BlockId Payload : Type) [Fintype Validator] [DecidableEq Validator]
    [Faults Validator] [Crashes Validator] [Leaders Validator] [LinearOrder BlockId]
    [ClaimFormat BlockId Payload] [Slots Validator] (U : SRecord Validator BlockId Payload)
    (tl : Timeline Validator BlockId) (T : Finset Validator) (G δ τ γ R N : ℕ),
    TimedRules U tl T G δ τ γ R N → ∀ b ∈ U.ids, (U.block b).creator ∈ T → tl.built b ≤ G →
      R < (U.block b).round → ∃ R', R < R' ∧
        (R' ≤ N → TimedRun U tl T G δ τ γ R' N ∧ ReachedBy U tl T R' (G + 3 * δ + 3 * τ))

/-- **Nothing the sub-DAG holds is lost**: when correct nodes keep on disk the
windows to depth `K` of their blocks' references, every block of the
available sub-DAG below a block with votes from `f + c + 1` distinct authors
is on the disk of a node of any quorum `T` of correct nodes from some time
on, through any crash. -/
def Durable : Prop :=
  ∀ (Validator BlockId Payload : Type) [Fintype Validator] [DecidableEq Validator]
    [F : Faults Validator] [Cr : Crashes Validator] [Leaders Validator] [LinearOrder BlockId]
    (U : SRecord Validator BlockId Payload) (tl : Timeline Validator BlockId)
    (T : Finset Validator) (K : ℕ), T ⊆ (Correct : Finset Validator) →
    kQuorum Validator ≤ T.card → KeepsHistory U tl K → ∀ A ∈ U.ids,
      F.f + Cr.c + 1 ≤ (supporters U A ((U.block A).round + 1)).card →
      ∀ z ∈ Avail U K A, ∃ w ∈ T, ∃ t₀, ∀ t, t₀ ≤ t → z ∈ tl.disk w t

/-- **Timed nodes meet the claim disciplines**: correct nodes that reference only
referenceable blocks and claim only what they back, on what they hold, check
claims to depth `K` and claim truthfully on the record. -/
def Checked : Prop :=
  ∀ (Validator BlockId Payload : Type) [Fintype Validator] [DecidableEq Validator]
    [Faults Validator] [Crashes Validator] [Leaders Validator] [LinearOrder BlockId]
    [ClaimFormat BlockId Payload] (U : SRecord Validator BlockId Payload)
    (tl : Timeline Validator BlockId) (K t : ℕ), (∀ v s, tl.held v s ⊆ U.ids) →
    TimedChecks U tl K t → Checks U K t ∧ Truthful U t

/-- **The wait never blocks a correct block**: when delivery carries what a
block's author held, a correct node holding a correct block holds it
referenceable. -/
def Unblocked : Prop :=
  ∀ (Validator BlockId Payload : Type) [Fintype Validator] [DecidableEq Validator]
    [Faults Validator] [Crashes Validator] [Leaders Validator] [LinearOrder BlockId]
    [ClaimFormat BlockId Payload] (U : SRecord Validator BlockId Payload)
    (tl : Timeline Validator BlockId) (K t : ℕ) (v : Validator) (s : ℕ) (b : BlockId),
    (∀ v s, tl.held v s ⊆ U.ids) → TimedChecks U tl K t → v ∈ (Correct : Finset Validator) → b ∈ tl.held v s →
    (U.block b).creator ∈ (Correct : Finset Validator) → Referenceable U K t (tl.held v s) b

/-- **Every claimer of `T` backs its claim**: on a timed run, at `τ ≥ 2δ`,
`δ < γ ≤ τ` and a threshold within the quorum, a block of `T` two rounds above
a slot led by `T`, from round `R + 1` on, is built once its author backs a
claim for the slot's leader block. -/
def Claimable : Prop :=
  ∀ (Validator BlockId Payload : Type) [Fintype Validator] [DecidableEq Validator]
    [Faults Validator] [Crashes Validator] [Leaders Validator] [LinearOrder BlockId]
    [ClaimFormat BlockId Payload] [S : Slots Validator] (U : SRecord Validator BlockId Payload)
    (tl : Timeline Validator BlockId) (T : Finset Validator) (G δ τ γ R N k t : ℕ)
    (c L : BlockId), TimedRun U tl T G δ τ γ R N → 2 * δ ≤ τ → δ < γ → γ ≤ τ →
    t ≤ kQuorum Validator → R + 1 ≤ S.slotRound k → S.slotRound k + 2 ≤ N → S.leader k ∈ T →
    c ∈ U.ids → (U.block c).creator ∈ T → (U.block c).round = S.slotRound k + 2 →
    IsLeaderBlock U k L → Backs U t (tl.held (U.block c).creator (tl.built c)) L

/-- **Timed nodes keep chains**: under the rules for nodes, correct authors that
build above their disk keep chains. -/
def Chained : Prop :=
  ∀ (Validator BlockId Payload : Type) [Fintype Validator] [DecidableEq Validator]
    [Faults Validator] [Crashes Validator] [Leaders Validator] [LinearOrder BlockId]
    [ClaimFormat BlockId Payload] [Slots Validator] (U : SRecord Validator BlockId Payload)
    (tl : Timeline Validator BlockId) (T : Finset Validator) (G δ τ γ R N : ℕ),
    TimedRules U tl T G δ τ γ R N → KPartialDag.BuildsAboveDisk U.ids U.block tl → Chains U

/-- **A valid block can always be built**: from the correct blocks one round
below of a quorum of distinct authors, a dense block; from a correct node's
own block one round below and a correct leader's block there, a sparse one,
when the node does not lead the round above; and on a timed run, at
`2δ ≤ γ ≤ τ` and `δ < γ`, a node of `T` building above round `r`, from `R + 1`
to `N`, holds the blocks of a valid one. -/
def Buildable : Prop :=
  ∀ (Validator BlockId Payload : Type) [Fintype Validator] [DecidableEq Validator]
    [Faults Validator] [Crashes Validator] [Ld : Leaders Validator] [LinearOrder BlockId]
    [ClaimFormat BlockId Payload] [Slots Validator] (U : SRecord Validator BlockId Payload)
    (H : Finset BlockId) (r : ℕ) (v : Validator) (pay : Payload),
    (H ⊆ U.ids → kQuorum Validator ≤ (creatorsOf U.block (H.filter fun x =>
        (U.block x).creator ∈ (Correct : Finset Validator) ∧ (U.block x).round = r)).card →
      ∃ b : Block Validator BlockId Payload, b.creator = v ∧ b.round = r + 1 ∧ b.refs ⊆ H ∧
        SValid Validator BlockId Payload U.block b) ∧
    (H ⊆ U.ids → v ∈ (Correct : Finset Validator) → v ∉ Ld.leaders (r + 1) →
      (∃ o ∈ H, (U.block o).creator = v ∧ (U.block o).round = r) →
      (∃ L ∈ H, (U.block L).creator ∈ (Correct : Finset Validator) ∧
        (U.block L).creator ∈ Ld.leaders r ∧ (U.block L).round = r) →
      ∃ b : Block Validator BlockId Payload, b.creator = v ∧ b.round = r + 1 ∧ b.refs ⊆ H ∧
        SValid Validator BlockId Payload U.block b) ∧
    ∀ (tl : Timeline Validator BlockId) (T : Finset Validator) (G δ τ γ R N : ℕ) (c : BlockId),
      TimedRun U tl T G δ τ γ R N → 2 * δ ≤ γ → δ < γ → γ ≤ τ → R + 1 ≤ r → r ≤ N →
      c ∈ U.ids → (U.block c).creator ∈ T → (U.block c).round = r + 1 →
      ∃ b : Block Validator BlockId Payload, b.creator = (U.block c).creator ∧ b.round = r + 1 ∧
        b.refs ⊆ tl.held (U.block c).creator (tl.built c) ∧
        SValid Validator BlockId Payload U.block b

/-- **Leaders of `T` cover `T`**: on a timed run, at `2δ ≤ γ ≤ τ` and `δ < γ`,
when each slot's leader leads its round on the substrate, a leader block of a
slot led by `T`, from round `R + 1` on, references every block of `T` one round
below. -/
def Covered : Prop :=
  ∀ (Validator BlockId Payload : Type) [Fintype Validator] [DecidableEq Validator]
    [Faults Validator] [Crashes Validator] [Ld : Leaders Validator] [LinearOrder BlockId]
    [ClaimFormat BlockId Payload] [S : Slots Validator] (U : SRecord Validator BlockId Payload)
    (tl : Timeline Validator BlockId) (T : Finset Validator) (G δ τ γ R N : ℕ),
    TimedRun U tl T G δ τ γ R N → 2 * δ ≤ γ → δ < γ → γ ≤ τ →
    (∀ k, S.leader k ∈ Ld.leaders (S.slotRound k)) → CoversFrom U T (R + 1) N

/-- **The ledger grows**: at a live row, on a disciplined record and a timed run,
at `τ ≥ 2δ` and `δ < γ ≤ τ`, when nodes of `T` fetch the available sub-DAG of
the leader blocks they hold within `Δ`, a two-round row links by `f + c + 1`
votes or more, and the schedule offers runs of `c` leaders of `T` spanning
eligibility, past any slot `k` there is a slot `b` such that, if the run
reaches the round of its last certificates, every node of `T`, at one time,
decides every slot below `b + c` and has fetched each leader it commits down
to `D` rounds below it. -/
def Ledger : Prop :=
  ∀ (Validator BlockId Payload : Type) [Fintype Validator] [DecidableEq Validator]
    [F : Faults Validator] [Cr : Crashes Validator] [Leaders Validator] [LinearOrder BlockId]
    [ClaimFormat BlockId Payload] [S : Slots Validator] (p : Params)
    (U : SRecord Validator BlockId Payload) (tl : Timeline Validator BlockId)
    (T : Finset Validator) (G δ τ γ R N K D Δ c : ℕ), Row Validator p →
    (p.voteIsCert = true → F.f + Cr.c + 1 ≤ p.linkSize) → Disciplined K p.certThreshold S U →
    LiveRow Validator p → TimedRun U tl T G δ τ γ R N → 2 * δ ≤ τ → δ < γ → γ ≤ τ →
    Fetches U tl T K G Δ → 0 < c →
    (∀ b i, i < b → EligibleAt (S := S) (p.waveLength - 1) i (b + c - 1)) → FairRunOn T c →
    ∀ k, ∃ b, k ≤ b ∧ (certRound p (S.slotRound (b + c - 1)) ≤ N → ∃ t, ∀ v ∈ T,
      ∃ g : ℕ → Option BlockId, ∀ i, i < b + c → NodeDecided p U K (tl.held v t) i (g i) ∧
        ∀ L, g i = some L → FetchedIn U K (tl.held v t) L ((U.block L).round - D))

/-- **Commits resume after a recovery**: at a live row, `τ ≥ 2δ` and
`δ < γ ≤ τ`, on a disciplined record, with the nodes of `T` up from `G` on, any
time after message delay is bounded, after any crashes and restarts before
it, when nodes of `T` fetch, a two-round row links by `f + c + 1` votes or
more, the schedule offers runs of `c` leaders of `T` spanning eligibility, and
a validator of `T` has built above round `R` by `G`: past any slot `k` there
is a slot `b` such that, if the record reaches the round of its last
certificates, every node of `T`, at one time, decides every slot below
`b + c` and has fetched each leader it commits down to `D` rounds below it. -/
def Recovers : Prop :=
  ∀ (Validator BlockId Payload : Type) [Fintype Validator] [DecidableEq Validator]
    [F : Faults Validator] [Cr : Crashes Validator] [Leaders Validator] [LinearOrder BlockId]
    [ClaimFormat BlockId Payload] [S : Slots Validator] (p : Params)
    (U : SRecord Validator BlockId Payload) (tl : Timeline Validator BlockId)
    (T : Finset Validator) (G δ τ γ R N K D Δ c : ℕ), Row Validator p →
    (p.voteIsCert = true → F.f + Cr.c + 1 ≤ p.linkSize) → Disciplined K p.certThreshold S U →
    LiveRow Validator p → TimedRules U tl T G δ τ γ R N → 2 * δ ≤ τ → δ < γ → γ ≤ τ →
    Fetches U tl T K G Δ → 0 < c →
    (∀ b i, i < b → EligibleAt (S := S) (p.waveLength - 1) i (b + c - 1)) → FairRunOn T c →
    ∀ b₀ ∈ U.ids, (U.block b₀).creator ∈ T → tl.built b₀ ≤ G → R < (U.block b₀).round →
    ∀ k, ∃ b, k ≤ b ∧ (certRound p (S.slotRound (b + c - 1)) ≤ N → ∃ t, ∀ v ∈ T,
      ∃ g : ℕ → Option BlockId, ∀ i, i < b + c → NodeDecided p U K (tl.held v t) i (g i) ∧
        ∀ L, g i = some L → FetchedIn U K (tl.held v t) L ((U.block L).round - D))

/-- Nodes in time. -/
def Statement : Prop :=
  Built ∧ CatchesUp ∧ Slow ∧ Fast ∧ Synchronised ∧ Commits ∧ Starts ∧ Resumes ∧ Durable ∧
    Checked ∧ Unblocked ∧ Claimable ∧ Chained ∧ Buildable ∧ Covered ∧ Ledger ∧ Recovers

end Reactive

end KPartialSparse

end LeanDag
