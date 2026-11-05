import LeanDag.KPartialDag.Model.Reactive
/-!
# Reactive nodes in time — statement

`docs/kpartial.md` §11. A correct validator that keeps on disk the last
round it built, and builds only above it (`Persists`), builds at most one
block a round, whatever it loses in a restart (`Persisted`). A validator
that builds above the blocks of its own on its disk does so
(`OnDisk`).

Under the rules for nodes from round `R` to round `N`, with message delay `δ`
from time `G`, timeout `τ`, grace period `γ` and minimum wait `μ`, and any
crashes and restarts before `G` (`NodeRules`):

* **operations resume** (`Resumes`): once a correct validator has built
  above round `R` by `G`, a reactive run starts above `R`, and every correct
  validator reaches it within `3δ + 3 max τ μ` of `G`.

Under the reactive rules, with every correct validator at round `R`
(`ReactiveRules`):

* **every round is reached** (`Built`): every correct validator builds at
  every round from `R` to `N` or above it;
* **nodes behind catch up within `δ`** (`CatchesUp`): once `f + 1` correct
  validators have built at a round, from `G` on, by `t`, every correct
  validator has reached the round by `t + δ`;
* **a reactive run starts** (`Starts`): the round after the last round a
  correct node reached before `G + τ` starts a reactive run (`ReactiveRun`),
  reached within `2δ + 2 max τ μ` of `G + τ`.

On a reactive run from round `R` to round `N`, at `δ < γ ≤ τ`, where no
correct node skips a round:

* **each round is built within `δ + max τ μ`** (`Slow`) of the round below;
* **rounds led by correct validators are built within `δ + max γ μ`**
  (`Fast`): at `τ ≥ 2δ`, when the slots of a round and of the round below
  have correct leaders, no correct node waits for its timeout;
* **the run is responsive** (`Responsive`): at `τ ≥ 2δ`, the record is
  responsive among the correct validators from round `R + 1` to `N`, so
  `Live.Progress` applies;
* **a slot led by correct validators commits within `3δ + 2 max γ μ`**
  (`Commits`): at `τ ≥ 2δ`, when the slots from one round below a slot to
  one round above it have correct leaders, every correct node commits the
  slot directly within that time of the last correct block at the slot's
  round;
* **the run is synchronous** (`Synchronised`): at `2δ ≤ γ`, every correct
  block from round `R + 2` to `N` references every correct block of the
  round below, so the inclusion results of `Order` apply;
* **the ledger grows** (`Ledger`): when nodes fetch the available sub-DAG of
  the certified leaders they hold, every correct node eventually decides
  every slot up to a run of correct leaders and fetches below the leaders
  it commits, so its ledger is defined there and agrees by `Order.Agrees`.

When correct nodes keep on disk the histories to depth `K` of their blocks'
references, nothing a leader outputs is lost, through any crash
(`Durable`).

No bound depends on `K`: the downloads to depth `K` are inside `δ`.
Statements only; the proofs are `Proof.lean`.
-/

namespace LeanDag

namespace KPartialDag

namespace Reactive

/-- **Persisting the last round built avoids equivocation**: a correct
validator that persists the last round it built builds at most one block a
round. -/
def Persisted : Prop :=
  ∀ (Validator BlockId Payload : Type) [Fintype Validator] [DecidableEq Validator]
    [Faults Validator] [DecidableEq BlockId] [Slots Validator]
    (ids : Finset BlockId) (block : BlockId → Block Validator BlockId Payload)
    (order : BlockId → ℕ) (next : Validator → ℕ → ℕ),
    Persists ids block order next → ∀ i ∈ ids, ∀ j ∈ ids,
      (block i).creator ∈ (Correct : Finset Validator) → (block i).creator = (block j).creator →
      (block i).round = (block j).round → i = j

/-- **Building above the disk persists the last round built**: a correct
validator that keeps its highest block on disk, builds at most one block at
a time, and builds only above the blocks of its own on its disk persists the
last round it built, numbering its builds by time. -/
def OnDisk : Prop :=
  ∀ (Validator BlockId Payload : Type) [Fintype Validator] [DecidableEq Validator]
    [Faults Validator] [DecidableEq BlockId] [Slots Validator]
    (ids : Finset BlockId) (block : BlockId → Block Validator BlockId Payload)
    (tl : Timeline Validator BlockId),
    BuildsAboveDisk ids block tl → ∃ next, Persists ids block tl.built next

/-- **Operations resume**: under the rules for nodes from round `R` to round
`N`, with any crashes and restarts before `G`, once a correct validator has
built above round `R` by `G`, there is a round `R' > R` such that, if
`R' ≤ N`, the timeline is a reactive run from `R'` to `N`, and every correct
validator has reached `R'` by `G + 3δ + 3 max τ μ`. -/
def Resumes : Prop :=
  ∀ (Validator BlockId Payload : Type) [Fintype Validator] [DecidableEq Validator]
    [Faults Validator] [DecidableEq BlockId] [Slots Validator]
    (U : KRecord Validator BlockId Payload) (tl : Timeline Validator BlockId)
    (G δ τ γ μ R N : ℕ),
    NodeRules U tl G δ τ γ μ R N → ∀ b ∈ U.ids,
      (U.block b).creator ∈ (Correct : Finset Validator) → tl.built b ≤ G →
      R < (U.block b).round → ∃ R', R < R' ∧
        (R' ≤ N → ReactiveRun U tl G δ τ γ μ R' N ∧
          ReachedBy U tl R' (G + 3 * δ + 3 * max τ μ))

/-- **Every round is reached**: under the reactive rules from round `R` to
round `N`, every correct validator has a block at every round from `R` to
`N`, or above it. -/
def Built : Prop :=
  ∀ (Validator BlockId Payload : Type) [Fintype Validator] [DecidableEq Validator]
    [Faults Validator] [DecidableEq BlockId] [Slots Validator]
    (U : KRecord Validator BlockId Payload) (tl : Timeline Validator BlockId)
    (G δ τ γ μ R N : ℕ),
    ReactiveRules U tl G δ τ γ μ R N → ∀ s, R ≤ s → s ≤ N → ∃ t, ReachedBy U tl s t

/-- **Nodes behind catch up within `δ`**: under the reactive rules from round
`R` to round `N`, once a set `A` of `f + 1` correct validators have built at
round `s + 1`, from `R + 1` to `N`, at times from `G` to `t`, every correct
validator has reached round `s + 1` by `t + δ`. -/
def CatchesUp : Prop :=
  ∀ (Validator BlockId Payload : Type) [Fintype Validator] [DecidableEq Validator]
    [F : Faults Validator] [DecidableEq BlockId] [Slots Validator]
    (U : KRecord Validator BlockId Payload) (tl : Timeline Validator BlockId)
    (G δ τ γ μ R N : ℕ),
    ReactiveRules U tl G δ τ γ μ R N → ∀ s t (A : Finset Validator), R ≤ s → s < N →
      A ⊆ (Correct : Finset Validator) → F.f + 1 ≤ A.card →
      (∀ v ∈ A, ∃ b ∈ U.ids, (U.block b).creator = v ∧ (U.block b).round = s + 1 ∧
        G ≤ tl.built b ∧ tl.built b ≤ t) →
      ReachedBy U tl (s + 1) (t + δ)

/-- **A reactive run starts**: under the reactive rules from round `R` to
round `N`, there is a round `R' ≥ R`, either `R` or one above a round that a
correct block reached before `G + τ`, such that, if `R' ≤ N`, the timeline
is a reactive run from `R'` to `N`, and every correct validator has reached
`R'` within `2δ + 2 max τ μ` of `G + τ` and of the time all reached `R`. -/
def Starts : Prop :=
  ∀ (Validator BlockId Payload : Type) [Fintype Validator] [DecidableEq Validator]
    [Faults Validator] [DecidableEq BlockId] [Slots Validator]
    (U : KRecord Validator BlockId Payload) (tl : Timeline Validator BlockId)
    (G δ τ γ μ R N : ℕ),
    ReactiveRules U tl G δ τ γ μ R N → ∃ R', R ≤ R' ∧
      (R' = R ∨ ∃ x ∈ U.ids, (U.block x).creator ∈ (Correct : Finset Validator) ∧
        (U.block x).round + 1 = R' ∧ tl.built x < G + τ) ∧
      (R' ≤ N → ReactiveRun U tl G δ τ γ μ R' N ∧
        ∀ t₀, ReachedBy U tl R t₀ → ReachedBy U tl R' (max t₀ (G + τ) + 2 * δ + 2 * max τ μ))

/-- **Each round within `δ + max τ μ`**: at `δ < γ ≤ τ`, once every correct
validator has reached round `s`, from `R` to below `N`, by `t`, every correct
validator has built at round `s + 1` by `t + δ + max τ μ`. -/
def Slow : Prop :=
  ∀ (Validator BlockId Payload : Type) [Fintype Validator] [DecidableEq Validator]
    [Faults Validator] [DecidableEq BlockId] [Slots Validator]
    (U : KRecord Validator BlockId Payload) (tl : Timeline Validator BlockId)
    (G δ τ γ μ R N : ℕ),
    ReactiveRun U tl G δ τ γ μ R N → δ < γ → γ ≤ τ → ∀ s t, R ≤ s → s < N →
      ReachedBy U tl s t → BuiltBy U tl (s + 1) (t + δ + max τ μ)

/-- **Rounds led by correct validators within `δ + max γ μ`**: at `τ ≥ 2δ`
and `δ < γ ≤ τ`, when the slots at round `s`, from `R + 2` to below `N`, and
one round below have correct leaders, once every correct validator has built
at round `s` by `t`, every correct validator has built at round `s + 1` by
`t + δ + max γ μ`. -/
def Fast : Prop :=
  ∀ (Validator BlockId Payload : Type) [Fintype Validator] [DecidableEq Validator]
    [Faults Validator] [DecidableEq BlockId] [S : Slots Validator]
    (U : KRecord Validator BlockId Payload) (tl : Timeline Validator BlockId)
    (G δ τ γ μ R N : ℕ),
    ReactiveRun U tl G δ τ γ μ R N → 2 * δ ≤ τ → δ < γ → γ ≤ τ → ∀ s t, R + 2 ≤ s → s < N →
      (∀ k, S.slotRound k = s ∨ S.slotRound k + 1 = s →
        S.leader k ∈ (Correct : Finset Validator)) →
      BuiltBy U tl s t → BuiltBy U tl (s + 1) (t + δ + max γ μ)

/-- **The run is responsive**: at `τ ≥ 2δ` and `δ < γ ≤ τ`, a reactive run
from round `R` to round `N` is responsive among the correct validators from
round `R + 1` to `N`. -/
def Responsive : Prop :=
  ∀ (Validator BlockId Payload : Type) [Fintype Validator] [DecidableEq Validator]
    [Faults Validator] [DecidableEq BlockId] [Slots Validator]
    (U : KRecord Validator BlockId Payload) (tl : Timeline Validator BlockId)
    (G δ τ γ μ R N : ℕ),
    ReactiveRun U tl G δ τ γ μ R N → 2 * δ ≤ τ → δ < γ → γ ≤ τ →
      RespondsFrom U (Correct : Finset Validator) (R + 1) N

/-- **A slot led by correct validators commits within `3δ + 2 max γ μ`**: at
`τ ≥ 2δ` and `δ < γ ≤ τ`, when every slot from one round below a slot at
round `r`, from `R + 2` to `N − 2`, to one round above it has a correct
leader, and every correct validator has built at round `r` by `t`, every
correct node commits the slot directly on what it holds at
`t + 3δ + 2 max γ μ`. -/
def Commits : Prop :=
  ∀ (Validator BlockId Payload : Type) [Fintype Validator] [DecidableEq Validator]
    [Faults Validator] [DecidableEq BlockId] [S : Slots Validator]
    (U : KRecord Validator BlockId Payload) (tl : Timeline Validator BlockId)
    (G δ τ γ μ R K N : ℕ),
    ReactiveRun U tl G δ τ γ μ R N → 2 * δ ≤ τ → δ < γ → γ ≤ τ → ∀ k t,
      R + 2 ≤ S.slotRound k → S.slotRound k + 2 ≤ N →
      (∀ j, S.slotRound k ≤ S.slotRound j + 1 → S.slotRound j ≤ S.slotRound k + 1 →
        S.leader j ∈ (Correct : Finset Validator)) →
      BuiltBy U tl (S.slotRound k) t → ∀ v ∈ (Correct : Finset Validator),
        ∃ L, IsLeaderBlock U k L ∧
          NodeDecided U K (tl.held v (t + 3 * δ + 2 * max γ μ)) k (some L)

/-- **The run is synchronous**: at `2δ ≤ γ ≤ τ` and `δ < γ`, a reactive run
from round `R` to round `N` is synchronous among the correct validators from
round `R + 1` to `N`. -/
def Synchronised : Prop :=
  ∀ (Validator BlockId Payload : Type) [Fintype Validator] [DecidableEq Validator]
    [Faults Validator] [DecidableEq BlockId] [Slots Validator]
    (U : KRecord Validator BlockId Payload) (tl : Timeline Validator BlockId)
    (G δ τ γ μ R N : ℕ),
    ReactiveRun U tl G δ τ γ μ R N → 2 * δ ≤ γ → δ < γ → γ ≤ τ →
      SyncFrom U (Correct : Finset Validator) (R + 1) N

/-- **Nothing a leader outputs is lost**: under the rules for nodes, when
correct nodes keep on disk the histories to depth `K` of their blocks'
references, every block of the available sub-DAG of a certified block is on
a correct node's disk from some time on, through any crash. -/
def Durable : Prop :=
  ∀ (Validator BlockId Payload : Type) [Fintype Validator] [DecidableEq Validator]
    [Faults Validator] [DecidableEq BlockId] [Slots Validator]
    (U : KRecord Validator BlockId Payload) (tl : Timeline Validator BlockId)
    (G δ τ γ μ R N K : ℕ),
    NodeRules U tl G δ τ γ μ R N → KeepsHistory U tl K → ∀ A ∈ U.ids, ∀ r,
      (certificatesAt U (IsVote U) (quorumCard Validator) A r).Nonempty → ∀ z ∈ Avail U K A,
      ∃ w ∈ (Correct : Finset Validator), ∃ t₀, ∀ t, t₀ ≤ t → z ∈ tl.disk w t

/-- **The ledger grows**: on a reactive run from round `R` to round `N`, at
`τ ≥ 2δ` and `δ < γ ≤ τ`, when correct nodes fetch the available sub-DAG of
the certified leader blocks they hold within `Δ`, and the schedule offers
runs of `c` correct leaders spanning eligibility, past any slot `k` there is
a slot `b` such that, if the run reaches round `σ(b + c − 1) + 2`, every
correct node, at one time, decides every slot below `b + c` and has fetched
each leader it commits down to `D` rounds below it. -/
def Ledger : Prop :=
  ∀ (Validator BlockId Payload : Type) [Fintype Validator] [DecidableEq Validator]
    [Faults Validator] [DecidableEq BlockId] [S : Slots Validator]
    (U : KRecord Validator BlockId Payload) (tl : Timeline Validator BlockId)
    (G δ τ γ μ R N K D Δ c : ℕ),
    ReactiveRun U tl G δ τ γ μ R N → 2 * δ ≤ τ → δ < γ → γ ≤ τ → Fetches U tl K G Δ →
    0 < c → (∀ b i, i < b → EligibleAt (S := S) 2 i (b + c - 1)) →
    FairRunOn (Correct : Finset Validator) c → ∀ k, ∃ b, k ≤ b ∧
      (S.slotRound (b + c - 1) + 2 ≤ N → ∃ t, ∀ v ∈ (Correct : Finset Validator),
        ∃ g : ℕ → Option BlockId, ∀ i, i < b + c → NodeDecided U K (tl.held v t) i (g i) ∧
          ∀ L, g i = some L → FetchedIn U K (tl.held v t) L ((U.block L).round - D))

/-- Reactive nodes in time. -/
def Statement : Prop :=
  Persisted ∧ OnDisk ∧ Resumes ∧ Built ∧ CatchesUp ∧ Starts ∧ Slow ∧ Fast ∧ Responsive ∧ Commits ∧
    Synchronised ∧ Durable ∧ Ledger

end Reactive

end KPartialDag

end LeanDag
