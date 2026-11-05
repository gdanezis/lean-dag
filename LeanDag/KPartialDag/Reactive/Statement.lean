import LeanDag.KPartialDag.Model.Reactive
/-!
# Reactive nodes in time — statement

`docs/kpartial.md` §11. A correct validator that keeps on disk the last
round it built, and builds only above it (`Persists`), builds at most one
block a round, whatever it loses in a restart (`Persisted`). A validator
that builds above the blocks of its own on its disk does so
(`OnDisk`).

Under the rules for nodes from round `R` to round `N`, with message delay `δ`
from time `G`, timeout `τ`, grace period `γ` and minimum wait `μ`, a set `T`
of at least `n − f` correct nodes up from `G` on, and any other crashes and
restarts (`NodeRules`):

* **operations resume** (`Resumes`): once a validator of `T` has built
  above round `R` by `G`, a reactive run starts above `R`, and every validator
  of `T` reaches it within `3δ + 3 max τ μ` of `G`.

Under the reactive rules, with every validator of `T` at round `R`
(`ReactiveRules`):

* **every round is reached** (`Built`): every validator of `T` builds at
  every round from `R` to `N` or above it;
* **nodes behind catch up within `δ`** (`CatchesUp`): once `f + 1`
  validators of `T` have built at a round, from `G` on, by `t`, every validator
  of `T` has reached the round by `t + δ`;
* **a reactive run starts** (`Starts`): the round after the last round a
  node of `T` reached before `G + τ` starts a reactive run (`ReactiveRun`),
  reached within `2δ + 2 max τ μ` of `G + τ`.

On a reactive run from round `R` to round `N`, at `δ < γ ≤ τ`, where no
node of `T` skips a round:

* **each round is built within `δ + max τ μ`** (`Slow`) of the round below;
* **rounds led by `T` are built within `δ + max γ μ`**
  (`Fast`): at `τ ≥ 2δ`, when the slots of a round and of the round below
  have leaders of `T`, no node of `T` waits for its timeout;
* **the run is responsive** (`Responsive`): at `τ ≥ 2δ`, the record is
  responsive among `T` from round `R + 1` to `N`, so
  `Live.Progress` applies;
* **a slot led by `T` commits within `3δ + 2 max γ μ`**
  (`Commits`): at `τ ≥ 2δ`, when the slots from one round below a slot to
  one round above it have leaders of `T`, every node of `T` commits the
  slot directly within that time of the last block of `T` at the slot's
  round;
* **the run is synchronous** (`Synchronised`): at `2δ ≤ γ`, every block of `T`
  from round `R + 2` to `N` references every block of `T` of the
  round below, so the inclusion results of `Order` apply;
* **the ledger grows** (`Ledger`): when nodes of `T` fetch the available sub-DAG of
  the certified leaders they hold, every node of `T` eventually decides
  every slot up to a run of leaders of `T` and fetches below the leaders
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
`N`, with any crashes and restarts before `G`, once a validator of `T` has
built above round `R` by `G`, there is a round `R' > R` such that, if
`R' ≤ N`, the timeline is a reactive run from `R'` to `N`, and every validator
of `T` has reached `R'` by `G + 3δ + 3 max τ μ`. -/
def Resumes : Prop :=
  ∀ (Validator BlockId Payload : Type) [Fintype Validator] [DecidableEq Validator]
    [Faults Validator] [DecidableEq BlockId] [Slots Validator]
    (U : KRecord Validator BlockId Payload) (tl : Timeline Validator BlockId)
    (T : Finset Validator) (G δ τ γ μ R N : ℕ),
    NodeRules U tl T G δ τ γ μ R N → ∀ b ∈ U.ids,
      (U.block b).creator ∈ T → tl.built b ≤ G →
      R < (U.block b).round → ∃ R', R < R' ∧
        (R' ≤ N → ReactiveRun U tl T G δ τ γ μ R' N ∧
          ReachedBy U tl T R' (G + 3 * δ + 3 * max τ μ))

/-- **Every round is reached**: under the reactive rules from round `R` to
round `N`, every validator of `T` has a block at every round from `R` to
`N`, or above it. -/
def Built : Prop :=
  ∀ (Validator BlockId Payload : Type) [Fintype Validator] [DecidableEq Validator]
    [Faults Validator] [DecidableEq BlockId] [Slots Validator]
    (U : KRecord Validator BlockId Payload) (tl : Timeline Validator BlockId)
    (T : Finset Validator) (G δ τ γ μ R N : ℕ),
    ReactiveRules U tl T G δ τ γ μ R N → ∀ s, R ≤ s → s ≤ N → ∃ t, ReachedBy U tl T s t

/-- **Nodes behind catch up within `δ`**: under the reactive rules from round
`R` to round `N`, once a set `A` of `f + 1` validators of `T` have built at
round `s + 1`, from `R + 1` to `N`, at times from `G` to `t`, every validator
of `T` has reached round `s + 1` by `t + δ`. -/
def CatchesUp : Prop :=
  ∀ (Validator BlockId Payload : Type) [Fintype Validator] [DecidableEq Validator]
    [F : Faults Validator] [DecidableEq BlockId] [Slots Validator]
    (U : KRecord Validator BlockId Payload) (tl : Timeline Validator BlockId)
    (T : Finset Validator) (G δ τ γ μ R N : ℕ),
    ReactiveRules U tl T G δ τ γ μ R N → ∀ s t (A : Finset Validator), R ≤ s → s < N →
      A ⊆ T → F.f + 1 ≤ A.card →
      (∀ v ∈ A, ∃ b ∈ U.ids, (U.block b).creator = v ∧ (U.block b).round = s + 1 ∧
        G ≤ tl.built b ∧ tl.built b ≤ t) →
      ReachedBy U tl T (s + 1) (t + δ)

/-- **A reactive run starts**: under the reactive rules from round `R` to
round `N`, there is a round `R' ≥ R`, either `R` or one above a round that a
block of `T` reached before `G + τ`, such that, if `R' ≤ N`, the timeline
is a reactive run from `R'` to `N`, and every validator of `T` has reached
`R'` within `2δ + 2 max τ μ` of `G + τ` and of the time all reached `R`. -/
def Starts : Prop :=
  ∀ (Validator BlockId Payload : Type) [Fintype Validator] [DecidableEq Validator]
    [Faults Validator] [DecidableEq BlockId] [Slots Validator]
    (U : KRecord Validator BlockId Payload) (tl : Timeline Validator BlockId)
    (T : Finset Validator) (G δ τ γ μ R N : ℕ),
    ReactiveRules U tl T G δ τ γ μ R N → ∃ R', R ≤ R' ∧
      (R' = R ∨ ∃ x ∈ U.ids, (U.block x).creator ∈ T ∧
        (U.block x).round + 1 = R' ∧ tl.built x < G + τ) ∧
      (R' ≤ N → ReactiveRun U tl T G δ τ γ μ R' N ∧
        ∀ t₀, ReachedBy U tl T R t₀ → ReachedBy U tl T R' (max t₀ (G + τ) + 2 * δ + 2 * max τ μ))

/-- **Each round within `δ + max τ μ`**: at `δ < γ ≤ τ`, once every validator
of `T` has reached round `s`, from `R` to below `N`, by `t`, every validator
of `T` has built at round `s + 1` by `t + δ + max τ μ`. -/
def Slow : Prop :=
  ∀ (Validator BlockId Payload : Type) [Fintype Validator] [DecidableEq Validator]
    [Faults Validator] [DecidableEq BlockId] [Slots Validator]
    (U : KRecord Validator BlockId Payload) (tl : Timeline Validator BlockId)
    (T : Finset Validator) (G δ τ γ μ R N : ℕ),
    ReactiveRun U tl T G δ τ γ μ R N → δ < γ → γ ≤ τ → ∀ s t, R ≤ s → s < N →
      ReachedBy U tl T s t → BuiltBy U tl T (s + 1) (t + δ + max τ μ)

/-- **Rounds led by `T` within `δ + max γ μ`**: at `τ ≥ 2δ`
and `δ < γ ≤ τ`, when the slots at round `s`, from `R + 2` to below `N`, and
one round below have leaders of `T`, once every validator of `T` has built
at round `s` by `t`, every validator of `T` has built at round `s + 1` by
`t + δ + max γ μ`. -/
def Fast : Prop :=
  ∀ (Validator BlockId Payload : Type) [Fintype Validator] [DecidableEq Validator]
    [Faults Validator] [DecidableEq BlockId] [S : Slots Validator]
    (U : KRecord Validator BlockId Payload) (tl : Timeline Validator BlockId)
    (T : Finset Validator) (G δ τ γ μ R N : ℕ),
    ReactiveRun U tl T G δ τ γ μ R N → 2 * δ ≤ τ → δ < γ → γ ≤ τ → ∀ s t, R + 2 ≤ s → s < N →
      (∀ k, S.slotRound k = s ∨ S.slotRound k + 1 = s → S.leader k ∈ T) →
      BuiltBy U tl T s t → BuiltBy U tl T (s + 1) (t + δ + max γ μ)

/-- **The run is responsive**: at `τ ≥ 2δ` and `δ < γ ≤ τ`, a reactive run
from round `R` to round `N` is responsive among `T` from
round `R + 1` to `N`. -/
def Responsive : Prop :=
  ∀ (Validator BlockId Payload : Type) [Fintype Validator] [DecidableEq Validator]
    [Faults Validator] [DecidableEq BlockId] [Slots Validator]
    (U : KRecord Validator BlockId Payload) (tl : Timeline Validator BlockId)
    (T : Finset Validator) (G δ τ γ μ R N : ℕ),
    ReactiveRun U tl T G δ τ γ μ R N → 2 * δ ≤ τ → δ < γ → γ ≤ τ →
      RespondsFrom U T (R + 1) N

/-- **A slot led by `T` commits within `3δ + 2 max γ μ`**: at
`τ ≥ 2δ` and `δ < γ ≤ τ`, when every slot from one round below a slot at
round `r`, from `R + 2` to `N − 2`, to one round above it has a leader in
`T`, and every validator of `T` has built at round `r` by `t`, every
node of `T` commits the slot directly on what it holds at
`t + 3δ + 2 max γ μ`. -/
def Commits : Prop :=
  ∀ (Validator BlockId Payload : Type) [Fintype Validator] [DecidableEq Validator]
    [Faults Validator] [DecidableEq BlockId] [S : Slots Validator]
    (U : KRecord Validator BlockId Payload) (tl : Timeline Validator BlockId)
    (T : Finset Validator) (G δ τ γ μ R K N : ℕ),
    ReactiveRun U tl T G δ τ γ μ R N → 2 * δ ≤ τ → δ < γ → γ ≤ τ → ∀ k t,
      R + 2 ≤ S.slotRound k → S.slotRound k + 2 ≤ N →
      (∀ j, S.slotRound k ≤ S.slotRound j + 1 → S.slotRound j ≤ S.slotRound k + 1 →
        S.leader j ∈ T) →
      BuiltBy U tl T (S.slotRound k) t → ∀ v ∈ T,
        ∃ L, IsLeaderBlock U k L ∧
          NodeDecided U K (tl.held v (t + 3 * δ + 2 * max γ μ)) k (some L)

/-- **The run is synchronous**: at `2δ ≤ γ ≤ τ` and `δ < γ`, a reactive run
from round `R` to round `N` is synchronous among `T` from
round `R + 1` to `N`. -/
def Synchronised : Prop :=
  ∀ (Validator BlockId Payload : Type) [Fintype Validator] [DecidableEq Validator]
    [Faults Validator] [DecidableEq BlockId] [Slots Validator]
    (U : KRecord Validator BlockId Payload) (tl : Timeline Validator BlockId)
    (T : Finset Validator) (G δ τ γ μ R N : ℕ),
    ReactiveRun U tl T G δ τ γ μ R N → 2 * δ ≤ γ → δ < γ → γ ≤ τ →
      SyncFrom U T (R + 1) N

/-- **Nothing a leader outputs is lost**: under the rules for nodes, when
correct nodes keep on disk the histories to depth `K` of their blocks'
references, every block of the available sub-DAG of a certified block is on
a correct node's disk from some time on, through any crash. -/
def Durable : Prop :=
  ∀ (Validator BlockId Payload : Type) [Fintype Validator] [DecidableEq Validator]
    [Faults Validator] [DecidableEq BlockId] [Slots Validator]
    (U : KRecord Validator BlockId Payload) (tl : Timeline Validator BlockId)
    (T : Finset Validator) (G δ τ γ μ R N K : ℕ),
    NodeRules U tl T G δ τ γ μ R N → KeepsHistory U tl K → ∀ A ∈ U.ids, ∀ r,
      (certificatesAt U (IsVote U) (quorumCard Validator) A r).Nonempty → ∀ z ∈ Avail U K A,
      ∃ w ∈ (Correct : Finset Validator), ∃ t₀, ∀ t, t₀ ≤ t → z ∈ tl.disk w t

/-- **The ledger grows**: on a reactive run from round `R` to round `N`, at
`τ ≥ 2δ` and `δ < γ ≤ τ`, when nodes of `T` fetch the available sub-DAG of
the certified leader blocks they hold within `Δ`, and the schedule offers
runs of `c` leaders of `T` spanning eligibility, past any slot `k` there is
a slot `b` such that, if the run reaches round `σ(b + c − 1) + 2`, every
node of `T`, at one time, decides every slot below `b + c` and has fetched
each leader it commits down to `D` rounds below it. -/
def Ledger : Prop :=
  ∀ (Validator BlockId Payload : Type) [Fintype Validator] [DecidableEq Validator]
    [Faults Validator] [DecidableEq BlockId] [S : Slots Validator]
    (U : KRecord Validator BlockId Payload) (tl : Timeline Validator BlockId)
    (T : Finset Validator) (G δ τ γ μ R N K D Δ c : ℕ),
    ReactiveRun U tl T G δ τ γ μ R N → 2 * δ ≤ τ → δ < γ → γ ≤ τ → Fetches U tl T K G Δ →
    0 < c → (∀ b i, i < b → EligibleAt (S := S) 2 i (b + c - 1)) →
    FairRunOn T c → ∀ k, ∃ b, k ≤ b ∧
      (S.slotRound (b + c - 1) + 2 ≤ N → ∃ t, ∀ v ∈ T,
        ∃ g : ℕ → Option BlockId, ∀ i, i < b + c → NodeDecided U K (tl.held v t) i (g i) ∧
          ∀ L, g i = some L → FetchedIn U K (tl.held v t) L ((U.block L).round - D))

/-- Reactive nodes in time. -/
def Statement : Prop :=
  Persisted ∧ OnDisk ∧ Resumes ∧ Built ∧ CatchesUp ∧ Starts ∧ Slow ∧ Fast ∧ Responsive ∧ Commits ∧
    Synchronised ∧ Durable ∧ Ledger

end Reactive

end KPartialDag

end LeanDag
