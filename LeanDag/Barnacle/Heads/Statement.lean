import LeanDag.Barnacle.Model.Heads
/-!
# BN9 — the heads descent

The base protocol's liveness clause, `LiveOn`, discharged for the
paper's own schedule at every configuration (`barnacle.md` §8):
from the descent laws of a rule and a run of correct-led heads, a
schedule is live with the run's gap; and round-robin has such runs by
pigeonhole whenever the committee bound `waveLength · slack + 1 ≤ n`
holds — which for Mysticeti is `3f + 1 ≤ n`, its own.

* **BN9a, the stretch descent** — a stretch of consecutive decided slots
  with a committed top decides everything a wave below the top.
* **BN9b, heads decide** — `waveLength` consecutive good-led heads decide
  every slot up to a wave below the first and commit it.
* **BN9c, live from heads** — a run of heads with gap `c₀` makes a
  configuration's schedule live with gap `c₀`.
* **BN9d, round-robin has runs of heads** — the pigeonhole.
* **BN9e, round-robin is live** — at every configuration whose heads are
  the rotation, with gap `n + waveLength − 1`.

Statements only; the proofs live in `Proof.lean`.
-/

namespace LeanDag

namespace Barnacle

namespace Heads

variable {Validator : Type} [Fintype Validator] [DecidableEq Validator]
  {BlockId : Type} [DecidableEq BlockId] {Payload : Type}

/-- **BN9a, the stretch descent**: from `indirect` alone. -/
def StretchDescent (R : LiveRule Validator BlockId Payload) (slack : ℕ) : Prop :=
  R.Descent slack →
  -- Any schedule, any view;
  ∀ (S : Slots Validator) (U : R.Universe) (V : R.View U) (b top : ℕ),
    -- a stretch of slots `[b, top]` whose top lies a full wave above every
    -- slot below `b` …
    (∀ i, i < b → S.slotRound i + R.waveLength ≤ S.slotRound top) →
    -- … every slot of which is decided …
    (∀ j, b ≤ j → j ≤ top → ∃ v, R.Decided S V j v) →
    -- … and whose top is committed …
    (∃ B, R.Decided S V top (some B)) →
    -- … decides every slot below `b`.
    ∀ i, i < b → ∃ v, R.Decided S V i v

/-- **BN9b, heads decide**: at a configuration, `waveLength` consecutive
good-led heads from round `ρ` decide every slot at a round in
`[ρ − waveLength, ρ)` and commit the head of `ρ`. -/
def HeadsDecide (R : LiveRule Validator BlockId Payload) (slack : ℕ) : Prop :=
  R.Descent slack → 0 < R.waveLength →
  ∀ (U : R.Universe) (V : R.View U) (Rnd N : ℕ) (T : Finset Validator),
    -- Given what `goodLeaders` gives for `T` on `U` from `Rnd` to `N`, on
    -- any view caught up to `N`,
    (∀ (S : Slots Validator) (κ : ℕ), Rnd ≤ S.slotRound κ → S.slotRound κ + R.waveLength ≤ N →
      S.leader κ ∈ T → ∃ L, R.Decided S V κ (some L)) →
    -- for every configuration `C` and every round `ρ` from `Rnd` whose
    -- `waveLength` heads have their waves under `N` …
    ∀ (C : Config Validator) (ρ : ℕ), Rnd ≤ ρ →
      ρ + R.waveLength + R.waveLength ≤ N + 1 →
      -- … if the heads of rounds `ρ, …, ρ + waveLength − 1` are `T`-led …
      (∀ i, i < R.waveLength → C.head (ρ + i) ∈ T) →
      -- … then every slot at a round below `ρ` and at most a wave below it
      -- is decided on that view …
      (∀ κ, C.sched.slotRound κ < ρ → ρ ≤ C.sched.slotRound κ + R.waveLength →
        ∃ v, R.Decided C.sched V κ v) ∧
      -- … and the head of `ρ`, slot `C.cum ρ`, is committed.
      ∃ L, R.Decided C.sched V (C.cum ρ) (some L)

/-- **BN9c, live from heads**: a run of good-led heads with gap `c₀`, for
the good set of every good DAG, makes a configuration's schedule live
with gap `c₀`. -/
def LiveOnOfHeads (R : LiveRule Validator BlockId Payload) (slack : ℕ)
    (C : Config Validator) (c₀ : ℕ) : Prop :=
  R.Descent slack → 0 < R.waveLength →
  -- If every set missing at most `slack` validators has a run of the
  -- configuration's heads …
  (∀ T : Finset Validator, Fintype.card Validator ≤ T.card + slack →
    HeadsRun C.head T R.waveLength c₀) →
  -- … then the configuration's schedule is live with gap `c₀`.
  R.LiveOn C.sched c₀

/-- **BN9d, round-robin has runs of heads**: on `n` validators, for every
set missing at most `slack`, when `g · slack + 1 ≤ n` — within
`n + g − 1` rounds. -/
def RoundRobinHeads : Prop :=
  ∀ (n : ℕ) (hn : 0 < n) (T : Finset (Fin n)) (slack g : ℕ),
    n ≤ T.card + slack → g * slack + 1 ≤ n →
    HeadsRun (roundRobin n hn) T g (n + g - 1)

/-- **BN9e, round-robin is live**: a live rule with descent laws at
`slack`, on `n ≥ waveLength · slack + 1` validators, is live under
round-robin at every count, with gap `n + waveLength − 1`. -/
def LiveOnRoundRobin : Prop :=
  ∀ (n : ℕ) (hn : 0 < n) (BlockId Payload : Type) [DecidableEq BlockId]
    (R : LiveRule (Fin n) BlockId Payload) (slack : ℕ), R.Descent slack →
    0 < R.waveLength → R.waveLength * slack + 1 ≤ n →
    ∀ C : Config (Fin n), C.head = roundRobin n hn →
      R.LiveOn C.sched (n + R.waveLength - 1)

/-- The heads descent, for every live rule with descent laws, every
configuration, and round-robin on every committee. -/
def Statement : Prop :=
  (∀ (Validator BlockId Payload : Type) [Fintype Validator] [DecidableEq Validator]
    [DecidableEq BlockId] (R : LiveRule Validator BlockId Payload) (slack : ℕ)
    (C : Config Validator) (c₀ : ℕ),
    StretchDescent R slack ∧ HeadsDecide R slack ∧ LiveOnOfHeads R slack C c₀) ∧
  RoundRobinHeads ∧ LiveOnRoundRobin

end Heads

end Barnacle

end LeanDag
