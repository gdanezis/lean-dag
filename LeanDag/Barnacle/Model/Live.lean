import LeanDag.Barnacle.Model.Run
/-!
# Barnacle: the liveness interface

A4's liveness half (`barnacle.md` §7): on a good DAG every slot is
eventually decided and new leaders committed infinitely often, both
read on any view caught up to a horizon. `LiveRule` adds one field,
`Good`, the rule's own notion of a DAG good from `Rnd` to horizon `N`;
`LiveOn S c` is that liveness on schedule `S`, with commit gap `c`
supplied by the schedule's own liveness theorem.

**Trusted core of the arc: definitions only.**
-/

namespace LeanDag

namespace Barnacle

variable {Validator : Type} [Fintype Validator] [DecidableEq Validator]
variable {BlockId : Type} [DecidableEq BlockId] {Payload : Type}

/-- **A base rule with a notion of a good DAG.** `Good U Rnd N`: the DAG
`U` is good from round `Rnd` to horizon `N` — what the base liveness
route asks of it, as the rule defines it. -/
structure LiveRule (Validator : Type) [Fintype Validator] [DecidableEq Validator]
    (BlockId : Type) [DecidableEq BlockId] (Payload : Type)
    extends BaseRule Validator BlockId Payload where
  /-- The DAG is good from round `Rnd` to horizon `N`. -/
  Good : Universe → ℕ → ℕ → Prop

/-- **A4, liveness, on one schedule with commit gap `c`.** -/
def LiveRule.LiveOn (R : LiveRule Validator BlockId Payload) (S : Slots Validator) (c : ℕ) :
    Prop :=
  -- On every DAG good from `Rnd` to `N` …
  ∀ (U : R.Universe) (V : R.View U) (Rnd N : ℕ), R.Good U Rnd N → R.toBaseRule.CoversUpto U V N →
    -- … every slot at a round from `Rnd`, with `c` rounds and a wave still
    -- under the horizon, is decided on any view caught up to `N` …
    (∀ κ, Rnd ≤ S.slotRound κ → S.slotRound κ + c + R.waveLength ≤ N →
      ∃ v, R.Decided S V κ v) ∧
    -- … and from every round `r` at or after `Rnd`, with `c` rounds and a
    -- wave still under the horizon, some slot at a round in `[r, r + c]`
    -- is committed on that view.
    (∀ r, Rnd ≤ r → r + c + R.waveLength ≤ N →
      ∃ κ, r ≤ S.slotRound κ ∧ S.slotRound κ ≤ r + c ∧
        ∃ L, R.Decided S V κ (some L))

/-- An update rule keeps the count in `[1, maxLeaders]`, whatever it is
given — what extending a run needs of it; BN7a for the AIMD rule. -/
def UpdBounded {R : BaseRule Validator BlockId Payload} (P : Params) (upd : UpdateRule R) :
    Prop :=
  ∀ m b U V A, 0 < (upd m b U V A).1 ∧ (upd m b U V A).1 ≤ P.maxLeaders

/-- **What a good DAG delivers**: a `slack`-missing set of validators
whose blocks, from `Rnd`, are reached by everything two rounds above
them — the base protocol's coverage read as delivery, the second law a
live rule carries beside `Descent`. -/
structure LiveRule.Delivers (R : LiveRule Validator BlockId Payload) (slack : ℕ) : Prop where
  /-- A good author's block is in the history of every block two rounds
  above it. -/
  reaches : ∀ (U : R.Universe) (Rnd N : ℕ), R.Good U Rnd N →
    ∃ T : Finset Validator, Fintype.card Validator ≤ T.card + slack ∧
      ∀ b ∈ R.ids U, (R.block U b).creator ∈ T → Rnd ≤ (R.block U b).round →
        (R.block U b).round + 1 ≤ N →
        ∀ c ∈ R.ids U, (R.block U b).round + 2 ≤ (R.block U c).round →
          b ∈ historyFrom (R.block U) c

/-- The horizon a run of height `K` needs, from a synchrony round at
genesis: each anchor within `interval + 1 + c` rounds of the last, plus
the gap and one wave to decide the final range. -/
def horizon (P : Params) (R : LiveRule Validator BlockId Payload) (c K : ℕ) : ℕ :=
  K * (P.interval + 1 + c + P.gap) + c + R.waveLength

end Barnacle

end LeanDag
