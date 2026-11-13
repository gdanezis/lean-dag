import LeanDag.Barnacle.Model.Run
/-!
# Barnacle: the liveness interface

A4's liveness half (`barnacle.md` §7): on a good DAG every slot is
eventually decided and new leaders committed infinitely often, both
read on any view caught up to a horizon. `LiveRule` adds one field,
`Good`, the rule's own notion of a DAG good under a schedule from `Rnd` to
horizon `N` — a responsive validator waits only for the leaders its
schedule names, so goodness is relative to one;
`LiveOn S c` is that liveness on schedule `S`, with commit gap `c`
supplied by the schedule's own liveness theorem.

**Trusted core of the arc: definitions only.**
-/

namespace LeanDag

namespace Barnacle

variable {Validator : Type} [Fintype Validator] [DecidableEq Validator]
variable {BlockId : Type} [DecidableEq BlockId] {Payload : Type}

/-- **A base rule with a notion of a good DAG.** `Good S U Rnd N`: the DAG
`U` is good under the schedule `S` from round `Rnd` to horizon `N` — what
the base liveness route asks of it, as the rule defines it. -/
structure LiveRule (Validator : Type) [Fintype Validator] [DecidableEq Validator]
    (BlockId : Type) [DecidableEq BlockId] (Payload : Type)
    extends BaseRule Validator BlockId Payload where
  /-- The DAG is good under schedule `S` from round `Rnd` to horizon `N`. -/
  Good : Slots Validator → Universe → ℕ → ℕ → Prop

/-- **A4, liveness, on one schedule with commit gap `c`.** -/
def LiveRule.LiveOn (R : LiveRule Validator BlockId Payload) (S : Slots Validator) (c : ℕ) :
    Prop :=
  -- On every DAG good under `S` from `Rnd` to `N` …
  ∀ (U : R.Universe) (V : R.View U) (Rnd N : ℕ), R.Good S U Rnd N →
    R.toBaseRule.CoversUpto U V N →
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

/-- **Slots below the good start settle**: on a DAG good under `S` from
`Rnd`, every slot of `S` below `Rnd` is decided on any view caught up to
`N`, once `c` rounds and a wave past `Rnd` lie under the horizon. A new
configuration's first rounds come before its validators learn it, so its
leaders are not waited for there; the slots of those rounds are decided by
a later commit. -/
def LiveRule.SettlesBelow (R : LiveRule Validator BlockId Payload) (S : Slots Validator)
    (c : ℕ) : Prop :=
  ∀ (U : R.Universe) (V : R.View U) (Rnd N : ℕ), R.Good S U Rnd N →
    R.toBaseRule.CoversUpto U V N →
    ∀ κ, S.slotRound κ < Rnd → Rnd + c + R.waveLength ≤ N → ∃ v, R.Decided S V κ v

/-- **An update rule preserves what a run assumes of a configuration**:
no round wider than `maxLeaders`, an interval that is positive and no
larger than `maxInterval`. This is what extending a run needs of it; BN7a for the
AIMD rule. Positivity of the widths is a `Config` field and needs no
clause. -/
def UpdBounded {R : BaseRule Validator BlockId Payload} (P : Params)
    (upd : UpdateRule R) : Prop :=
  ∀ C b U V v A, C.InBounds P → (upd C b U V v A).1.InBounds P

/-- **What a good DAG delivers**: a `slack`-missing set of validators
whose blocks, from `Rnd`, are reached by everything two rounds above
them — the base protocol's coverage read as delivery, the second law a
live rule carries beside `Descent`. -/
structure LiveRule.Delivers (R : LiveRule Validator BlockId Payload) (slack : ℕ) : Prop where
  /-- A good author's block is in the history of every block two rounds
  above it. -/
  reaches : ∀ (S : Slots Validator) (U : R.Universe) (Rnd N : ℕ), R.Good S U Rnd N →
    ∃ T : Finset Validator, Fintype.card Validator ≤ T.card + slack ∧
      ∀ b ∈ R.ids U, (R.block U b).creator ∈ T → Rnd ≤ (R.block U b).round →
        (R.block U b).round + 1 ≤ N →
        ∀ c ∈ R.ids U, (R.block U b).round + 2 ≤ (R.block U c).round →
          b ∈ historyFrom (R.block U) c

/-- **What an update rule preserves.** From a configuration satisfying
`Q` it writes one satisfying `Q` — the clause a liveness argument needs of a
reconfiguration, and the reason such an argument need not hold of every
configuration in the bounds. For the AIMD rule `Q` may be "the heads are
`head`", which it meets by carrying its leader function across, or "one
width throughout", which it meets by emitting `Config.uniform`. -/
def UpdKeeps {R : BaseRule Validator BlockId Payload} (upd : UpdateRule R)
    (Q : Config Validator → Prop) : Prop :=
  ∀ C b U V v A, Q C → Q (upd C b U V v A).1

/-- The horizon a run of height `K` needs, from a synchrony round at
genesis: each anchor within `maxInterval + 1 + c` rounds of the last,
plus the gap and one wave to decide the final range. -/
def horizon (P : Params) (R : LiveRule Validator BlockId Payload) (c K : ℕ) : ℕ :=
  K * (P.maxInterval + 1 + c) + c + R.waveLength

/-- The horizon a run of height `K` needs when each configuration's
schedule is good only `δ` rounds after its start: the pivot is looked for
from the later of the threshold and that round. -/
def horizonFrom (P : Params) (R : LiveRule Validator BlockId Payload) (c δ K : ℕ) : ℕ :=
  K * (max (P.maxInterval + 1) δ + c) + c + R.waveLength

end Barnacle

end LeanDag
