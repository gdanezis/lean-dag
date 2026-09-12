import LeanDag.Adaptive.Model.Segment
import LeanDag.Barnacle.Model.Live
import LeanDag.Barnacle.Helpers.DagRule
/-!
# AL16 — the segmented configuration sequence exists

BN8 at a run whose boundaries are fixed before the anchors are found
(`adaptive-leaders.md` §9): a run whose current configuration lies past
the synchrony round extends by one, and from a synchrony round at genesis
runs of every height exist under the horizon that height needs — both on
any view caught up to the horizon.

* **AL16a, progress** — one more configuration, needing `LiveOn` at the
  run's own configuration only.
* **AL16b, every height** — runs of every height, under `LiveOn` at every
  configuration within the bounds that the rule can emit.

The horizon is `Barnacle.horizon` unchanged. A boundary sits within
`maxInterval` of the previous one and the anchor within the commit gap of
the boundary, so the same arithmetic bounds the same heights; the new
boundary is in fact reached more tightly, by `maxInterval` rather than by
`maxInterval + 1 + c`.

Statements only; the proofs live in `Proof.lean`.
-/

namespace LeanDag

namespace Adaptive

namespace Progress

open Barnacle

variable {Validator : Type} [Fintype Validator] [DecidableEq Validator]
  {BlockId : Type} [DecidableEq BlockId] {Payload : Type}

/-- **AL16a, progress**: a run past the synchrony round extends by one
configuration. -/
def ConfigProgress (R : LiveRule Validator BlockId Payload) (P : Params)
    (upd : UpdateRule R.toBaseRule) (C₀ : Config Validator) (c : ℕ) : Prop :=
  -- A run of height `K` on any view of `U` caught up to the horizon —
  -- what a validator that has received everything up to `N` holds …
  ∀ (U : R.Universe) (V : R.View U) (Rnd N K : ℕ),
    R.toBaseRule.CoversUpto U V N →
    ∀ (Rn : SegRun R.toBaseRule P upd C₀ U V K),
    -- … whose current configuration's schedule is live with gap `c` …
    R.LiveOn (Rn.cfg K).sched c →
    -- … on a DAG good from `Rnd` to `N`, where the current configuration's
    -- range starts at or after `Rnd` …
    R.Good U Rnd N → Rnd ≤ Rn.start K + 1 →
    -- … and the horizon leaves room for the threshold, the gap to the
    -- anchor, and the gap and one wave above it:
    Rn.start K + P.maxInterval + 1 + 2 * c + R.waveLength ≤ N →
    -- there is a run of height `K + 1`.
    Nonempty (SegRun R.toBaseRule P upd C₀ U V (K + 1))

/-- **AL16b, every height**: from a synchrony round at genesis, a run of
every height exists under the horizon that height needs. -/
def EveryHeight (R : LiveRule Validator BlockId Payload) (P : Params)
    (upd : UpdateRule R.toBaseRule) (C₀ : Config Validator)
    (Q : Config Validator → Prop) (c : ℕ) : Prop :=
  -- If the schedule of every configuration within the bounds that the rule
  -- can emit is live with gap `c`, and the genesis configuration is within
  -- the bounds and is one of them …
  (∀ C : Config Validator, C.InBounds P → Q C → R.LiveOn C.sched c) →
  C₀.InBounds P → Q C₀ →
  -- … then on a DAG good from round `1` (or `0`) to `N` …
  ∀ (U : R.Universe) (V : R.View U) (Rnd N : ℕ), R.Good U Rnd N →
    R.toBaseRule.CoversUpto U V N → Rnd ≤ 1 →
    -- … every height whose horizon fits under `N` is reached, on any view
    -- caught up to `N`.
    ∀ K, horizon P R c K ≤ N →
      Nonempty (SegRun R.toBaseRule P upd C₀ U V K)

/-- Progress and every height, for every live rule satisfying the laws,
every parameter set, every update rule that keeps a configuration within
the bounds, every genesis configuration, every clause the rule's output
satisfies, and every gap. -/
def Statement : Prop :=
  ∀ (Validator BlockId Payload : Type) [Fintype Validator] [DecidableEq Validator]
    [DecidableEq BlockId] (R : LiveRule Validator BlockId Payload),
    Properties.Agree R.toBaseRule.toDagRule →
    ∀ (P : Params) (upd : UpdateRule R.toBaseRule), UpdBounded P upd →
      ∀ (C₀ : Config Validator) (Q : Config Validator → Prop), UpdKeeps upd Q →
        ∀ c : ℕ, ConfigProgress R P upd C₀ c ∧ EveryHeight R P upd C₀ Q c


end Progress

end Adaptive

end LeanDag
