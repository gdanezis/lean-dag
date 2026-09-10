import LeanDag.Barnacle.Helpers.DagRule
import LeanDag.Barnacle.Model.Live
/-!
# BN8 — the configuration sequence exists

The paper's Configuration Progress lemma and Liveness theorem
(`barnacle.md` §7), in the prefix form a finite universe admits (§5): a
run whose current configuration lies past the synchrony round extends
by one configuration, and from a synchrony round at genesis runs of
every height exist, each under the horizon it needs — both on any view
caught up to the horizon (`CoversUpto`). Agreement identifies the
verdict chosen for the anchor's slot with the commit liveness provides
for it.

* **BN8a, progress** — one more configuration, needing `LiveOn` at the
  run's own configuration only.
* **BN8b, every height** — runs of every height, under `LiveOn` at every
  configuration within the bounds that the rule can emit.

Statements only; the proofs live in `Proof.lean`.
-/

namespace LeanDag

namespace Barnacle

namespace Progress

variable {Validator : Type} [Fintype Validator] [DecidableEq Validator]
  {BlockId : Type} [DecidableEq BlockId] {Payload : Type}

/-- **BN8a, progress**: a run past the synchrony round extends by one
configuration. -/
def ProgressStmt (R : LiveRule Validator BlockId Payload) (P : Params)
    (upd : UpdateRule R.toBaseRule) (C₀ : Config Validator) (c : ℕ) : Prop :=
  -- A run of height `K` on any view of `U` caught up to the horizon —
  -- what a validator that has received everything up to `N` holds …
  ∀ (U : R.Universe) (V : R.View U) (Rnd N K : ℕ),
    R.toBaseRule.CoversUpto U V N →
    ∀ (Rn : PartialRun R.toBaseRule P upd C₀ U V K),
    -- … whose current configuration's schedule is live with gap `c` …
    R.LiveOn (Rn.cfg K).sched c →
    -- … on a DAG good from `Rnd` to `N`, where the current configuration's
    -- range starts at or after `Rnd` …
    R.Good U Rnd N → Rnd ≤ Rn.start K + 1 →
    -- … and the horizon leaves room for the threshold, the gap to the
    -- anchor, and the gap and one wave above it:
    Rn.start K + P.maxInterval + 1 + 2 * c + R.waveLength ≤ N →
    -- there is a run of height `K + 1`.
    Nonempty (PartialRun R.toBaseRule P upd C₀ U V (K + 1))

/-- **BN8b, every height**: from a synchrony round at genesis, a run of
every height exists under the horizon that height needs. -/
def EveryHeight (R : LiveRule Validator BlockId Payload) (P : Params)
    (upd : UpdateRule R.toBaseRule) (C₀ : Config Validator)
    (Q : Config Validator → Prop) (c : ℕ) : Prop :=
  -- If the schedule of every configuration within the bounds that the rule
  -- can emit is live with gap `c`, and the genesis configuration is within
  -- the bounds and is one of them …
  (∀ C : Config Validator, (∀ r, C.slotsAt r ≤ P.maxLeaders) → 0 < C.interval →
    C.interval ≤ P.maxInterval → Q C → R.LiveOn C.sched c) →
  (∀ r, C₀.slotsAt r ≤ P.maxLeaders) → 0 < C₀.interval → C₀.interval ≤ P.maxInterval →
  Q C₀ →
  -- … then on a DAG good from round `1` (or `0`) to `N` …
  ∀ (U : R.Universe) (V : R.View U) (Rnd N : ℕ), R.Good U Rnd N →
    R.toBaseRule.CoversUpto U V N → Rnd ≤ 1 →
    -- … every height whose horizon fits under `N` is reached, on any view
    -- caught up to `N`.
    ∀ K, horizon P R c K ≤ N →
      Nonempty (PartialRun R.toBaseRule P upd C₀ U V K)

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
        ∀ c : ℕ, ProgressStmt R P upd C₀ c ∧ EveryHeight R P upd C₀ Q c

end Progress

end Barnacle

end LeanDag
