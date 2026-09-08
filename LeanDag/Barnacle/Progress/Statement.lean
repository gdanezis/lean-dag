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
  run's own count only.
* **BN8b, every height** — runs of every height, under `LiveOn` at every
  count.

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
    (getLeader : ℕ → Validator) (hk : Keyed getLeader P.maxLeaders)
    (upd : UpdateRule R.toBaseRule) (c : ℕ) : Prop :=
  -- A run of height `K` on any view of `U` caught up to the horizon —
  -- what a validator that has received everything up to `N` holds …
  ∀ (U : R.Universe) (V : R.View U) (Rnd N K : ℕ),
    R.toBaseRule.CoversUpto U V N →
    ∀ (Rn : PartialRun R.toBaseRule P getLeader hk upd U V K),
    -- … whose current configuration's schedule is live with gap `c` …
    R.LiveOn (Sched getLeader hk (Rn.count K) (Rn.count_pos K) (Rn.count_le K)) c →
    -- … on a DAG good from `Rnd` to `N`, where the current configuration's
    -- range starts at or after `Rnd` …
    R.Good U Rnd N → Rnd ≤ Rn.start K + 1 →
    -- … and the horizon leaves room for the threshold, the gap to the
    -- anchor, and the gap and one wave above it:
    Rn.start K + P.interval + 1 + 2 * c + R.waveLength ≤ N →
    -- there is a run of height `K + 1`.
    Nonempty (PartialRun R.toBaseRule P getLeader hk upd U V (K + 1))

/-- **BN8b, every height**: from a synchrony round at genesis, a run of
every height exists under the horizon that height needs. -/
def EveryHeight (R : LiveRule Validator BlockId Payload) (P : Params)
    (getLeader : ℕ → Validator) (hk : Keyed getLeader P.maxLeaders)
    (upd : UpdateRule R.toBaseRule) (c : ℕ) : Prop :=
  -- If every configuration's schedule is live with gap `c` …
  (∀ m (hm : 0 < m) (hmax : m ≤ P.maxLeaders), R.LiveOn (Sched getLeader hk m hm hmax) c) →
  -- … then on a DAG good from round `1` (or `0`) to `N` …
  ∀ (U : R.Universe) (V : R.View U) (Rnd N : ℕ), R.Good U Rnd N →
    R.toBaseRule.CoversUpto U V N → Rnd ≤ 1 →
    -- … every height whose horizon fits under `N` is reached, on any view
    -- caught up to `N`.
    ∀ K, horizon P R c K ≤ N →
      Nonempty (PartialRun R.toBaseRule P getLeader hk upd U V K)

/-- Progress and every height, for every live rule satisfying the laws,
every parameter set, every keyed leader function, every update rule that
keeps the count in range, and every gap. -/
def Statement : Prop :=
  ∀ (Validator BlockId Payload : Type) [Fintype Validator] [DecidableEq Validator]
    [DecidableEq BlockId] (R : LiveRule Validator BlockId Payload),
    Properties.Agree R.toBaseRule.toDagRule →
    ∀ (P : Params) (getLeader : ℕ → Validator) (hk : Keyed getLeader P.maxLeaders)
      (upd : UpdateRule R.toBaseRule), UpdBounded P upd → ∀ c,
      ProgressStmt R P getLeader hk upd c ∧ EveryHeight R P getLeader hk upd c

end Progress

end Barnacle

end LeanDag
