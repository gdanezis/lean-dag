import LeanDag.Barnacle.Model.Window
/-!
# Barnacle: the run

Configuration `k` (`barnacle.md` §5) is in force above round `start k`,
and its range runs to the next anchor's round; every slot of the range
is decided against the configuration's own schedule `(cfg k).sched`,
which is what makes the dependency on `k` well-founded. A configuration
carries its leaders, its slots per round and its interval together
(`Model/Config.lean`), so a reconfiguration replaces all three at once.
`PartialRun` closes configurations `0, …, K` from a genesis
configuration `C₀`: their ranges decided in full, `K` itself only determined — there is no total run, since a
universe holds finitely many blocks. The run starts after round `0`, so
round `0` lies in no range, matching Algorithm 2.

**Trusted core of the arc: definitions only.**
-/

namespace LeanDag

namespace Barnacle

variable {Validator : Type} [Fintype Validator] [DecidableEq Validator]
variable {BlockId : Type} [DecidableEq BlockId] {Payload : Type}

/-- **A run closed up to height `K`.** Configurations `0, …, K` are
determined, and the ranges of configurations below `K` are decided in
full.

`closed` is the paper's `TryDecide`: every slot of the range — the
rounds after `start k`, through the anchor's round `start (k + 1)` —
decided against the configuration's schedule. `anchor_commits`
and `anchor_least` are `TryCommit`'s trigger: the anchor is the least
committed slot whose round exceeds `start k + (cfg k).interval`.
`update` is `UpdateLeaders`, for an arbitrary rule. `slotsAt_le` and
`interval_pos` are clauses of the run because the rule is arbitrary; for
the AIMD rule they are theorems. -/
structure PartialRun (R : BaseRule Validator BlockId Payload) (P : Params)
    (upd : UpdateRule R) (C₀ : Config Validator) (U : R.Universe) (V : R.View U)
    (K : ℕ) where
  /-- The round after which configuration `k` is in force. -/
  start : ℕ → ℕ
  /-- Configuration `k`: its leaders, its slots per round, its interval. -/
  cfg : ℕ → Config Validator
  /-- The back-off of configuration `k`. -/
  backoff : ℕ → ℕ
  /-- The slot, in `(cfg k).sched`, of the anchor that closes
  configuration `k`. -/
  anchor : ℕ → ℕ
  /-- `vdct k κ`: the verdict of slot `κ` of `(cfg k).sched`. -/
  vdct : ℕ → ℕ → Option BlockId
  /-- The run starts after round `0`, in the genesis configuration. -/
  init : start 0 = 0 ∧ cfg 0 = C₀ ∧ backoff 0 = 0
  /-- No round of any configuration has more slots than the bound. -/
  slotsAt_le : ∀ k r, (cfg k).slotsAt r ≤ P.maxLeaders
  /-- Every configuration waits at least one round before reconfiguring. -/
  interval_pos : ∀ k, 0 < (cfg k).interval
  /-- No configuration waits longer than the bound. -/
  interval_le : ∀ k, (cfg k).interval ≤ P.maxInterval
  /-- Every slot of the range — after `start k`, through the anchor's
  round — decided against the configuration's schedule (`TryDecide`). -/
  closed : ∀ k, k < K → ∀ κ, start k < (cfg k).roundOf κ →
    (cfg k).roundOf κ ≤ start (k + 1) → R.Decided (cfg k).sched V κ (vdct k κ)
  /-- The anchor is committed, past the threshold … -/
  anchor_commits : ∀ k, k < K →
    (∃ A, vdct k (anchor k) = some A) ∧
      start k + (cfg k).interval < (cfg k).roundOf (anchor k)
  /-- … and is the least such slot. -/
  anchor_least : ∀ k, k < K → ∀ κ, κ < anchor k →
    start k + (cfg k).interval < (cfg k).roundOf κ → vdct k κ = none
  /-- The next configuration is in force after the anchor's round. -/
  start_succ : ∀ k, k < K → start (k + 1) = (cfg k).roundOf (anchor k)
  /-- The next configuration is the rule's. -/
  update : ∀ k, k < K → ∀ A, vdct k (anchor k) = some A →
    (cfg (k + 1), backoff (k + 1)) = upd (cfg k) (backoff k) U V A

variable {R : BaseRule Validator BlockId Payload} {P : Params}
variable {upd : UpdateRule R} {C₀ : Config Validator} {U : R.Universe} {V : R.View U}

/-- The schedule of configuration `k`. -/
abbrev PartialRun.sched {K : ℕ} (Rn : PartialRun R P upd C₀ U V K) (k : ℕ) :
    Slots Validator :=
  (Rn.cfg k).sched

/-! ## The ledger -/

/-- The committed blocks of the slots `[lo, hi)`, in slot order. -/
def ledgerOf (v : ℕ → Option BlockId) (lo hi : ℕ) : List BlockId :=
  (List.range' lo (hi - lo)).filterMap v

/-- The ledger of configuration `k`: its range's committed blocks, from
the first slot after `start k` to the last slot of round `start (k + 1)`.
Meaningful for the closed configurations, `k < K`. -/
def PartialRun.rangeLedger {K : ℕ} (Rn : PartialRun R P upd C₀ U V K) (k : ℕ) :
    List BlockId :=
  ledgerOf (Rn.vdct k) ((Rn.cfg k).cum (Rn.start k + 1))
    ((Rn.cfg k).cum (Rn.start (k + 1) + 1))

/-- The ledger through configuration `K' − 1`: the ranges' ledgers,
concatenated in configuration order. Meaningful for `K' ≤ K`. -/
def PartialRun.ledgerUpto {K : ℕ} (Rn : PartialRun R P upd C₀ U V K) (K' : ℕ) :
    List BlockId :=
  (List.range K').flatMap Rn.rangeLedger

end Barnacle

end LeanDag
