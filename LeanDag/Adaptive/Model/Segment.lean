import LeanDag.Barnacle.Model.Run
/-!
# The segmented adaptive run

A run of configurations in the shape the Hammerhead paper's
`ORDERHISTORY` gives it (`adaptive-leaders.md` §9): a configuration
governs a fixed span of rounds, decisions are taken under it as far as
the anchor that closes the span, and **output stops at the span's own
boundary** rather than at the anchor.

The two bounds are the point. `closed` reaches
`(cfg k).roundOf (anchor k)`, because finding the anchor is what settles
the span and the anchor may lie far above the boundary under asynchrony.
`rangeLedger` reads only `(start k, start (k + 1)]`, and
`start (k + 1) = start k + (cfg k).interval` is fixed before the anchor
is looked for. The rounds between carry a verdict in this segment and
another in the next, computed under the next configuration, and only the
later one is output — the retroactive re-derivation the paper describes.

`Barnacle.PartialRun` collapses the two bounds into one by taking the
anchor's round as the boundary, which is what its own paper does
(`adaptive-leaders.md` D19). The structures otherwise agree, and this
file borrows Barnacle's vocabulary — `Config`, `UpdateRule`, `Anchored`,
`Config.InBounds`, `ledgerOf` — rather than restating it. Lifting the run
itself to a common layer with the ledger bound as a parameter is D21,
deferred until this arc's shape is known rather than guessed.

**Trusted core of the arc: definitions only.**
-/

namespace LeanDag

namespace Adaptive

open Barnacle

variable {Validator : Type} [Fintype Validator] [DecidableEq Validator]
variable {BlockId : Type} [DecidableEq BlockId] {Payload : Type}

/-- **A segmented run closed up to height `K`.** Configurations
`0, …, K` are determined, and the spans of configurations below `K` are
decided in full.

`closed` decides every slot from after `start k` through the anchor's
round, against configuration `k`'s schedule — the schedule in force
throughout, since the anchor has not yet been found and the switch has
not yet happened. `anchor_commits` and `anchor_least` make the anchor
the least committed slot **past the boundary**, not past a threshold
inside the span. `update` hands the rule the verdicts of the span it just
closed — `spanVdct`, agreed between validators before either applies the
rule — so a reputation rule may read the committed leaders of the span
without a hypothesis. `start_succ` fixes the next boundary from the current
one and the interval alone, so the boundaries are known before any
commit. -/
structure SegRun (R : BaseRule Validator BlockId Payload) (P : Params)
    (upd : UpdateRule R) (C₀ : Config Validator) (U : R.Universe) (V : R.View U)
    (K : ℕ) where
  /-- The round after which configuration `k` is in force. -/
  start : ℕ → ℕ
  /-- Configuration `k`: its leaders, its slots per round, its interval. -/
  cfg : ℕ → Config Validator
  /-- The back-off of configuration `k`, for rules that carry one. -/
  backoff : ℕ → ℕ
  /-- The slot, in `(cfg k).sched`, of the anchor that closes the span. -/
  anchor : ℕ → ℕ
  /-- `vdct k κ`: the verdict of slot `κ` of `(cfg k).sched`. -/
  vdct : ℕ → ℕ → Option BlockId
  /-- The run starts after round `0`, in the genesis configuration. -/
  init : start 0 = 0 ∧ cfg 0 = C₀ ∧ backoff 0 = 0
  /-- Every configuration is within the parameters. -/
  bounds : ∀ k, (cfg k).InBounds P
  /-- **Decisions run to the anchor.** Every slot after `start k` and at
  or below the anchor's round is decided against the configuration's
  schedule. -/
  closed : ∀ k, k < K → ∀ κ, start k < (cfg k).roundOf κ →
    (cfg k).roundOf κ ≤ (cfg k).roundOf (anchor k) →
      R.Decided (cfg k).sched V κ (vdct k κ)
  /-- The anchor is committed, past the boundary … -/
  anchor_commits : ∀ k, k < K →
    (∃ A, vdct k (anchor k) = some A) ∧ start (k + 1) < (cfg k).roundOf (anchor k)
  /-- … and is the least such slot. -/
  anchor_least : ∀ k, k < K → ∀ κ, κ < anchor k →
    start (k + 1) < (cfg k).roundOf κ → vdct k κ = none
  /-- **The boundary is fixed before the anchor is found**: the next
  configuration takes force an interval after this one did. -/
  start_succ : ∀ k, k < K → start (k + 1) = start k + (cfg k).interval
  /-- The next configuration is the rule's, at the anchor's block. -/
  update : ∀ k, k < K → ∀ A, vdct k (anchor k) = some A →
    (cfg (k + 1), backoff (k + 1)) = upd (cfg k) (backoff k) U V
      (spanVdct (cfg k) (start k) ((cfg k).roundOf (anchor k)) (vdct k)) A

variable {R : BaseRule Validator BlockId Payload} {P : Params}
variable {upd : UpdateRule R} {C₀ : Config Validator} {U : R.Universe} {V : R.View U}

/-- The schedule of configuration `k`. -/
abbrev SegRun.sched {K : ℕ} (Rn : SegRun R P upd C₀ U V K) (k : ℕ) : Slots Validator :=
  (Rn.cfg k).sched

/-- **The verdicts configuration `k`'s update rule is handed**: the span
it decided, `(start k, roundOf (anchor k)]`, and `none` outside. The
`update` field names this function; `spanVdct_agree` is why two
validators name one function. -/
def SegRun.spanOf {K : ℕ} (Rn : SegRun R P upd C₀ U V K) (k : ℕ) : ℕ → Option BlockId :=
  spanVdct (Rn.cfg k) (Rn.start k) ((Rn.cfg k).roundOf (Rn.anchor k)) (Rn.vdct k)

/-- **The output of configuration `k`**: the committed blocks of the
rounds it governs, `(start k, start (k + 1)]`, and not of the rounds
between its boundary and its anchor. Those are decided again under
configuration `k + 1`. -/
def SegRun.rangeLedger {K : ℕ} (Rn : SegRun R P upd C₀ U V K) (k : ℕ) : List BlockId :=
  ledgerOf (Rn.vdct k) ((Rn.cfg k).cum (Rn.start k + 1))
    ((Rn.cfg k).cum (Rn.start (k + 1) + 1))

/-- The ledger through configuration `K' − 1`. -/
def SegRun.ledgerUpto {K : ℕ} (Rn : SegRun R P upd C₀ U V K) (K' : ℕ) : List BlockId :=
  (List.range K').flatMap Rn.rangeLedger

end Adaptive

end LeanDag
