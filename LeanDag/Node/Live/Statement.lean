import LeanDag.Node.Model.Timed
import LeanDag.Node.Converge.Statement
import LeanDag.Node.Boot.Statement
import LeanDag.Node.Vote
import Mathlib.Algebra.BigOperators.Intervals
/-!
# The reliable nodes produce rounds and decide — statement

`docs/validator.md` §13, V11. Over a timed trace (`time i` the time of
event `i`) of honest nodes `H` and an adversary, a reliable set `T ⊆ H`
of at least `q` nodes, and a GST `gst`, assume up to a time `t₁`:

* **times do not decrease** (`TimeMono`);
* **delivery** (`DeliveredWithin`): a message one reliable node sends
  another at `t` arrives by `max t gst + Δ`;
* **timers** (`TimersOnTime`): a timer a reliable node sets at `t` for
  `a` ticks fires at `t + a`, none fires earlier, and each setting fires
  once;
* **synchronisation** (`SyncedWithin`): a reliable node that receives a
  reliable node's block at `t` receives after it, by `max t gst + Δₛ`,
  each block the honest nodes know in its history at or above its
  horizon that it did not make. Efficient synchronisation is out of scope
  (`docs/validator.md` §1);
* every reliable node **starts** by `gst` (`StartedBy`) and none
  restarts; and none is stalled twice at a timer by `gst + 3Δ + Δₛ`
  (`NoStallBy`): before then the network may strand a node below its
  peers' horizon, and the claim does not cover its recovery;
* timely authentication, of blocks, certificates and the chain's hash,
  since honest nodes outside `T` may rejoin (as for V9);
* the injective hash, injective on every block, no rate limiting, at
  most `f` nodes outside `H`, `n − f − c` reliable nodes, a quorum of two
  or more that holds a reliable node (`n < q + |T|`), so that a
  certificate rests on a reliable store, `2 (3Δ + Δₛ) < timeout r` at
  every round, and a horizon lag
  `Λ` no smaller than the vote offset, so that the leader blocks a node's
  reach and certificate tests read lie at or above its horizon.

Then, for `A = 3Δ + Δₛ`, the time a reliable block and its history take
to be held by every reliable node, a certificate's catch-up included:

* **production** (`Produces`): past GST, once every reliable node is at
  round `n` or above, every reliable node is above `n` a timeout later;
* **decision** (`Decides`): suppose the reliable nodes built some round
  `n₀` past GST within `A` of each other, agreeing from then on which
  authors they exclude for equivocating (`ExposedFrom`; a node relays the
  evidence, so this holds once every exposure has spread), and the slots
  `b … b + c − 1` at or above `n₀` are led by reliable nodes and span the
  rule's eligibility. Once every reliable node is at the decision round of slot
  `b + c − 1`, `A` later every reliable node has output the decisions of
  every slot below `b + c`;
* **the time bound** (`DecidesBy`): under the same premises, every
  reliable node has output them by `s + A + Σ timeout r + A`, the sum
  over the rounds `r` from `n₀` to below that decision round.

Statements only; the proofs are `Proof.lean`.
-/

namespace LeanDag

namespace Node

namespace Live

variable {Validator BlockId Payload : Type} [Fintype Validator] [DecidableEq Validator]
variable [LinearOrder BlockId]

/-- **Times do not decrease** along the trace. -/
def TimeMono (tr : Trace Validator BlockId Payload) (time : ℕ → ℕ) : Prop :=
  ∀ i j, i ≤ j → j < tr.length → time i ≤ time j

/-- **Delivery within `Δ` past GST**: a message one reliable node sends
another at `t` arrives by `max t gst + Δ`, if that is by `t₁`. -/
def DeliveredWithin (cfg : Config Validator BlockId Payload) (T : Finset Validator)
    (tr : Trace Validator BlockId Payload) (time : ℕ → ℕ) (gst Δ t₁ : ℕ) : Prop :=
  ∀ i u inp, tr[i]? = some (u, inp) → u ∈ T → ∀ m, Sends u (outputsAt cfg tr i) m → m.1 ∈ T →
    max (time i) gst + Δ ≤ t₁ → ∃ j, i < j ∧ tr[j]? = some m ∧ time j ≤ max (time i) gst + Δ

/-- **Timers fire on time**: a timer a reliable node sets at `t` for `a`
ticks fires at `t + a`, if that is by `t₁`; and every timer a reliable
node is given was set, no less than its delay before, and has not fired
since. -/
def TimersOnTime (cfg : Config Validator BlockId Payload) (T : Finset Validator)
    (tr : Trace Validator BlockId Payload) (time : ℕ → ℕ) (t₁ : ℕ) : Prop :=
  (∀ i u inp, tr[i]? = some (u, inp) → u ∈ T → ∀ r a, Output.setTimer r a ∈ outputsAt cfg tr i →
      time i + a ≤ t₁ → ∃ j, i < j ∧ tr[j]? = some (u, .timer r) ∧ time j = time i + a) ∧
    ∀ j u r, tr[j]? = some (u, .timer r) → u ∈ T →
      ∃ i < j, ∃ a, (tr[i]?.map Prod.fst) = some u ∧ Output.setTimer r a ∈ outputsAt cfg tr i ∧
        time i + a ≤ time j ∧ ∀ k, i < k → k < j → tr[k]? ≠ some (u, .timer r)

open Classical in
/-- **The block the honest nodes know under an identifier**, the genesis
block under one they know none under. -/
noncomputable def knownBlock (cfg : Config Validator BlockId Payload) (H : Finset Validator)
    (tr : Trace Validator BlockId Payload) (j : BlockId) : Block Validator BlockId Payload :=
  if h : ∃ x ∈ Converge.knownIn cfg H tr, x.1 = j then (Classical.choose h).2 else cfg.genesis

/-- **Synchronisation within `Δₛ` past GST**: a reliable node `v` given
a reliable author's block at `t` is given after it, by `max t gst + Δₛ`,
each block the honest nodes `H` know that the block reaches through the
blocks they know, at or above `v`'s horizon then, that `v` did not make. -/
def SyncedWithin (cfg : Config Validator BlockId Payload) (H T : Finset Validator)
    (tr : Trace Validator BlockId Payload) (time : ℕ → ℕ) (gst Δₛ t₁ : ℕ) : Prop :=
  ∀ j v id b, tr[j]? = some (v, .deliver id b) → v ∈ T → b.creator ∈ T → id = cfg.idOf b →
    max (time j) gst + Δₛ ≤ t₁ → ∀ x ∈ Converge.knownIn cfg H tr,
      ReachesFrom (knownBlock cfg H tr) id x.1 →
      horAt cfg tr time v (max (time j) gst + Δₛ) ≤ x.2.round → x.2.creator ≠ v →
      ∃ k, j < k ∧ tr[k]? = some (v, .deliver x.1 x.2) ∧ time k ≤ max (time j) gst + Δₛ

/-- **No reliable node stalls twice by `τ`**: no timer at or before `τ`
finds a reliable node stalled at the timer's round a second time. -/
def NoStallBy (cfg : Config Validator BlockId Payload) (T : Finset Validator)
    (tr : Trace Validator BlockId Payload) (time : ℕ → ℕ) (τ : ℕ) : Prop :=
  ∀ i v r, v ∈ T → tr[i]? = some (v, .timer r) → time i ≤ τ →
    stallsTwice (cfg.at v) (stateBefore cfg tr i v) r = false

/-- **Every reliable node starts by `gst`.** -/
def StartedBy (T : Finset Validator) (tr : Trace Validator BlockId Payload) (time : ℕ → ℕ)
    (gst : ℕ) : Prop :=
  ∀ v ∈ T, ∃ i, tr[i]? = some (v, .start) ∧ time i ≤ gst

/-- **Production**: past GST, once every reliable node is at round `n` or
above at `s`, every reliable node is above `n` at `s + timeout n`. -/
def Produces (cfg : Config Validator BlockId Payload) (T : Finset Validator)
    (tr : Trace Validator BlockId Payload) (time : ℕ → ℕ) (gst t₁ : ℕ) : Prop :=
  ∀ s n, gst ≤ s → s + cfg.timeout n ≤ t₁ → (∀ v ∈ T, n ≤ topAt cfg tr time v s) →
    ∀ v ∈ T, n + 1 ≤ topAt cfg tr time v (s + cfg.timeout n)

/-- **The reliable nodes agree on the exposed authors from `s` on**: after
every event at `s` or later, each reliable node holds the same authors
exposed. -/
def ExposedFrom (cfg : Config Validator BlockId Payload) (T : Finset Validator)
    (tr : Trace Validator BlockId Payload) (time : ℕ → ℕ) (s : ℕ) : Prop :=
  ∃ X : Finset Validator, ∀ v ∈ T, ∀ k < tr.length, s ≤ time k →
    (stateBefore cfg tr (k + 1) v).exposed = X

/-- **Decision**: if every reliable node built round `n₀` between `s ≥ gst`
and `s + D`, agreeing from `s` on which authors are exposed, and the
slots `b … b + c − 1`, at or above `n₀`, are led by reliable nodes and
span the rule's eligibility, then once every reliable node is at the
decision round of slot `b + c − 1` at `t`, every reliable node has
output the decisions of the slots below `b + c` by `t + D`. -/
def Decides (cfg : Config Validator BlockId Payload) (T : Finset Validator)
    (tr : Trace Validator BlockId Payload) (time : ℕ → ℕ) (gst D t₁ : ℕ) : Prop :=
  letI := cfg.slots
  ∀ b c n₀ s, 0 < c → (Scheme.schemeAnchored cfg.p
      (boundedSel (BlockId := BlockId) (Payload := Payload) (P := ValidAt cfg.q Clause.none)
        (honest := T))).SpansEligible c →
    (∀ i < c, cfg.slots.leader (b + i) ∈ T) → n₀ ≤ cfg.slots.slotRound b → gst ≤ s →
    (∀ v ∈ T, n₀ ≤ topAt cfg tr time v (s + D) ∧ s ≤ builtAt cfg tr time v n₀ ∧
      builtAt cfg tr time v n₀ ≤ s + D) → ExposedFrom cfg T tr time s →
    ∀ t, (∀ v ∈ T, cfg.slots.slotRound (b + c - 1) + (cfg.p.waveLength - 1) ≤
        topAt cfg tr time v t) → t + D ≤ t₁ →
      ∀ v ∈ T, b + c ≤ (decisionsBy cfg tr time v (t + D)).length

/-- **Decision by a time bound**: under the premises of `Decides`, every
reliable node has output the decisions of the slots below `b + c` by
`s + D + Σ timeout r + D`, the sum over the rounds `r` from `n₀` to below
the decision round of slot `b + c − 1`. -/
def DecidesBy (cfg : Config Validator BlockId Payload) (T : Finset Validator)
    (tr : Trace Validator BlockId Payload) (time : ℕ → ℕ) (gst D t₁ : ℕ) : Prop :=
  letI := cfg.slots
  ∀ b c n₀ s, 0 < c → (Scheme.schemeAnchored cfg.p
      (boundedSel (BlockId := BlockId) (Payload := Payload) (P := ValidAt cfg.q Clause.none)
        (honest := T))).SpansEligible c →
    (∀ i < c, cfg.slots.leader (b + i) ∈ T) → n₀ ≤ cfg.slots.slotRound b → gst ≤ s →
    (∀ v ∈ T, n₀ ≤ topAt cfg tr time v (s + D) ∧ s ≤ builtAt cfg tr time v n₀ ∧
      builtAt cfg tr time v n₀ ≤ s + D) → ExposedFrom cfg T tr time s →
    s + D + (∑ r ∈ Finset.Ico n₀ (cfg.slots.slotRound (b + c - 1) + (cfg.p.waveLength - 1)),
      cfg.timeout r) + D ≤ t₁ →
    ∀ v ∈ T, b + c ≤ (decisionsBy cfg tr time v (s + D + (∑ r ∈ Finset.Ico n₀
      (cfg.slots.slotRound (b + c - 1) + (cfg.p.waveLength - 1)), cfg.timeout r) + D)).length

/-- **The reliable nodes produce rounds and decide**, over a timed trace
meeting the assumptions up to `t₁`. -/
def Progresses : Prop :=
  ∀ (Validator BlockId Payload : Type) [Fintype Validator] [DecidableEq Validator]
    [LinearOrder BlockId] (cfg : Config Validator BlockId Payload) (H T : Finset Validator)
    (tr : Trace Validator BlockId Payload) (time : ℕ → ℕ) (gst Δ Δₛ t₁ : ℕ),
    cfg.σ = boundedSel → cfg.Admissible → Hᶜ.card ≤ cfg.f → T ⊆ H →
    cfg.q ≤ T.card → Fintype.card Validator - cfg.f - cfg.c ≤ T.card →
    Fintype.card Validator < cfg.q + T.card → 2 ≤ cfg.q →
    Function.Injective cfg.idOf → cfg.p.voteOffset ≤ cfg.lag →
    (∀ r, 2 * (3 * Δ + Δₛ) < cfg.timeout r) →
    Converge.TimelyAuthentic cfg H tr → Boot.TimelyCerts cfg H tr →
    Converge.HashInjective cfg H tr → Boot.ChainInjective cfg H tr → Converge.NoRestart T tr →
    NoStallBy cfg T tr time (gst + (3 * Δ + Δₛ)) → TimeMono tr time →
    DeliveredWithin cfg T tr time gst Δ t₁ →
    TimersOnTime cfg T tr time t₁ → SyncedWithin cfg H T tr time gst Δₛ t₁ →
    StartedBy T tr time gst →
    Produces cfg T tr time gst t₁ ∧ Decides cfg T tr time gst (3 * Δ + Δₛ) t₁ ∧
      DecidesBy cfg T tr time gst (3 * Δ + Δₛ) t₁

/-- The reliable nodes' liveness. -/
def Statement : Prop := Progresses

end Live

end Node

end LeanDag
