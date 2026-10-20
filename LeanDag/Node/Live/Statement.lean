import LeanDag.Node.Model.Timed
import LeanDag.Node.Converge.Statement
import LeanDag.Node.Vote
/-!
# The reliable nodes produce rounds and decide — statement

`docs/validator.md` §13, V11. Over a timed trace (`time i` the time of
event `i`) of honest nodes `H` and an adversary, a reliable set `T ⊆ H`
of at least `q` nodes, and a GST `gst`, assume up to a time `t₁`:

* **times do not decrease** (`TimeMono`);
* **delivery** (`DeliveredWithin`): a message one reliable node sends
  another at `t` arrives by `max t gst + Δ`;
* **timers** (`TimersOnTime`): a timer a reliable node sets at `t` for
  `a` ticks fires at `t + a`, and none fires earlier;
* **synchronisation** (`SyncedWithin`): a reliable node that receives a
  reliable node's block at `t` has received, by `max t gst + Δₛ`, each
  block of its history at or above its horizon that it did not make;
  efficient synchronisation is out of scope (`docs/validator.md` §1);
* every reliable node **starts** by `gst` (`StartedBy`), and none
  restarts or is offered a base or a certificate;
* timely authentication, the injective hash, no rate limiting, at most
  `f` nodes outside `H`, `n − f − c` reliable nodes, and
  `2 (Δ + Δₛ) ≤ timeout r` at every round.

Then:

* **production** (`Produces`): past GST, once every reliable node is at
  round `n` or above, every reliable node is above `n` a timeout later;
* **decision** (`Decides`): suppose the reliable nodes built some round
  `n₀` past GST within `Δ + Δₛ` of each other, and the slots
  `b … b + c − 1` at or above `n₀` are led by reliable nodes and span
  the rule's eligibility. Once every reliable node is at the decision
  round of slot `b + c − 1`, `Δ + Δₛ` later every reliable node has
  output the decisions of every slot below `b + c`.

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
node is given was set, no less than its delay before. -/
def TimersOnTime (cfg : Config Validator BlockId Payload) (T : Finset Validator)
    (tr : Trace Validator BlockId Payload) (time : ℕ → ℕ) (t₁ : ℕ) : Prop :=
  (∀ i u inp, tr[i]? = some (u, inp) → u ∈ T → ∀ r a, Output.setTimer r a ∈ outputsAt cfg tr i →
      time i + a ≤ t₁ → ∃ j, i < j ∧ tr[j]? = some (u, .timer r) ∧ time j = time i + a) ∧
    ∀ j u r, tr[j]? = some (u, .timer r) → u ∈ T →
      ∃ i < j, ∃ a, (tr[i]?.map Prod.fst) = some u ∧ Output.setTimer r a ∈ outputsAt cfg tr i ∧
        time i + a ≤ time j

/-- **Synchronisation within `Δₛ` past GST**: a reliable node `v` given
a reliable author's block at `t` is given, by `max t gst + Δₛ`, each
block of the history the author broadcast it with, at or above `v`'s
horizon then, that `v` did not make. -/
def SyncedWithin (cfg : Config Validator BlockId Payload) (T : Finset Validator)
    (tr : Trace Validator BlockId Payload) (time : ℕ → ℕ) (gst Δₛ t₁ : ℕ) : Prop :=
  ∀ j v id b, tr[j]? = some (v, .deliver id b) → v ∈ T → b.creator ∈ T →
    max (time j) gst + Δₛ ≤ t₁ →
    ∀ i, (tr[i]?.map Prod.fst) = some b.creator → (id, b) ∈ broadcasts (outputsAt cfg tr i) →
      let st := (stateBefore cfg tr (i + 1) b.creator).store
      ∀ y ∈ historyFrom st.blk id,
        horAt cfg tr time v (max (time j) gst + Δₛ) ≤ (st.blk y).round → (st.blk y).creator ≠ v →
        ∃ k, tr[k]? = some (v, .deliver y (st.map.getD y st.junk)) ∧
          time k ≤ max (time j) gst + Δₛ

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

/-- **Decision**: if every reliable node built round `n₀` between `s ≥ gst`
and `s + D`, and the slots `b … b + c − 1`, at or above `n₀`, are led by
reliable nodes and span the rule's eligibility, then once every reliable
node is at the decision round of slot `b + c − 1` at `t`, every reliable
node has output the decisions of the slots below `b + c` by `t + D`. -/
def Decides (cfg : Config Validator BlockId Payload) (T : Finset Validator)
    (tr : Trace Validator BlockId Payload) (time : ℕ → ℕ) (gst D t₁ : ℕ) : Prop :=
  letI := cfg.slots
  ∀ b c n₀ s, 0 < c → (Scheme.schemeAnchored cfg.p
      (boundedSel (BlockId := BlockId) (Payload := Payload) (P := ValidAt cfg.q Clause.none)
        (honest := T))).SpansEligible c →
    (∀ i < c, cfg.slots.leader (b + i) ∈ T) → n₀ ≤ cfg.slots.slotRound b → gst ≤ s →
    (∀ v ∈ T, n₀ ≤ topAt cfg tr time v (s + D) ∧ s ≤ builtAt cfg tr time v n₀ ∧
      builtAt cfg tr time v n₀ ≤ s + D) →
    ∀ t, (∀ v ∈ T, cfg.slots.slotRound (b + c - 1) + (cfg.p.waveLength - 1) ≤
        topAt cfg tr time v t) → t + D ≤ t₁ →
      ∀ v ∈ T, b + c ≤ (decisionsBy cfg tr time v (t + D)).length

/-- **The reliable nodes produce rounds and decide**, over a timed trace
meeting the assumptions up to `t₁`. -/
def Progresses : Prop :=
  ∀ (Validator BlockId Payload : Type) [Fintype Validator] [DecidableEq Validator]
    [LinearOrder BlockId] (cfg : Config Validator BlockId Payload) (H T : Finset Validator)
    (tr : Trace Validator BlockId Payload) (time : ℕ → ℕ) (gst Δ Δₛ t₁ : ℕ),
    cfg.σ = boundedSel → cfg.Admissible → cfg.limit = none → Hᶜ.card ≤ cfg.f → T ⊆ H →
    cfg.q ≤ T.card → Fintype.card Validator - cfg.f - cfg.c ≤ T.card →
    (∀ r, 2 * (Δ + Δₛ) ≤ cfg.timeout r) →
    Converge.TimelyAuthentic cfg H tr → Converge.HashInjective cfg H tr →
    Converge.NoRestart T tr → Converge.NoRejoin T tr →
    TimeMono tr time → DeliveredWithin cfg T tr time gst Δ t₁ → TimersOnTime cfg T tr time t₁ →
    SyncedWithin cfg T tr time gst Δₛ t₁ → StartedBy T tr time gst →
    Produces cfg T tr time gst t₁ ∧ Decides cfg T tr time gst (Δ + Δₛ) t₁

/-- The reliable nodes' liveness. -/
def Statement : Prop := Progresses

end Live

end Node

end LeanDag
