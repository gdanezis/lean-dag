import LeanDag.Node.Model.Timed
import LeanDag.Node.Converge.Statement
import LeanDag.Node.Vote
import Mathlib.Algebra.BigOperators.Intervals
/-!
# The reliable nodes produce rounds and decide — statement

`docs/validator.md` §5, V11. Over a timed trace (`time i` the time of
event `i`) of honest nodes `H` and an adversary, a reliable set `T ⊆ H`
of at least `q` nodes, and a GST `gst`, assume up to a time `t₁`:

* **times do not decrease** (`TimeMono`);
* **delivery** (`DeliveredWithin`): a message one reliable node sends
  another at `t` arrives by `max t gst + Δ`;
* **timers** (`TimersFire`, `TimersAfterSet`): a timer a reliable node
  sets at `t` for `a` ticks fires at `t + a`, and no honest node's timer
  fires earlier than its delay after it was set;
* **synchronisation** (`SyncedWithin`): a reliable node that receives a
  reliable node's block at `t`, at its author's round at `gst` or above,
  holds it on its disk by `max t gst + Δₛ`, having synced its history.
  This is assumed of the syncs, not proved (`docs/validator.md` §5.1);
* every reliable node **starts** by `gst` (`StartedBy`), and does not
  **restart** by `t₁` (`UpFrom` from `0`);
* timely authentication of blocks;
* **no dropping** (`cfg.drops = false`): no node lets go of a block it
  accepted;
* the injective hash, injective on every block, at most `f` nodes
  outside `H`, `n − f − c` reliable nodes, a quorum of two or more, and
  `2 (Δ + Δₛ) < timeout r` at every round.

Then, for `A = Δ + Δₛ`, the time a reliable block and its history take
to be held by every reliable node:

* **production** (`Produces`): past GST, once every reliable node is at
  round `n` or above at `s`, every reliable node is above `n` at
  `s + A + timeout n`;
* **decision** (`Decides`): suppose every reliable node is below a round
  `n₀` at GST, and the slots `b … b + c − 1` at or above `n₀` are
  led by reliable nodes and span the rule's eligibility. Once every
  reliable node is at the decision round of slot `b + c − 1`, `A` later
  every reliable node has output the decisions of every slot below
  `b + c`;
* **the time bound** (`DecidesBy`): under the same premises, if every
  reliable node is at round `n₁` or above at `s ≥ gst`, every reliable
  node has output them by `s + Σ (timeout r + A) + A`, the sum over the
  rounds `r` from `n₁` to below that decision round.

**With crashes** (`Recovers`). Reliable nodes may crash and restart until
a time `t_r`, losing the messages and timers of their outages, and stay
up from `t_r` to `t₁` (`UpFrom`); restarts after `t₁` are not read.
Delivery and synchronisation are assumed only from `t_r` on
(`DeliveredFrom`, `SyncedFrom`), and a timer fires unless its node
restarts before (`TimersFireUp`). Then the three
conclusions hold with GST replaced by `max t_r gst + W`, for `W` twice
the largest timeout of the round below the one a reliable node is at by
`max t_r gst`, the delay of its retry timer: within it every reliable
node sends one of its blocks there again or builds above, and the
history of that block brings the blocks the crashes lost. The honest
nodes outside `T` may crash and restart at any time, and need meet no
timing assumption but that their timers do not fire early. With `T`
every honest node: after every node crashed and restarted, the nodes
decide each reliably led run of slots above the rounds they reached by
then.

**With dropping** (`SyncedHeld`, `Eventually`). For nodes that drop,
synchronisation is assumed only when every block the receiver needs at its
floor, the history of the block from that floor up (`Needs`), is held by a
reliable node at the delivery (`docs/dos-bounds.md`, Phase 3.2 item 4.3).
A steady window (`Steady`) is a stretch over which no node of `T` decides
and each is at the floor at its next undecided slot (`floorAt`) or above.
Over an infinite run (`prefixOf`) whose prefixes meet the assumptions, with
every honest node reliable and reliably led runs beyond every slot, every
honest node's next undecided slot grows without bound (`Eventually`).

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

/-- **Timers fire**: a timer a reliable node sets at `t` for `a` ticks
fires at `t + a`, if that is by `t₁`. -/
def TimersFire (cfg : Config Validator BlockId Payload) (T : Finset Validator)
    (tr : Trace Validator BlockId Payload) (time : ℕ → ℕ) (t₁ : ℕ) : Prop :=
  ∀ i u inp, tr[i]? = some (u, inp) → u ∈ T → ∀ r a, Output.setTimer r a ∈ outputsAt cfg tr i →
    time i + a ≤ t₁ → ∃ j, i < j ∧ tr[j]? = some (u, .timer r) ∧ time j = time i + a

/-- **Timers fire no earlier than set**: every timer a node of `T` is
given was set, no less than its delay before. -/
def TimersAfterSet (cfg : Config Validator BlockId Payload) (T : Finset Validator)
    (tr : Trace Validator BlockId Payload) (time : ℕ → ℕ) : Prop :=
  ∀ j u r, tr[j]? = some (u, .timer r) → u ∈ T →
    ∃ i < j, ∃ a, (tr[i]?.map Prod.fst) = some u ∧ Output.setTimer r a ∈ outputsAt cfg tr i ∧
      time i + a ≤ time j


/-- **Synchronisation within `Δₛ` past GST**: a reliable node `v` given a
reliable author's block at `t`, at the author's round at `gst` or above,
holds it on its disk by `max t gst + Δₛ`. -/
def SyncedWithin (cfg : Config Validator BlockId Payload) (T : Finset Validator)
    (tr : Trace Validator BlockId Payload) (time : ℕ → ℕ) (gst Δₛ t₁ : ℕ) : Prop :=
  ∀ j v u id b, tr[j]? = some (v, .deliver u id b) → v ∈ T → b.creator ∈ T → id = cfg.idOf b →
    topAt cfg tr time b.creator gst ≤ b.round →
    ∀ τ, max (time j) gst + Δₛ ≤ τ → τ ≤ t₁ → id ∈ (stateAt cfg tr time v τ).disk.ids

/-- **The blocks a node at floor `F` needs to accept a block `b`**, under
their hash: the references of `b` if it lies at `F` or above, and the
references of each such block at `F` or above. -/
inductive Needs (cfg : Config Validator BlockId Payload) (F : ℕ)
    (b : Block Validator BlockId Payload) : Block Validator BlockId Payload → Prop
  | ref {x : Block Validator BlockId Payload} : F ≤ b.round → cfg.idOf x ∈ b.refs →
      Needs cfg F b x
  | step {y x : Block Validator BlockId Payload} : Needs cfg F b y → F ≤ y.round →
      cfg.idOf x ∈ y.refs → Needs cfg F b x

/-- **Synchronisation within `Δₛ` past GST from the blocks reliable nodes
hold**, for nodes that drop: as `SyncedWithin`, when every block the
receiver needs at its floor (`Needs`) is on the disk of a reliable node at
the delivery; the receiver then holds the block, or its floor lies above
the block's round. -/
def SyncedHeld (cfg : Config Validator BlockId Payload) (T : Finset Validator)
    (tr : Trace Validator BlockId Payload) (time : ℕ → ℕ) (gst Δₛ t₁ : ℕ) : Prop :=
  ∀ j v u id b, tr[j]? = some (v, .deliver u id b) → v ∈ T → b.creator ∈ T → id = cfg.idOf b →
    topAt cfg tr time b.creator gst ≤ b.round →
    (∀ x, Needs cfg (stateBefore cfg tr j v).floor b x →
      ∃ w ∈ T, cfg.idOf x ∈ (stateBefore cfg tr j w).disk.ids) →
    ∀ τ, max (time j) gst + Δₛ ≤ τ → τ ≤ t₁ →
      id ∈ (stateAt cfg tr time v τ).disk.ids ∨ b.round < (stateAt cfg tr time v τ).floor

/-- **A steady window from `G` to `t₁` at slot `L`**: at every event from `G`
to `t₁`, the next undecided slot of every node of `T` is `L`, and its round
is the floor at slot `L` (`floorAt`) or above. -/
def Steady (cfg : Config Validator BlockId Payload) (T : Finset Validator)
    (tr : Trace Validator BlockId Payload) (time : ℕ → ℕ) (G t₁ L : ℕ) : Prop :=
  ∀ v ∈ T, ∀ k, eventsBy tr time G ≤ k → k ≤ eventsBy tr time t₁ →
    (stateBefore cfg tr k v).lo = L ∧
      floorAt cfg L ≤ (stateBefore cfg tr k v).top.getD 0

/-- **Delivery within `Δ` past GST, from `t_r` on**: a message one
reliable node sends another at a time `t ≥ t_r` arrives by
`max t gst + Δ`, if that is by `t₁`. -/
def DeliveredFrom (cfg : Config Validator BlockId Payload) (T : Finset Validator)
    (tr : Trace Validator BlockId Payload) (time : ℕ → ℕ) (gst Δ t_r t₁ : ℕ) : Prop :=
  ∀ i u inp, tr[i]? = some (u, inp) → u ∈ T → t_r ≤ time i → ∀ m, Sends u (outputsAt cfg tr i) m →
    m.1 ∈ T → max (time i) gst + Δ ≤ t₁ →
      ∃ j, i < j ∧ tr[j]? = some m ∧ time j ≤ max (time i) gst + Δ

/-- **Synchronisation within `Δₛ` past GST, from `t_r` on**: as
`SyncedWithin`, for the blocks a reliable node is given at a time
`t ≥ t_r`, at the author's round at `max t_r gst` or above. -/
def SyncedFrom (cfg : Config Validator BlockId Payload) (T : Finset Validator)
    (tr : Trace Validator BlockId Payload) (time : ℕ → ℕ) (gst Δₛ t_r t₁ : ℕ) : Prop :=
  ∀ j v u id b, tr[j]? = some (v, .deliver u id b) → v ∈ T → b.creator ∈ T → id = cfg.idOf b →
    topAt cfg tr time b.creator (max t_r gst) ≤ b.round → t_r ≤ time j →
      ∀ τ, max (time j) gst + Δₛ ≤ τ → τ ≤ t₁ → id ∈ (stateAt cfg tr time v τ).disk.ids

/-- **Timers fire unless the node restarts**: a timer a reliable node sets
at `t` for `a` ticks fires at `t + a`, if that is by `t₁` and the node
does not restart by then. -/
def TimersFireUp (cfg : Config Validator BlockId Payload) (T : Finset Validator)
    (tr : Trace Validator BlockId Payload) (time : ℕ → ℕ) (t₁ : ℕ) : Prop :=
  ∀ i u inp, tr[i]? = some (u, inp) → u ∈ T → ∀ r a, Output.setTimer r a ∈ outputsAt cfg tr i →
    time i + a ≤ t₁ → (∀ k, i < k → time k ≤ time i + a → tr[k]? ≠ some (u, .restart)) →
      ∃ j, i < j ∧ tr[j]? = some (u, .timer r) ∧ time j = time i + a

/-- **Up from `t_r` to `t₁`**: no reliable node restarts at or after `t_r`
and at or before `t₁`. -/
def UpFrom (T : Finset Validator) (tr : Trace Validator BlockId Payload) (time : ℕ → ℕ)
    (t_r t₁ : ℕ) : Prop :=
  ∀ k v, tr[k]? = some (v, .restart) → v ∈ T → time k ≤ t₁ → time k < t_r

/-- **Every reliable node starts by `gst`.** -/
def StartedBy (T : Finset Validator) (tr : Trace Validator BlockId Payload) (time : ℕ → ℕ)
    (gst : ℕ) : Prop :=
  ∀ v ∈ T, ∃ i, tr[i]? = some (v, .start) ∧ time i ≤ gst

/-- **The evidence spreads**, for a set `D` and a round `nE`: every author
that evidence in a block the honest nodes knew names, or with two blocks
of a round among those blocks, is in `D`; and an honest node that persists
a block above round `nE` has convicted every author of `D` before that
event. -/
def Spread (cfg : Config Validator BlockId Payload) (H : Finset Validator)
    (tr : Trace Validator BlockId Payload) (D : Finset Validator) (nE : ℕ) : Prop :=
  (∀ y ∈ Converge.knownIn cfg H tr, ∀ e ∈ cfg.xp.ev y.2.payload, e.2.1 ≠ e.2.2 → e.1 ∈ D) ∧
  (∀ y ∈ Converge.knownIn cfg H tr, ∀ z ∈ Converge.knownIn cfg H tr, y.1 ≠ z.1 →
    y.2.creator = z.2.creator → y.2.round = z.2.round → y.2.creator ∈ D) ∧
  ∀ j v inp, tr[j]? = some (v, inp) → v ∈ H → ∀ e ∈ persists (outputsAt cfg tr j),
    nE < e.2.round → D ⊆ (stateBefore cfg tr j v).detected

/-- **Production**: past GST, once every reliable node is at round `n` or
above at `s`, every reliable node is above `n` at `s + D + timeout n`. -/
def Produces (cfg : Config Validator BlockId Payload) (T : Finset Validator)
    (tr : Trace Validator BlockId Payload) (time : ℕ → ℕ) (gst D t₁ : ℕ) : Prop :=
  ∀ s n, gst ≤ s → s + D + cfg.timeout n ≤ t₁ → (∀ v ∈ T, n ≤ topAt cfg tr time v s) →
    ∀ v ∈ T, n + 1 ≤ topAt cfg tr time v (s + D + cfg.timeout n)

/-- **Decision**: if every reliable node is below round `n₀` at
`gst`, and the slots `b … b + c − 1`, at or above `n₀`, are led by
reliable nodes and span the rule's eligibility, then once every reliable
node is at the decision round of slot `b + c − 1` at `t`, every reliable
node has output the decisions of the slots below `b + c` by `t + D`. -/
def Decides (cfg : Config Validator BlockId Payload) (T : Finset Validator)
    (tr : Trace Validator BlockId Payload) (time : ℕ → ℕ) (gst D t₁ : ℕ) : Prop :=
  letI := cfg.slots
  ∀ b c n₀, 0 < c → (Scheme.schemeAnchored cfg.p
      (boundedSel (BlockId := BlockId) (Payload := Payload) (P := ValidAt cfg.q Clause.none)
        (honest := T))).SpansEligible c →
    (∀ i < c, cfg.slots.leader (b + i) ∈ T) → n₀ ≤ cfg.slots.slotRound b →
    (∀ v ∈ T, topAt cfg tr time v gst < n₀) →
    ∀ t, (∀ v ∈ T, cfg.slots.slotRound (b + c - 1) + (cfg.p.waveLength - 1) ≤
        topAt cfg tr time v t) → t + D ≤ t₁ →
      ∀ v ∈ T, b + c ≤ (decisionsBy cfg tr time v (t + D)).length

/-- **Decision by a time bound**: under the premises of `Decides`, if every
reliable node is at round `n₁` or above at `s ≥ gst`, every reliable node
has output the decisions of the slots below `b + c` by
`s + Σ (timeout r + D) + D`, the sum over the rounds `r` from `n₁` to
below the decision round of slot `b + c − 1`. -/
def DecidesBy (cfg : Config Validator BlockId Payload) (T : Finset Validator)
    (tr : Trace Validator BlockId Payload) (time : ℕ → ℕ) (gst D t₁ : ℕ) : Prop :=
  letI := cfg.slots
  ∀ b c n₀ n₁ s, 0 < c → (Scheme.schemeAnchored cfg.p
      (boundedSel (BlockId := BlockId) (Payload := Payload) (P := ValidAt cfg.q Clause.none)
        (honest := T))).SpansEligible c →
    (∀ i < c, cfg.slots.leader (b + i) ∈ T) → n₀ ≤ cfg.slots.slotRound b →
    (∀ v ∈ T, topAt cfg tr time v gst < n₀) → gst ≤ s →
    (∀ v ∈ T, n₁ ≤ topAt cfg tr time v s) →
    s + (∑ r ∈ Finset.Ico n₁ (cfg.slots.slotRound (b + c - 1) + (cfg.p.waveLength - 1)),
      (cfg.timeout r + D)) + D ≤ t₁ →
    ∀ v ∈ T, b + c ≤ (decisionsBy cfg tr time v (s + (∑ r ∈ Finset.Ico n₁
      (cfg.slots.slotRound (b + c - 1) + (cfg.p.waveLength - 1)), (cfg.timeout r + D)) + D)).length

/-- **The reliable nodes produce rounds and decide**, over a timed trace
meeting the assumptions up to `t₁`. -/
def Progresses : Prop :=
  ∀ (Validator BlockId Payload : Type) [Fintype Validator] [DecidableEq Validator]
    [LinearOrder BlockId] (cfg : Config Validator BlockId Payload) (H T : Finset Validator)
    (tr : Trace Validator BlockId Payload) (time : ℕ → ℕ) (gst Δ Δₛ t₁ : ℕ)
    (D : Finset Validator) (nE : ℕ),
    cfg.σ = boundedSel → cfg.Admissible → cfg.Faithful → Hᶜ.card ≤ cfg.f → T ⊆ H →
    cfg.q ≤ T.card → Fintype.card Validator - cfg.f - cfg.c ≤ T.card → 2 ≤ cfg.q →
    Function.Injective cfg.idOf → (∀ r, 2 * (Δ + Δₛ) < cfg.timeout r) →
    Converge.TimelyAuthentic cfg H tr → Converge.HashInjective cfg H tr →
    Converge.EvidenceAuthentic cfg H tr → cfg.drops = false → TimeMono tr time →
    Spread cfg H tr D nE → (∀ v ∈ T, nE ≤ topAt cfg tr time v gst) →
    DeliveredWithin cfg T tr time gst Δ t₁ →
    TimersFire cfg T tr time t₁ → TimersAfterSet cfg H tr time →
    SyncedWithin cfg T tr time gst Δₛ t₁ → StartedBy T tr time gst → UpFrom T tr time 0 t₁ →
    Produces cfg T tr time gst (Δ + Δₛ) t₁ ∧ Decides cfg T tr time gst (Δ + Δₛ) t₁ ∧
      DecidesBy cfg T tr time gst (Δ + Δₛ) t₁

/-- **The reliable nodes recover from crashes**: over a timed trace in
which the reliable nodes stay up from `t_r` to `t₁`, meeting the
assumptions from `t_r` on, they produce rounds and decide past
`max t_r gst + W`, for `W` twice the largest timeout of the round below
the one a reliable node is at by `max t_r gst`. -/
def Recovers : Prop :=
  ∀ (Validator BlockId Payload : Type) [Fintype Validator] [DecidableEq Validator]
    [LinearOrder BlockId] (cfg : Config Validator BlockId Payload) (H T : Finset Validator)
    (tr : Trace Validator BlockId Payload) (time : ℕ → ℕ) (gst Δ Δₛ t_r t₁ : ℕ)
    (D : Finset Validator) (nE : ℕ),
    cfg.σ = boundedSel → cfg.Admissible → cfg.Faithful → Hᶜ.card ≤ cfg.f → T ⊆ H →
    cfg.q ≤ T.card → Fintype.card Validator - cfg.f - cfg.c ≤ T.card → 2 ≤ cfg.q →
    Function.Injective cfg.idOf → (∀ r, 2 * (Δ + Δₛ) < cfg.timeout r) →
    Converge.TimelyAuthentic cfg H tr → Converge.HashInjective cfg H tr →
    Converge.EvidenceAuthentic cfg H tr → cfg.drops = false → TimeMono tr time →
    Spread cfg H tr D nE → (∀ v ∈ T, nE ≤ topAt cfg tr time v (max t_r gst)) →
    DeliveredFrom cfg T tr time gst Δ t_r t₁ → TimersFireUp cfg T tr time t₁ →
    TimersAfterSet cfg H tr time → SyncedFrom cfg T tr time gst Δₛ t_r t₁ →
    UpFrom T tr time t_r t₁ → StartedBy T tr time gst →
    let G := max t_r gst +
      T.sup fun u => 2 * cfg.timeout (topAt cfg tr time u (max t_r gst) - 1)
    Produces cfg T tr time G (Δ + Δₛ) t₁ ∧ Decides cfg T tr time G (Δ + Δₛ) t₁ ∧
      DecidesBy cfg T tr time G (Δ + Δₛ) t₁

/-- **The first `N` events of an infinite run.** -/
def prefixOf (ev : ℕ → Validator × Input Validator BlockId Payload) (N : ℕ) :
    Trace Validator BlockId Payload :=
  (List.range N).map ev

/-- **The reliable nodes' next undecided slots grow without bound, with
dropping**: over an infinite run whose events are timed without decrease
and without bound, every prefix of which meets the assumptions of V11 up to
a time before its end, with synchronisation from the blocks reliable nodes
hold (`SyncedHeld`) in place of `SyncedWithin`, every honest node reliable,
skip and commit thresholds above `f`, and
runs of `c` slots led by honest nodes, spanning the rule's eligibility,
beyond every slot: for every slot `k`, after some number of events every
honest node is past `k`. -/
def Eventually : Prop :=
  ∀ (Validator BlockId Payload : Type) [Fintype Validator] [DecidableEq Validator]
    [LinearOrder BlockId] [Infinite BlockId] (cfg : Config Validator BlockId Payload)
    (H : Finset Validator) (ev : ℕ → Validator × Input Validator BlockId Payload)
    (time : ℕ → ℕ) (gst Δ Δₛ c : ℕ) (D : Finset Validator) (nE : ℕ),
    letI := cfg.slots
    cfg.σ = boundedSel → cfg.Admissible → cfg.Faithful → Hᶜ.card ≤ cfg.f → cfg.q ≤ H.card →
    Fintype.card Validator - cfg.f - cfg.c ≤ H.card → 2 ≤ cfg.q →
    cfg.f < cfg.p.skipThreshold → cfg.f < cfg.p.commitThreshold →
    Function.Injective cfg.idOf → (∀ r, 2 * (Δ + Δₛ) < cfg.timeout r) → cfg.drops = true →
    Monotone time → (∀ t, ∃ N, t < time N) →
    0 < c → (Scheme.schemeAnchored cfg.p
      (boundedSel (BlockId := BlockId) (Payload := Payload) (P := ValidAt cfg.q Clause.none)
        (honest := H))).SpansEligible c → FairRunOn H c →
    (∀ N, Converge.TimelyAuthentic cfg H (prefixOf ev N) ∧
      Converge.HashInjective cfg H (prefixOf ev N) ∧
      Converge.EvidenceAuthentic cfg H (prefixOf ev N) ∧ Spread cfg H (prefixOf ev N) D nE ∧
      TimersAfterSet cfg H (prefixOf ev N) time) →
    (∀ N t₁, t₁ < time N → DeliveredWithin cfg H (prefixOf ev N) time gst Δ t₁ ∧
      TimersFire cfg H (prefixOf ev N) time t₁ ∧ SyncedHeld cfg H (prefixOf ev N) time gst Δₛ t₁ ∧
      UpFrom H (prefixOf ev N) time 0 t₁) →
    (∀ N, gst < time N → StartedBy H (prefixOf ev N) time gst ∧
      ∀ v ∈ H, nE ≤ topAt cfg (prefixOf ev N) time v gst) →
    ∀ k, ∃ N, ∀ v ∈ H, k < (stateBefore cfg (prefixOf ev N) N v).lo

/-- The reliable nodes' liveness, without crashes and with them, and with
dropping. -/
def Statement : Prop := Progresses ∧ Recovers ∧ Eventually

end Live

end Node

end LeanDag
