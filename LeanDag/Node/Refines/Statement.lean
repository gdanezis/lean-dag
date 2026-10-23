import LeanDag.Node.Live.Statement
import LeanDag.Scheme.Model.Reactive
import LeanDag.Scheme.Model.TryDecide
/-!
# The node refines the scheme — statement

`docs/validator.md` §5, V12. Over a trace of honest nodes `H` and an
adversary, with timely authentication, the hash injective on what the
honest nodes knew, and at most `f` nodes outside `H`, there is a block
record `U` at quorum `q` whose honest set is `H`, the run's record, such
that:

* **holdings** (`Holds`): every honest node's disk, before every event, is
  a cut of `U`;
* **decisions** (`Loops`): every honest node's decisions before every
  event are none, or the scheme's loop `tryDecide` from slot `0` on a view
  of `U` the node's disk holds.

Over a timed trace meeting the assumptions of `Live.Progresses`, but that
no timer need fire, a reliable set `T` gives, for `A = Δ + Δₛ`:

* **wave facts** (`Waves`): from a round `n₀` above every reliable node's
  round at GST to a round `N` every reliable node has reached at a time
  `t ≥ gst`, with `t + A` within the assumptions, the scheme's
  `WaveFacts` hold on `U`;
* **leaders** (`Leads`): under the premises of `Live.Decides`, `A` after
  every reliable node reached the decision round of slot `b + c − 1`,
  every reliable node has decided each slot `j` of `b … b + c − 1` to a
  leader block `L` of `U`.

With crashes (`Recovering`), under the assumptions of `Live.Recovers`,
the same hold with GST replaced by `max t_r gst + W`.

Statements only; the proofs are `Proof.lean`.
-/

namespace LeanDag

namespace Node

namespace Refines

variable {Validator BlockId Payload : Type} [Fintype Validator] [DecidableEq Validator]
variable [LinearOrder BlockId]

/-- **Holdings**: every honest node's disk, before every event, is a cut
of `U`. -/
def Holds (cfg : Config Validator BlockId Payload) (H : Finset Validator)
    (tr : Trace Validator BlockId Payload)
    (U : BlockRecord Validator BlockId Payload (ValidAt cfg.q Clause.none) H) : Prop :=
  ∀ v ∈ H, ∀ i, ∀ j ∈ (stateBefore cfg tr i v).disk.ids,
    j ∈ U.ids ∧ U.block j = (stateBefore cfg tr i v).disk.blk j

/-- **Decisions**: every honest node's decisions before every event are
none, or the scheme's loop from slot `0` on a view of `U` its disk
holds. -/
def Loops (cfg : Config Validator BlockId Payload) (H : Finset Validator)
    (tr : Trace Validator BlockId Payload)
    (U : BlockRecord Validator BlockId Payload (ValidAt cfg.q Clause.none) H) : Prop :=
  ∀ v ∈ H, ∀ i,
    commitsOf (run (cfg.at v) (State.init (cfg.at v)) (inputsBefore tr i v)).2 = [] ∨
      ∃ (V : U.View) (N : ℕ), V.ids ⊆ (stateBefore cfg tr i v).disk.ids ∧
        commitsOf (run (cfg.at v) (State.init (cfg.at v)) (inputsBefore tr i v)).2 =
          Scheme.tryDecide (S := cfg.slots) cfg.p boundedSel U V 0 N

/-- **Wave facts**: from a round `n₀` above every reliable node's round
at `gst` to a round `N` every reliable node has reached at `t ≥ gst`, with
`t + D ≤ t₁`, the scheme's `WaveFacts` hold on `U`. -/
def Waves (cfg : Config Validator BlockId Payload) {H : Finset Validator}
    (T : Finset Validator) (tr : Trace Validator BlockId Payload) (time : ℕ → ℕ)
    (gst D t₁ : ℕ) (U : BlockRecord Validator BlockId Payload (ValidAt cfg.q Clause.none) H) :
    Prop :=
  letI := cfg.slots
  ∀ n₀ N t, (∀ v ∈ T, topAt cfg tr time v gst < n₀) → gst ≤ t →
    (∀ v ∈ T, N ≤ topAt cfg tr time v t) → t + D ≤ t₁ →
    Scheme.WaveFacts cfg.p boundedSel U T N n₀

/-- **Leaders**: under the premises of `Live.Decides`, by `t + D` every
reliable node has decided each slot `j` of `b … b + c − 1` to a leader
block `L` of `U`. -/
def Leads (cfg : Config Validator BlockId Payload) {H : Finset Validator}
    (T : Finset Validator) (tr : Trace Validator BlockId Payload) (time : ℕ → ℕ)
    (gst D t₁ : ℕ) (U : BlockRecord Validator BlockId Payload (ValidAt cfg.q Clause.none) H) :
    Prop :=
  letI := cfg.slots
  ∀ b c n₀, 0 < c → (Scheme.schemeAnchored cfg.p
      (boundedSel (BlockId := BlockId) (Payload := Payload) (P := ValidAt cfg.q Clause.none)
        (honest := T))).SpansEligible c →
    (∀ i < c, cfg.slots.leader (b + i) ∈ T) → n₀ ≤ cfg.slots.slotRound b →
    (∀ v ∈ T, topAt cfg tr time v gst < n₀) →
    ∀ t, (∀ v ∈ T, cfg.slots.slotRound (b + c - 1) + (cfg.p.waveLength - 1) ≤
        topAt cfg tr time v t) → t + D ≤ t₁ →
      ∀ v ∈ T, ∀ j, b ≤ j → j < b + c → ∃ L, IsLeaderBlock U j L ∧
        (j, some L) ∈ decisionsBy cfg tr time v (t + D)

/-- **Without crashes**: under the assumptions of `Live.Progresses`, but
that no timer need fire, `U` has the wave facts and the leaders. -/
def Timed (cfg : Config Validator BlockId Payload) (H : Finset Validator)
    (tr : Trace Validator BlockId Payload)
    (U : BlockRecord Validator BlockId Payload (ValidAt cfg.q Clause.none) H) : Prop :=
  ∀ (T : Finset Validator) (time : ℕ → ℕ) (gst Δ Δₛ t₁ : ℕ), T ⊆ H →
    cfg.q ≤ T.card → Fintype.card Validator - cfg.f - cfg.c ≤ T.card → 2 ≤ cfg.q →
    Function.Injective cfg.idOf → (∀ r, 2 * (Δ + Δₛ) < cfg.timeout r) →
    Live.TimeMono tr time → Live.DeliveredWithin cfg T tr time gst Δ t₁ →
    Live.TimersAfterSet cfg H tr time → Live.SyncedWithin cfg H T tr time gst Δₛ t₁ →
    Live.StartedBy T tr time gst → Live.UpFrom T tr time 0 →
    Waves cfg T tr time gst (Δ + Δₛ) t₁ U ∧ Leads cfg T tr time gst (Δ + Δₛ) t₁ U

/-- **With crashes**: under the assumptions of `Live.Recovers`, `U` has
the wave facts and the leaders past `max t_r gst + W`. -/
def Recovering (cfg : Config Validator BlockId Payload) (H : Finset Validator)
    (tr : Trace Validator BlockId Payload)
    (U : BlockRecord Validator BlockId Payload (ValidAt cfg.q Clause.none) H) : Prop :=
  ∀ (T : Finset Validator) (time : ℕ → ℕ) (gst Δ Δₛ t_r t₁ : ℕ), T ⊆ H →
    cfg.q ≤ T.card → Fintype.card Validator - cfg.f - cfg.c ≤ T.card → 2 ≤ cfg.q →
    Function.Injective cfg.idOf → (∀ r, 2 * (Δ + Δₛ) < cfg.timeout r) →
    Live.TimeMono tr time → Live.DeliveredFrom cfg T tr time gst Δ t_r t₁ →
    Live.TimersFireUp cfg T tr time t₁ → Live.TimersAfterSet cfg H tr time →
    Live.SyncedFrom cfg H T tr time gst Δₛ t_r t₁ → Live.UpFrom T tr time t_r →
    Live.StartedBy T tr time gst →
    let G := max t_r gst +
      T.sup fun u => 2 * cfg.timeout (topAt cfg tr time u (max t_r gst) - 1)
    Waves cfg T tr time G (Δ + Δₛ) t₁ U ∧ Leads cfg T tr time G (Δ + Δₛ) t₁ U

/-- **The node refines the scheme**: a run has a record on which the
honest nodes' disks are cuts and their decisions the scheme's loop, and
which has the wave facts and the leaders the timing assumptions give. -/
def HasRecord : Prop :=
  ∀ (Validator BlockId Payload : Type) [Fintype Validator] [DecidableEq Validator]
    [LinearOrder BlockId] (cfg : Config Validator BlockId Payload) (H : Finset Validator)
    (tr : Trace Validator BlockId Payload),
    cfg.σ = boundedSel → cfg.Admissible → Hᶜ.card ≤ cfg.f →
    Converge.TimelyAuthentic cfg H tr → Converge.HashInjective cfg H tr →
    ∃ U : BlockRecord Validator BlockId Payload (ValidAt cfg.q Clause.none) H,
      Holds cfg H tr U ∧ Loops cfg H tr U ∧ Timed cfg H tr U ∧ Recovering cfg H tr U

/-- The node refines the scheme. -/
def Statement : Prop := HasRecord

end Refines

end Node

end LeanDag
