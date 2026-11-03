import LeanDag.Node.Converge.Statement
import LeanDag.Node.Live.Statement
/-!
# The run's record, one for each cut — statement

`docs/dos-bounds.md` §5, Phase 3.2. Over a trace with timely authentication,
the hash injective on what the honest nodes knew and injective identifiers,
at the bounded vote of an admissible configuration with at most `f` nodes
outside the honest set `H`, for every round `G` there is a block record `U`
at quorum `q` whose honest set is `H`, such that:

* **holdings** (`Cuts`): the blocks at or above `G` of every honest disk
  whose cut is at most `G`, that is whose next undecided slot's round is at
  most `G + 1`, are blocks of `U`, at the same round and author, and above
  `G` the same blocks, as the disk accepted them;
* **decisions** (`Cuts`): every honest node's decision of a slot whose round
  is `G + 1`, or `0` for `G = 0`, is a verdict on a view of `U`.

So two honest nodes decide each slot alike (`Agrees`), on the record of the
slot's cut alone. Under bypass a disk may hold, at or below its cut, a block
whose bypassed reference no honest node knew, and a node that decides on a
proof takes in blocks below its new cut without their references; the
decisions read only the record of the slot's cut, which need not hold the
history below it.

Statements only; the proofs are `Proof.lean`.
-/

namespace LeanDag

namespace Node

namespace Cut

/-- **One record for each cut.** -/
def Cuts : Prop :=
  ∀ (Validator BlockId Payload : Type) [Fintype Validator] [DecidableEq Validator]
    [LinearOrder BlockId] (cfg : Config Validator BlockId Payload) (H : Finset Validator)
    (tr : Trace Validator BlockId Payload),
    cfg.σ = boundedSel → cfg.Admissible → Hᶜ.card ≤ cfg.f →
    Converge.TimelyAuthentic cfg H tr → Converge.HashInjective cfg H tr →
    Function.Injective cfg.idOf →
    ∀ G, ∃ U : BlockRecord Validator BlockId Payload (ValidAt cfg.q Clause.none) H,
      (∀ v ∈ H, ∀ i, cfg.slots.slotRound (stateBefore cfg tr i v).lo ≤ G + 1 →
        ∀ j ∈ (stateBefore cfg tr i v).disk.ids,
        G ≤ ((stateBefore cfg tr i v).disk.blk j).round →
        j ∈ U.ids ∧ (U.block j).round = ((stateBefore cfg tr i v).disk.blk j).round ∧
          (U.block j).creator = ((stateBefore cfg tr i v).disk.blk j).creator ∧
          (G < ((stateBefore cfg tr i v).disk.blk j).round →
            U.block j = (stateBefore cfg tr i v).disk.full j)) ∧
      ∀ v ∈ H, ∀ i,
        ∀ e ∈ commitsOf (run (cfg.at v) (State.init (cfg.at v)) (inputsBefore tr i v)).2,
          cfg.slots.slotRound e.1 - 1 = G →
          ∃ V : U.View,
            (Scheme.schemeAnchored cfg.p boundedSel).Decided (S := cfg.slots) U V e.1 e.2

/-- **Two honest nodes decide each slot alike**, each on the record of the
slot's cut. -/
def Agrees : Prop :=
  ∀ (Validator BlockId Payload : Type) [Fintype Validator] [DecidableEq Validator]
    [LinearOrder BlockId] (cfg : Config Validator BlockId Payload) (H : Finset Validator)
    (tr : Trace Validator BlockId Payload),
    cfg.σ = boundedSel → cfg.Admissible → Hᶜ.card ≤ cfg.f →
    Converge.TimelyAuthentic cfg H tr → Converge.HashInjective cfg H tr →
    Function.Injective cfg.idOf →
    ∀ v ∈ H, ∀ w ∈ H, ∀ i j,
      ∀ e ∈ commitsOf (run (cfg.at v) (State.init (cfg.at v)) (inputsBefore tr i v)).2,
      ∀ e' ∈ commitsOf (run (cfg.at w) (State.init (cfg.at w)) (inputsBefore tr j w)).2,
        e.1 = e'.1 → e.2 = e'.2

/-- The run's record, one for each cut. -/
def Statement : Prop := Cuts ∧ Agrees

end Cut

end Node

end LeanDag
