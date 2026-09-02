import LeanDag.Barnacle.Helpers.Hydrozoan
import LeanDag.Hydrozoan.Model.Liveness

/-!
# Barnacle over Hydrozoan — statement

The dual-path commit rule under hybrid faults (`LeanDag/Hydrozoan/`;
`docs/hydrozoan.md`) as a base rule with its laws, so that the adaptive
leader count of `LeanDag/Barnacle/` runs over it. The liveness half —
`LiveRule`, `Good` and the descent laws — is P2
(`docs/hydrozoan-integration.md` §13).

**What this instantiation needs, and what it does not.** It reads
Hydrozoan's arc through the block adapter of `Helpers/Hydrozoan.lean`
and nothing else. In particular it needs **neither** the committee
condition `c ≤ k` of `docs/hydrozoan-integration.md` §2 **nor** the
self-parent clause of its §3: `BaseRule.Universe` is an arbitrary type,
so the interface never asks a Hydrozoan universe to be a core one, and
the history layer it does ask for comes from `CausalStructure`, whose
two fields Hydrozoan's own universe supplies. No file of either arc is
modified.

Three points where the instantiation carries Hydrozoan's shape.

* **The universe needs no subtype.** Orcaella's carrier is
  `{U // HonestNoEquiv U}`, because the hybrid model's non-equivocation
  at the wider honest class is a hypothesis its `agree` law has no slot
  for. Hydrozoan states the same condition as a *field* of
  `BlockUniverse`, guarded by `NonByzantine`, so the carrier is the
  universe itself.

* **Two direct routes, one window.** `waveLength` is the number of
  rounds the direct rule reads from a proposal, and Hydrozoan has two
  direct commits at different depths: the fast path reads the propose
  and voting rounds, the slow path also the decision round. The wave is
  therefore three and `DirectCommitIn` is the disjunction. The cost is
  recorded rather than hidden: the leader-count mechanism scores a fast
  commit as occupying a three-round window where it occupies two, which
  makes the window count conservative and never unsound.

* **The payload is `Unit`.** Hydrozoan's blocks carry none, and the
  interface's `block` returns the core's. `adapt` supplies it.

`LinearOrder BlockId` is Hydrozoan's, for the tie-break of the indirect
rule's second rung, and supplies the interface's `DecidableEq` — as in
Orcaella, so that the two cannot diverge.

Statements only; the proofs live in `Proof.lean`.
-/

namespace LeanDag

namespace Barnacle

variable {Replica : Type} [Fintype Replica] [DecidableEq Replica]
variable {BlockId : Type} [LinearOrder BlockId]

/-- **The schedules are one class.** `LeanDag.Slots` and
`LeanDag.Hydrozoan.Slots` carry the same five fields, so the
identification is field-for-field and every component is `rfl`. Stated
here rather than in the helpers because a reader of the instantiation
must see that the rule runs under the schedule the interface hands it,
unchanged. -/
@[reducible]
def slotsOf (S : Slots Replica) : LeanDag.Hydrozoan.Slots Replica where
  slotRound := S.slotRound
  leader := S.leader
  mono := S.mono
  unbounded := S.unbounded
  keyed := S.keyed

/-- **Hydrozoan as a base rule.** The universe is Hydrozoan's own; wave
length three; the direct commit predicate is the disjunction of the two
direct routes, each judged from the view. -/
def hydrozoan [LeanDag.Hydrozoan.Faults Replica] :
    BaseRule Replica BlockId Unit where
  Universe := LeanDag.Hydrozoan.BlockUniverse Replica BlockId
  View := fun U => LeanDag.Hydrozoan.View U
  block := fun U => Hydrozoan.adaptBlk U
  ids := fun U => U.ids
  viewIds := fun V => V.ids
  full := fun U => LeanDag.Hydrozoan.View.full U
  historyView := fun U A hA => Hydrozoan.historyView U A hA
  waveLength := 3
  DirectCommitIn := fun {U} V L r =>
    LeanDag.Hydrozoan.FastCommitInView U V L r ∨ LeanDag.Hydrozoan.SlowCommitInView U V L r
  decDirect := fun _ _ _ => inferInstance
  Decided := fun S {U} V k v =>
    letI := slotsOf S; LeanDag.Hydrozoan.Decided U V k v

namespace Hydrozoan

/-- **Hydrozoan satisfies the laws.** Agreement is HZ3
(`LeanDag.Hydrozoan.SlotAgreement`), which is already quantified over
every universe and every schedule, so the law is that theorem applied.
The remaining six are read off the `View` structure and the `Decided`
constructors. -/
def Laws : Prop :=
  ∀ (Replica BlockId : Type) [Fintype Replica] [DecidableEq Replica]
    [LinearOrder BlockId] [LeanDag.Hydrozoan.Faults Replica],
    BaseRule.Laws (hydrozoan (Replica := Replica) (BlockId := BlockId))

/-- The laws of the base rule. The live rule is P2. -/
def Statement : Prop := Laws

end Hydrozoan

end Barnacle

end LeanDag
