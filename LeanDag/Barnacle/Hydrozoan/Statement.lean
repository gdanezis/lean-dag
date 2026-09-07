import LeanDag.Barnacle.Model.Anchored
import LeanDag.Hydrozoan.Helpers.Carrier
/-!
# Barnacle over Hydrozoan — statement

The dual-path commit rule under hybrid faults (`LeanDag/Hydrozoan/`;
`docs/hydrozoan.md`) as a base rule with its laws, so that the adaptive
leader count of `LeanDag/Barnacle/` runs over it: `ofAnchored` at
`hydrozoanAnchored`. The liveness half — the live rule and the descent
laws — is `Barnacle/HydrozoanLive/` (`docs/hydrozoan-integration.md` §3).

**What this instantiation needs, and what it does not.** It needs
**neither** the committee condition `c ≤ k` **nor** the self-parent
clause of its §3: the universe is Hydrozoan's own block record, whose
own fields carry the history layer.

Two points where the instantiation carries Hydrozoan's shape.

* **The universe needs no subtype.** Orcaella's carrier is
  `{U // HonestNoEquiv U}`, because the hybrid model's non-equivocation
  at the wider honest class is a hypothesis its `agree` law has no slot
  for. Hydrozoan states the same condition as a *field* of its record,
  guarded by `NonByzantine`, so the carrier is the universe itself.
* **Two direct routes, one window, and the wave length is forced.**
  Hydrozoan has two direct commits at different depths: the fast path
  reads the propose and voting rounds, the slow path also the decision
  round. The wave length is nonetheless not free to follow the shallower
  one, because it is also the anchor gap of `LiveRule.Descent`'s
  `indirect` law, which reads `S.slotRound i + waveLength ≤ S.slotRound j`;
  Hydrozoan's `EligibleAsAnchor i j` unfolds to
  `decisionRound i < S.slotRound j`, so at wave length two that law
  demands its conclusion from a gap no Hydrozoan derivation admits. The
  anchored rule's wave is two, the wave length three, and the direct
  predicate is the disjunction of the two routes. What that changes for
  the leader count is only which slots `WindowHealthy` *requires*:
  `observed` (`Barnacle/Model/Window.lean`) counts a fast commit
  wherever it sits, while `expected` and `WindowHealthy` start at depth
  `waveLength`, so the two sides of the comparison move together.
  Neither branch may be dropped: without the slow branch the count
  falls to zero exactly when the actual faults exceed `p`
  (`docs/hydrozoan.md` §0); without the fast branch it misses the
  commits the protocol exists for (§11).

`LinearOrder BlockId` is Hydrozoan's, for the tie-break of the indirect
rule's second rung.
Statements only; the proofs live in `Proof.lean`.
-/

namespace LeanDag

namespace Barnacle

variable {Replica : Type} [Fintype Replica] [DecidableEq Replica]
variable {BlockId : Type} [LinearOrder BlockId]

/-- **Hydrozoan as a base rule**: its anchored rule, over its own record. -/
def hydrozoan [LeanDag.Hydrozoan.Faults Replica] : BaseRule Replica BlockId Unit :=
  ofAnchored (LeanDag.Hydrozoan.hydrozoanAnchored Replica BlockId)

namespace Hydrozoan

/-- **Hydrozoan satisfies the laws.** Agreement is HZ3
(`LeanDag.Hydrozoan.SlotAgreement`), already quantified over every
universe and every schedule. -/
def Laws : Prop :=
  ∀ (Replica BlockId : Type) [Fintype Replica] [DecidableEq Replica]
    [LinearOrder BlockId] [LeanDag.Hydrozoan.Faults Replica],
    BaseRule.Laws (hydrozoan (Replica := Replica) (BlockId := BlockId))

/-- The laws of the base rule. The live rule is P2. -/
def Statement : Prop := Laws

end Hydrozoan

end Barnacle

end LeanDag
