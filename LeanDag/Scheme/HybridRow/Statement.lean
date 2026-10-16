import LeanDag.Scheme.Model.Hydrozoan
import LeanDag.Scheme.Model.Local
import LeanDag.Properties.Arcs.Headline
import LeanDag.Timed.Coverage
import LeanDag.Hydrozoan.Helpers.Carrier
/-!
# The Hybrid Mysticeti row against Hydrozoan, and the rows at its fault model — statement

`docs/scheme.md` §10. On Hydrozoan's universe, `n ≥ 3f + 2c + k + 1`
replicas of which at most `f` Byzantine and at most `c` crashed, at every
vote-selection rule:

* **The row is Hydrozoan without its fast path** (`SlowRow`): it decides
  as `hydrozoanSlowAnchored`, Hydrozoan's slow commit with a skip on
  `⌊(n + f + 1)/2⌋` blames and the certificate rung alone.
* **Every covered row's carrier is safe and progresses** (`OnHydrozoan`),
  at a local vote, under Hydrozoan's fault model (slack `f + c`), which
  admits `n = 3f + 2c + 1`, when its commit and certificate thresholds
  are within `n − f − c`: the support commits there, and its coverage law
  holds. Hybrid Mysticeti, Orcaella, Async Orcaella, Hybrid Mahi-Mahi and
  Async Nemo-Nemo are instances (`Scheme/Rows/`).
* **With self-reference it lives** (`WithSelfParent`): on records whose
  blocks also reference their author's previous block (`HybridValid`),
  the carrier is safe and lives, progress and inclusion.

Statements only; the proofs are `Proof.lean`.
-/

namespace LeanDag

namespace Scheme

namespace HybridRow

open Properties

/-- **The row is Hydrozoan without its fast path.** -/
def SlowRow : Prop :=
  ∀ (Replica BlockId : Type) [Fintype Replica] [DecidableEq Replica] [LinearOrder BlockId]
    [F : Hydrozoan.Faults Replica]
    (σ : VoteSel Replica BlockId Unit Hydrozoan.ValidWrt Hydrozoan.NonByzantine),
    (schemeAnchored (Params.hybridMysticeti (Fintype.card Replica) F.f F.c) σ).toDagRule =
      (hydrozoanSlowAnchored Replica BlockId).toDagRule

/-- **On Hydrozoan's universe every covered row's carrier is safe and
progresses**, at a local vote, under Hydrozoan's fault model, when its
commit and certificate thresholds are within `n − f − c`; and its support's
coverage law holds there. -/
def OnHydrozoan : Prop :=
  ∀ (Replica BlockId : Type) [Fintype Replica] [DecidableEq Replica] [LinearOrder BlockId]
    [F : Hydrozoan.Faults Replica] (p : Params)
    (σ : VoteSel Replica BlockId Unit Hydrozoan.ValidWrt Hydrozoan.NonByzantine), σ.Local →
    p.Covered (Fintype.card Replica) F.f (Hydrozoan.q Replica) →
    p.commitThreshold ≤ Hydrozoan.q Replica → p.certThreshold ≤ Hydrozoan.q Replica →
    Safe (schemeRule p σ Hydrozoan.NonByzantine) ∧
    Support.Progresses (R := schemeRule p σ Hydrozoan.NonByzantine)
      (familySupport p σ Hydrozoan.NonByzantine) (Hydrozoan.hzReliability Replica) ∧
    Timed.OfCoverage (R := schemeRule p σ Hydrozoan.NonByzantine)
      (familySupport p σ Hydrozoan.NonByzantine) (Hydrozoan.hzReliability Replica)

/-- **With self-reference every covered row's carrier is safe and lives**,
at a local vote, under Hydrozoan's fault model, when its commit threshold
is within `n − f − c`. -/
def WithSelfParent : Prop :=
  ∀ (Replica BlockId : Type) [Fintype Replica] [DecidableEq Replica] [LinearOrder BlockId]
    [F : Hydrozoan.Faults Replica] (p : Params)
    (σ : VoteSel Replica BlockId Unit HybridValid Hydrozoan.NonByzantine), σ.Local →
    p.Covered (Fintype.card Replica) F.f (Hydrozoan.q Replica) →
    p.commitThreshold ≤ Hydrozoan.q Replica →
    Safe (schemeRule p σ Hydrozoan.NonByzantine) ∧
    Support.Lives (R := schemeRule p σ Hydrozoan.NonByzantine)
      (familySupport p σ Hydrozoan.NonByzantine) (Hydrozoan.hzReliability Replica)

/-- The row against Hydrozoan. -/
def Statement : Prop := SlowRow ∧ OnHydrozoan ∧ WithSelfParent

end HybridRow

end Scheme

end LeanDag
