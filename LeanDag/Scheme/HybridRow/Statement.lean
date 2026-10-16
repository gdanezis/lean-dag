import LeanDag.Scheme.Model.Hydrozoan
import LeanDag.Scheme.Model.Local
import LeanDag.Properties.Arcs.Headline
import LeanDag.Timed.Coverage
import LeanDag.Hydrozoan.Helpers.Carrier
/-!
# The Hybrid Mysticeti row against Hydrozoan — statement

`docs/scheme.md` §10. On Hydrozoan's universe, `n ≥ 3f + 2c + k + 1`
replicas of which at most `f` Byzantine and at most `c` crashed, at every
vote-selection rule:

* **The row is Hydrozoan without its fast path** (`SlowRow`): it decides
  as `hydrozoanSlowAnchored`, Hydrozoan's slow commit with a skip on
  `⌊(n + f + 1)/2⌋` blames and the certificate rung alone.
* **The row's carrier is safe and progresses** (`OnHydrozoan`), at a local
  vote, under Hydrozoan's fault model (slack `f + c`), which admits
  `n = 3f + 2c + 1`: the support commits there, and its coverage law holds.
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

/-- **On Hydrozoan's universe the row's carrier is safe and progresses**,
at a local vote, under Hydrozoan's fault model, and its support's coverage
law holds there. -/
def OnHydrozoan : Prop :=
  ∀ (Replica BlockId : Type) [Fintype Replica] [DecidableEq Replica] [LinearOrder BlockId]
    [F : Hydrozoan.Faults Replica]
    (σ : VoteSel Replica BlockId Unit Hydrozoan.ValidWrt Hydrozoan.NonByzantine), σ.Local →
    Safe (schemeRule (Params.hybridMysticeti (Fintype.card Replica) F.f F.c) σ
      Hydrozoan.NonByzantine) ∧
    Support.Progresses (R := schemeRule (Params.hybridMysticeti (Fintype.card Replica) F.f F.c) σ
        Hydrozoan.NonByzantine)
      (familySupport (Params.hybridMysticeti (Fintype.card Replica) F.f F.c) σ
        Hydrozoan.NonByzantine) (Hydrozoan.hzReliability Replica) ∧
    Timed.OfCoverage (R := schemeRule (Params.hybridMysticeti (Fintype.card Replica) F.f F.c) σ
        Hydrozoan.NonByzantine)
      (familySupport (Params.hybridMysticeti (Fintype.card Replica) F.f F.c) σ
        Hydrozoan.NonByzantine) (Hydrozoan.hzReliability Replica)

/-- **With self-reference the row's carrier is safe and lives**, at a local
vote, under Hydrozoan's fault model. -/
def WithSelfParent : Prop :=
  ∀ (Replica BlockId : Type) [Fintype Replica] [DecidableEq Replica] [LinearOrder BlockId]
    [F : Hydrozoan.Faults Replica]
    (σ : VoteSel Replica BlockId Unit HybridValid Hydrozoan.NonByzantine), σ.Local →
    Safe (schemeRule (Params.hybridMysticeti (Fintype.card Replica) F.f F.c) σ
      Hydrozoan.NonByzantine) ∧
    Support.Lives (R := schemeRule (Params.hybridMysticeti (Fintype.card Replica) F.f F.c) σ
        Hydrozoan.NonByzantine)
      (familySupport (Params.hybridMysticeti (Fintype.card Replica) F.f F.c) σ
        Hydrozoan.NonByzantine) (Hydrozoan.hzReliability Replica)

/-- The row against Hydrozoan. -/
def Statement : Prop := SlowRow ∧ OnHydrozoan ∧ WithSelfParent

end HybridRow

end Scheme

end LeanDag
