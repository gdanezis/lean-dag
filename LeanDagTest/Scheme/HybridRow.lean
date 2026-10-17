import LeanDag.Scheme.HybridRow.Proof
import LeanDag.Scheme.Model.LeastSel
import LeanDag.Hybrid.Faults
/-!
# The Hybrid Mysticeti row at its committee

Six replicas, one Byzantine and one crashed: `n = 3f + 2c + 1` at
`f = c = 1`, which Hydrozoan's fault model admits at `k = 0` and the
core's excludes. The row's thresholds are all `4 = q`, so the correct
quorum reaches the commit, the certificate and the skip; Hydrozoan's
skip threshold `q_fast = 6` exceeds it. The statements hold here at the
least vote.
-/

namespace LeanDagTest

namespace Scheme

open LeanDag LeanDag.Scheme

instance sixReplicas : LeanDag.Hydrozoan.Faults (Fin 6) where
  f := 1
  c := 1
  k := 0
  byzantine := {0}
  crashed := {1}
  byzantine_disjoint_crashed := by decide
  card_replicas := by decide
  card_byzantine := by decide
  card_crashed := by decide

/-- The committee is Hybrid Mysticeti's, the row's thresholds are the
quorum, and Hydrozoan's skip threshold is above it. -/
example : Fintype.card (Fin 6) = 3 * 1 + 2 * 1 + 1 ∧
    (Params.hybridMysticeti 6 1 1).commitThreshold = 4 ∧
    (Params.hybridMysticeti 6 1 1).skipThreshold = 4 ∧
    (Params.hybridMysticeti 6 1 1).certThreshold = 4 ∧
    Hydrozoan.q (Fin 6) = 4 ∧ Hydrozoan.qCert (Fin 6) = 4 ∧ Hydrozoan.qFast (Fin 6) = 6 := by
  decide

/-- The row is Hydrozoan without its fast path. -/
example : (schemeAnchored (Params.hybridMysticeti (Fintype.card (Fin 6)) 1 1)
      (leastSel (Validator := Fin 6) (BlockId := Fin 20) (Payload := Unit)
        (P := Hydrozoan.ValidWrt) (honest := Hydrozoan.NonByzantine))).toDagRule =
    (hydrozoanSlowAnchored (Fin 6) (Fin 20)).toDagRule :=
  HybridRow.slowRow (Fin 6) (Fin 20) leastSel

/-- With self-reference, the row's carrier is safe and lives at the least
vote. -/
example : Properties.Safe (schemeRule (Params.hybridMysticeti (Fintype.card (Fin 6)) 1 1)
      (leastSel (Validator := Fin 6) (BlockId := Fin 20) (Payload := Unit) (P := HybridValid)
        (honest := Hydrozoan.NonByzantine))) :=
  (HybridRow.withSelfParent (Fin 6) (Fin 20) _ leastSel leastSel_local hybridMysticeti_covered
    (by decide)).1

/-- **The hybrid arc's records, read at the honest set.** A block universe
of the hybrid fault model is keyed to the fully correct validators; read at
`Honest`, its non-equivocating set, it keeps its blocks and has at most
`fb` validators outside its honest set, as `Params.Tolerates` counts. -/
example {Validator BlockId Payload : Type} [Fintype Validator] [DecidableEq Validator]
    [H : HybridFaults Validator] (U : BlockUniverse Validator BlockId Payload)
    (h : HonestNoEquiv U) :
    (withHonest U h).ids = U.ids ∧ (withHonest U h).block = U.block ∧
      (Honest Validator)ᶜ.card ≤ H.fb :=
  ⟨rfl, rfl, card_compl_honest_le⟩

end Scheme

end LeanDagTest

#print axioms LeanDag.Scheme.HybridRow.holds
