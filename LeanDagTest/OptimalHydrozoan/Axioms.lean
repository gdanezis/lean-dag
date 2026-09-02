import LeanDag.OptimalHydrozoan.ThresholdArithmetic.Proof
import LeanDag.OptimalHydrozoan.DirectSafety.Proof
import LeanDag.OptimalHydrozoan.SlotAgreement.Proof
import LeanDag.OptimalHydrozoan.PrefixAgreement.Proof
import LeanDag.OptimalHydrozoan.DirectLiveness.Proof
import LeanDag.OptimalHydrozoan.IndirectLiveness.Proof
import LeanDag.OptimalHydrozoan.EventualDecision.Proof
import LeanDag.OptimalHydrozoan.Grounding.Proof

/-!
# Optimal-Hydrozoan: the axioms tripwire

Every headline `holds` of the arc pinned to Lean's three standard axioms
by `#guard_msgs`: a `sorryAx`, a bespoke axiom or `native_decide`
anywhere in a proof's dependency tree changes the printed list and fails
the build, before any script runs. The Hydrozoan arc's tripwire is
`LeanDagTest/Hydrozoan/Axioms.lean`.
-/

/--
info: 'LeanDag.OptimalHydrozoan.ThresholdArithmetic.holds' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms LeanDag.OptimalHydrozoan.ThresholdArithmetic.holds

/--
info: 'LeanDag.OptimalHydrozoan.DirectSafety.holds' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms LeanDag.OptimalHydrozoan.DirectSafety.holds

/--
info: 'LeanDag.OptimalHydrozoan.SlotAgreement.holds' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms LeanDag.OptimalHydrozoan.SlotAgreement.holds

/--
info: 'LeanDag.OptimalHydrozoan.PrefixAgreement.holds' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms LeanDag.OptimalHydrozoan.PrefixAgreement.holds

/--
info: 'LeanDag.OptimalHydrozoan.DirectLiveness.holds' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms LeanDag.OptimalHydrozoan.DirectLiveness.holds

/--
info: 'LeanDag.OptimalHydrozoan.DirectLiveness.fastLatency' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms LeanDag.OptimalHydrozoan.DirectLiveness.fastLatency

/--
info: 'LeanDag.OptimalHydrozoan.IndirectLiveness.holds' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms LeanDag.OptimalHydrozoan.IndirectLiveness.holds

/--
info: 'LeanDag.OptimalHydrozoan.EventualDecision.holds' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms LeanDag.OptimalHydrozoan.EventualDecision.holds

/--
info: 'LeanDag.OptimalHydrozoan.Grounding.holds' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms LeanDag.OptimalHydrozoan.Grounding.holds
