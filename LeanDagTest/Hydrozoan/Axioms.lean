import LeanDag.Hydrozoan.ThresholdArithmetic.Proof
import LeanDag.Hydrozoan.DirectSafety.Proof
import LeanDag.Hydrozoan.SlotAgreement.Proof
import LeanDag.Hydrozoan.PrefixAgreement.Proof
import LeanDag.Hydrozoan.DirectLiveness.Proof
import LeanDag.Hydrozoan.IndirectLiveness.Proof
import LeanDag.Hydrozoan.EventualDecision.Proof
import LeanDag.Hydrozoan.Grounding.Proof

/-!
# The axioms tripwire

Build-failing enforcement of the acceptance criterion: every headline
theorem depends on exactly the standard triple `propext`,
`Classical.choice`, `Quot.sound` (the guard compares the full output,
so a *dropped* axiom trips it as loudly as a smuggled one — stricter
than the "at most" criterion, in the safe direction). `#guard_msgs`
fails elaboration — hence `lake build`, hence CI — on any deviation (a
smuggled axiom, a `sorry` anywhere in the dependency tree, or a
toolchain change to the message format, which a pin bump surfaces
loudly).
-/

/--
info: 'LeanDag.Hydrozoan.ThresholdArithmetic.holds' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms LeanDag.Hydrozoan.ThresholdArithmetic.holds

/--
info: 'LeanDag.Hydrozoan.DirectSafety.holds' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms LeanDag.Hydrozoan.DirectSafety.holds

/--
info: 'LeanDag.Hydrozoan.SlotAgreement.holds' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms LeanDag.Hydrozoan.SlotAgreement.holds

/--
info: 'LeanDag.Hydrozoan.PrefixAgreement.holds' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms LeanDag.Hydrozoan.PrefixAgreement.holds

/--
info: 'LeanDag.Hydrozoan.DirectLiveness.holds' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms LeanDag.Hydrozoan.DirectLiveness.holds

/--
info: 'LeanDag.Hydrozoan.DirectLiveness.fastLatency' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms LeanDag.Hydrozoan.DirectLiveness.fastLatency

/--
info: 'LeanDag.Hydrozoan.DirectLiveness.skipLatency' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms LeanDag.Hydrozoan.DirectLiveness.skipLatency

/--
info: 'LeanDag.Hydrozoan.IndirectLiveness.holds' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms LeanDag.Hydrozoan.IndirectLiveness.holds

/--
info: 'LeanDag.Hydrozoan.EventualDecision.holds' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms LeanDag.Hydrozoan.EventualDecision.holds

/--
info: 'LeanDag.Hydrozoan.Grounding.holds' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms LeanDag.Hydrozoan.Grounding.holds









