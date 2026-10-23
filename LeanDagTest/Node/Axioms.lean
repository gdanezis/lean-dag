import LeanDag.Node.Vote
import LeanDag.Node.Store
import LeanDag.Node.Local.Proof
import LeanDag.Node.Runs.Proof
import LeanDag.Node.Converge.Proof
import LeanDag.Node.Live.Proof
import LeanDag.Node.Refines.Proof
import LeanDag.Node.Sync.Proof
/-!
# The node's theorems use only the standard axioms
-/

/--
info: 'LeanDag.historyUptoFrom_eq_levels' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms LeanDag.historyUptoFrom_eq_levels

/--
info: 'LeanDag.Node.boundedSel_sel_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms LeanDag.Node.boundedSel_sel_eq

/--
info: 'LeanDag.Node.Local.holds' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms LeanDag.Node.Local.holds

/--
info: 'LeanDag.Node.ViewsAbove.tryDecide_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms LeanDag.Node.ViewsAbove.tryDecide_eq

/--
info: 'LeanDag.Node.Runs.holds' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms LeanDag.Node.Runs.holds

/--
info: 'LeanDag.Node.Converge.holds' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms LeanDag.Node.Converge.holds

/--
info: 'LeanDag.Node.Live.holds' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms LeanDag.Node.Live.holds

/--
info: 'LeanDag.Node.Refines.holds' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms LeanDag.Node.Refines.holds

/--
info: 'LeanDag.Node.Sync.holds' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms LeanDag.Node.Sync.holds
