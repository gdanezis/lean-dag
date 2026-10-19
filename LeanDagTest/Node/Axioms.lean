import LeanDag.Node.Vote
import LeanDag.Node.Store
import LeanDag.Node.Local.Proof
import LeanDag.Node.Runs.Proof
import LeanDag.Node.Converge.Proof
import LeanDag.Node.Restart.Proof
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
info: 'LeanDag.Node.treeMap_getD_filter_of' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms LeanDag.Node.treeMap_getD_filter_of

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
info: 'LeanDag.Node.Restart.holds' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms LeanDag.Node.Restart.holds
