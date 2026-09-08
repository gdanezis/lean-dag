import LeanDagTest.Barnacle.Rules.Mysticeti.Proof
import LeanDag.Barnacle.Window.Proof
import LeanDag.Barnacle.Agreement.Proof
import LeanDag.Barnacle.Ledger.Proof
import LeanDag.Barnacle.Conservativity.Proof
import LeanDag.Barnacle.Progress.Proof
import LeanDag.Barnacle.Heads.Proof
import LeanDagTest.Barnacle.Rules.MysticetiLive.Proof
import LeanDagTest.Barnacle.Rules.Odontoceti.Proof
import LeanDagTest.Barnacle.Rules.Nemo.Proof
import LeanDagTest.Barnacle.Rules.Orcaella.Proof
import LeanDagTest.Barnacle.Rules.Hydrozoan.Proof
import LeanDagTest.Barnacle.Rules.HydrozoanLive.Proof
import LeanDagTest.Barnacle.Rules.OptimalHydrozoan.Proof
import LeanDagTest.Barnacle.Rules.OptimalHydrozoanLive.Proof
import LeanDag.Barnacle.Aimd.Proof
import LeanDag.Barnacle.Live.Proof
import LeanDag.Barnacle.Healthy.Proof
import LeanDag.Barnacle.Validity.Proof
import LeanDag.Barnacle.Helpers.Delivery
/-!
# Barnacle — axiom audit

Every principal result of the arc, checked to depend on the three
standard axioms and nothing else. Drift detection: a `sorryAx` or a
bespoke axiom would show here before anywhere else.
-/

#print axioms LeanDag.Barnacle.Mysticeti.holds
#print axioms LeanDag.Barnacle.Window.holds
#print axioms LeanDag.Barnacle.Agreement.holds
#print axioms LeanDag.Barnacle.Ledger.holds
#print axioms LeanDag.Barnacle.Conservativity.holds
#print axioms LeanDag.Barnacle.Progress.holds
#print axioms LeanDag.Barnacle.Heads.holds
#print axioms LeanDag.Barnacle.MysticetiLive.holds
#print axioms LeanDag.Barnacle.Odontoceti.holds
#print axioms LeanDag.Barnacle.Nemo.holds
#print axioms LeanDag.Barnacle.Orcaella.holds
#print axioms LeanDag.Barnacle.Hydrozoan.holds
#print axioms LeanDag.Barnacle.HydrozoanLive.holds
#print axioms LeanDag.Barnacle.OptimalHydrozoan.holds
#print axioms LeanDag.Barnacle.OptimalHydrozoanLive.holds
#print axioms LeanDag.Barnacle.Aimd.holds
#print axioms LeanDag.Barnacle.Live.holds
#print axioms LeanDag.Barnacle.Healthy.holds
#print axioms LeanDag.Barnacle.Validity.holds
#print axioms LeanDag.Barnacle.delivers_core
