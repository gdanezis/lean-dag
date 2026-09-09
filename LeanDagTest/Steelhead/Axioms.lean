import LeanDag.Steelhead.Properties
import LeanDag.Steelhead.Safety.Proof
import LeanDag.Steelhead.Liveness.Proof
import LeanDag.Steelhead.Period.Proof
/-!
# Steelhead — axiom audit

Every principal result of the arc, checked to depend on the three
standard axioms and nothing else. Drift detection: a `sorryAx` or a
bespoke axiom would show here before anywhere else.
-/

#print axioms LeanDag.Steelhead.Safety.holds
#print axioms LeanDag.Steelhead.Liveness.holds
#print axioms LeanDag.Steelhead.Period.holds
#print axioms LeanDag.SteelheadProperties.persist
#print axioms LeanDag.SteelheadProperties.liveness
