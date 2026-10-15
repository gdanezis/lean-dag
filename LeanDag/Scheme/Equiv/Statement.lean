import LeanDag.Scheme.Model.Rule
import LeanDag.Scheme.Model.Variants
import LeanDag.Mysticeti.Properties
import LeanDag.Odontoceti.Carrier
import LeanDag.Hybrid.Carrier
import LeanDag.Nemo.Carrier
/-!
# The scheme's rows as carriers — statement

`docs/scheme.md` §5. At every vote-selection rule, the scheme's decider at
a row's parameters is a carrier of this development:

* **Mysticeti** is `mysticetiRule`, **Blue Bottle PS** is
  `odontocetiRule`, and **Orcaella** at `n = 5f + 3c + 1` is
  `hybridRule (n − 3f − 2c)`: each row's carrier is equal to the rule's,
  so every theorem about the rule's carrier holds of the row.
* **Cordial Miners PS** is `cordialAnchored`, the core's rule with no
  direct skip, and two views decide alike.
* **Nemo-Nemo** at `n = 2c + 1` is `nemoBlameAnchored`, Nemo's rule with a
  direct skip on a blame from every validator, and two views decide alike.

Statements only; the proofs are `Proof.lean`.
-/

namespace LeanDag

namespace Scheme

namespace Equiv

open LeanDag.Properties

/-- **The Mysticeti row is the core's carrier.** -/
def MysticetiRow : Prop :=
  ∀ (Validator BlockId Payload : Type) [Fintype Validator] [DecidableEq Validator]
    [F : Faults Validator] [LinearOrder BlockId]
    (σ : VoteSel Validator BlockId Payload ValidWrt Correct),
    (schemeAnchored (Params.mysticeti (Fintype.card Validator) F.f) σ).toDagRule =
      MysticetiProperties.mysticetiRule (Validator := Validator) (BlockId := BlockId)
        (Payload := Payload)

/-- **The Blue Bottle PS row is Odontoceti's carrier.** -/
def BlueBottlePSRow : Prop :=
  ∀ (Validator BlockId Payload : Type) [Fintype Validator] [DecidableEq Validator]
    [F : Faults5 Validator] [LinearOrder BlockId]
    (σ : VoteSel Validator BlockId Payload ValidWrt Correct),
    (schemeAnchored (Params.blueBottlePS (Fintype.card Validator) F.f) σ).toDagRule =
      OdontocetiProperties.odontocetiRule (Validator := Validator) (BlockId := BlockId)
        (Payload := Payload)

/-- **The Orcaella row is Hybrid's carrier** at `n = 5f + 3c + 1`, with
the indirect threshold `n − 3f − 2c`. -/
def OrcaellaRow : Prop :=
  ∀ (Validator BlockId Payload : Type) [Fintype Validator] [DecidableEq Validator]
    [H : HybridFaults Validator] [LinearOrder BlockId]
    (σ : VoteSel Validator BlockId Payload ValidWrt Correct),
    Fintype.card Validator = 5 * H.fb + 3 * H.fc + 1 →
    (schemeAnchored (Params.orcaella (Fintype.card Validator) H.fb H.fc) σ).toDagRuleOn
        HonestNoEquiv =
      HybridProperties.hybridRule (Validator := Validator) (BlockId := BlockId)
        (Payload := Payload) (Fintype.card Validator - 3 * H.fb - 2 * H.fc)

/-- **The Cordial Miners PS row is the core's rule with no direct skip**,
and two views decide alike. -/
def CordialMinersPSRow : Prop :=
  ∀ (Validator BlockId Payload : Type) [Fintype Validator] [DecidableEq Validator]
    [F : Faults Validator] [LinearOrder BlockId]
    (σ : VoteSel Validator BlockId Payload ValidWrt Correct),
    (schemeAnchored (Params.cordialMinersPS (Fintype.card Validator) F.f) σ).toDagRule =
      (cordialAnchored Validator BlockId Payload).toDagRule ∧
    Agree (schemeAnchored (Params.cordialMinersPS (Fintype.card Validator) F.f) σ).toDagRule

/-- **The Nemo-Nemo row is Nemo's rule with a skip on a blame from every
validator** at `n = 2c + 1`, and two views decide alike. -/
def NemoNemoRow : Prop :=
  ∀ (Validator BlockId Payload : Type) [Fintype Validator] [DecidableEq Validator]
    [LinearOrder BlockId] (σ : VoteSel Validator BlockId Payload Nemo.ValidWrt Finset.univ)
    (c : ℕ), Fintype.card Validator = 2 * c + 1 →
    (schemeAnchored (Params.nemoNemo (Fintype.card Validator) c) σ).toDagRule =
      (nemoBlameAnchored Validator BlockId Payload).toDagRule ∧
    Agree (schemeAnchored (Params.nemoNemo (Fintype.card Validator) c) σ).toDagRule

/-- The five rows, together. -/
def Statement : Prop :=
  MysticetiRow ∧ BlueBottlePSRow ∧ OrcaellaRow ∧ CordialMinersPSRow ∧ NemoNemoRow

end Equiv

end Scheme

end LeanDag
