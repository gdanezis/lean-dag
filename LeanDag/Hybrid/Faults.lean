import LeanDag.Common.BlockDag
/-!
# The hybrid fault model: Byzantine and crash-prone

`hybrid-plan.md`'s model: `fb` Byzantine (may equivocate), `fc`
crash-prone (honest, may halt, never equivocate), `n ≥ 5fb + 3fc + 1`.
Splits the base `Correct` into `Honest` (`≥ n − fb`) and `Correct`
(`≥ n − fb − fc`, honest and available); the derived instance
`HybridFaults.toFaults` lets the whole DAG layer instantiate verbatim,
except its P5 binds only the fully-correct class, which
`HonestNoEquiv` strengthens to `Honest` — the arc's one new hypothesis,
and `H1`'s counting core.
-/

namespace LeanDag

/-- The hybrid fault model: at most `fb` Byzantine, at most `fc`
crash-prone. The committee bound `n ≥ 5·fb + 3·fc + 1` enters through
the admissible threshold interval, not here — see `card_validators`. -/
class HybridFaults (Validator : Type*) [Fintype Validator]
    [DecidableEq Validator] where
  /-- The Byzantine bound. -/
  fb : ℕ
  /-- The crash bound. -/
  fc : ℕ
  /-- The Byzantine validators: may equivocate. -/
  byzantine : Finset Validator
  /-- The crash-prone validators: honest, may halt. -/
  crash : Finset Validator
  disjoint : Disjoint byzantine crash
  card_byzantine : byzantine.card ≤ fb
  card_crash : crash.card ≤ fc
  /-- The base bound the derived instance needs — deliberately not the
  hybrid committee bound `n ≥ 5fb + 3fc + 1`, which every safety
  theorem consumes through the admissible interval instead, so the
  one-short committee `n = 5fb + 3fc` stays expressible for the
  tightness counterexample (H10). -/
  card_validators : 3 * (fb + fc) + 1 ≤ Fintype.card Validator

variable {Validator : Type*} [Fintype Validator] [DecidableEq Validator]
variable [H : HybridFaults Validator]

/-- **The derived instance**: the union class in the base structure,
with `Correct` the fully-correct class and quorum `q = n − fb − fc`,
so every quorum-shaped base clause instantiates with no restatement. -/
instance HybridFaults.toFaults : Faults Validator where
  f := H.fb + H.fc
  byzantine := H.byzantine ∪ H.crash
  card_validators := by have := H.card_validators; omega
  card_byzantine :=
    le_trans (Finset.card_union_le _ _)
      (Nat.add_le_add H.card_byzantine H.card_crash)

@[simp] theorem hybrid_f : (HybridFaults.toFaults (Validator := Validator)).f =
    H.fb + H.fc := rfl

@[simp] theorem hybrid_byzantine :
    (HybridFaults.toFaults (Validator := Validator)).byzantine =
      H.byzantine ∪ H.crash := rfl

variable (Validator) in
/-- The honest validators: everyone outside the Byzantine set. A
crash-prone validator is honest — its blocks are consistent; only its
availability is in doubt. -/
def Honest : Finset Validator := (H.byzantine)ᶜ

@[simp]
theorem mem_honest {v : Validator} :
    v ∈ Honest Validator ↔ v ∉ H.byzantine := by
  simp [Honest]

/-- The fully-correct class is honest: `Correct`, read through the
derived instance, excludes the crash-prone as well. -/
theorem correct_subset_honest :
    (Correct : Finset Validator) ⊆ Honest Validator := by
  intro v hv
  rw [mem_correct] at hv
  rw [mem_honest]
  intro hb
  exact hv (Finset.mem_union_left _ hb)

/-- The honest and Byzantine classes partition the committee — the
complement identity the counting arguments cancel against. -/
theorem card_honest_add_byzantine :
    (Honest Validator).card + H.byzantine.card = Fintype.card Validator := by
  have h : (Honest Validator).card =
      Fintype.card Validator - H.byzantine.card :=
    Finset.card_compl H.byzantine
  have hle : H.byzantine.card ≤ Fintype.card Validator := Finset.card_le_univ _
  omega

/-- The validators outside `Honest` are the Byzantine ones: at most `fb`. -/
theorem card_compl_honest_le : (Honest Validator)ᶜ.card ≤ H.fb := by
  rw [Honest, compl_compl]; exact H.card_byzantine

section NoEquiv

variable {BlockId : Type*} {Payload : Type*}

/-- **The strengthened equivocation clause.** Non-equivocation over
`Honest` rather than the derived instance's `Correct` — P5's shape at
the larger class, the base clause following from it — is the hybrid
model's one genuinely new assumption. -/
def HonestNoEquiv (U : BlockUniverse Validator BlockId Payload) : Prop :=
  U.NoEquivOn (Honest Validator)

instance {U : BlockUniverse Validator BlockId Payload} [DecidableEq BlockId] :
    Decidable (HonestNoEquiv U) :=
  inferInstanceAs (Decidable (U.NoEquivOn (Honest Validator)))

end NoEquiv

end LeanDag
