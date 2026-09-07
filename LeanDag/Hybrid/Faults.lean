import LeanDag.Common.BlockDag
/-!
# The hybrid fault model: Byzantine and crash-prone

The model of `hybrid-plan.md`: `fb` Byzantine validators (may
equivocate), `fc` crash-prone validators (honest, may halt, never
equivocate), committee `n ≥ 5·fb + 3·fc + 1`. The base development's
`Correct` plays two roles at once — the non-equivocating population and
the reliable population — and this file splits them:

* **`Honest`** (`≥ n − fb`): the complement of the Byzantine set alone.
  Crash-prone validators are honest — a block they produce is one
  block, identical to all recipients. This is the population the
  safety counting discounts against.
* **`Correct`** (`≥ n − fb − fc`, through the derived instance): honest
  *and* available — the population liveness may rely on.

Two devices keep the arc small. The **derived instance**
`HybridFaults.toFaults` places the union class `byzantine ∪ crash` in
the base `Faults` structure, so the base quorum `n − F.f` is the hybrid
quorum `q = n − fb − fc` on the nose and the whole DAG layer — validity
P3, views, the counting vocabulary, the `T`-relativised liveness
interface — instantiates verbatim. And crashing itself is *invisible to
a structural model*: a crash is absence, so the crash class needs no
behavioural clause — only the cardinality arithmetic here and its
exclusion from liveness's reliable set.

What the derived instance gets wrong is exactly one clause: its P5
binds only the fully-correct class, and the hybrid safety counting
needs non-equivocation over the larger `Honest`. That strengthening is
`HonestNoEquiv`, the arc's one genuinely new assumption — a clause of
the *fault model* (the honesty of a class, like the Byzantine bound
itself), not conduct the protocol enforces. `H1` is the counting core
every conflict argument routes through: two author sets whose sizes sum
past `n + fb` share an honest member.
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
  /-- The base bound — what the *derived instance* needs. The hybrid
  committee bound `n ≥ 5·fb + 3·fc + 1` deliberately does **not** live
  here: every safety theorem consumes it through the admissible
  interval, whose nonemptiness implies it — and keeping the class at
  the base bound is what lets the one-short committee `n = 5·fb + 3·fc`
  be *expressed*, so that the tightness counterexample (H10) is a
  theorem rather than an unstatable aside. -/
  card_validators : 3 * (fb + fc) + 1 ≤ Fintype.card Validator

variable {Validator : Type*} [Fintype Validator] [DecidableEq Validator]
variable [H : HybridFaults Validator]

/-- **The derived instance**: the union class in the base structure.
Its `Correct` is the fully-correct class and its quorum is
`q = n − fb − fc` — so every quorum-shaped clause of the base
development instantiates at the hybrid parameters with no
restatement. -/
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
`Honest` rather than the derived instance's `Correct`: a crash-prone
validator authors at most one block per round too. This is P5's shape
at the larger class — the base clause follows from it — and it is the
one genuinely new assumption of the hybrid model, threaded through the
safety theorems as a hypothesis the way `DoSValid` is. -/
def HonestNoEquiv (U : BlockUniverse Validator BlockId Payload) : Prop :=
  U.NoEquivOn (Honest Validator)

instance {U : BlockUniverse Validator BlockId Payload} [DecidableEq BlockId] :
    Decidable (HonestNoEquiv U) :=
  inferInstanceAs (Decidable (U.NoEquivOn (Honest Validator)))

end NoEquiv

end LeanDag
