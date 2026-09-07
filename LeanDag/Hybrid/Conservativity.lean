import LeanDag.Hybrid.Liveness
import LeanDag.Odontoceti.Rules
/-!
# Conservativity: the crash-free hybrid is Odontoceti

H8. At `fc = 0` the hybrid thresholds are the pure-Byzantine two-round
ones — `q = n − f`, `kRel = n − 3f`, the admissible interval anchored
at `2f + 1` — and the fault models identify: every `Faults5` committee
is a crash-free hybrid committee (`Faults5.toHybrid`), and the two
derived `Faults` instances are *equal* (`toHybrid_toFaults`), so a
block universe over one is a block universe over the other with no
transport. The hybrid rule bodies at these parameters are syntactically
the Odontoceti ones — `q` supporters, `q` blamers, `k` in-cone
authors — which is what the plan meant by conservativity being
definitional rather than a theorem with content.
-/

namespace LeanDag

namespace Hybrid

variable {Validator : Type*} [Fintype Validator] [DecidableEq Validator]

section Collapse

variable [H : HybridFaults Validator]

/-- At `fc = 0` the hybrid quorum is the Byzantine quorum. -/
theorem q_eq_of_fc_zero (h : H.fc = 0) :
    q Validator = Fintype.card Validator - H.fb := by
  unfold q; omega

/-- At `fc = 0` the `n`-relative threshold is Odontoceti's `n − 3f`. -/
theorem kRel_eq_of_fc_zero (h : H.fc = 0) :
    kRel Validator = Fintype.card Validator - 3 * H.fb := by
  unfold kRel; omega

/-- At `fc = 0` the tight threshold is the thesis's `2f + 1`. -/
theorem kTight_eq_of_fc_zero (h : H.fc = 0) :
    kTight Validator = 2 * H.fb + 1 := by
  unfold kTight; omega

/-- **At `fc = 0` the strengthened clause is free.** With no crash
class, honest *is* correct — the union class is the Byzantine class
alone — so the base structure's `no_equivocation` already yields
`HonestNoEquiv`: the hybrid model's one genuinely new assumption
restricts nothing in the crash-free case, and Orcaella's subtype
universe is full. The counterpart of `Ubad`
(`LeanDagTest/Barnacle/Orcaella.lean`), which shows the clause is a
real restriction as soon as a crash class exists. -/
theorem honestNoEquiv_of_fc_zero {BlockId Payload : Type*} (h : H.fc = 0)
    (U : BlockUniverse Validator BlockId Payload) : HonestNoEquiv U := by
  intro i hi j hj hbyz hc hr
  refine U.no_equivocation i hi j hj ?_ hc hr
  have hcrash : H.crash = ∅ :=
    Finset.card_eq_zero.mp (Nat.le_zero.mp (h ▸ H.card_crash))
  rw [mem_correct, hybrid_byzantine, hcrash, Finset.union_empty]
  exact mem_honest.mp hbyz

end Collapse

/-- Two `Faults` instances with one bound and one Byzantine set are one
instance: the proof fields are propositions. -/
theorem Faults.ext' {F₁ F₂ : Faults Validator} (hf : F₁.f = F₂.f)
    (hb : F₁.byzantine = F₂.byzantine) : F₁ = F₂ := by
  cases F₁; cases F₂
  cases hf; cases hb
  rfl

/-- **Every pure-Byzantine committee is a crash-free hybrid committee.**
The generalization direction of H8. -/
def _root_.LeanDag.Faults5.toHybrid [F : Faults5 Validator] :
    HybridFaults Validator where
  fb := F.f
  fc := 0
  byzantine := F.byzantine
  crash := ∅
  disjoint := Finset.disjoint_empty_right _
  card_byzantine := F.card_byzantine
  card_crash := le_refl 0
  card_validators := by have := F.card_validators5; omega

/-- The two derived instances are equal, so a block universe over the
`Faults5` development *is* one over its crash-free hybrid reading, with
no transport. -/
theorem toHybrid_toFaults [F : Faults5 Validator] :
    (HybridFaults.toFaults (H := Faults5.toHybrid)) =
      (F.toFaults : Faults Validator) :=
  Faults.ext' (by show F.f + 0 = F.f; omega) (Finset.union_empty _)

end Hybrid

end LeanDag
