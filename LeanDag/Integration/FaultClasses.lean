import LeanDag.Checkpoint.BaseSpec
import LeanDag.Common.Density

/-!
# The three fault classes, on plain sets

The checkpoint paper's fault model without a carrier: Byzantine,
crash-prone and alive-but-corrupt validators as three finite sets under
their bounds `f`, `c`, `fa`, and the resilience bound
`3·f + 2·c + fa < n`. Nothing else is assumed of the committee, so the
structure is inhabited at every row of the scheme's table, including
those below `3(f + c) + 1` (Hybrid Mysticeti at `3f + 2c + 1`, Nemo-Nemo
at `2c + 1`), which `HybridFaults` excludes.

`signing` is the `SigningFaults` at the quorum `n − f − c`, and
`reliability` is the `Reliability` whose correct set is the
rule-following validators, at slack `f + c`. The rule-following
validators are a quorum of both (`quorum_alive`, `isQuorum_alive`),
alive-but-corrupt validators included.

The classes need not be disjoint: every count uses a union bound.
-/

namespace LeanDag

namespace Integration

open LeanDag.Checkpoint

/-- Byzantine, crash-prone and alive-but-corrupt validators under their
bounds, at the resilience bound `3·f + 2·c + fa < n`. -/
structure FaultClasses (Validator : Type*) [Fintype Validator] [DecidableEq Validator] where
  /-- The Byzantine bound. -/
  f : ℕ
  /-- The crash bound. -/
  c : ℕ
  /-- The alive-but-corrupt bound. -/
  fa : ℕ
  /-- Validators that may do anything. -/
  byzantine : Finset Validator
  /-- Validators that may halt. -/
  crash : Finset Validator
  /-- Validators that are live for the DAG rule and sign what they
  commit, and may sign anything else. -/
  abc : Finset Validator
  card_byzantine : byzantine.card ≤ f
  card_crash : crash.card ≤ c
  card_abc : abc.card ≤ fa
  /-- The resilience bound. -/
  resilient : 3 * f + 2 * c + fa < Fintype.card Validator

namespace FaultClasses

variable {Validator : Type*} [Fintype Validator] [DecidableEq Validator]
variable (F : FaultClasses Validator)

/-- The Byzantine and AbC classes together stay under their bounds. -/
theorem card_byzantine_union_abc : (F.byzantine ∪ F.abc).card ≤ F.f + F.fa :=
  le_trans (Finset.card_union_le _ _) (Nat.add_le_add F.card_byzantine F.card_abc)

/-- The Byzantine and crash classes together stay under their bounds. -/
theorem card_byzantine_union_crash : (F.byzantine ∪ F.crash).card ≤ F.f + F.c :=
  le_trans (Finset.card_union_le _ _) (Nat.add_le_add F.card_byzantine F.card_crash)

/-- The classes as signing faults: quorum `n − f − c`, reliable signers
outside the Byzantine and AbC classes, recovery-correct validators that
also do not crash, and rule-following validators outside the Byzantine
and crash classes. -/
def signing : SigningFaults Validator where
  q := Fintype.card Validator - (F.f + F.c)
  reliableSigner := (F.byzantine ∪ F.abc)ᶜ
  recoveryCorrect := (F.byzantine ∪ F.abc)ᶜ \ F.crash
  alive := (F.byzantine ∪ F.crash)ᶜ
  recoveryCorrect_subset_alive := by
    intro v hv
    simp only [Finset.mem_sdiff, Finset.mem_compl, Finset.mem_union] at hv ⊢
    tauto
  intersect := by
    rw [compl_compl]
    have := F.card_byzantine_union_abc
    have := F.resilient
    omega
  reach := by
    have heq : ((F.byzantine ∪ F.abc)ᶜ \ F.crash)ᶜ = F.byzantine ∪ F.abc ∪ F.crash := by
      ext v
      simp only [Finset.mem_compl, Finset.mem_sdiff, Finset.mem_union]
      tauto
    rw [heq]
    have hcard : (F.byzantine ∪ F.abc ∪ F.crash).card ≤ F.f + F.fa + F.c :=
      le_trans (Finset.card_union_le _ _)
        (Nat.add_le_add F.card_byzantine_union_abc F.card_crash)
    have := F.resilient
    omega

/-- The classes as a reliability: the rule-following validators, at
slack `f + c`. -/
def reliability : Reliability Validator where
  correct := (F.byzantine ∪ F.crash)ᶜ
  slack := F.f + F.c
  covers := by
    rw [compl_compl]
    exact F.card_byzantine_union_crash
  minority := by
    have := F.resilient
    omega

@[simp] theorem signing_q : F.signing.q = Fintype.card Validator - (F.f + F.c) := rfl

@[simp] theorem signing_alive : F.signing.alive = (F.byzantine ∪ F.crash)ᶜ := rfl

@[simp] theorem reliability_slack : F.reliability.slack = F.f + F.c := rfl

/-- The rule-following validators form the signing quorum, AbC
validators included. -/
theorem quorum_alive : F.signing.q ≤ F.signing.alive.card := by
  have h := Finset.card_add_card_compl (F.byzantine ∪ F.crash)
  have := F.card_byzantine_union_crash
  simp only [signing_q, signing_alive]
  omega

/-- The rule-following validators are a quorum of the reliability, AbC
validators included. -/
theorem isQuorum_alive : F.reliability.IsQuorum F.signing.alive :=
  F.reliability.isQuorum_correct

/-! ## The resilience bound, read as committee slack -/

/-- At the quorum `n − f − c`, with the Byzantine and AbC classes at
their bounds, the resilience bound is the intersection law. -/
theorem resilient_iff_intersect (n f c fa : ℕ) :
    n + (f + fa) < 2 * (n - (f + c)) ↔ 3 * f + 2 * c + fa < n := by
  omega

/-- A two-round committee `n ≥ 5f + 3c + 1` tolerates any
`fa ≤ 2f + c` without adding a validator. -/
theorem resilient_of_twoRound {n f c fa : ℕ} (hn : 5 * f + 3 * c + 1 ≤ n)
    (hfa : fa ≤ 2 * f + c) : 3 * f + 2 * c + fa < n := by
  omega

/-- A three-round committee at `n = 3f + 2c + 1` has no slack: the
resilience bound holds there only at `fa = 0`. -/
theorem resilient_threeRound_iff {f c fa : ℕ} :
    3 * f + 2 * c + fa < 3 * f + 2 * c + 1 ↔ fa = 0 := by
  omega

end FaultClasses

end Integration

end LeanDag
