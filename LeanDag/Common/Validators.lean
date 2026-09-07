import Mathlib.Data.Fintype.Card
import Mathlib.Data.Finset.Card
import Mathlib.Tactic.Push
import Mathlib.Tactic.ByContra

/-!
# Validators, faults, and quorum intersection

The system model of `spec.md` §2, plus the quorum-intersection lemma T0.

There are `n ≥ 3f+1` validators, of which at most `f` are Byzantine. A
*quorum* is any set of at least `n − f` validators — at `n = 3f+1` this is
the familiar `2f+1`. The single fact everything downstream rests on is
that two quorums always share a **correct** validator
(`exists_correct_mem_inter`): two sets of size `n − f` drawn from `n`
overlap in at least `n − 2f ≥ f+1` elements, one more than the fault
bound.

The quorum threshold is written literally as
`quorumCard Validator` throughout, which keeps every counting
argument within `omega`'s reach given `card_validators`.

The fault model is bundled as a class `Faults` rather than threaded as
section variables. Bundling keeps the two cardinality hypotheses attached to
the instance, so they never appear as explicit arguments and no `include` is
needed; it also lets `Correct` be written without an argument, since the
instance is inferred from `Validator`. Refer to the fault bound as `F.f`,
never as a bare `f` — a bare field access cannot determine which `Validator`
it belongs to and will elaborate to a metavariable.
-/

namespace LeanDag

/-- The fault model: `n ≥ 3f+1` validators, at most `f` of them
Byzantine. -/
class Faults (Validator : Type*) [Fintype Validator] [DecidableEq Validator] where
  /-- The fault bound. -/
  f : ℕ
  /-- The Byzantine validators. Everything else is correct. -/
  byzantine : Finset Validator
  /-- There are at least `3f+1` validators. -/
  card_validators : 3 * f + 1 ≤ Fintype.card Validator
  /-- At most `f` validators are Byzantine. -/
  card_byzantine : byzantine.card ≤ f

variable {Validator : Type*} [Fintype Validator] [DecidableEq Validator]
variable [F : Faults Validator]

/-- The quorum size `n − f`: what every counting argument counts to.

Notation rather than a definition, deliberately: the term *is* the
subtraction, so every lemma, `omega` call and `decide` sees exactly what
it always saw, while statements and goals read and print as
`quorumCard Validator`. -/
scoped notation:max "quorumCard " V:max => Fintype.card V - Faults.f V

/-- The correct (non-Byzantine) validators. -/
def Correct : Finset Validator := (F.byzantine)ᶜ

/-- Correctness is the complement of the Byzantine set. -/
@[simp]
theorem mem_correct {v : Validator} : v ∈ (Correct : Finset Validator) ↔ v ∉ F.byzantine := by
  simp [Correct]

/-- The correct and Byzantine validators partition the whole set.

Stated additively so it yields both bounds without ℕ subtraction. The
*upper* bound on `Correct.card` is the one the counting arguments need —
they divide an incidence count by the number of correct validators, for
which a lower bound is useless. -/
theorem card_correct_add_byzantine :
    (Correct : Finset Validator).card + F.byzantine.card = Fintype.card Validator := by
  have h : (Correct : Finset Validator).card = Fintype.card Validator - F.byzantine.card :=
    Finset.card_compl F.byzantine
  have hle : F.byzantine.card ≤ Fintype.card Validator := Finset.card_le_univ _
  omega

/-- **The standing arithmetic of the fault model**, in the form `omega`
consumes it: the correct and Byzantine sets partition the validators, at
most `f` are Byzantine, and there are at least `3f+1` in all.

A conjunction because the three are always wanted together — every
counting argument in the development opens by introducing them, and
naming the bundle says that these, and only these, are what the fault
model contributes to an arithmetic step. -/
theorem faults_arith :
    (Correct : Finset Validator).card + F.byzantine.card = Fintype.card Validator ∧
      F.byzantine.card ≤ F.f ∧ 3 * F.f + 1 ≤ Fintype.card Validator :=
  ⟨card_correct_add_byzantine, F.card_byzantine, F.card_validators⟩

/-- The correct validators alone meet the quorum threshold: at least
`n − f` of them. This is what the threshold `n − f` is *for* — the
correct pool suffices on its own. -/
theorem card_correct : quorumCard Validator ≤ (Correct : Finset Validator).card := by
  have := card_correct_add_byzantine (Validator := Validator)
  have := F.card_byzantine
  omega

/-- **At full fault load the reliable set is forced.** The liveness results
run at any `T ⊆ Correct` with `n - f ≤ T.card`, which is strictly weaker than
`T = Correct` — correct validators outside `T` may be starved for the whole
run. This says how much weaker: none at all, when the adversary spends its
whole budget. `|byzantine| = f` makes `Correct` exactly `n - f` large, and a
subset of a set of the same cardinality is that set.

So the generality has bite only below full fault load, and `T := Correct`
(`commits_recur`, at `Correct`) is not a restriction but the only
instantiation always available. -/
theorem reliable_eq_correct {T : Finset Validator} (hfull : F.byzantine.card = F.f)
    (hT : T ⊆ (Correct : Finset Validator))
    (hcard : quorumCard Validator ≤ T.card) :
    T = (Correct : Finset Validator) :=
  Finset.eq_of_subset_of_card_le hT (by
    have := card_correct_add_byzantine (Validator := Validator)
    have := F.card_validators
    omega)

/-- At least `2f+1` validators are correct — the `n = 3f+1` reading of
`card_correct`, kept for arguments that count in `f` alone. -/
theorem two_f_add_one_le_card_correct :
    2 * F.f + 1 ≤ (Correct : Finset Validator).card := by
  have := card_correct (Validator := Validator)
  have := F.card_validators
  omega

/-- Any set of more than `f` validators contains a correct one, since the
Byzantine validators number at most `f`. -/
theorem exists_correct_of_card {S : Finset Validator} (h : F.f + 1 ≤ S.card) :
    ∃ v ∈ S, v ∈ (Correct : Finset Validator) := by
  by_contra hcon
  push Not at hcon
  have hsub : S ⊆ F.byzantine := fun v hv => by simpa using hcon v hv
  have := Finset.card_le_card hsub
  have := F.card_byzantine
  omega

/-- Byzantine validators can absorb at most `f` of any set: removing the
correct members of `S` leaves something no bigger than the Byzantine set.

The workhorse behind "a quorum still contains many correct validators".
Stated additively so it composes without ℕ subtraction. -/
theorem card_le_card_inter_correct_add_byzantine (S : Finset Validator) :
    S.card ≤ (S ∩ (Correct : Finset Validator)).card + F.byzantine.card := by
  have hsplit := Finset.card_inter_add_card_sdiff S (Correct : Finset Validator)
  have hsdiff : (S \ (Correct : Finset Validator)).card ≤ F.byzantine.card := by
    refine Finset.card_le_card fun x hx => ?_
    rw [Finset.mem_sdiff] at hx
    simpa using hx.2
  omega

/-- A quorum contains at least `f+1` *correct* validators:
`(n − f) − f = n − 2f ≥ f+1`.

The cardinality strengthening of `exists_correct_of_card`, which only
produces one. -/
theorem card_inter_correct_of_quorum {S : Finset Validator}
    (h : quorumCard Validator ≤ S.card) :
    F.f + 1 ≤ (S ∩ (Correct : Finset Validator)).card := by
  have := card_le_card_inter_correct_add_byzantine S
  have := F.card_byzantine
  have := F.card_validators
  omega

/-- **T0 (cardinality half).** Two quorums overlap in at least `f+1`
validators: `(n−f) + (n−f) − n = n − 2f ≥ f+1`. -/
theorem card_inter_ge_of_quorum {Q₁ Q₂ : Finset Validator}
    (h₁ : quorumCard Validator ≤ Q₁.card)
    (h₂ : quorumCard Validator ≤ Q₂.card) :
    F.f + 1 ≤ (Q₁ ∩ Q₂).card := by
  have hunion : (Q₁ ∪ Q₂).card ≤ Fintype.card Validator := by
    rw [← Finset.card_univ]
    exact Finset.card_le_univ _
  have hadd := Finset.card_union_add_card_inter Q₁ Q₂
  have := F.card_validators
  omega

/-- **`f + 1` validators are more than a quorum can miss.** A block
references `n − f` distinct creators, so it misses at most `f`; this
turns a count of `f + 1` backers into the form the hitting lemma reads. -/
theorem lt_card_add_quorumCard {T : Finset Validator} (h : F.f + 1 ≤ T.card) :
    Fintype.card Validator < T.card + quorumCard Validator := by
  have := F.card_validators
  omega

/-- **T0.** Two quorums always share a *correct* validator. This is the form
every later proof cites. -/
theorem exists_correct_mem_inter {Q₁ Q₂ : Finset Validator}
    (h₁ : quorumCard Validator ≤ Q₁.card)
    (h₂ : quorumCard Validator ≤ Q₂.card) :
    ∃ v ∈ Q₁ ∩ Q₂, v ∈ (Correct : Finset Validator) :=
  exists_correct_of_card (card_inter_ge_of_quorum h₁ h₂)

end LeanDag
