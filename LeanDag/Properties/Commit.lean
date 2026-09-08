import LeanDag.Properties.Bounded
import LeanDag.Properties.Carrier
/-!
# The indirect rule

`docs/target-properties.md` §4 and §11.8. The one liveness-side
obligation that is a property: an anchor eligible for a slot, committed,
with every eligible slot between them skipped, decides it, at a bound
and under any reassignment of the other leaders. `Derived/Descent.lean`
derives `Descends` from it; `Derived/LeaderCommits.lean` derives
`LeaderCommits` from `Support`, so neither is a second obligation.
-/

namespace LeanDag

namespace Properties

variable {Validator : Type} [Fintype Validator] [DecidableEq Validator]
variable {BlockId : Type} [DecidableEq BlockId] {Payload : Type}

/-- **The indirect rule.** An anchor eligible for slot `i`, committed,
with every eligible slot strictly between them skipped, decides `i`.

`Elig` is a parameter and reads the **round structure alone**: every
rule here makes an anchor eligible when it sits a wave above the slot,
and the property does not care which wave. Reading only `slotRound`
also means eligibility is unchanged by a reassignment of leaders, which
the second quantifier needs.

**The second quantifier is what makes this carry a bound.** A protocol
that proves the indirect rule by cases on the evidence at slot `i` —
which is how all of them prove it — proves this stronger form without
extra work: the case split reads slot `i`'s own candidate and the
anchor's history, and a schedule that renames leaders elsewhere changes
neither. `Descends` is the payoff, derived in `Derived/Descent.lean`
where it was three protocol-specific inductions.

Taking `S' := S` gives the plain rule, which is what a mechanism that
does not track bounds consumes. -/
def Indirect (R : DagRule Validator BlockId Payload)
    (Elig : (ℕ → ℕ) → ℕ → ℕ → Prop) : Prop :=
  ∀ (S : Slots Validator) {U : R.Universe} (V : R.View U) (i j : ℕ) (A : BlockId),
    Elig S.slotRound i j → R.Decided S V j (some A) →
    (∀ i', i < i' → i' < j → Elig S.slotRound i i' → R.Decided S V i' none) →
    ∃ v, ∀ S' : Slots Validator, S'.slotRound = S.slotRound → S'.leader i = S.leader i →
      R.Decided S' V j (some A) →
      (∀ i', i < i' → i' < j → Elig S.slotRound i i' → R.Decided S' V i' none) →
      R.Decided S' V i v

/-- The indirect property transfers along an equivalence of eligibility
relations. -/
theorem Indirect.congr {R : DagRule Validator BlockId Payload}
    {E₁ E₂ : (ℕ → ℕ) → ℕ → ℕ → Prop} (he : ∀ sr i j, E₁ sr i j ↔ E₂ sr i j)
    (h : Indirect R E₁) : Indirect R E₂ := by
  intro S U V i j A helig hj hmid
  obtain ⟨v, hv⟩ := h S V i j A ((he _ i j).mpr helig) hj
    (fun i' h1 h2 h3 => hmid i' h1 h2 ((he _ i i').mp h3))
  exact ⟨v, fun S' hround hlead hj' hmid' => hv S' hround hlead hj'
    (fun i' h1 h2 h3 => hmid' i' h1 h2 ((he _ i i').mp h3))⟩

/-- **The plain indirect rule**, at the schedule it was given. -/
theorem Indirect.decided {R : DagRule Validator BlockId Payload}
    {Elig : (ℕ → ℕ) → ℕ → ℕ → Prop} (h : Indirect R Elig)
    (S : Slots Validator) {U : R.Universe} (V : R.View U) {i j : ℕ} {A : BlockId}
    (he : Elig S.slotRound i j) (hj : R.Decided S V j (some A))
    (hmid : ∀ i', i < i' → i' < j → Elig S.slotRound i i' → R.Decided S V i' none) :
    ∃ v, R.Decided S V i v := by
  obtain ⟨v, hv⟩ := h S V i j A he hj hmid
  exact ⟨v, hv S rfl rfl hj hmid⟩

/-- **The descent laws** at gap `g` and slack `slack`, under a goodness
predicate on the universe: what a protocol owes a schedule mechanism on
the liveness side. `goodLeaders` is A4's direct half, `indirect` the
indirect rule read at the gap. -/
structure Descent (R : DagRule Validator BlockId Payload)
    (Good : R.Universe → ℕ → ℕ → Prop) (g slack : ℕ) : Prop where
  /-- **A4, direct commits.** On a good DAG some `slack`-missing set of
  validators commits every slot it leads whose gap fits under `N`, on any
  view caught up to `N`. -/
  goodLeaders : ∀ (U : R.Universe) (Rnd N : ℕ), Good U Rnd N →
    ∃ T : Finset Validator, Fintype.card Validator ≤ T.card + slack ∧
      ∀ (S : Slots Validator) (V : R.View U) (κ : ℕ), R.CoversUpto U V N →
        Rnd ≤ S.slotRound κ → S.slotRound κ + g ≤ N →
        S.leader κ ∈ T → ∃ L, R.Decided S V κ (some L)
  /-- **A3, the indirect rule.** A committed slot a gap above `i`, with
  every gap-eligible slot between them skipped, decides `i`. -/
  indirect : ∀ (S : Slots Validator) {U : R.Universe} (V : R.View U) (i j : ℕ) (A : BlockId),
    S.slotRound i + g ≤ S.slotRound j → R.Decided S V j (some A) →
    (∀ i', i < i' → i' < j → S.slotRound i + g ≤ S.slotRound i' →
      R.Decided S V i' none) →
    ∃ v, R.Decided S V i v

end Properties

end LeanDag
