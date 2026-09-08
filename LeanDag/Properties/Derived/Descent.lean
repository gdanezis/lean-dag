import LeanDag.Properties.Commit
import LeanDag.Properties.Derived.Bounded
/-!
# `Descends` from the indirect rule

`docs/target-properties.md` §4. `Descends` was an obligation each
protocol discharged the same way: a downward induction taking, at each
step, the least eligible anchor that commits. `Indirect` is that last
step, and the induction lives here once. `Indirect`'s tight-bound
clause is what makes this possible: a protocol proves it for its own
indirect step at no extra cost, since the step reads only slot `i`'s
candidate and the anchor's history.
-/

namespace LeanDag

namespace Properties

variable {Validator : Type} [Fintype Validator] [DecidableEq Validator]
variable {BlockId : Type} [DecidableEq BlockId] {Payload : Type}
variable {R : DagRule Validator BlockId Payload} {Elig : (ℕ → ℕ) → ℕ → ℕ → Prop}

/-- **A committed run decides everything below it.** `c` consecutive
slots from `b`, each committed within `b + c`, decide every slot below
`b` within `b + c`. -/
def Descends (R : DagRule Validator BlockId Payload) (S : Slots Validator) (c : ℕ) : Prop :=
  ∀ {U : R.Universe} (V : R.View U) (b : ℕ),
    (∀ j, b ≤ j → j < b + c → ∃ L, DecidedBelow R S (b + c) V j (some L)) →
    ∀ i, i < b → ∃ v, DecidedBelow R S (b + c) V i v

/-- **The committed-run descent.** A stretch of slots `[b, n]`, each
committed below `n + 1`, decides every slot under `b` — at the same
bound, provided every slot under `b` has `n` eligible.

The anchor for slot `i` is the least eligible slot that commits, which
is what makes the intervening eligible slots skipped rather than merely
undecided: any one of them that committed would have been the least. -/
theorem decidedBelow_of_committed_run (hind : Indirect R Elig)
    (S : Slots Validator) {U : R.Universe} {V : R.View U} {b n B : ℕ}
    (hbn : b ≤ n) (hnB : n < B)
    (hspan : ∀ i, i < b → Elig S.slotRound i n)
    (hrun : ∀ j, b ≤ j → j ≤ n → ∃ A, DecidedBelow R S B V j (some A)) :
    ∀ i, i < b → ∃ v, DecidedBelow R S B V i v := by
  classical
  have key : ∀ d i, i < b → b - i ≤ d → ∃ v, DecidedBelow R S B V i v := by
    intro d
    induction d with
    | zero => intro i hi hd; omega
    | succ d ih =>
      intro i hi hd
      have hex : ∃ j, Elig S.slotRound i j ∧ ∃ A, DecidedBelow R S B V j (some A) :=
        ⟨n, hspan i hi, hrun n hbn le_rfl⟩
      have hle : Nat.find hex ≤ n := Nat.find_le ⟨hspan i hi, hrun n hbn le_rfl⟩
      set j := Nat.find hex with hj
      obtain ⟨helig, A, hA⟩ : Elig S.slotRound i j ∧ ∃ A, DecidedBelow R S B V j (some A) :=
        Nat.find_spec hex
      have hmid : ∀ i', i < i' → i' < j → Elig S.slotRound i i' →
          DecidedBelow R S B V i' none := by
        intro i' h1 h2 h3
        have hnc : ¬ ∃ C, DecidedBelow R S B V i' (some C) :=
          fun hc => Nat.find_min hex h2 ⟨h3, hc⟩
        have hi'b : i' < b := by
          by_contra hge
          exact hnc (hrun i' (by omega) (by omega))
        obtain ⟨v, hv⟩ := ih i' hi'b (by omega)
        cases v with
        | none => exact hv
        | some C => exact absurd ⟨C, hv⟩ hnc
      have hmid' : ∀ i', i < i' → i' < j → Elig S.slotRound i i' → R.Decided S V i' none :=
        fun i' h1 h2 h3 => (hmid i' h1 h2 h3).2.1
      obtain ⟨v, hv⟩ := hind S V i j A helig hA.2.1 hmid'
      refine ⟨v, by omega, hv S rfl rfl hA.2.1 hmid', ?_⟩
      intro S' hround hlead
      exact hv S' hround (hlead i (by omega)) (hA.2.2 S' hround hlead)
        (fun i' h1 h2 h3 => (hmid i' h1 h2 h3).2.2 S' hround hlead)
  intro i hi
  exact key (b - i) i hi le_rfl

/-- **`Descends` is a consequence, not an obligation.** The run is `c`
consecutive commits from `b`; its top is `b + c - 1`, and the spanning
hypothesis is the protocol's own condition on the round structure —
that every slot below `b` has the run's top eligible. -/
theorem Descends.of_indirect (hind : Indirect R Elig) {S : Slots Validator} {c : ℕ}
    (hc : 0 < c) (hspans : ∀ b i, i < b → Elig S.slotRound i (b + c - 1)) :
    Descends R S c := by
  intro U V b hrun i hi
  exact decidedBelow_of_committed_run hind S (b := b) (n := b + c - 1) (B := b + c)
    (by omega) (by omega) (fun i hi => hspans b i hi)
    (fun j h1 h2 => hrun j h1 (by omega)) i hi

end Properties

end LeanDag
