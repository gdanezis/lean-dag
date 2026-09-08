import LeanDag.FinWhale.Procedure.Model.Verdict
import Mathlib.Order.Interval.Finset.Nat

/-!
# FinWhale — the reverse pass, as a procedure

`Model/Verdict.lean` states the pass as a condition on a verdict
assignment; this file computes it. `slotVerdict` decides one slot from
the verdicts above it, and `passFrom` threads that down from the
horizon to slot `0`, giving `decOf`. `Pass.lean` proves it well formed.
-/


namespace LeanDag

namespace FinWhale

variable {Validator : Type*} [Fintype Validator] [DecidableEq Validator]
variable [F : Faults Validator] [P : Params Validator]
variable {BlockId : Type*} [DecidableEq BlockId] [LinearOrder BlockId] {Payload : Type*}
variable {S : Slots Validator}

/-- The blocks of a slot that are directly committed. At most one, by
`direct_commit_unique`. -/
def directCommits (S : Slots Validator) (D : Dag Validator BlockId Payload) (r : ℕ) : Finset BlockId :=
  (slotBlocks S D r).filter (fun l => DirectCommit D l)

/-- The candidates for the anchor of `r`: the **eligible** slots below
the horizon that the verdicts above do not skip. Filtered over `Iic N`
rather than the interval `Ioc (r + 2) N`, so the pass stays well formed
at whatever eligibility it is run with. -/
def anchorCands (Elig : ℕ → ℕ → Prop) [DecidableRel Elig] (N : ℕ)
    (above : ℕ → Verdict BlockId) (r : ℕ) : Finset ℕ :=
  (Finset.Iic N).filter (fun a => Elig r a ∧ above a ≠ Verdict.skip)

/-- **The indirect verdict**: read the first non-skipped slot above
`r + 2` through the tie-break. Where there is none the slot stays
undecided, which is what an undecided anchor gives too. -/
def anchorVerdict (Elig : ℕ → ℕ → Prop) [DecidableRel Elig]
    (choose : BlockId → ℕ → Option BlockId) (N : ℕ)
    (above : ℕ → Verdict BlockId) (r : ℕ) : Verdict BlockId :=
  if hc : (anchorCands Elig N above r).Nonempty then
    match above ((anchorCands Elig N above r).min' hc) with
    | Verdict.commit A =>
        match choose A r with
        | some b => Verdict.commit b
        | none => Verdict.skip
    | _ => Verdict.undecided
  else Verdict.undecided

/-- **One slot's verdict, from the verdicts above it.** -/
def slotVerdict (S : Slots Validator) (Elig : ℕ → ℕ → Prop) [DecidableRel Elig]
    (D : Dag Validator BlockId Payload)
    (choose : BlockId → ℕ → Option BlockId) (N : ℕ)
    (above : ℕ → Verdict BlockId) (r : ℕ) : Verdict BlockId :=
  if h : (directCommits S D r).Nonempty then Verdict.commit ((directCommits S D r).min' h)
  else if DirectSkip S D r then Verdict.skip
  else anchorVerdict Elig choose N above r

/-- **The pass, from slot `s` downward.** Slots below `s` are left
undecided; slot `s` is decided from the verdicts above it, and those are
what the pass from `s + 1` gives. -/
def passFrom (S : Slots Validator) (Elig : ℕ → ℕ → Prop) [DecidableRel Elig]
    (D : Dag Validator BlockId Payload)
    (choose : BlockId → ℕ → Option BlockId) (N : ℕ) (s : ℕ) : ℕ → Verdict BlockId :=
  if h : N < s then fun _ => Verdict.undecided
  else fun r =>
    if r = s then slotVerdict S Elig D choose N (passFrom S Elig D choose N (s + 1)) s
    else passFrom S Elig D choose N (s + 1) r
termination_by N + 1 - s
decreasing_by all_goals omega

/-- **The verdicts of a validator whose view is `D`.** -/
def decOf (S : Slots Validator) (Elig : ℕ → ℕ → Prop) [DecidableRel Elig]
    (D : Dag Validator BlockId Payload)
    (choose : BlockId → ℕ → Option BlockId) (N : ℕ) : ℕ → Verdict BlockId :=
  passFrom S Elig D choose N 0

variable {D : Dag Validator BlockId Payload} {choose : BlockId → ℕ → Option BlockId} {N : ℕ}


end FinWhale

end LeanDag
