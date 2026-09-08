import LeanDag.FinWhale.Model.Anchor
import Mathlib.Data.Finset.Max

/-!
# FinWhale — verdicts, the reverse pass, and the tie-break

A validator's decisions are a verdict per leader slot: a slot the
direct rules decide takes that verdict, and otherwise the validator
finds its anchor — the first non-skipped slot above `r + 2` — and reads
the slot off its causal history. `Verdict`, `Anchor` and `WellFormed`
state that as a condition on a verdict assignment; `Model/Pass.lean`
gives the procedure. `choose` is the paper's deterministic tie-break,
shared since it reads only the anchor and the round; `chooseLeast` is
one instance, the least candidate in the identifier order.
-/


namespace LeanDag

namespace FinWhale

variable {Validator : Type*} [Fintype Validator] [DecidableEq Validator]
variable [F : Faults Validator] [P : Params Validator]
variable {BlockId : Type*} [DecidableEq BlockId] {Payload : Type*}
variable {D : Dag Validator BlockId Payload}
variable {S : Slots Validator}

/-- A validator's verdict for a leader slot. -/
inductive Verdict (BlockId : Type*) where
  /-- The slot is decided, and this block of it is committed. -/
  | commit (b : BlockId)
  /-- The slot is decided, and no block of it is committed. -/
  | skip
  /-- The slot is not yet decided. -/
  | undecided
  deriving DecidableEq

/-- A decided verdict, as the relation's option: `some b` for a commit,
`none` for a skip. Read only where the slot is decided. -/
def Verdict.optOf {BlockId : Type*} : Verdict BlockId → Option BlockId
  | Verdict.commit b => some b
  | _ => none

/-- **The anchor of `r`**: the first eligible slot above `r` that is not
skipped. Eligibility is a parameter rather than the fixed `r + 2 < a`,
so nothing here depends on which relation it is. -/
def Anchor (Elig : ℕ → ℕ → Prop) (dec : ℕ → Verdict BlockId) (r a : ℕ) : Prop :=
  Elig r a ∧ dec a ≠ Verdict.skip ∧ ∀ a', Elig r a' → a' < a → dec a' = Verdict.skip

/-- **The reverse pass, as a condition on the verdicts.** The direct
rules are parameters, since each validator evaluates them on its own
view; `choose` is shared, reading only the anchor and the round. -/
structure WellFormed (Elig : ℕ → ℕ → Prop) (dcommit : ℕ → BlockId → Prop) (dskip : ℕ → Prop)
    (choose : BlockId → ℕ → Option BlockId) (dec : ℕ → Verdict BlockId) : Prop where
  /-- A direct commit is taken. -/
  direct_commit : ∀ r l, dcommit r l → dec r = Verdict.commit l
  /-- A direct skip is taken. -/
  direct_skip : ∀ r, dskip r → dec r = Verdict.skip
  /-- Undecided where the anchor is undecided. -/
  indirect_undecided : ∀ r a, (¬ ∃ l, dcommit r l) → ¬ dskip r → Anchor Elig dec r a →
    dec a = Verdict.undecided → dec r = Verdict.undecided
  /-- Decided by the anchor otherwise. -/
  indirect_commit : ∀ r a A, (¬ ∃ l, dcommit r l) → ¬ dskip r → Anchor Elig dec r a →
    dec a = Verdict.commit A →
    dec r = (match choose A r with
      | some b => Verdict.commit b
      | none => Verdict.skip)
  /-- A slot decided without a direct rule was decided from an anchor. -/
  has_anchor : ∀ r, (¬ ∃ l, dcommit r l) → ¬ dskip r → dec r ≠ Verdict.undecided →
    ∃ a, Anchor Elig dec r a

/-- **What the deterministic rule must satisfy**: it names only blocks
the anchor could indirectly commit, and names one whenever there is one
to name. -/
structure ChooseSound (S : Slots Validator) (D : Dag Validator BlockId Payload)
    (choose : BlockId → ℕ → Option BlockId) : Prop where
  /-- Whatever it names is a candidate. -/
  sound : ∀ A r b, choose A r = some b → IndirectCommit S D A r b
  /-- Where there is a candidate, it names one. -/
  total : ∀ A r, (∃ b, IndirectCommit S D A r b) → ∃ b, choose A r = some b

open scoped Classical in
/-- **The deterministic rule, exhibited**: the least candidate in the
identifier order, sound and total by construction, and a function of
the anchor and the round alone, so two validators holding the same
anchor make the same choice. -/
noncomputable def chooseLeast [LinearOrder BlockId] (S : Slots Validator)
    (D : Dag Validator BlockId Payload) (A : BlockId) (r : ℕ) : Option BlockId :=
  if h : ((slotBlocks S D r).filter (fun b => IndirectCommit S D A r b)).Nonempty then
    some (((slotBlocks S D r).filter (fun b => IndirectCommit S D A r b)).min' h)
  else none

end FinWhale

end LeanDag
