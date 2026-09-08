import LeanDag.Properties.Extends
import LeanDag.Properties.Derived.Persist
/-!
# Skippability: settling an unsupported slot without an anchor

**Optional.** `docs/target-properties.md` §11.4c. A protocol may show
this and need not: if every block of `T` one round above a slot
references none of that slot's candidates, the protocol skips the
slot, with the size `T` must reach left as a grade since it differs by
rule.

It is a claim about *promptness*, not about liveness. A rule without
it still settles a fill's fresh candidate once an anchor resolves it:
the anchored case splits on whether a candidate is reachable from the
anchor, and a fresh one falls on the negative side, since nothing old
references it and the anchor is old (`Banded`'s `not_certifiedIn_band_novel`
and its analogues). So eventual decision after a fill rests on
`Descends`, which every protocol has, rather than on a direct skip,
which only some do — Nemo has none.

`unsupported_of_novel` is the bridge from the mechanism's side: after an
extension, a slot all of whose candidates are novel is unsupported by
the old blocks, since an old block references only old blocks
(`Extends.old_refs_old`).
-/

namespace LeanDag

namespace Properties

variable {Validator : Type} [Fintype Validator] [DecidableEq Validator]
variable {BlockId : Type} [DecidableEq BlockId] {Payload : Type}
variable {R : DagRule Validator BlockId Payload}

/-- **A slot's candidates are unsupported by `T`**: every `T`-authored
block in view one round above the slot references none of them. -/
def Unsupported (R : DagRule Validator BlockId Payload) (S : Slots Validator)
    (U : R.Universe) (V : R.View U) (T : Finset Validator) (k : ℕ) : Prop :=
  ∀ c, c ∈ R.viewIds V → (R.block U c).creator ∈ T →
    (R.block U c).round = S.slotRound k + 1 →
    ∀ L, R.IsCandidate S U k L → L ∉ (R.block U c).refs

/-- **`T` is present at a round, in view**: each member has a block
there that the view holds. -/
def PresentAt (R : DagRule Validator BlockId Payload) {U : R.Universe} (V : R.View U)
    (T : Finset Validator) (r : ℕ) : Prop :=
  ∀ v ∈ T, ∃ c, c ∈ R.viewIds V ∧ (R.block U c).creator = v ∧ (R.block U c).round = r

/-- **Skippability, graded.** A slot whose candidates `T` does not
support is skipped, provided `T` meets the protocol's condition. -/
def SkipsUnsupported (R : DagRule Validator BlockId Payload)
    (Ok : Finset Validator → Prop) : Prop :=
  ∀ (S : Slots Validator) (U : R.Universe) (V : R.View U) (T : Finset Validator) (k : ℕ),
    Ok T → PresentAt R V T (S.slotRound k + 1) → Unsupported R S U V T k →
    R.Decided S V k none

namespace SkipsUnsupported

variable {Ok Ok' : Finset Validator → Prop}

end SkipsUnsupported

/-- **The bridge from the mechanism**: after an extension, a slot all of
whose candidates are novel is unsupported by any `T` whose voting-round
blocks are old. -/
theorem unsupported_of_novel {U U' : R.Universe} (he : Extends R U U')
    {S : Slots Validator} {V' : R.View U'} {T : Finset Validator} {k : ℕ}
    (hnov : ∀ L, R.IsCandidate S U' k L → Novel R U U' L)
    (hold : ∀ c, c ∈ R.viewIds V' → (R.block U' c).creator ∈ T →
      (R.block U' c).round = S.slotRound k + 1 → c ∈ R.ids U) :
    Unsupported R S U' V' T k := by
  intro c hcV hT hr L hL hmem
  exact (hnov L hL).2 (he.old_refs_old (hold c hcV hT hr) hmem)

end Properties

end LeanDag
