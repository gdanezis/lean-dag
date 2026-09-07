import LeanDag.Common.BlockDag
import LeanDag.Common.Causality
/-!
# Causal history

`spec.md` §3.4 and T2.

`Reaches U c b` says `b` lies in the causal history of `c`: one can walk
from `c` down to `b` by following references zero or more times. This is the
relation the persistence theorem (T3) concludes.

The walk itself is `Causality.lean`'s, stated over the raw block data: a
universe supplies a `CausalStructure` — references stay inside `ids`, and a
reference sits one round below — and everything here is that layer read at
`U.block`/`U.ids`. What remained genuinely Byzantine was the self-parent descent, now `SelfParent.reaches_of_creator`,
which needs the self-parent clause and non-equivocation, neither of which the
structural layer knows about.

Note that T3 inducts on the round *number*, an ordinary `ℕ`, not on `Reaches`
itself; no well-founded relation instance is needed, only the fact that a
block's references sit at a strictly smaller round.
-/

namespace LeanDag

variable {Validator : Type*} [DecidableEq Validator]
variable {BlockId : Type*} {Payload : Type*}
variable {P : Validity Validator BlockId Payload} {honest : Finset Validator}
variable {U : BlockRecord Validator BlockId Payload P honest}

/-- **A block record is a causal structure.** The two facts the history
layer consumes, projected out of the record's completeness and the
predecessor fact its validity owes. Stated at the record, so every
rule's universe has it. -/
theorem BlockRecord.causal [P.Mechanised] (U : BlockRecord Validator BlockId Payload P honest) :
    CausalStructure U.block U.ids :=
  ⟨U.complete, fun i hi j hj => Validity.Mechanised.pred U.block (U.block i) (U.valid i hi) j hj⟩

/-- `Reaches U c b` — `b` lies in the causal history of `c`. -/
def Reaches (U : BlockRecord Validator BlockId Payload P honest) : BlockId → BlockId → Prop :=
  ReachesFrom U.block

namespace Reaches

/-- Every block is in its own causal history. -/
@[refl]
theorem refl {c : BlockId} : Reaches U c c :=
  ReachesFrom.refl

/-- A direct reference is one step of causal history. -/
theorem single {i j : BlockId} (h : j ∈ (U.block i).refs) : Reaches U i j :=
  ReachesFrom.single h

/-- Causal history composes. This is what glues `c → i` onto `i` reaches `b`
at the end of both branches of T3. -/
theorem trans {a b c : BlockId} (h₁ : Reaches U a b) (h₂ : Reaches U b c) : Reaches U a c :=
  ReachesFrom.trans h₁ h₂

/-- Prepend a direct reference: if `i` references `j` and `j` reaches `b`,
then `i` reaches `b`. The exact shape T3's inductive step needs. -/
theorem of_mem_refs {i j b : BlockId} (hij : j ∈ (U.block i).refs) (hjb : Reaches U j b) :
    Reaches U i b :=
  ReachesFrom.of_mem_refs hij hjb

end Reaches

variable [P.Mechanised]

/-- Causal history stays inside the universe: completeness propagates along
every step. -/
theorem mem_ids_of_reaches {c b : BlockId} (hc : c ∈ U.ids) (h : Reaches U c b) : b ∈ U.ids :=
  U.causal.mem_ids_of_reaches hc h

/-! A block with no references reaches only itself — in particular genesis
blocks are causal-history leaves. That is `Causality.lean`'s
`eq_of_reaches_of_refs_empty`, which applies here unchanged: it is stated
over the block assignment, and `Reaches U` *is* `ReachesFrom U.block`. -/

/-- **T2.** Causal history runs downward in rounds: anything `c` reaches
sits at a round no greater than `c`'s.

This is the substantive half of T2 — reflexivity, single steps and
transitivity are inherited from `ReflTransGen`. It rests on `spec.md` §3.2's
predecessor condition, which is the second field of the universe's
`CausalStructure`. -/
theorem round_le_of_reaches {c b : BlockId} (hc : c ∈ U.ids) (h : Reaches U c b) :
    (U.block b).round ≤ (U.block c).round :=
  U.causal.round_le_of_reaches hc h

/-- A block cannot reach anything strictly above it. Contrapositive of T2,
and the form that rules out spurious causal links. -/
theorem not_reaches_of_round_lt {c b : BlockId} (hc : c ∈ U.ids)
    (h : (U.block c).round < (U.block b).round) : ¬ Reaches U c b :=
  U.causal.not_reaches_of_round_lt hc h

/-! ## Views

`spec.md` T6a. A view is downward-closed, so causal history computed inside
one coincides with causal history in the universe. That is what lets two
validators holding *different* views nonetheless agree about what lies in a
given block's history — the check does not depend on which view asks.

Both facts below are the structural layer's `mem_of_reaches_of_closed` at a
view's holdings rather than a universe's population: the closure is all the
walk ever needed. -/

omit [P.Mechanised] in
/-- **T6a.** Causal history never escapes a view. -/
theorem View.mem_of_reaches {U : BlockRecord Validator BlockId Payload P honest}
    {V : U.View} {c b : BlockId}
    (hc : c ∈ V.ids) (h : Reaches U c b) : b ∈ V.ids :=
  mem_of_reaches_of_closed V.complete hc h

omit [P.Mechanised] in
/-- **T6a, in the form the commit rules consume.** Asking "is there a `P`-block
in `c`'s causal history?" gives the same answer whether or not the search is
confined to the view. Restricting to `V` changes nothing, because the answer
could never have lain outside it.

This is what makes a view-relative certificate check well defined: two
validators with different views but the same anchor cannot disagree. -/
theorem View.exists_reaches_iff {U : BlockRecord Validator BlockId Payload P honest}
    {V : U.View} {Q : BlockId → Prop} {c : BlockId}
    (hc : c ∈ V.ids) :
    (∃ b, b ∈ V.ids ∧ Q b ∧ Reaches U c b) ↔ (∃ b, Q b ∧ Reaches U c b) := by
  constructor
  · rintro ⟨b, _, hP, hr⟩
    exact ⟨b, hP, hr⟩
  · rintro ⟨b, hP, hr⟩
    exact ⟨b, View.mem_of_reaches hc hr, hP, hr⟩

end LeanDag
