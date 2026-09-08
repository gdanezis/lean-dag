import LeanDag.FinWhale.Model.Decision
import LeanDag.Mysticeti.ViewPace
/-!
# FinWhale — the interfaces liveness supplies and safety consumes

Three definitions that pass information between layers without either
learning which schedule produced it. `CommitsCorrectLeaders` is the
liveness input, supplied by `commits_of_creation` and
`commits_of_reactive`; `SeesCommits` is the form Lemma 23 consumes; and
`settled` is the instant by which every reliable block up to the
horizon has arrived.
-/

namespace LeanDag

namespace FinWhale

variable {Validator : Type} [Fintype Validator] [DecidableEq Validator]
variable [F : Faults Validator] [P : Params Validator]
variable {BlockId : Type} [DecidableEq BlockId] {Payload : Type}
variable {D : Dag Validator BlockId Payload}
variable {U : BlockUniverse Validator BlockId Payload} {T : Finset Validator} {M : ℕ}
variable {S : Slots Validator}

/-- **The liveness input, as an interface.** Every correct-led slot past
the coverage round and below the horizon carries a direct commit. Two
routes supply it — `commits_of_reactive`, from the reactive schedule's
wait clauses, and `commits_of_creation`, from the block-creation
conditions themselves — and nothing below cares which. -/
def CommitsCorrectLeaders (S : Slots Validator) (D : Dag Validator BlockId Payload)
    (R N : ℕ) : Prop :=
  ∀ s, R ≤ S.slotRound s → S.slotRound s + 2 ≤ N → S.leader s ∈ (Correct : Finset Validator) →
    ∃ l ∈ slotBlocks S D s, SPCommitBy D l (Correct : Finset Validator)

/-- **What Lemma 23 consumes**: the deciding validator *sees* a direct
commit at every correct-led slot below the horizon. One clause where
there were two — a commit in the universe, and the view seeing it —
because the second is where a view's holdings enter and the first is
where the schedule does. -/
def SeesCommits (S : Slots Validator) (D : Dag Validator BlockId Payload)
    (dc : ℕ → BlockId → Prop) (R N : ℕ) : Prop :=
  ∀ s, R ≤ S.slotRound s → S.slotRound s + 2 ≤ N → S.leader s ∈ (Correct : Finset Validator) →
    ∃ l, l ∈ slotBlocks S D s ∧ dc s l

/-- The instant by which every reliable block of every round up to `M`
has arrived: the latest build of any of those rounds, plus one delay. -/
def settled (pc : PaceCore U T M) : ℕ :=
  (Finset.range (M + 1)).sup (fun n => pc.latest n + pc.delay)

end FinWhale

end LeanDag
