import LeanDag.Properties.Carrier
/-!
# What a commit names

`docs/target-properties.md` §11.5 item 4. A verdict of `some L` is a
claim about a block, and this is the property that says the claim is
about a **real** block — present in the DAG, at the slot's round, by
the slot's leader. Nothing above the carrier needs it until a
consumer reasons about the committed block itself rather than about the
verdict; then it needs it immediately, because `Decided S V k (some L)`
alone says nothing about `L` at all.

**Seven protocols proved this before it had a name.** `Mysticeti`,
`Odontoceti`, `Nemo`, `Mahi-Mahi`, `Hybrid`, `Hydrozoan` and
`Optimal-Hydrozoan` each carry an `isLeaderBlock_of_decided`, and
`Integration/Hydrozoan/ChopDecided.lean` carries an eighth copy for a
second schedule. Every one is the same two-case discharge: a commit
constructor carries its `IsLeaderBlock` premise, and a skip constructor
concludes `none`. That is what a property is for.

**The consumer is chain quality.** `Quality/Coverage.lean` and
`Quality/Inclusion.lean` take a commit and then reason about `L`'s
round and causal cone — `card_coveredAt_ge` wants `L ∈ U.ids`, and the
ledger wants the same. The structural half of that arc, the density
bound, is about valid DAGs and needs no rule; this property is the
whole of its dependence on one.
-/

namespace LeanDag

namespace Properties

variable {Validator : Type} [Fintype Validator] [DecidableEq Validator]
variable {BlockId : Type} [DecidableEq BlockId] {Payload : Type}
variable {R : DagRule Validator BlockId Payload}

/-- **A slot's candidate**, in the vocabulary the carrier supplies: the
right round, the right author, present. Every protocol's
`IsLeaderBlock` is this. -/
def DagRule.IsCandidate (R : DagRule Validator BlockId Payload)
    (S : Slots Validator) (U : R.Universe) (k : ℕ) (L : BlockId) : Prop :=
  L ∈ R.ids U ∧ (R.block U L).round = S.slotRound k ∧
    (R.block U L).creator = S.leader k

/-- Decidable on concrete data, so a witness can settle it by `decide`. -/
instance instDecidableIsCandidate (R : DagRule Validator BlockId Payload) (S : Slots Validator)
    (U : R.Universe) (k : ℕ) (L : BlockId) : Decidable (R.IsCandidate S U k L) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _))

/-- **A commit names the slot's candidate.** Where a rule commits `L`
at slot `k`, `L` is a block the universe holds, at that slot's round,
authored by that slot's leader.

Not derivable from the band. `Banded` says which DAGs a verdict cannot
tell apart; it says nothing about what the verdict's payload denotes,
and a rule that committed an id it had never seen would satisfy every
band. -/
def CommitsCandidate (R : DagRule Validator BlockId Payload) : Prop :=
  ∀ (S : Slots Validator) (U : R.Universe) (V : R.View U) (k : ℕ) (L : BlockId),
    R.Decided S V k (some L) → R.IsCandidate S U k L

namespace CommitsCandidate

variable {S : Slots Validator} {U : R.Universe} {V : R.View U} {k : ℕ} {L : BlockId}

/-- The committed block is a block. -/
theorem mem (h : CommitsCandidate R) (hd : R.Decided S V k (some L)) :
    L ∈ R.ids U := (h S U V k L hd).1

/-- At the slot's round. -/
theorem round (h : CommitsCandidate R) (hd : R.Decided S V k (some L)) :
    (R.block U L).round = S.slotRound k := (h S U V k L hd).2.1

/-- Authored by the slot's leader. -/
theorem creator (h : CommitsCandidate R) (hd : R.Decided S V k (some L)) :
    (R.block U L).creator = S.leader k := (h S U V k L hd).2.2

/-- **A commit's causal cone is real and below it.** Everything the
committed block reaches is a block of the universe, and everything it
reaches *strictly* sits below the slot's round. The shape every
chain-quality statement starts from, and the whole of what such a
statement needs from the rule. -/
theorem reaches_mem (h : CommitsCandidate R)
    (hd : R.Decided S V k (some L)) {b : BlockId}
    (hb : ReachesFrom (R.block U) L b) : b ∈ R.ids U :=
  (R.causal U).mem_ids_of_reaches (h.mem hd) hb

end CommitsCandidate

end Properties

end LeanDag
