import LeanDag.FinWhale.Model.Params
import LeanDag.Common.Causality
import LeanDag.Common.BlockRecord
import LeanDag.Common.Support
import LeanDag.Common.Slots
/-!
# FinWhale — the fast path, as the paper defines it

The vocabulary the paper states Lemma 4 in: votes, leader-consistency,
the two branches of FP-evidence, and the direct decision rules. Only
what the fast path needs is modelled; the slow path is Mysticeti's and
unchanged. `ExposesEquivocationBy` is the parent-set reading of "exposes
equivocation", which coincides with the paper's causal-history one
because a parent's own references sit one round below it and validity
gives each parent at most one edge per validator.
-/

namespace LeanDag

namespace FinWhale

variable {Validator : Type*} [Fintype Validator] [DecidableEq Validator]
variable [F : Faults Validator] [P : Params Validator]
variable {BlockId : Type*} [DecidableEq BlockId] {Payload : Type*}

/-- **Validity, as FinWhale extends Mysticeti's**: the core's three
clauses, plus leader exclusion, which the fast path's counting rests
on. -/
structure ValidHere (blk : BlockId → Block Validator BlockId Payload)
    (b : Block Validator BlockId Payload) : Prop where
  /-- Every edge points to the round immediately below. -/
  predecessor : ∀ i ∈ b.refs, (blk i).round + 1 = b.round
  /-- No two edges share a validator. -/
  distinct_creators : ∀ i ∈ b.refs, ∀ j ∈ b.refs, (blk i).creator = (blk j).creator → i = j
  /-- A non-genesis block carries `n − f` edges by distinct validators. -/
  quorum : 0 < b.round → quorumCard Validator ≤ (creators blk b).card
  /-- **FinWhale's clause**: `Clause.leaderExcluded` of the common
  layer, a genuine but harmless strengthening of the paper's rule. -/
  leader_clause : Clause.leaderExcluded blk b

/-! **FinWhale's validity is the family** at the core's quorum, with
distinct creators and leader exclusion, so the four instances are the
family's. Each carries the equivalence itself rather than a shared
theorem: this is a `Model/` file, and the arc's partition admits
definitions and instances only (`scripts/check-arc-holes.py`). -/

/-- **Mechanised**, along the family. -/
instance ValidHere.mechanised :
    Validity.Mechanised
      (ValidHere (Validator := Validator) (BlockId := BlockId) (Payload := Payload)) :=
  Validity.Mechanised.of_iff
    (Q := ValidAt (quorumCard Validator) (Clause.distinct.and Clause.leaderExcluded)) fun _ _ =>
    ⟨fun h => ⟨h.predecessor, h.quorum, h.distinct_creators, h.leader_clause⟩,
     fun h => ⟨h.predecessor, h.clause.1, h.quorum, h.clause.2⟩⟩

/-- **With distinct creators among references.** -/
instance ValidHere.distinct :
    Validity.Distinct
      (ValidHere (Validator := Validator) (BlockId := BlockId) (Payload := Payload)) :=
  Validity.Distinct.of_validAt (C := Clause.distinct.and Clause.leaderExcluded) (fun _ _ =>
    ⟨fun h => ⟨h.predecessor, h.quorum, h.distinct_creators, h.leader_clause⟩,
     fun h => ⟨h.predecessor, h.clause.1, h.quorum, h.clause.2⟩⟩) fun _ _ h => h.1

/-- **And quorate at the core's quorum.** -/
instance ValidHere.quorate :
    Validity.Quorate
      (ValidHere (Validator := Validator) (BlockId := BlockId) (Payload := Payload))
      (quorumCard Validator) :=
  Validity.Quorate.of_validAt (C := Clause.distinct.and Clause.leaderExcluded)
    (by have := F.card_validators; omega) fun _ _ =>
    ⟨fun h => ⟨h.predecessor, h.quorum, h.distinct_creators, h.leader_clause⟩,
     fun h => ⟨h.predecessor, h.clause.1, h.quorum, h.clause.2⟩⟩

/-- **And does not read the creator**, so the copy fill is valid. -/
instance ValidHere.copyStable :
    Validity.CopyStable
      (ValidHere (Validator := Validator) (BlockId := BlockId) (Payload := Payload)) :=
  Validity.CopyStable.of_iff
    (Q := ValidAt (quorumCard Validator) (Clause.distinct.and Clause.leaderExcluded)) fun _ _ =>
    ⟨fun h => ⟨h.predecessor, h.quorum, h.distinct_creators, h.leader_clause⟩,
     fun h => ⟨h.predecessor, h.clause.1, h.quorum, h.clause.2⟩⟩

/-- **A DAG the communication component can build**: the block record
at FinWhale's validity, with non-equivocation asked of the correct
validators. Equivocating blocks are admitted, of faulty validators
only. -/
abbrev Dag (Validator BlockId Payload : Type*) [Fintype Validator]
    [DecidableEq Validator] [Faults Validator] :=
  BlockRecord Validator BlockId Payload ValidHere (Correct : Finset Validator)

variable {D : Dag Validator BlockId Payload}

/-! **Which slots may anchor which** is the shared `EligibleAt` at wave
two: the anchor's candidate must sit at least three rounds above the
one it anchors. -/

/-- The validators whose round-`(r+1)` block references `l`: `l`'s voters,
the record's `supporters` at the round above `l`. -/
abbrev voters (D : Dag Validator BlockId Payload) (l : BlockId) : Finset Validator :=
  supporters D l ((D.block l).round + 1)

/-- The parents of `b`, as validators. -/
def parentSet (D : Dag Validator BlockId Payload) (b : BlockId) : Finset Validator :=
  creatorsOf D.block ((D.block b).refs)

/-- The parents of `b` that vote for the leader block `l`. -/
def parentsVoting (D : Dag Validator BlockId Payload) (b l : BlockId) : Finset Validator :=
  creatorsOf D.block (((D.block b).refs).filter (fun q => l ∈ (D.block q).refs))

/-- Two blocks of the same slot: one leader, one round, not equal. -/
def Conflicting (D : Dag Validator BlockId Payload) (l l' : BlockId) : Prop :=
  l ≠ l' ∧ (D.block l).round = (D.block l').round ∧
    (D.block l).creator = (D.block l').creator

instance (D : Dag Validator BlockId Payload) (l l' : BlockId) :
    Decidable (Conflicting D l l') := inferInstanceAs (Decidable (_ ∧ _ ∧ _))

/-- **Exposing a validator's equivocation, the parent-set reading**: two
parents of `b` vote for two different blocks of `v`. Stated at a
validator rather than at a leader, which is what keeps it
schedule-free and hence bandable. -/
def ExposesEquivocationBy (D : Dag Validator BlockId Payload) (b : BlockId)
    (v : Validator) : Prop :=
  ∃ l ∈ (D.ids : Finset BlockId), ∃ l' ∈ (D.ids : Finset BlockId),
    Conflicting D l l' ∧ (D.block l).creator = v ∧
      (parentsVoting D b l).Nonempty ∧ (parentsVoting D b l').Nonempty

instance (D : Dag Validator BlockId Payload) (b : BlockId) (v : Validator) :
    Decidable (ExposesEquivocationBy D b v) :=
  inferInstanceAs (Decidable (∃ _ ∈ _, ∃ _ ∈ _, _))

/-- **FP-evidence**, the two branches of the paper's definition: `f + p`
parents voting for `l` and fewer than that for any conflicting block
where the equivocation is seen, `f + p − 1` where it is not. -/
def FPEvidence (D : Dag Validator BlockId Payload) (b l : BlockId) : Prop :=
  if ExposesEquivocationBy D b (D.block l).creator then
    F.f + P.p ≤ (parentsVoting D b l).card ∧
      ∀ l' ∈ (D.ids : Finset BlockId), Conflicting D l l' →
        (parentsVoting D b l').card + 1 ≤ F.f + P.p
  else
    F.f + P.p ≤ (parentsVoting D b l).card + 1

instance (D : Dag Validator BlockId Payload) (b l : BlockId) :
    Decidable (FPEvidence D b l) := by
  unfold FPEvidence; infer_instance

/-- **An SP-certificate**, Mysticeti's, at this committee's quorum. -/
def SPCertificate (D : Dag Validator BlockId Payload) (b l : BlockId) : Prop :=
  spQuorum Validator ≤ (parentsVoting D b l).card

instance (D : Dag Validator BlockId Payload) (b l : BlockId) :
    Decidable (SPCertificate D b l) := inferInstanceAs (Decidable (_ ≤ _))

/-- **The fast direct commit**: `n − p` distinct validators vote for `l`
one round up. -/
def FastCommit (D : Dag Validator BlockId Payload) (l : BlockId) : Prop :=
  fastCard Validator ≤ (voters D l).card

instance (D : Dag Validator BlockId Payload) (l : BlockId) :
    Decidable (FastCommit D l) := inferInstanceAs (Decidable (_ ≤ _))

end FinWhale

end LeanDag
