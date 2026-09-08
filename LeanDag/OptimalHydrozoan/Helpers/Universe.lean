import LeanDag.OptimalHydrozoan.Model.Universe
import LeanDag.Hydrozoan.Helpers.Block
/-!
# Optimal-Hydrozoan: universe lemmas

Not part of the audit surface. The projection to Hydrozoan's universe,
exclusion at every schedule from the clause, and the two ways a witness
model builds an Optimal universe.
-/

namespace LeanDag

namespace OptimalHydrozoan

open LeanDag.Hydrozoan

variable {Replica BlockId : Type*} [Fintype Replica] [DecidableEq Replica]
  [DecidableEq BlockId] [F : LeanDag.Hydrozoan.Faults Replica]

@[simp] theorem OptUniverse.toBlockRecord_ids (U : OptUniverse Replica BlockId) :
    U.toBlockRecord.ids = U.ids := rfl

@[simp] theorem OptUniverse.toBlockRecord_block (U : OptUniverse Replica BlockId) :
    U.toBlockRecord.block = U.block := rfl

/-- **An Optimal universe from a Hydrozoan one whose blocks all satisfy
the clause.** -/
def OptUniverse.ofExcluded (U : LeanDag.Hydrozoan.BlockUniverse Replica BlockId)
    (h : ∀ i ∈ U.ids, Clause.leaderExcluded U.block (U.block i)) : OptUniverse Replica BlockId :=
  { U with valid := fun i hi => ⟨U.valid i hi, h i hi⟩ }

@[simp] theorem OptUniverse.ofExcluded_toBlockRecord
    (U : LeanDag.Hydrozoan.BlockUniverse Replica BlockId)
    (h : ∀ i ∈ U.ids, Clause.leaderExcluded U.block (U.block i)) :
    (OptUniverse.ofExcluded U h).toBlockRecord = U := rfl

/-- **An Optimal universe from one with no equivocation**: the clause is
vacuous when no replica has two blocks in one round. -/
def OptUniverse.ofNoEquivocation (U : LeanDag.Hydrozoan.BlockUniverse Replica BlockId)
    (h : ∀ i ∈ U.ids, ∀ j ∈ U.ids, (U.block i).creator = (U.block j).creator →
      (U.block i).round = (U.block j).round → i = j) : OptUniverse Replica BlockId :=
  OptUniverse.ofExcluded U fun b hb v => Or.inl fun i hi j hj x hx y hy hxv hyv => by
    have hiU := U.complete b hb i hi
    have hjU := U.complete b hb j hj
    have hxU := U.complete i hiU x hx
    have hyU := U.complete j hjU y hy
    have hir := (U.valid b hb).predecessor i hi
    have hjr := (U.valid b hb).predecessor j hj
    have hxr := (U.valid i hiU).predecessor x hx
    have hyr := (U.valid j hjU).predecessor y hy
    exact h x hxU y hyU (hxv.trans hyv.symm) (by omega)

@[simp] theorem OptUniverse.ofNoEquivocation_toBlockRecord
    (U : LeanDag.Hydrozoan.BlockUniverse Replica BlockId)
    (h : ∀ i ∈ U.ids, ∀ j ∈ U.ids, (U.block i).creator = (U.block j).creator →
      (U.block i).round = (U.block j).round → i = j) :
    (OptUniverse.ofNoEquivocation U h).toBlockRecord = U := rfl

variable [S : Slots Replica]

/-- **An Optimal universe is leader-excluded at every schedule**: the
clause at each block, read at the slot. -/
theorem OptUniverse.leader_excluded (U : OptUniverse Replica BlockId) :
    LeaderExcluded (S := S) U.toBlockRecord := by
  intro b hb k _ hwit j hj hjc
  obtain ⟨L₁, L₂, hL₁, hL₂, hne, ⟨j₁, hj₁, hv₁⟩, ⟨j₂, hj₂, hv₂⟩⟩ := hwit
  rcases (U.valid b hb).2 (S.leader k) with hcons | hnone
  · exact hne (hcons j₁ hj₁ j₂ hj₂ L₁ hv₁ L₂ hv₂ hL₁.2.2 hL₂.2.2)
  · exact hnone j hj hjc

omit [DecidableEq BlockId] in
/-- Witnessing an equivocation, read off the refs' refs: the two
candidates are votes' targets, two references below `b`. -/
theorem witnessesEquivocation_iff_refs (U : LeanDag.Hydrozoan.BlockUniverse Replica BlockId)
    (k : ℕ) (b : BlockId) :
    WitnessesEquivocation U k b ↔
      ∃ j₁ ∈ (U.block b).refs, ∃ L₁ ∈ (U.block j₁).refs,
      ∃ j₂ ∈ (U.block b).refs, ∃ L₂ ∈ (U.block j₂).refs,
        IsLeaderBlock U k L₁ ∧ IsLeaderBlock U k L₂ ∧ L₁ ≠ L₂ := by
  constructor
  · rintro ⟨L₁, L₂, h₁, h₂, hne, ⟨j₁, hj₁, hv₁⟩, ⟨j₂, hj₂, hv₂⟩⟩
    exact ⟨j₁, hj₁, L₁, hv₁, j₂, hj₂, L₂, hv₂, h₁, h₂, hne⟩
  · rintro ⟨j₁, hj₁, L₁, hv₁, j₂, hj₂, L₂, hv₂, h₁, h₂, hne⟩
    exact ⟨L₁, L₂, h₁, h₂, hne, ⟨j₁, hj₁, hv₁⟩, ⟨j₂, hj₂, hv₂⟩⟩

/-- Witnessing an equivocation is decidable, through the refs' form. -/
instance decidableWitnessesEquivocation
    (U : LeanDag.Hydrozoan.BlockUniverse Replica BlockId) (k : ℕ) (b : BlockId) :
    Decidable (WitnessesEquivocation U k b) :=
  decidable_of_iff _ (witnessesEquivocation_iff_refs U k b).symm

omit [DecidableEq BlockId] in
/-- A universe with no two blocks of one creator in one round witnesses no
equivocation anywhere. -/
theorem not_witnessesEquivocation_of_noEquivocation
    (U : LeanDag.Hydrozoan.BlockUniverse Replica BlockId)
    (h : ∀ i ∈ U.ids, ∀ j ∈ U.ids, (U.block i).creator = (U.block j).creator →
      (U.block i).round = (U.block j).round → i = j)
    (k : ℕ) (b : BlockId) : ¬ WitnessesEquivocation U k b := by
  rintro ⟨L₁, L₂, hL₁, hL₂, hne, -, -⟩
  exact hne (h L₁ hL₁.1 L₂ hL₂.1 (hL₁.2.2.trans hL₂.2.2.symm)
    (hL₁.2.1.trans hL₂.2.1.symm))

end OptimalHydrozoan

end LeanDag
