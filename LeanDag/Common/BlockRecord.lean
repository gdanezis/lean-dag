import LeanDag.Common.Block
/-!
# The block record

**One universe shape for every rule.** A universe is a set of
identifiers, a block map, closure under references, validity of every
block against a rule's own predicate, and one block per author per
round for the authors the rule's fault model constrains. The core, Nemo
and FinWhale *are* this record at their own validity predicate and
honest set; Hydrozoan is it through its block adapter
(`Hydrozoan/Helpers/Record.lean`); Orcaella and Optimal-Hydrozoan are a
neighbour's record under one further invariant.

**What a validity predicate owes the mechanisms** is `Validity.Mechanised`:
references sit one round below, the predicate reads only referenced
blocks, a reference-free round-zero block is valid, and validity
survives the cut strictly above the horizon. With those four facts the
cut (`Record/Chop.lean`), the fill (`Record/Fill.lean`) and re-genesis
(`Record/Genesis.lean`) are built once, and a rule's mechanism cell is
the generic construction at its instance. A predicate that does not
read the author (`Validity.CopyStable`) also gets the copy fill's
validity for free; the core's fill adds a self reference for its
self-parent clause and proves that block valid itself.

The block-level cut `chopBlk` lives here because it is what the
`chops` obligation is stated against.
-/

namespace LeanDag

variable {Validator : Type*} {BlockId : Type*} {Payload : Type*}

/-- A validity predicate: what a rule asks of one block, read against
the block map. -/
abbrev Validity (Validator BlockId Payload : Type*) :=
  (BlockId → Block Validator BlockId Payload) → Block Validator BlockId Payload → Prop

/-- **The block record**: every universe type in the development, at a
validity predicate `P` and an honest set. `block` is total, with junk
outside `ids`; every clause quantifies over `i ∈ ids`, so the junk is
never observed. -/
structure BlockRecord (Validator BlockId Payload : Type*)
    (P : Validity Validator BlockId Payload) (honest : Finset Validator) where
  /-- Which blocks exist. -/
  ids : Finset BlockId
  /-- What each id denotes. -/
  block : BlockId → Block Validator BlockId Payload
  /-- Every referenced block is present. -/
  complete : ∀ i ∈ ids, ∀ j ∈ (block i).refs, j ∈ ids
  /-- Every block present is valid. -/
  valid : ∀ i ∈ ids, P block (block i)
  /-- An honest author has at most one block per round. -/
  no_equivocation : ∀ i ∈ ids, ∀ j ∈ ids,
    (block i).creator ∈ honest →
    (block i).creator = (block j).creator →
    (block i).round = (block j).round → i = j

namespace BlockRecord

variable {P : Validity Validator BlockId Payload} {honest : Finset Validator}

/-- **A view**: a reference-closed part of the universe. Views share
`U.block`, so they disagree about *which* blocks they hold, never about
what an id denotes. -/
structure View (U : BlockRecord Validator BlockId Payload P honest) where
  /-- The ids this validator holds. -/
  ids : Finset BlockId
  /-- A view holds only blocks that exist. -/
  subset_ids : ids ⊆ U.ids
  /-- A view is closed under references. -/
  complete : ∀ i ∈ ids, ∀ j ∈ (U.block i).refs, j ∈ ids

variable {U : BlockRecord Validator BlockId Payload P honest}

/-- Completeness, as a subset statement. -/
theorem refs_subset {i : BlockId} (hi : i ∈ U.ids) : (U.block i).refs ⊆ U.ids :=
  fun _ hj => U.complete i hi _ hj

/-- **A view is a record.** Its ids under the universe's block map:
closure is the view's, validity and non-equivocation are inherited,
since the block map is unchanged. This is what a rule evaluates its
rules on when it reads a view as a DAG in its own right. -/
def View.toRecord (V : U.View) : BlockRecord Validator BlockId Payload P honest where
  ids := V.ids
  block := U.block
  complete := V.complete
  valid := fun i hi => U.valid i (V.subset_ids hi)
  no_equivocation := fun i hi j hj => U.no_equivocation i (V.subset_ids hi) j (V.subset_ids hj)

@[simp] theorem View.toRecord_ids (V : U.View) : V.toRecord.ids = V.ids := rfl
@[simp] theorem View.toRecord_block (V : U.View) : V.toRecord.block = U.block := rfl

/-- **The full view**: every block of the record. Every honest
validator's eventual view, downward-closed by `U.complete`. -/
def View.full (U : BlockRecord Validator BlockId Payload P honest) : U.View :=
  ⟨U.ids, Finset.Subset.rfl, U.complete⟩

@[simp] theorem View.full_ids (U : BlockRecord Validator BlockId Payload P honest) :
    (View.full U).ids = U.ids := rfl

/-- **A view caught up to round `N`**: it holds every block of the
record at a round at or below `N`. What a validator that has received
everything up to `N` holds, and the hypothesis under which a liveness
result holds of a validator's own view rather than of the full view. -/
def View.CoversUpto (V : U.View) (N : ℕ) : Prop :=
  ∀ b ∈ U.ids, (U.block b).round ≤ N → b ∈ V.ids

/-- The full view is caught up to every horizon. -/
theorem View.coversUpto_full (U : BlockRecord Validator BlockId Payload P honest) (N : ℕ) :
    (View.full U).CoversUpto N :=
  fun _ hb _ => hb

/-- Caught up to `N` is caught up to every lower horizon. -/
theorem View.CoversUpto.mono {V : U.View} {M N : ℕ} (h : V.CoversUpto N) (hMN : M ≤ N) :
    V.CoversUpto M :=
  fun b hb hr => h b hb (le_trans hr hMN)

end BlockRecord

/-! `View.full` and `View.coversUpto_full` are spelled without the
record prefix at every rule; `CoversUpto` itself is reached by dot
notation only, which resolves through each rule's `View` abbreviation. -/
namespace View
export BlockRecord.View (full full_ids coversUpto_full)
end View

/-! ## The cut, over raw block data

The *data* of a cut is the same for every rule: the round is rebased by
`−G`, and blocks at or below the cut — the new base layer, plus junk —
lose their references. -/

section Chop

variable {G : ℕ} {i : BlockId} {blk : BlockId → Block Validator BlockId Payload}

/-- One block of the truncation, over the raw block assignment. -/
def chopBlk (blk : BlockId → Block Validator BlockId Payload) (G : ℕ)
    (i : BlockId) : Block Validator BlockId Payload :=
  if (blk i).round ≤ G then
    { blk i with round := (blk i).round - G, refs := ∅ }
  else
    { blk i with round := (blk i).round - G }

@[simp] theorem chopBlk_creator :
    (chopBlk blk G i).creator = (blk i).creator := by unfold chopBlk; split <;> rfl

@[simp] theorem chopBlk_round :
    (chopBlk blk G i).round = (blk i).round - G := by unfold chopBlk; split <;> rfl

@[simp] theorem chopBlk_payload :
    (chopBlk blk G i).payload = (blk i).payload := by unfold chopBlk; split <;> rfl

theorem chopBlk_refs_of_le
    (h : (blk i).round ≤ G) : (chopBlk blk G i).refs = ∅ := by
  unfold chopBlk; rw [if_pos h]

theorem chopBlk_refs_of_lt
    (h : G < (blk i).round) : (chopBlk blk G i).refs = (blk i).refs := by
  unfold chopBlk; rw [if_neg (by omega)]

theorem chopBlk_of_lt (h : G < (blk i).round) :
    chopBlk blk G i = { blk i with round := (blk i).round - G } := by
  unfold chopBlk; rw [if_neg (by omega)]

theorem chopBlk_refs_subset : (chopBlk blk G i).refs ⊆ (blk i).refs := by
  rcases Nat.lt_or_ge G (blk i).round with h | h
  · rw [chopBlk_refs_of_lt h]
  · rw [chopBlk_refs_of_le h]; exact Finset.empty_subset _

theorem creatorsOf_chopBlk [DecidableEq Validator] (s : Finset BlockId) :
    creatorsOf (chopBlk blk G) s = creatorsOf blk s := by
  simp only [creatorsOf, chopBlk_creator]

end Chop

/-! ## What a validity predicate owes -/

namespace Validity

variable (P : Validity Validator BlockId Payload)

/-- **The four facts the mechanisms consume of a validity predicate.**
Every predicate in the development has them; a rule proves them once and
its cut, fill and re-genesis are the generic constructions. -/
class Mechanised : Prop where
  /-- References sit one round below. -/
  pred : ∀ (blk : BlockId → Block Validator BlockId Payload) (b : Block Validator BlockId Payload),
    P blk b → ∀ j ∈ b.refs, (blk j).round + 1 = b.round
  /-- Validity reads only referenced blocks: two maps agreeing on a
  reference-closed set holding `b`'s references judge `b` alike. -/
  reads : ∀ (blk blk' : BlockId → Block Validator BlockId Payload) (ids : Finset BlockId)
    (b : Block Validator BlockId Payload),
    (∀ i ∈ ids, ∀ j ∈ (blk i).refs, j ∈ ids) → (∀ j ∈ b.refs, j ∈ ids) →
    (∀ j ∈ ids, blk' j = blk j) → P blk b → P blk' b
  /-- A reference-free block at round zero is valid. -/
  base : ∀ (blk : BlockId → Block Validator BlockId Payload) (b : Block Validator BlockId Payload),
    b.round = 0 → b.refs = ∅ → P blk b
  /-- Validity survives the cut strictly above the horizon. -/
  chops : ∀ (blk : BlockId → Block Validator BlockId Payload) (G : ℕ)
    (b : Block Validator BlockId Payload),
    P blk b → G < b.round → P (chopBlk blk G) { b with round := b.round - G }

/-- **The author is not read.** What the copy fill needs: a rule with no
self-parent clause judges a re-authored block as it judged the original. -/
class CopyStable : Prop where
  copy : ∀ (blk : BlockId → Block Validator BlockId Payload) (b : Block Validator BlockId Payload)
    (v : Validator), P blk b → P blk { b with creator := v }

variable {P} in
/-- The obligations transfer along an equivalence of predicates. -/
theorem Mechanised.of_iff {Q : Validity Validator BlockId Payload} [Q.Mechanised]
    (h : ∀ blk b, P blk b ↔ Q blk b) : P.Mechanised where
  pred := fun blk b hp => Mechanised.pred blk b ((h blk b).mp hp)
  reads := fun blk blk' ids b hcl hb hag hp =>
    (h blk' b).mpr (Mechanised.reads blk blk' ids b hcl hb hag ((h blk b).mp hp))
  base := fun blk b h0 hr => (h blk b).mpr (Mechanised.base blk b h0 hr)
  chops := fun blk G b hp hG => (h _ _).mpr (Mechanised.chops blk G b ((h blk b).mp hp) hG)

variable {P} in
theorem CopyStable.of_iff {Q : Validity Validator BlockId Payload} [Q.CopyStable]
    (h : ∀ blk b, P blk b ↔ Q blk b) : P.CopyStable where
  copy := fun blk b v hp => (h _ _).mpr (CopyStable.copy blk b v ((h blk b).mp hp))

end Validity

/-! ## The validity family

Every validity predicate in the development has one shape: references
sit one round below, a non-genesis block references a quorum of
distinct creators at the rule's threshold, and one further clause. The
clause is where the rules differ — the core adds a self-parent,
FinWhale a leader-consistency condition, Hydrozoan nothing beyond
distinct creators, Nemo nothing at all — and it is the only part a rule
proves anything about: given the clause's obligations, `ValidAt` is
`Mechanised` once, and a rule's predicate inherits it along the
equivalence with its own record. -/

/-- A clause a validity predicate adds beyond the common shape. -/
abbrev Clause (Validator BlockId Payload : Type*) :=
  (BlockId → Block Validator BlockId Payload) → Block Validator BlockId Payload → Prop

/-- **The common shape of every validity predicate**, at threshold `q`
with clause `C`. -/
structure ValidAt [DecidableEq Validator] (q : ℕ) (C : Clause Validator BlockId Payload)
    (blk : BlockId → Block Validator BlockId Payload) (b : Block Validator BlockId Payload) :
    Prop where
  /-- Every reference sits in the immediately preceding round. -/
  predecessor : ∀ i ∈ b.refs, (blk i).round + 1 = b.round
  /-- Non-genesis blocks reference `q` distinct creators. -/
  quorum : 0 < b.round → q ≤ (creators blk b).card
  /-- The rule's own clause. -/
  clause : C blk b

/-- **What a clause owes**: the three facts of `Validity.Mechanised` that
concern it, the predecessor fact being the family's. -/
class Clause.Mechanised (C : Clause Validator BlockId Payload) : Prop where
  reads : ∀ (blk blk' : BlockId → Block Validator BlockId Payload) (ids : Finset BlockId)
    (b : Block Validator BlockId Payload),
    (∀ i ∈ ids, ∀ j ∈ (blk i).refs, j ∈ ids) → (∀ j ∈ b.refs, j ∈ ids) →
    (∀ j ∈ ids, blk' j = blk j) → C blk b → C blk' b
  base : ∀ (blk : BlockId → Block Validator BlockId Payload) (b : Block Validator BlockId Payload),
    b.round = 0 → b.refs = ∅ → C blk b
  chops : ∀ (blk : BlockId → Block Validator BlockId Payload) (G : ℕ)
    (b : Block Validator BlockId Payload),
    C blk b → (∀ i ∈ b.refs, (blk i).round + 1 = b.round) → G < b.round →
    C (chopBlk blk G) { b with round := b.round - G }

/-- The clause does not read the creator. -/
class Clause.CopyStable (C : Clause Validator BlockId Payload) : Prop where
  copy : ∀ (blk : BlockId → Block Validator BlockId Payload) (b : Block Validator BlockId Payload)
    (v : Validator), C blk b → C blk { b with creator := v }

namespace Clause

/-- No clause. -/
def none : Clause Validator BlockId Payload := fun _ _ => True

instance : Mechanised (none (Validator := Validator) (BlockId := BlockId)
    (Payload := Payload)) where
  reads := fun _ _ _ _ _ _ _ _ => True.intro
  base := fun _ _ _ _ => True.intro
  chops := fun _ _ _ _ _ _ => True.intro

instance : CopyStable (none (Validator := Validator) (BlockId := BlockId)
    (Payload := Payload)) where
  copy := fun _ _ _ _ => True.intro

/-- No two references share a creator. -/
def distinct : Clause Validator BlockId Payload := fun blk b =>
  ∀ i ∈ b.refs, ∀ j ∈ b.refs, (blk i).creator = (blk j).creator → i = j

instance : Mechanised (distinct (Validator := Validator) (BlockId := BlockId)
    (Payload := Payload)) where
  reads := fun blk blk' _ b _ hb hag h j hj l hl hjl => by
    rw [hag j (hb j hj), hag l (hb l hl)] at hjl
    exact h j hj l hl hjl
  base := fun _ b _ hr j hj => by rw [hr] at hj; exact absurd hj (Finset.notMem_empty j)
  chops := fun blk G b h _ _ j hj l hl hjl => by
    simp only [chopBlk_creator] at hjl
    exact h j hj l hl hjl

instance : CopyStable (distinct (Validator := Validator) (BlockId := BlockId)
    (Payload := Payload)) where
  copy := fun _ _ _ h => h

/-- A non-genesis block references a block by its own creator. Read by
the core; not `CopyStable`, which is why the core's fill adds a self
reference. -/
def selfParent : Clause Validator BlockId Payload := fun blk b =>
  0 < b.round → ∃ i ∈ b.refs, (blk i).creator = b.creator

instance : Mechanised (selfParent (Validator := Validator) (BlockId := BlockId)
    (Payload := Payload)) where
  reads := fun blk blk' _ b _ hb hag h hr => by
    obtain ⟨j, hj, hjc⟩ := h hr
    exact ⟨j, hj, by rw [hag j (hb j hj)]; exact hjc⟩
  base := fun _ b h0 _ hr => by change 0 < b.round at hr; omega
  chops := fun blk G b h _ hG hr => by
    obtain ⟨j, hj, hjc⟩ := h (by change 0 < b.round - G at hr; omega)
    exact ⟨j, hj, by rw [chopBlk_creator]; exact hjc⟩

/-- Two clauses together. -/
def and (C D : Clause Validator BlockId Payload) : Clause Validator BlockId Payload :=
  fun blk b => C blk b ∧ D blk b

instance {C D : Clause Validator BlockId Payload} [Mechanised C] [Mechanised D] :
    Mechanised (and C D) where
  reads := fun blk blk' ids b hcl hb hag h =>
    ⟨Mechanised.reads blk blk' ids b hcl hb hag h.1, Mechanised.reads blk blk' ids b hcl hb hag h.2⟩
  base := fun blk b h0 hr => ⟨Mechanised.base blk b h0 hr, Mechanised.base blk b h0 hr⟩
  chops := fun blk G b h hp hG =>
    ⟨Mechanised.chops blk G b h.1 hp hG, Mechanised.chops blk G b h.2 hp hG⟩

instance {C D : Clause Validator BlockId Payload} [CopyStable C] [CopyStable D] :
    CopyStable (and C D) where
  copy := fun blk b v h => ⟨CopyStable.copy blk b v h.1, CopyStable.copy blk b v h.2⟩

end Clause

section ValidAtMechanised

variable [DecidableEq Validator] {q : ℕ} {C : Clause Validator BlockId Payload}

/-- **The family is mechanised** whenever its clause is. -/
instance ValidAt.mechanised [Clause.Mechanised C] :
    Validity.Mechanised (ValidAt q C) where
  pred := fun _ _ h => h.predecessor
  reads := by
    intro blk blk' ids b hcl hb hagree h
    refine ⟨?_, ?_, Clause.Mechanised.reads blk blk' ids b hcl hb hagree h.clause⟩
    · intro j hj; rw [hagree j (hb j hj)]; exact h.predecessor j hj
    · intro hr
      refine le_trans (h.quorum hr) (Finset.card_le_card ?_)
      intro c hc
      unfold creators creatorsOf at hc ⊢
      obtain ⟨j, hj, hjc⟩ := Finset.mem_image.mp hc
      exact Finset.mem_image.mpr ⟨j, hj, by rw [hagree j (hb j hj)]; exact hjc⟩
  base := by
    intro blk b h0 hr
    refine ⟨?_, ?_, Clause.Mechanised.base blk b h0 hr⟩
    · intro j hj; rw [hr] at hj; exact absurd hj (Finset.notMem_empty j)
    · intro h; rw [h0] at h; exact absurd h (lt_irrefl 0)
  chops := by
    intro blk G b h hG
    refine ⟨?_, ?_, Clause.Mechanised.chops blk G b h.clause h.predecessor hG⟩
    · intro j hj
      have := h.predecessor j hj
      change (chopBlk blk G j).round + 1 = b.round - G
      rw [chopBlk_round]; omega
    · intro hr
      change q ≤ (creatorsOf (chopBlk blk G) b.refs).card
      rw [creatorsOf_chopBlk]
      exact h.quorum (by change 0 < b.round - G at hr; omega)

/-- **And does not read the creator** whenever its clause does not. -/
instance ValidAt.copyStable [Clause.CopyStable C] : Validity.CopyStable (ValidAt q C) where
  copy := fun blk b v h => ⟨h.predecessor, h.quorum, Clause.CopyStable.copy blk b v h.clause⟩

end ValidAtMechanised

/-! ## Quorate validity

A validity predicate is **quorate at `q`** when every non-genesis block
it admits references `q` distinct creators: the counting clause of the
family, named on its own because the hitting lemma and everything built
on it — coverage, persistence, the common core — need nothing else of
validity. The quorum is read off the predicate, so no record restates
it. -/

namespace Validity

/-- Non-genesis blocks reference `q` distinct creators, and `q` is
positive, so a non-genesis block references something. -/
class Quorate [DecidableEq Validator] (P : Validity Validator BlockId Payload)
    (q : outParam ℕ) : Prop where
  quorum : ∀ (blk : BlockId → Block Validator BlockId Payload)
    (b : Block Validator BlockId Payload), P blk b → 0 < b.round → q ≤ (creators blk b).card
  pos : 0 < q

/-- References have distinct creators: the clause the counting arguments
read when two votes of one validator must be one vote. -/
class Distinct (P : Validity Validator BlockId Payload) : Prop where
  distinct : ∀ (blk : BlockId → Block Validator BlockId Payload)
    (b : Block Validator BlockId Payload), P blk b →
    ∀ i ∈ b.refs, ∀ j ∈ b.refs, (blk i).creator = (blk j).creator → i = j

/-- A predicate equivalent to the family with a clause implying distinct
creators has them. -/
theorem Distinct.of_validAt [DecidableEq Validator] {P : Validity Validator BlockId Payload}
    {q : ℕ} {C : Clause Validator BlockId Payload}
    (h : ∀ blk b, P blk b ↔ ValidAt q C blk b)
    (hC : ∀ blk b, C blk b → Clause.distinct blk b) : P.Distinct where
  distinct := fun blk b hp => hC blk b ((h blk b).mp hp).clause

/-- A predicate equivalent to the family at `q` is quorate at `q`. -/
theorem Quorate.of_validAt [DecidableEq Validator] {P : Validity Validator BlockId Payload}
    {q : ℕ} {C : Clause Validator BlockId Payload} (hq : 0 < q)
    (h : ∀ blk b, P blk b ↔ ValidAt q C blk b) : P.Quorate q where
  quorum := fun blk b hp hr => ((h blk b).mp hp).quorum hr
  pos := hq

end Validity

/-! ## Facts of any record

The block-level facts every argument starts from, at any record: what
completeness, the predecessor clause, non-equivocation and the quorum
clause say about a block the record holds. -/

namespace BlockRecord

variable {P : Validity Validator BlockId Payload} {honest : Finset Validator}
variable {U : BlockRecord Validator BlockId Payload P honest}

/-- A reference sits in the round immediately below its referrer. -/
theorem round_of_mem_refs [P.Mechanised] {i j : BlockId} (hi : i ∈ U.ids)
    (hj : j ∈ (U.block i).refs) : (U.block j).round + 1 = (U.block i).round :=
  Validity.Mechanised.pred U.block (U.block i) (U.valid i hi) j hj

/-- **T1.** An honest validator authors at most one block per round, so
two ids in the record with the same honest author and the same round
are the *same id*.

Phrased around the author `v` rather than around `(U.block i).creator`,
because that is how every use site arrives: a quorum intersection
yields an honest validator, and T1 turns two blocks known to be
authored by it into a single concrete id. -/
theorem eq_of_creator_eq {v : Validator} {i j : BlockId}
    (hi : i ∈ U.ids) (hj : j ∈ U.ids) (hv : v ∈ honest)
    (hic : (U.block i).creator = v) (hjc : (U.block j).creator = v)
    (hround : (U.block i).round = (U.block j).round) : i = j :=
  U.no_equivocation i hi j hj (hic ▸ hv) (hic.trans hjc.symm) hround

/-- Two references of one block by one author are one reference. -/
theorem distinct_creators [P.Distinct] {i j k : BlockId} (hi : i ∈ U.ids)
    (hj : j ∈ (U.block i).refs) (hk : k ∈ (U.block i).refs)
    (hc : (U.block j).creator = (U.block k).creator) : j = k :=
  Validity.Distinct.distinct U.block (U.block i) (U.valid i hi) j hj k hk hc

variable [DecidableEq Validator]

/-- References of a non-genesis block carry the record's quorum of
distinct authors. -/
theorem creators_quorum {q : ℕ} [P.Quorate q] {i : BlockId} (hi : i ∈ U.ids)
    (hround : 0 < (U.block i).round) :
    q ≤ (creatorsOf U.block (U.block i).refs).card :=
  Validity.Quorate.quorum U.block (U.block i) (U.valid i hi) hround

/-- A non-genesis block references at least one block. -/
theorem refs_nonempty {q : ℕ} [P.Quorate q] {i : BlockId} (hi : i ∈ U.ids)
    (hround : 0 < (U.block i).round) : (U.block i).refs.Nonempty :=
  nonempty_of_creatorsOf_card_pos
    (lt_of_lt_of_le (Validity.Quorate.pos (P := P)) (creators_quorum hi hround))

end BlockRecord

/-! ## Non-equivocation on a set

Every counting argument reads non-equivocation on some set of validators:
the record's own honest set, or a larger one a rule proves it for, as the
hybrid model does for its crash-prone validators. Stated once so the
arguments are stated once. -/

namespace BlockRecord

variable {P : Validity Validator BlockId Payload} {honest : Finset Validator}
variable {U : BlockRecord Validator BlockId Payload P honest}

/-- The validators of `Hon` author at most one block per round in `U`. -/
def NoEquivOn (U : BlockRecord Validator BlockId Payload P honest) (Hon : Finset Validator) :
    Prop :=
  ∀ i ∈ U.ids, ∀ j ∈ U.ids, (U.block i).creator ∈ Hon →
    (U.block i).creator = (U.block j).creator →
    (U.block i).round = (U.block j).round → i = j

instance [DecidableEq Validator] [DecidableEq BlockId]
    (U : BlockRecord Validator BlockId Payload P honest) (Hon : Finset Validator) :
    Decidable (U.NoEquivOn Hon) :=
  inferInstanceAs (Decidable (∀ _ ∈ _, ∀ _ ∈ _, _ → _ → _ → _))

/-- The record's honest set does not equivocate: its own clause. -/
theorem noEquivOn_honest (U : BlockRecord Validator BlockId Payload P honest) :
    U.NoEquivOn honest :=
  U.no_equivocation

/-- T1 on the set: two ids with one author from `Hon` and one round are one id. -/
theorem NoEquivOn.eq_of_creator_eq {Hon : Finset Validator} (hne : U.NoEquivOn Hon)
    {v : Validator} {i j : BlockId} (hi : i ∈ U.ids) (hj : j ∈ U.ids) (hv : v ∈ Hon)
    (hic : (U.block i).creator = v) (hjc : (U.block j).creator = v)
    (hround : (U.block i).round = (U.block j).round) : i = j :=
  hne i hi j hj (hic ▸ hv) (hic.trans hjc.symm) hround

end BlockRecord

end LeanDag
