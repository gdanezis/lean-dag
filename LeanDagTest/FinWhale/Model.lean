import LeanDag.FinWhale.Procedure.Order
import LeanDag.FinWhale.Rotation
import LeanDag.FinWhale.Procedure.Decided
import LeanDag.FinWhale.View
import LeanDag.FinWhale.Procedure.Pass
import Mathlib.Tactic.IntervalCases
import LeanDag.FinWhale.Procedure.View

/-!
# FinWhale witnesses — the commit rules on data

Every definition of `LeanDag/FinWhale/` settled by `decide` on a concrete
execution before anything is proved from it (`finwhale.md` §7).

The committee is the smallest non-degenerate one: `f = 2` and `p = 2`, so
`n = 3f + 2p − 1 = 9`, the slow-path quorum is `2f + p = 6`, block
validity asks for `n − f = 7` parents and the fast path asks for
`n − p = 7` votes. At `p = 1` the slow-path quorum and the validity
quorum coincide, and the gap between them would go untested.

Three executions, because the rules they exercise exclude one another.
`Dfast` commits the round-0 leader by both paths. `Dequiv` has the leader
equivocate, and separates the two branches of FP-evidence. `Dskip` skips
the slot.
-/

namespace LeanDagTest

namespace FinWhale

-- `decide` over these DAGs reduces through nested `Finset` structure, which
-- recurses past the default depth; the heartbeat and `synthInstance` limits
-- this file used to raise are no longer needed.
set_option maxRecDepth 4000

open LeanDag LeanDag.FinWhale

/-- Nine validators, two of them Byzantine. -/
local instance fwFaults : Faults (Fin 9) where
  f := 2
  byzantine := {0, 1}
  card_validators := by decide
  card_byzantine := by decide

/-- One fast-path slot: `p = 2`, so `n + 1 = 3f + 2p = 10`. -/
local instance fwParams : Params (Fin 9) where
  p := 2
  p_pos := by omega
  p_le_f := by decide
  card_add_one := by decide

/-- The committee's numbers, as the arc reads them. -/
example : spQuorum (Fin 9) = 6 ∧ fastCard (Fin 9) = 7 ∧ quorumCard (Fin 9) = 7 := by decide

/-- The slow-path quorum is strictly below the validity quorum, which is
what `p = 2` separates and `p = 1` would hide. -/
example : spQuorum (Fin 9) < quorumCard (Fin 9) := by decide

/-- Round robin: round `r` is led by validator `r % 9`. -/
def fwLeader : ℕ → Fin 9 := fun r => ⟨r % 9, Nat.mod_lt _ (by omega)⟩

/-! ## `Dfast` — the slot committed, by both paths

Four rounds of nine blocks: id `i` sits at round `i / 9` and is authored
by validator `i % 9`. Validators `0` to `6` vote for the round-0 leader
block, which is `n − p = 7` votes and a fast commit; validators `7` and
`8` do not. Every round-2 block carries `7` parents voting for it, above
the slow-path quorum of `6`, so the slot is committed by either path. -/
def fastBlk : Fin 36 → Block (Fin 9) (Fin 36) Unit := fun i =>
  { round := (i : ℕ) / 9,
    creator := ⟨(i : ℕ) % 9, Nat.mod_lt _ (by omega)⟩,
    refs :=
      if (i : ℕ) < 9 then ∅
      else if (i : ℕ) < 16 then {0, 1, 2, 3, 4, 5, 6}
      else if (i : ℕ) < 18 then {1, 2, 3, 4, 5, 6, 7}
      else if (i : ℕ) < 27 then {9, 10, 11, 12, 13, 14, 15}
      else {18, 19, 20, 21, 22, 23, 24},
    payload := () }

/-- The schedule the witnesses run: one slot a round. -/
def fwSched : Slots (Fin 9) := Slots.identity fwLeader

theorem fastValid : ∀ i : Fin 36, ValidHere fastBlk (fastBlk i) := by
  intro i
  refine ⟨?_, ?_, ?_, ?_⟩ <;> revert i <;> decide

/-- The execution, with all three DAG conditions by `decide`. -/
def Dfast : Dag (Fin 9) (Fin 36) Unit where
  ids := Finset.univ
  block := fastBlk
  complete := by decide
  valid := fun i _ => fastValid i
  no_equivocation := by decide

/-! ### The votes

Seven validators vote for the round-0 leader block, two do not. Seven is
`n − p`, so the fast path fires; the two abstainers are two short of the
slow-path skip quorum of six. -/

example : slotBlocks fwSched Dfast 0 = {0} := by decide

example : voters Dfast 0 = {0, 1, 2, 3, 4, 5, 6} ∧ nonVoters Dfast 0 = {7, 8} := by decide

example : FastCommit Dfast 0 := by decide

example : ¬ SPSkip Dfast 0 := by decide

/-! ### The slow path

Every round-2 block carries seven parents voting for the leader block,
one above the slow-path quorum, so each is an SP-certificate and six of
them are a slow-path commit. -/

example : parentsVoting Dfast 18 0 = {0, 1, 2, 3, 4, 5, 6} := by decide

example : SPCertificate Dfast 18 0 := by decide

/-- The certificates of validators `0` to `5` are a slow-path commit. -/
example : SPCommit Dfast 0 :=
  ⟨{0, 1, 2, 3, 4, 5}, by decide, by decide⟩

example : DirectCommit Dfast 0 := Or.inl (by decide)

/-- **The slot is not skipped**, by Lemma 6 rather than by search. -/
example : ¬ DirectSkip fwSched Dfast 0 :=
  no_directSkip_of_commit (l := 0) (by decide) (Or.inl (by decide))

/-! ### The fast path's evidence

No round-2 block has seen an equivocation here, so FP-evidence is the
weaker branch: `f + p − 1 = 3` parents voting, against the seven each of
them has. -/

example : ¬ ExposesEquivocationBy Dfast 18 (Dfast.block 0).creator := by decide

example : FPEvidence Dfast 18 0 := by decide

/-- Lemma 4 on data: under the fast commit, *every* round-2 block is
FP-evidence for the committed block. -/
example : ∀ b ∈ blocksAt Dfast 2, FPEvidence Dfast b 0 := by decide

/-! ### The anchor

A round-3 block reaches a round-2 certificate in one step, which is the
indirect rule's first route. -/

example : IndirectCommit fwSched Dfast 27 0 0 :=
  ⟨by decide, Or.inl ⟨18, by decide, ReachesFrom.single (by decide), by decide⟩⟩

/-- **And the rule settles by computation**, through the decidable form:
`historyFrom` is reachability as a `Finset`, so a model can check the
whole indirect rule rather than exhibit a path. -/
example : IndirectCommitOn fwSched Dfast 27 0 0 := by decide

example : IndirectCommit fwSched Dfast 27 0 0 :=
  indirectCommitOn_iff (by decide) |>.1 (by decide)

/-- Anti-vacuity: the rule is not settled by the slot condition alone.
No round-2 block is an anchor for its own slot, having nothing above it
to reach. -/
example : ¬ IndirectCommitOn fwSched Dfast 18 2 18 := by decide

/-! ## `Dequiv` — the leader equivocates

Three rounds of nine blocks, plus id `27`: a second round-0 block by
validator `0`, who is Byzantine and is the leader of round `0`. Five
round-1 blocks vote for one version, two for the other, two for neither,
so neither version reaches a quorum and the slot is decided by nobody
directly.

The round-2 blocks are where the two branches of FP-evidence separate.
Block `18` has seen both versions and carries the `f + p = 4` parents
voting for the first that the equivocating branch demands, against `2`
for the second. Block `19` has seen only the first, and the branch for a
block that has not seen the equivocation asks it for `f + p − 1 = 3`.
Block `20` has seen both and carries too few of either.

Validity is what forces block `18` to drop the leader's own round-1
block: a block whose parents disagree about the leader must exclude the
leader from its parents, which is `leader_not_parent_of_exposes`. -/
def eqBlk : Fin 28 → Block (Fin 9) (Fin 28) Unit := fun i =>
  if (i : ℕ) = 27 then
    { round := 0, creator := 0, refs := ∅, payload := () }
  else
  { round := (i : ℕ) / 9,
    creator := ⟨(i : ℕ) % 9, Nat.mod_lt _ (by omega)⟩,
    refs :=
      if (i : ℕ) < 9 then ∅
      else if (i : ℕ) < 14 then {0, 1, 2, 3, 4, 5, 6}
      else if (i : ℕ) < 16 then {27, 1, 2, 3, 4, 5, 6}
      else if (i : ℕ) < 18 then {1, 2, 3, 4, 5, 6, 7}
      else if (i : ℕ) = 18 then {10, 11, 12, 13, 14, 15, 16}
      else if (i : ℕ) = 20 then {11, 12, 13, 14, 15, 16, 17}
      else {9, 10, 11, 12, 13, 16, 17},
    payload := () }

theorem eqValid : ∀ i : Fin 28, ValidHere eqBlk (eqBlk i) := by
  intro i
  refine ⟨?_, ?_, ?_, ?_⟩ <;> revert i <;> decide

/-- The equivocating execution. Validator `0` is Byzantine, so
`no_equivocation` still holds. -/
def Dequiv : Dag (Fin 9) (Fin 28) Unit where
  ids := Finset.univ
  block := eqBlk
  complete := by decide
  valid := fun i _ => eqValid i
  no_equivocation := by decide

/-- The slot has two blocks, and they conflict. -/
example : slotBlocks fwSched Dequiv 0 = {0, 27} ∧ Conflicting Dequiv 0 27 := by decide

/-- The author of both is Byzantine — the only way `no_equivocation`
admits the pair. -/
example : (Dequiv.block 0).creator ∉ (Correct : Finset (Fin 9)) := by decide

/-- Neither version is committed or skipped: five votes and two against
the slow-path quorum of six, and four abstentions against the skip
quorum. -/
example : voters Dequiv 0 = {0, 1, 2, 3, 4} ∧ voters Dequiv 27 = {5, 6} := by decide

example : ¬ DirectCommit Dequiv 0 ∧ ¬ DirectCommit Dequiv 27 ∧ ¬ DirectSkip fwSched Dequiv 0 := by
  refine ⟨by decide, by decide, ?_⟩
  intro h
  exact absurd (h.1 0 (by decide)) (by decide)

/-! ### The two branches -/

/-- Block `18` has seen the equivocation, and its counts meet the
equivocating branch for one version and fail it for the other. -/
example : ExposesEquivocationBy Dequiv 18 (Dequiv.block 0).creator ∧
    parentsVoting Dequiv 18 0 = {1, 2, 3, 4} ∧ parentsVoting Dequiv 18 27 = {5, 6} := by decide

example : FPEvidence Dequiv 18 0 ∧ ¬ FPEvidence Dequiv 18 27 := by decide

/-- Block `19` has not seen it, and the weaker branch applies. -/
example : ¬ ExposesEquivocationBy Dequiv 19 (Dequiv.block 0).creator ∧
    parentsVoting Dequiv 19 0 = {0, 1, 2, 3, 4} := by
  decide

example : FPEvidence Dequiv 19 0 ∧ ¬ FPEvidence Dequiv 19 27 := by decide

/-- Block `20` has seen the equivocation and carries too few of either
version: evidence for nothing in the slot. -/
example : NonFPEvidence Dequiv 20 (slotBlocks fwSched Dequiv 0) := by decide

/-- **The validity clause on data.** Block `18` exposes the equivocation,
so its parents exclude the leader's own round-1 block — `9`, which every
other round-2 block here carries. -/
example : (9 : Fin 28) ∉ (Dequiv.block 18).refs ∧ (9 : Fin 28) ∈ (Dequiv.block 19).refs := by
  decide

example : (Dequiv.block 0).creator ∉ parentSet Dequiv 18 :=
  exposed_not_parent (D := Dequiv) (b := 18) (by decide) (by decide)

/-- And the equivocating author is validator `0`, whose round-1 block is
`9`: the parent block `18` had to drop. It is also the slot's leader, but
the rule no longer has to know that. -/
example : fwLeader ((Dequiv.block 18).round - 2) = 0 ∧
    (Dequiv.block 9).creator = 0 := by decide

/-! ## `Dskip` — the slot skipped

Three rounds of nine blocks, and no round-1 block references the round-0
leader. All nine validators decline, above the skip quorum of six, and no
round-2 block is FP-evidence for anything in the slot. -/
def skipBlk : Fin 27 → Block (Fin 9) (Fin 27) Unit := fun i =>
  { round := (i : ℕ) / 9,
    creator := ⟨(i : ℕ) % 9, Nat.mod_lt _ (by omega)⟩,
    refs :=
      if (i : ℕ) < 9 then ∅
      else if (i : ℕ) < 18 then {1, 2, 3, 4, 5, 6, 7}
      else {9, 10, 11, 12, 13, 14, 15},
    payload := () }

theorem skipValid : ∀ i : Fin 27, ValidHere skipBlk (skipBlk i) := by
  intro i
  refine ⟨?_, ?_, ?_, ?_⟩ <;> revert i <;> decide

/-- The skipping execution. -/
def Dskip : Dag (Fin 9) (Fin 27) Unit where
  ids := Finset.univ
  block := skipBlk
  complete := by decide
  valid := fun i _ => skipValid i
  no_equivocation := by decide

example : slotBlocks fwSched Dskip 0 = {0} ∧ voters Dskip 0 = ∅ := by decide

example : SPSkip Dskip 0 ∧ nonVoters Dskip 0 = {0, 1, 2, 3, 4, 5, 6, 7, 8} := by decide

example : ∀ b ∈ blocksAt Dskip 2, NonFPEvidence Dskip b (slotBlocks fwSched Dskip 0) := by decide

/-- The direct skip, on the certificates of validators `0` to `5`. -/
example : DirectSkip fwSched Dskip 0 :=
  ⟨by decide, {0, 1, 2, 3, 4, 5}, by decide, by decide⟩

example : ¬ DirectCommit Dskip 0 := by decide

/-- **No anchor can reverse it**, whatever it reaches: the skip pattern
denies both routes of the indirect rule. -/
example (A : Fin 27) : ¬ IndirectCommit fwSched Dskip A 0 0 :=
  no_indirectCommit_of_directSkip ⟨by decide, {0, 1, 2, 3, 4, 5}, by decide, by decide⟩

/-! ## The commit sequence and the delivered order

The list layer, on concrete verdicts. A validator that commits at slot
`0`, skips slot `1` and has not decided slot `2` commits one block; a
validator that has decided one slot further commits a sequence extending
it, and the delivery orders extend likewise. -/

/-- Two verdict assignments, the second deciding one slot further. -/
def decA : ℕ → Verdict (Fin 4) := fun s =>
  if s = 0 then Verdict.commit 1 else if s = 1 then Verdict.skip else Verdict.undecided

/-- The same, with slot `2` committed. -/
def decB : ℕ → Verdict (Fin 4) := fun s =>
  if s = 0 then Verdict.commit 1 else if s = 1 then Verdict.skip
  else if s = 2 then Verdict.commit 2 else Verdict.undecided

example : commitSeq decA 2 = [1] ∧ commitSeq decB 3 = [1, 2] := by decide

/-- Lemma 13 on data: the shorter sequence is a prefix of the longer. -/
example : commitSeq decA 2 <+: commitSeq decB 3 ∨ commitSeq decB 3 <+: commitSeq decA 2 :=
  lemma13 (k := 2) (k' := 3)
    (by
      intro s h1 _
      match s with
      | 0 => rfl
      | 1 => rfl
      | (n + 2) => exact absurd (by simp [decA]) h1)
    (by decide) (by decide)

/-- Anti-vacuity: the two sequences are not the same list, so the prefix
above has content. -/
example : commitSeq decA 2 ≠ commitSeq decB 3 := by decide

/-- A causal history per block: everything reaches the genesis block `0`. -/
def histFW : Fin 4 → List (Fin 4) := fun b => if b = 0 then [0] else [b, 0]

/-- The delivery order, on histories that overlap: the second leader's
history repeats a block the first already delivered, and it is delivered
once. -/
example : linearise histFW [1, 2] = [1, 0, 2] := by decide

/-- Theorem 14 on the same data: one more leader extends the order rather
than revising it. -/
example : linearise histFW [1] <+: linearise histFW [1, 2] :=
  theorem14 _ ⟨[2], by decide⟩

/-- Theorem 15: block `0` lies in both histories and is delivered once. -/
example : (linearise histFW [1, 2]).Nodup := theorem15 _ (by decide) _

/-! ## `Dsync` — the liveness input, and the commit it forces

A synchronised execution: three rounds of nine blocks, each referencing
every block of the round below. Coverage over the correct validators is
what the pacing line derives (`synchronised_of_viewPace`), and this is a
DAG that has it.

The leader schedule is shifted so that round `0` is led by validator `2`,
which is correct — validators `0` and `1` are the Byzantine pair, and a
Byzantine leader proves nothing about liveness. -/
def syncLeader : ℕ → Fin 9 := fun r => ⟨(r + 2) % 9, Nat.mod_lt _ (by omega)⟩

/-- Every block references the whole round below it. -/
def syncBlk : Fin 27 → Block (Fin 9) (Fin 27) Unit := fun i =>
  { round := (i : ℕ) / 9,
    creator := ⟨(i : ℕ) % 9, Nat.mod_lt _ (by omega)⟩,
    refs :=
      if (i : ℕ) < 9 then ∅
      else if (i : ℕ) < 18 then {0, 1, 2, 3, 4, 5, 6, 7, 8}
      else {9, 10, 11, 12, 13, 14, 15, 16, 17},
    payload := () }

/-- And the synchronous witness's. -/
def syncSched : Slots (Fin 9) := Slots.identity syncLeader

theorem syncValid : ∀ i : Fin 27, ValidHere syncBlk (syncBlk i) := by
  intro i
  refine ⟨?_, ?_, ?_, ?_⟩ <;> revert i <;> decide

/-- The synchronised execution. -/
def Dsync : Dag (Fin 9) (Fin 27) Unit where
  ids := Finset.univ
  block := syncBlk
  complete := by decide
  valid := fun i _ => syncValid i
  no_equivocation := by decide

/-- No block sits above round `2`, which is what makes coverage a finite
check. -/
theorem syncRounds : ∀ b : Fin 27, (syncBlk b).round ≤ 2 := by decide

/-- **Coverage on data.** Every correct block references every correct
block of the round below, from round `0` on. Above round `1` the
condition is empty, the DAG having stopped. -/
theorem syncCovers :
    SynchronisedFrom Dsync.block Dsync.ids (Correct : Finset (Fin 9)) 0 := by
  intro n _
  rcases Nat.lt_or_ge n 2 with h2 | h2
  · interval_cases n <;> decide
  · intro b _ hbr _ _ _ _ _
    have hb2 : (Dsync.block b).round ≤ 2 := syncRounds b
    omega

/-- Production on data, at the two rounds the commit reads. -/
theorem syncPopulated : ∀ r ≤ 2,
    PopulatedFrom Dsync.block Dsync.ids (Correct : Finset (Fin 9)) r := by
  intro r hr
  interval_cases r <;> decide

/-- The round-0 leader block is `2`, and its author is correct. -/
example : (2 : Fin 27) ∈ slotBlocks syncSched Dsync 0 ∧
    (Dsync.block 2).creator ∈ (Correct : Finset (Fin 9)) := by decide

/-- **Lemma 18 on data**: every correct round-1 block votes for it. -/
example : ∀ v ∈ (Correct : Finset (Fin 9)),
    ∃ b ∈ blocksAt Dsync 1, (Dsync.block b).creator = v ∧ (2 : Fin 27) ∈ (Dsync.block b).refs := by
  decide

/-- **Lemma 19 on data**: every correct round-2 block is an SP-certificate
for it. -/
example : ∀ b ∈ blocksAt Dsync 2, SPCertificate Dsync b 2 := by decide

/-- **Lemma 20 on data**: the slot is committed by the slow path. Which
route reached it is not this model's business — the schedule lives in
`Pace.lean`, and this execution only exhibits the pattern. -/
example : SPCommit Dsync 2 := by decide

/-- **Theorem 21 on data.** Two Byzantine validators is `p`, so the
correct validators alone are the `n − p = 7` votes a fast commit needs —
and here they are nine. -/
example : FastCommit Dsync 2 := by decide

/-- And the slot is not skipped, by Lemma 6 rather than by search. -/
example : ¬ DirectSkip syncSched Dsync 0 :=
  no_directSkip_of_commit (l := 2) (by decide) (Or.inl (by decide))

/-! ## The rotation

`fwLeader` is round robin over nine validators, which `RoundRobin`
records as a cyclic order. Lemma 22 then names three consecutive correct
leaders in any window of `3f + 3 = 9` rounds. -/

theorem fwRoundRobin : RoundRobin fwLeader := by
  refine ⟨Equiv.refl (Fin 9), fun r => ?_⟩
  apply Fin.ext
  show r % 9 = ZMod.val ((r : ZMod 9))
  exact (ZMod.val_natCast (n := 9) r).symm

/-- The window of Lemma 22, here: three consecutive rounds whose leaders
are all correct, from round `0`. -/
example : ∃ r, 0 ≤ r ∧ r + 2 < 0 + (3 * Faults.f (Fin 9) + 3) ∧
    fwLeader r ∈ (Correct : Finset (Fin 9)) ∧
    fwLeader (r + 1) ∈ (Correct : Finset (Fin 9)) ∧
    fwLeader (r + 2) ∈ (Correct : Finset (Fin 9)) :=
  lemma22 fwRoundRobin 0

/-- And one such triple, exhibited: rounds `2`, `3` and `4` are led by
validators `2`, `3` and `4`, none of them Byzantine. -/
example : fwLeader 2 ∈ (Correct : Finset (Fin 9)) ∧
    fwLeader 3 ∈ (Correct : Finset (Fin 9)) ∧
    fwLeader 4 ∈ (Correct : Finset (Fin 9)) := by decide

/-- Anti-vacuity: the schedule does name Byzantine leaders, so the lemma
is not about a committee without faults. -/
example : fwLeader 0 ∉ (Correct : Finset (Fin 9)) ∧
    fwLeader 1 ∉ (Correct : Finset (Fin 9)) := by decide

/-! ## The reverse pass, on a concrete verdict assignment

`WellFormed` and `Anchor` settled on data. Slots `3`, `4` and `5` are
committed directly, slots `1` and `2` are skipped directly, and slot `0`
is decided indirectly: its anchor is the first slot above `2` that is not
skipped, which is `3`, and the deterministic rule names block `1` there.
Nothing above `5` is decided, as a DAG that stops must have it. -/

/-- The verdicts. -/
def decW : ℕ → Verdict (Fin 4) := fun s =>
  if s = 0 then Verdict.commit 1
  else if s ≤ 2 then Verdict.skip
  else if s ≤ 5 then Verdict.commit 0
  else Verdict.undecided

/-- The direct commit rule of this validator's view. -/
def dcW : ℕ → Fin 4 → Prop := fun r l => 3 ≤ r ∧ r ≤ 5 ∧ l = 0

/-- Its direct skip rule. -/
def dsW : ℕ → Prop := fun r => r = 1 ∨ r = 2

/-- The deterministic tie-break, which names a block only at slot `0`. -/
def chooseW : Fin 4 → ℕ → Option (Fin 4) := fun _ r => if r = 0 then some 1 else none

/-- **The anchor of slot `0` is slot `3`**, and nothing else: the slots
between are skipped, and `3` is not. -/
theorem anchorW : ∀ a, Anchor (fun r a => r + 2 < a) decW 0 a → a = 3 := by
  rintro a ⟨h1, h2, h3⟩
  have h1' : (0 : ℕ) + 2 < a := h1
  by_contra hne
  have hlt : 3 < a := by omega
  have := h3 3 (show (0:ℕ) + 2 < 3 by omega) hlt
  simp [decW] at this

example : Anchor (fun r a => r + 2 < a) decW 0 3 :=
  ⟨by show (0:ℕ) + 2 < 3; omega, by decide,
   by intro a' h1 h2; have : (0:ℕ) + 2 < a' := h1; omega⟩

/-- **The reverse pass is followed.** -/
theorem wellFormedW : WellFormed (fun r a => r + 2 < a) dcW dsW chooseW decW where
  direct_commit r l := by
    rintro ⟨h3, h5, rfl⟩
    simp only [decW, if_neg (by omega : ¬ r = 0), if_neg (by omega : ¬ r ≤ 2), if_pos h5]
  direct_skip r := by rintro (rfl | rfl) <;> decide
  indirect_undecided r a := by
    intro hdc hds hanc hau
    rcases Nat.lt_or_ge r 6 with hr | hr
    · interval_cases r
      · rw [anchorW a hanc] at hau
        simp [decW] at hau
      · exact absurd (Or.inl rfl) hds
      · exact absurd (Or.inr rfl) hds
      · exact absurd ⟨0, by exact ⟨by omega, by omega, rfl⟩⟩ hdc
      · exact absurd ⟨0, by exact ⟨by omega, by omega, rfl⟩⟩ hdc
      · exact absurd ⟨0, by exact ⟨by omega, by omega, rfl⟩⟩ hdc
    · simp only [decW, if_neg (by omega : ¬ r = 0), if_neg (by omega : ¬ r ≤ 2),
        if_neg (by omega : ¬ r ≤ 5)]
  indirect_commit r a A := by
    intro hdc hds hanc hcom
    rcases Nat.lt_or_ge r 6 with hr | hr
    · interval_cases r
      · have ha3 : a = 3 := anchorW a hanc
        subst ha3
        have hA : (0 : Fin 4) = A := by simpa [decW] using hcom
        subst hA
        simp [decW, chooseW]
      · exact absurd (Or.inl rfl) hds
      · exact absurd (Or.inr rfl) hds
      · exact absurd ⟨0, by exact ⟨by omega, by omega, rfl⟩⟩ hdc
      · exact absurd ⟨0, by exact ⟨by omega, by omega, rfl⟩⟩ hdc
      · exact absurd ⟨0, by exact ⟨by omega, by omega, rfl⟩⟩ hdc
    · -- above the decided range no anchor is committed
      have h1 : (6 : ℕ) ≤ a := by have : r + 2 < a := hanc.1; omega
      rw [show decW a = Verdict.undecided by
        simp only [decW, if_neg (by omega : ¬ a = 0), if_neg (by omega : ¬ a ≤ 2),
          if_neg (by omega : ¬ a ≤ 5)]] at hcom
      exact absurd hcom (by simp)
  has_anchor r := by
    intro hdc hds hdecided
    rcases Nat.lt_or_ge r 6 with hr | hr
    · interval_cases r
      · exact ⟨3, show (0:ℕ) + 2 < 3 by omega, by decide,
          by intro a' h1 h2; have : (0:ℕ) + 2 < a' := h1; omega⟩
      · exact absurd (Or.inl rfl) hds
      · exact absurd (Or.inr rfl) hds
      · exact absurd ⟨0, by exact ⟨by omega, by omega, rfl⟩⟩ hdc
      · exact absurd ⟨0, by exact ⟨by omega, by omega, rfl⟩⟩ hdc
      · exact absurd ⟨0, by exact ⟨by omega, by omega, rfl⟩⟩ hdc
    · exact absurd (by
        simp only [decW, if_neg (by omega : ¬ r = 0), if_neg (by omega : ¬ r ≤ 2),
          if_neg (by omega : ¬ r ≤ 5)]) hdecided

/-- **Lemma 23 on data.** Slots `3`, `4` and `5` are a committed triple,
and slot `0` lies below it, so the reverse pass decides it. -/
example : decW 0 ≠ Verdict.undecided :=
  lemma23 (fun _ _ => Iff.rfl) wellFormedW (show (0 : ℕ) < 3 by omega)
    (fun s h1 h2 => by interval_cases s <;> exact ⟨by decide, by decide⟩)

/-- Anti-vacuity: the triple is genuinely needed. Nothing above `5` is
decided here, and the slots between `0` and its anchor are skipped. -/
example : decW 6 = Verdict.undecided ∧ decW 1 = Verdict.skip ∧ decW 2 = Verdict.skip := by
  decide

/-! ## Delivery, on the same verdicts -/

/-- **Lemma 25 on data**: the block committed at slot `2` is in the
commit sequence. -/
example : (2 : Fin 4) ∈ commitSeq decB 3 := lemma25 (r := 2) (by omega) (by decide)

/-- **Theorem 24 on data**: two validators that have decided the same
slots deliver the same sequence. -/
example : linearise histFW (commitSeq decA 2) = linearise histFW (commitSeq decB 2) :=
  theorem24 (by
      intro s h1 _
      match s with
      | 0 => rfl
      | 1 => rfl
      | (n + 2) => exact absurd (by simp [decA]) h1)
    (by decide) (by decide) histFW

/-- **Theorem 26 on data**: the genesis block lies in the history of the
leader committed at slot `2`, and is delivered — once, though it lies in
both leaders' histories. -/
example : (0 : Fin 4) ∈ linearise histFW (commitSeq decB 3) :=
  theorem26 (r := 2) (l := 2) (by omega) (by decide) (by decide)

/-! ## A view that has seen one version of an equivocation

`Dequiv` has the leader of round `0` issue two blocks, `0` and `27`. A
validator that has received only the first holds a reference-closed part
of the DAG — everything except `27` and the blocks whose parents include
it — and that part is a `Dag` in its own right.

It is what makes the skip rule's first condition view-relative: the slot
has two blocks, and this view sees one. -/

/-- Everything except the second version and the blocks that reference
it, directly or through a parent. -/
def Vpart : Finset (Fin 28) := Finset.univ \ {14, 15, 18, 20, 27}

/-- As a view of `Dequiv`. -/
def VpartView : Dequiv.View := ⟨Vpart, by decide, by decide⟩

/-- **The slot looks different from inside.** The universe has two blocks
of slot `0`; the view has one. -/
example : slotBlocks fwSched Dequiv 0 = {0, 27} ∧
    slotBlocks fwSched (VpartView.toRecord) 0 = {0} := by decide

/-- The view is smaller, and genuinely so. -/
example : (27 : Fin 28) ∈ Dequiv.ids ∧ (27 : Fin 28) ∉ Vpart := by decide

/-- **And no block cites both versions**, in this execution or any other:
validity admits one reference per author. That is what a parent-selection
clause must respect — obliging a builder to reference every version of
the leader's block it holds would be satisfiable by no valid DAG
(`not_refs_conflicting`). -/
example : ∀ c ∈ Dequiv.ids,
    ¬ ((0 : Fin 28) ∈ (Dequiv.block c).refs ∧ (27 : Fin 28) ∈ (Dequiv.block c).refs) := by
  decide

example {c : Fin 28} (hc : c ∈ Dequiv.ids) (h0 : (0 : Fin 28) ∈ (Dequiv.block c).refs)
    (h27 : (27 : Fin 28) ∈ (Dequiv.block c).refs) : False :=
  not_refs_conflicting hc (by decide) h0 h27

/-- What a block's parents say does not change with the view, which is
why FP-evidence transfers: block `19` reads the same parents either
way. -/
example : parentsVoting (VpartView.toRecord) 19 0 = parentsVoting Dequiv 19 0 :=
  rfl

/-- And the rules the view can evaluate agree with the universe's where
the view holds the rounds they read. On `Dsync`, which holds everything,
the whole DAG is a view and the direct commit is seen there. -/
def fullView : Dsync.View :=
  ⟨Finset.univ, fun _ _ => Finset.mem_univ _, fun _ _ _ _ => Finset.mem_univ _⟩

example : DirectCommit fullView.toRecord 2 :=
  directCommit_of_holds (V := fullView) (fun _ _ => Finset.mem_univ _)
    (fun _ _ => Finset.mem_univ _) (Or.inl (by decide))

/-! ## The pass, on data

`decOf` is a function of the DAG, so the verdicts of `Dfast` are not a
hypothesis about a validator but a computation. Its equations are proved
rather than evaluated: the pass is defined by recursion down from the
horizon, which the kernel does not unfold. -/

/-- Every block of `Dfast` sits at round `3` or below. -/
theorem dfast_horizon : ∀ b ∈ Dfast.ids, (Dfast.block b).round ≤ 3 := by decide

/-- **The pass commits slot `0`**, by its direct rule and whatever
tie-break the validator applies. -/
example (choose : Fin 36 → ℕ → Option (Fin 36)) :
    decOf fwSched (fun r a => r + 2 < a) Dfast choose 3 0 = Verdict.commit 0 :=
  (wellFormed_decOf dfast_horizon (fun _ _ h => by omega) (fun _ h => h) choose).direct_commit 0 0 ⟨by decide, Or.inl (by decide)⟩

/-- And decides nothing above the horizon, which is the finiteness Lemma
12 consumes. -/
example (choose : Fin 36 → ℕ → Option (Fin 36)) (s : ℕ) (hs : 3 < s) :
    decOf fwSched (fun r a => r + 2 < a) Dfast choose 3 s = Verdict.undecided :=
  decOf_of_gt hs

/-- The skipping execution decides its slot the other way, by the same
route. -/
example (choose : Fin 27 → ℕ → Option (Fin 27)) :
    decOf fwSched (fun r a => r + 2 < a) Dskip choose 2 0 = Verdict.skip :=
  (wellFormed_decOf (by decide) (fun _ _ h => by omega) (fun _ h => h) choose).direct_skip 0
    ⟨by decide, {0, 1, 2, 3, 4, 5}, by decide, by decide⟩

/-! ## The arc's axioms -/

#print axioms LeanDag.FinWhale.finWhaleLaws
#print axioms LeanDag.FinWhale.decided_of_wellFormed
#print axioms LeanDag.FinWhale.lemma22
#print axioms LeanDag.FinWhale.agreement_of_commits

end FinWhale

end LeanDagTest
