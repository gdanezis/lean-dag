import Mathlib.Tactic.Ring
import LeanDag.Common.Schedule
import LeanDag.Mysticeti.Liveness
import LeanDag.Mysticeti.ViewPace
import LeanDag.Network.Quorum
/-!
# `Ugrow` — a witness family for `Live`

`liveness.md` §4.4, §7. The non-vacuity check for the liveness primitives.

Every other model in `LeanDagTest` is a `Fin n` of fixed height, checked by
`decide`. None can serve here: `Live U N` demands blocks at every round up to
`N`, so a witness has to exist at *every* horizon, and `BlockId` has to be
infinite even though each `U.ids` is finite.

`Ugrow N` is the obvious such DAG over `Fin 4` validators (`f = 1`):

- `BlockId := ℕ`, with block `b` at round `b / 4`, authored by `b % 4`
- `ids := Finset.range (4 * (N + 1))` — rounds `0 … N`, four blocks each
- refs are the *whole* previous round, written `Finset.Ico (4 * r - 4) (4 * r)`

The `Ico` form is chosen so membership is an arithmetic fact `omega` can
discharge, and so the genesis case needs no branch: at `r = 0` truncated
subtraction makes it `Ico 0 0 = ∅`.

**Why this file exists.** The first draft of `Live` had no horizon, and was
*unsatisfiable* — L1 was proved against it and said nothing. It was caught by
sitting down to write this file. The staging rule that follows: a definition
gets a witness before anything is proved from it.
-/

namespace LeanDagTest

open LeanDag

instance : Faults (Fin 4) where
  f := 1
  byzantine := {0}
  card_validators := by decide
  card_byzantine := by decide

/-! ## The round-robin scheme

Every concrete model in this development lays its blocks out the same
way: four validators, one block each per round, with block `b` sitting at
round `b / 4` under author `b % 4`, so validator `v`'s round-`r` block is
`4 * r + v`. Only the reference sets differ.

`rrUniverse` proves once what that layout alone decides — completeness,
non-equivocation, the predecessor relation and distinctness of cited
authors — leaving a model to supply only the two clauses its references
actually control. -/

/-- A block of the round-robin scheme, over a given reference function. -/
def rrBlock (refs : ℕ → Finset ℕ) (b : ℕ) : Block (Fin 4) ℕ Unit where
  round := b / 4
  creator := ⟨b % 4, by omega⟩
  refs := refs b
  payload := ()

@[simp] theorem rrBlock_round (refs : ℕ → Finset ℕ) (b : ℕ) :
    (rrBlock refs b).round = b / 4 := rfl
@[simp] theorem rrBlock_creator_val (refs : ℕ → Finset ℕ) (b : ℕ) :
    ((rrBlock refs b).creator : ℕ) = b % 4 := rfl
@[simp] theorem rrBlock_refs (refs : ℕ → Finset ℕ) (b : ℕ) :
    (rrBlock refs b).refs = refs b := rfl

/-- **The scheme, as a universe.** Rounds `0` to `N`, four blocks each.

The two hypotheses are exactly what the layout cannot decide: that
references sit in the round below (`hrefs`), and the two `ValidWrt`
clauses that read the reference *set* rather than its bounds — a quorum
of distinct authors, and a parent by the block's own creator. -/
def rrUniverse (N : ℕ) (refs : ℕ → Finset ℕ)
    (hrefs : ∀ b i, i ∈ refs b → 4 * (b / 4) - 4 ≤ i ∧ i < 4 * (b / 4))
    (hquorum : ∀ b, 0 < b / 4 → 3 ≤ (creators (rrBlock refs) (rrBlock refs b)).card)
    (hself : ∀ b, 0 < b / 4 → 4 * (b / 4) - 4 + b % 4 ∈ refs b) :
    BlockUniverse (Fin 4) ℕ Unit where
  ids := Finset.range (4 * (N + 1))
  block := rrBlock refs
  complete := by
    intro i hi j hj
    rw [Finset.mem_range] at hi ⊢
    have := hrefs i j hj
    omega
  valid := by
    intro i _
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro j hj
      have := hrefs i j hj
      simp only [rrBlock_round]
      omega
    · intro j hj k hk hjk
      have := hrefs i j hj
      have := hrefs i k hk
      have : (j % 4) = (k % 4) := by
        have := congrArg (fun (v : Fin 4) => (v : ℕ)) hjk
        simpa using this
      omega
    · intro h
      simp only [rrBlock_round] at h
      have hf : Faults.f (Fin 4) = 1 := rfl
      have hn : Fintype.card (Fin 4) = 4 := rfl
      have := hquorum i h
      omega
    · intro h
      simp only [rrBlock_round] at h
      refine ⟨4 * (i / 4) - 4 + i % 4, hself i h, ?_⟩
      apply Fin.ext
      simp only [rrBlock_creator_val]
      omega
  no_equivocation := by
    intro i _ j _ _ hc hr
    have hv : (i % 4) = (j % 4) := by
      have := congrArg (fun (v : Fin 4) => (v : ℕ)) hc
      simpa using this
    simp only [rrBlock_round] at hr
    omega

@[simp] theorem rrUniverse_ids (N refs hrefs hquorum hself) :
    (rrUniverse N refs hrefs hquorum hself).ids = Finset.range (4 * (N + 1)) := rfl
@[simp] theorem rrUniverse_block (N refs hrefs hquorum hself) :
    (rrUniverse N refs hrefs hquorum hself).block = rrBlock refs := rfl

/-- **Every round of the scheme is populated**, for any set of validators:
validator `v`'s round-`r` block is `4 * r + v`, and the layout puts it in
`ids` with the right author and round. This is what the models' `base`,
`builds` and `blk` clauses all come down to. -/
theorem rrUniverse_populatedOn (N : ℕ) (refs : ℕ → Finset ℕ) (hrefs hquorum hself)
    (T : Finset (Fin 4)) {r : ℕ} (hr : r ≤ N) :
    PopulatedOn (rrUniverse N refs hrefs hquorum hself) T r := by
  intro v _
  have hv := v.isLt
  refine ⟨4 * r + (v : ℕ), ?_, ?_, ?_⟩
  · simp only [rrUniverse_ids, Finset.mem_range]; omega
  · apply Fin.ext
    simp only [rrUniverse_block, rrBlock_creator_val]
    omega
  · simp only [rrUniverse_block, rrBlock_round]; omega


/-- `Ugrow`'s references: the whole round below. -/
def growRefs (b : ℕ) : Finset ℕ := Finset.Ico (4 * (b / 4) - 4) (4 * (b / 4))

@[simp] theorem growBlock_refs (b : ℕ) :
    (rrBlock growRefs b).refs = Finset.Ico (4 * (b / 4) - 4) (4 * (b / 4)) := rfl

theorem mem_growBlock_refs {b i : ℕ} :
    i ∈ (rrBlock growRefs b).refs ↔ 4 * (b / 4) - 4 ≤ i ∧ i < 4 * (b / 4) :=
  Finset.mem_Ico

/-- The DAG grown to round `N`: four blocks per round, rounds `0` to `N`,
each block referencing the whole round below.

The block layout and the validity it decides are `rrUniverse`'s; what is
left is that four references are a quorum and that one of them is the
author's own. -/
def Ugrow (N : ℕ) : BlockUniverse (Fin 4) ℕ Unit :=
  rrUniverse N growRefs
    (fun _ _ hi => Finset.mem_Ico.mp hi)
    (by
      -- all four authors of the round below are cited
      intro i h
      have hcard : (creators (rrBlock growRefs) (rrBlock growRefs i)).card = 4 := by
        rw [creators, creatorsOf, Finset.card_image_of_injOn, rrBlock_refs, growRefs,
          Nat.card_Ico]
        · omega
        · intro a ha b hb hab
          rw [Finset.mem_coe, mem_growBlock_refs] at ha hb
          have : (a % 4) = (b % 4) := by
            have := congrArg (fun (v : Fin 4) => (v : ℕ)) hab
            simpa using this
          omega
      omega)
    (by
      intro i h
      rw [growRefs, Finset.mem_Ico]
      omega)

@[simp] theorem ugrow_ids (N : ℕ) : (Ugrow N).ids = Finset.range (4 * (N + 1)) := rfl

@[simp] theorem ugrow_block (N : ℕ) : (Ugrow N).block = rrBlock growRefs := rfl

/-! ## `Ugrow N` is populated at every round below its horizon

The fact every production route comes down to on this layout: validator
`v`'s round-`r` block is `4 * r + v`. -/

theorem ugrow_populated {N r : ℕ} (hr : r ≤ N) : Populated (Ugrow N) r :=
  rrUniverse_populatedOn _ _ _ _ _ _ hr

/-- And it is synchronised from round 0: a `Ugrow` block references the
*whole* round below, so honest-to-honest coverage is immediate. This is what
rules out `Live` and `Synchronised` being jointly unsatisfiable, which would
leave L4–L6 vacuous however satisfiable each was alone. -/
theorem ugrow_synchronised (N : ℕ) : Synchronised (Ugrow N) 0 := by
  intro n _ b _ hbr _ a _ har _
  simp only [ugrow_block, rrBlock_round] at hbr har
  simp only [ugrow_block, mem_growBlock_refs]
  omega

/-! ## The family is genuinely unbounded

Each `Ugrow N` is finite, but the heights are cofinal — which is what "the
DAG grows without bound" means once `U.ids` is a `Finset` (§4.4). -/

theorem ugrow_card (N : ℕ) : (Ugrow N).ids.card = 4 * (N + 1) := by
  simp

example : ∀ N, ∃ M, N < (Ugrow M).ids.card := fun N => ⟨N, by
  rw [ugrow_card]; omega⟩

-- Concretely: `Ugrow 5` is a six-round DAG, and validator 3 is at its top.
example : (Ugrow 5).ids.card = 24 := by decide
example : (rrBlock growRefs 23).round = 5 := by decide
example : ((rrBlock growRefs 23).creator : ℕ) = 3 := by decide

/-! ## L1 against the witness

The point of the family is that L1 now says something. These also pin the
horizon down as **tight**: L1 reaches round `N` and stops, and it stops
because there is genuinely nothing above. -/

/-- **Production at the top round** — every correct validator has a block
there. -/
example (N : ℕ) : Populated (Ugrow N) N := ugrow_populated (le_refl N)

/-- The quorum corollary, which L4 will consume. -/
example (N r : ℕ) (h : r ≤ N) :
    (Fintype.card (Fin 4) - Faults.f (Fin 4)) ≤ (authorsAt (Ugrow N) r).card :=
  card_authorsAt_of_populated (ugrow_populated h)

/-- **The horizon is tight, not slack.** One round further and the conclusion
is false — so L1's bound `r ≤ N` is doing real work rather than being a
conservative guess. -/
theorem ugrow_not_populated_succ (N : ℕ) : ¬ Populated (Ugrow N) (N + 1) := by
  intro h
  obtain ⟨b, hb, _, hbr⟩ := h 1 (by decide)
  simp only [ugrow_ids, Finset.mem_range] at hb
  simp only [ugrow_block, rrBlock_round] at hbr
  omega

/-- L0 also applies, and agrees: `Ugrow N` is dense below its frontier. -/
example (N : ℕ) (hN : 0 < N) : (Fintype.card (Fin 4) - Faults.f (Fin 4)) ≤ (authorsAt (Ugrow N) 0).card :=
  card_authorsAt_of_lt (U := Ugrow N) (r := N) (n := 0) hN
    (i := 4 * N)
    (by simp only [ugrow_ids, Finset.mem_range]; omega)
    (by simp only [ugrow_block, rrBlock_round]; omega)

/-! ## L4 against the witness

`Model.lean` also declares `Faults (Fin 4)` and `Slots (Fin 4)`. This file
deliberately does **not** import it and carries its own: `Model`'s schedule
names validator `0`, which is Byzantine under that same fault model, so L4
can never fire against it — the case L4 is about is exactly the one that
schedule excludes. The two instance sets never meet, since neither file
imports the other. -/

/-- A schedule whose leader is correct. Validator 1 is not Byzantine. -/
instance fairSlots : Slots (Fin 4) := Slots.uniformSingle 3 (by omega) (fun _ => 1)

@[simp] theorem fairSlots_slotRound (k : ℕ) : fairSlots.slotRound k = 3 * k := by
  simp

@[simp] theorem fairSlots_leader (k : ℕ) : fairSlots.leader k = 1 := rfl

example : fairSlots.leader 0 ∈ (Correct : Finset (Fin 4)) := by decide

/-- **L4 applied.** Every slot whose certificate rounds fit under the horizon
is directly committed. `Ugrow` is synchronised from round 0, so the `R ≤ r`
side condition is free; the horizon condition is the only real one. -/
theorem ugrow_directCommit (N k : ℕ) (h : 3 * k + 2 ≤ N) :
    ∃ L, IsLeaderBlock (Ugrow N) k L ∧
      DirectCommit (Ugrow N) L (fairSlots.slotRound k) :=
  directCommit_of_correct_leader (R := 0) (ugrow_synchronised N) (Nat.zero_le _)
    (ugrow_populated (by simp only [fairSlots_slotRound]; omega))
    (ugrow_populated (by simp only [fairSlots_slotRound]; omega))
    (ugrow_populated (by simp only [fairSlots_slotRound]; omega))
    (by simp only [fairSlots_leader]; decide)

/-- **And as a decision** — the form L6 consumes and L3 propagates. -/
theorem ugrow_decided (N k : ℕ) (h : 3 * k + 2 ≤ N) :
    ∃ L, IsLeaderBlock (Ugrow N) k L ∧
      Decided (Ugrow N) (View.full (Ugrow N)) k (some L) :=
  decided_of_correct_leader (R := 0) (ugrow_synchronised N) (Nat.zero_le _)
    (ugrow_populated (by simp only [fairSlots_slotRound]; omega))
    (ugrow_populated (by simp only [fairSlots_slotRound]; omega))
    (ugrow_populated (by simp only [fairSlots_slotRound]; omega))
    (by simp only [fairSlots_leader]; decide)

-- Concretely: with the DAG grown to round 8, slot 2 commits.
example : ∃ L, IsLeaderBlock (Ugrow 8) 2 L ∧
    DirectCommit (Ugrow 8) L (fairSlots.slotRound 2) := ugrow_directCommit 8 2 (by omega)

/-! ## L5, L6, L7 against the witness -/

/-- **The unsupported skip, refuted on data.** Above the horizon the
universe has no blocks at the voting round, so no view reaches the count
`Decided.directSkip` asks for and the slot is not directly skipped.

An earlier form of this theorem asserted the opposite — that *every*
view decides the slot `none` there, the leader having published nothing
— and `ugrow_commits_recur` below contradicts it: the same slot carries
a commit once the DAG has grown past it. Two validators would then hold
`none` and `some L` for one slot, in universes no uniqueness theorem
compares. A skip resting on the absence of a candidate is not final,
which is why the rule counts blockers instead. -/
theorem ugrow_not_directSkip (N k : ℕ) (h : N < 3 * k)
    (V : View (Fin 4) ℕ Unit (Ugrow N)) :
    ¬ DirectSkipSlotIn (Ugrow N) V k := by
  intro hskip
  have hempty : slotBlamers (Ugrow N) k ∩ V.ids = ∅ := by
    rw [Finset.eq_empty_iff_forall_notMem]
    intro q hq
    rw [Finset.mem_inter, slotBlamers, Finset.mem_filter, mem_blocksAt] at hq
    obtain ⟨⟨⟨hqi, hqr⟩, -⟩, -⟩ := hq
    simp only [ugrow_ids, Finset.mem_range] at hqi
    simp only [ugrow_block, rrBlock_round, fairSlots_slotRound] at hqr
    omega
  simp only [DirectSkipSlotIn, HoldsAtLeast, heldAuthors, hempty] at hskip
  simp only [creatorsOf, Finset.image_empty, Finset.card_empty] at hskip
  have hc : 3 * Faults.f (Fin 4) + 1 ≤ Fintype.card (Fin 4) := Faults.card_validators
  omega

/-- The schedule is fair: its leader is correct at every slot. -/
theorem ugrow_fair : FairSchedule (Validator := Fin 4) :=
  fun k => ⟨k, le_refl k, by simp only [fairSlots_leader]; decide⟩

/-- **L6 applied.** For every slot there is a later one *and* a horizon at
which it commits. This is unboundedness made concrete: no single `Ugrow N`
commits infinitely often, but no slot is the last one some `Ugrow` commits. -/
theorem ugrow_commits_recur (k : ℕ) :
    ∃ k', k ≤ k' ∧ ∃ N L, IsLeaderBlock (Ugrow N) k' L ∧
      Decided (Ugrow N) (View.full (Ugrow N)) k' (some L) := by
  obtain ⟨k', hk', _, hcommit⟩ :=
    commits_recur (BlockId := ℕ) (Payload := Unit) ugrow_fair 0 k
  obtain ⟨L, hL, hd⟩ :=
    hcommit (Ugrow (Slots.slotRound (Validator := Fin 4) k' + 2)) _
      (fun r _ hr => ugrow_populated hr)
      (ugrow_synchronised _) (le_refl _)
  exact ⟨k', hk', _, L, hL, hd⟩

#print axioms ugrow_synchronised
#print axioms ugrow_not_populated_succ
#print axioms ugrow_directCommit
#print axioms ugrow_decided
#print axioms ugrow_not_directSkip
#print axioms ugrow_commits_recur
/-- **Q2 applied.** A *quorum* of correct validators suffices — here
`{1, 2, 3}`, which is all of `Correct` at `f = 1`, but the theorem no longer
demands that they be all of it. -/
example (N k : ℕ) (h : 3 * k + 2 ≤ N) :
    ∃ L, IsLeaderBlock (Ugrow N) k L ∧
      DirectCommit (Ugrow N) L (fairSlots.slotRound k) :=
  directCommit_of_leader_mem (T := {1, 2, 3}) (R := 0) (by decide)
    (SynchronisedOn.mono (by decide) (ugrow_synchronised N)) (Nat.zero_le _)
    (PopulatedOn.mono (by decide)
      (ugrow_populated
        (by simp only [fairSlots_slotRound]; omega)))
    (PopulatedOn.mono (by decide)
      (ugrow_populated
        (by simp only [fairSlots_slotRound]; omega)))
    (PopulatedOn.mono (by decide)
      (ugrow_populated
        (by simp only [fairSlots_slotRound]; omega)))
    (by simp only [fairSlots_leader]; decide)

/-! ## The rated schedule against the witness

Non-vacuity for the rated backoff of `Quantitative.lean`, over the partial
schedule. Real time is `2 ^ n`: every validator builds its round-`n` block
at time `2 ^ n` with a timeout of `2 ^ n`, so the backoff is rated. Drift
is `0` and delay is `0` — the no-adversity case, which is the point: it
shows the hypotheses are *satisfiable*, not that they are easy to meet. -/

/-- What anyone holds at `t`: every block built by `t`. Lockstep and
`delay = 0`, so holdings are homogeneous across validators. -/
def timingHolds (N : ℕ) (_v : Fin 4) (t : ℕ) : Finset ℕ :=
  (Finset.range (4 * (N + 1))).filter fun b => 2 ^ (b / 4) ≤ t

def ugrowTimingPace (N : ℕ) : ViewPace (Ugrow N) {1, 2, 3} N where
  top _ := N
  built _ n := 2 ^ n
  timeout n := 2 ^ n
  gst := 0
  delay := 0
  rounds_le b hb := by
    simp only [ugrow_ids, Finset.mem_range] at hb
    simp only [ugrow_block, rrBlock_round]
    omega
  built_of_le_top v hv n hn := rrUniverse_populatedOn _ _ _ _ _ _ hn v hv
  le_top_of_built _ _ b hb _ := by
    simp only [ugrow_ids, Finset.mem_range] at hb
    simp only [ugrow_block, rrBlock_round]
    omega
  waits _ _ n _ := by
    have h : 2 ^ n + 2 ^ n = 2 ^ (n + 1) := by ring
    omega
  timeout_pos n := Nat.one_le_two_pow
  latest n := 2 ^ n
  built_le_latest _ _ _ _ := le_refl _
  proc := 0
  refs_held v _ n b hb hbc hbr := by
    intro j hj
    simp only [ugrow_block, mem_growBlock_refs] at hj
    simp only [ugrow_block, rrBlock_round] at hbr
    simp only [timingHolds, Finset.mem_filter, Finset.mem_range]
    simp only [ugrow_ids, Finset.mem_range] at hb
    have hjn : j / 4 = n := by omega
    refine ⟨by omega, ?_⟩
    rw [hjn]
    exact Nat.pow_le_pow_right (by omega) (by omega)
  holds := timingHolds N
  holds_sub _ _ := by
    simp only [timingHolds, ugrow_ids]; exact Finset.filter_subset _ _
  holds_closed v hv t b hb j hj := by
    simp only [timingHolds, Finset.mem_filter, Finset.mem_range] at hb ⊢
    simp only [ugrow_block, mem_growBlock_refs] at hj
    have hjd : j / 4 < b / 4 := by omega
    have := Nat.pow_le_pow_right (by omega : 1 ≤ 2) (le_of_lt hjd)
    exact ⟨by omega, by omega⟩
  holds_own v _ n _ b hb _ hbr := by
    simp only [ugrow_ids, Finset.mem_range] at hb
    simp only [ugrow_block, rrBlock_round] at hbr
    simp only [timingHolds, Finset.mem_filter, Finset.mem_range]
    exact ⟨hb, by rw [hbr]⟩
  holds_mono v s t hst := by
    intro b hb
    simp only [timingHolds, Finset.mem_filter, Finset.mem_range] at hb ⊢
    exact ⟨hb.1, by omega⟩
  converges _ _ _ _ t _ := by
    intro b hb
    simp only [timingHolds, Finset.mem_filter, Finset.mem_range] at hb ⊢
    exact ⟨hb.1, by omega⟩
  references v _ n _ c hc _ hcr a ha har := by
    have hv := v.isLt
    simp only [ugrow_ids, Finset.mem_range] at hc
    simp only [ugrow_block, rrBlock_round] at hcr har
    simp only [timingHolds, Finset.mem_filter, Finset.mem_range] at ha
    simp only [ugrow_block, mem_growBlock_refs]
    omega
  advances _ _ _ hn _ _ := hn
  catchup v _ n hn b hb _ hbr t _ hheld := by
    simp only [ugrow_ids, Finset.mem_range] at hb
    simp only [ugrow_block, rrBlock_round] at hbr
    simp only [timingHolds, Finset.mem_filter, Finset.mem_range] at hheld
    rw [hbr] at hheld
    exact ⟨hn, by omega⟩

#print axioms ugrow_synchronised
#print axioms ugrow_not_populated_succ
#print axioms ugrow_directCommit
#print axioms ugrow_decided
#print axioms ugrow_not_directSkip
#print axioms ugrow_commits_recur

end LeanDagTest
