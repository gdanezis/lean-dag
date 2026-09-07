import LeanDag.Hydrozoan.DirectSafety.Proof
import LeanDag.Hydrozoan.Model.Decided
import LeanDag.Hydrozoan.Helpers.IndirectRules
import LeanDagTest.Hydrozoan.DirectRules
/-!
# Witness: the structural fast-commit-without-certificate universe

The fast path's structural hazard made into a model: a slot
fast-commits while
**zero LeanDag.Hydrozoan.certificates exist in the whole universe** — not "not yet"
(the temporal reading pinned in `HydrozoanTest/DirectRules.lean`) but
structurally, through Byzantine equivocation: replica 0's second copy
(id 8) omits the leader from its refs, and every round-2 block
adopts that copy, capping every certificate candidate at 4 < q_cert
vote-creators. This universe is the anti-vacuity guard for
`FastSlowAgreement` (the theorem is not true merely because a fast
commit drags LeanDag.Hydrozoan.certificates along) and the consistency argument's
Case 1: the fast path leaves only its weak footprint for the indirect
rule.

The view `V4` withholds one voter (id 13), so slot 0's **direct rules
all fail in view** — no fast quorum, no LeanDag.Hydrozoan.certificates, no slotBlames — and
the weak rung is exercised end to end as the *only*
route, with its rung-1-empty and tie-break premises discharged
non-vacuously.

Same pipelined schedule as `HydrozoanTest.DirectRules` (slot `k` at
round `k`, leader `(k + 2) % 7`); thresholds q_fast 6 / q_cert 5 /
q_slow 4 / q_weak 3.
-/

namespace LeanDagTest

namespace Hydrozoan

open LeanDag LeanDag.Hydrozoan

set_option maxRecDepth 8192

/-- Thirty-two blocks over five rounds. Ids 0–6: genesis (creator = id).
Round 1: id 7 (creator 0) votes leader 2; **id 8 (creator 0), the
equivocating copy, has refs `{0, 1, 3, 4, 5}` — it does NOT vote for
2**; ids 9–13 (creators 2–6) vote for 2. Round 2 (ids 14–19, creators
0, 2, 3, 4, 5, 6): every block adopts the non-voting copy — refs
`{8, 9, 10, 11, 12}` — so its votes for 2 come from only four creators:
no certificate. Round 3 (ids 20–25): refs `{14, 15, 16, 18, 19}`;
id 24 (creator 5 = slot 3's leader) is the anchor. Round 4 (ids 26–31):
refs `{20, 21, 22, 24, 25}` — six votes fast-commit the anchor.
Crashed replica 1 creators only its genesis block. -/
def lk4 : Fin 32 → Block (Fin 7) (Fin 32) := fun i =>
  if h : (i : ℕ) < 7 then
    { round := 0, creator := ⟨i, by omega⟩, refs := ∅, payload := () }
  else if (i : ℕ) = 7 then
    { round := 1, creator := 0, refs := {0, 1, 2, 3, 4}, payload := () }
  else if (i : ℕ) = 8 then
    { round := 1, creator := 0, refs := {0, 1, 3, 4, 5}, payload := () }
  else if h : (i : ℕ) < 14 then
    { round := 1, creator := ⟨(i : ℕ) - 7, by omega⟩, refs := {0, 1, 2, 3, 4}, payload := () }
  else if (i : ℕ) = 14 then
    { round := 2, creator := 0, refs := {8, 9, 10, 11, 12}, payload := () }
  else if h : (i : ℕ) < 20 then
    { round := 2, creator := ⟨(i : ℕ) - 13, by omega⟩, refs := {8, 9, 10, 11, 12}, payload := () }
  else if (i : ℕ) = 20 then
    { round := 3, creator := 0, refs := {14, 15, 16, 18, 19}, payload := () }
  else if h : (i : ℕ) < 26 then
    { round := 3, creator := ⟨(i : ℕ) - 19, by omega⟩, refs := {14, 15, 16, 18, 19}, payload := () }
  else if (i : ℕ) = 26 then
    { round := 4, creator := 0, refs := {20, 21, 22, 24, 25}, payload := () }
  else
    { round := 4, creator := ⟨(i : ℕ) - 25, by omega⟩, refs := {20, 21, 22, 24, 25}, payload := () }

/-- The structural witness universe. -/
def U4 : BlockUniverse (Fin 7) (Fin 32) where
  ids := Finset.univ
  block := lk4
  complete := by decide
  valid := by decide
  no_equivocation := by decide

/-- A replica's view withholding one voter (id 13 — referenced by
nothing, so ref-closure is immediate). -/
def V4 : View U4 where
  ids := {0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 14, 15, 16, 17, 18,
    19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31}
  subset_ids := by decide
  complete := by decide

-- The universe fast-commits slot 0's candidate: six of seven creators
-- vote (the equivocator counts once, through its voting copy).
example : supporters U4 2 1 = {0, 2, 3, 4, 5, 6} := by decide
example : FastCommit U4 2 0 := by decide

-- THE STRUCTURAL FACT: zero LeanDag.Hydrozoan.certificates for the fast-committed leader
-- exist anywhere — every round-2 block's votes for id 2 stop at four
-- creators.
example : LeanDag.Hydrozoan.certificates U4 2 0 = ∅ := by decide
example : ¬ SlowCommit U4 2 0 := by decide

-- In the view V4 (missing one voter), every direct rule fails: the
-- indirect route is the only one.
example : ¬ FastCommitInView U4 V4 2 0 := by decide
example : ¬ SlowCommitInView U4 V4 2 0 := by decide
example : ¬ SkippedLeaderInView U4 V4 0 := by decide

-- The weak footprint survives in the anchor's causal history: four
-- anchor-linked voters, above q_weak = 3 — the consistency argument's
-- Case 1.
example : WeakLinked U4 24 2 0 :=
  (weakLinked_iff_history (by decide)).mpr (by decide)

-- The anchor itself: slot 3's candidate, fast-committed in the view.
example : IsLeaderBlock U4 3 24 := by decide
example : FastCommitInView U4 V4 24 3 := by decide

-- The seam, non-degenerately: slot 0 commits via the weak rung — the
-- rung-1-empty premise is discharged against a genuinely empty
-- certificate set, and the tie-break against the (unique) candidate.
example : Decided U4 V4 0 (some 2) := by
  have hall : ∀ M : Fin 32, IsLeaderBlock U4 0 M → M = 2 := by decide
  refine Decided.indirectCommit (j := 3) (A := 24) (i := 1) (by omega) (by decide)
    (Decided.directCommit (by decide) (Or.inl (by decide)))
    (fun i h1 h2 h3 => by
      have hi : i = 1 ∨ i = 2 := by omega
      rcases hi with rfl | rfl
      · exact absurd h3 (by decide)
      · exact absurd h3 (by decide))
    (by decide)
    (fun i hi L' hL' hcert => by
      have := hall L' hL'
      subst this
      have : i = 0 := by omega
      subst this
      exact absurd ((linkedVia_iff_history (by decide)).mp hcert) (by decide))
    (by decide)
    (show WeakLinked U4 24 2 0 from (weakLinked_iff_history (by decide)).mpr (by decide))
    (fun L' hL' _ => by
      have := hall L' hL'
      subst this
      exact lt_irrefl _)

end Hydrozoan

end LeanDagTest
