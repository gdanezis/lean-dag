import LeanDag.Hydrozoan.Model.Decided
import LeanDag.Hydrozoan.Helpers.IndirectRules
import LeanDagTest.Hydrozoan.DirectRules
/-!
# Witness: the decision relation

A five-round universe under the pipelined schedule of
`HydrozoanTest.DirectRules` (slot `k` at round `k`, leader `(k + 2) % 7`),
exercising the direct commit, the direct skip and the indirect commit
at rung `0` end to end:

* slot 3 (leader 5, candidate id 24) is **fast-committed** — the anchor;
* slot 2 (leader 4, candidate id 17) is **skipped** — every round-3
  block omits id 17 from its refs;
* slot 0 (leader 2, candidate id 2) commits **indirectly via rung 0**,
  anchored on slot 3: the anchor's refs include the certificate
  id 15.

The weak rung and the indirect skip are deliberately not exercised
here: the scenario they need — a fast footprint with no certificate —
is Phase 5's planned witness.

Thresholds at `n = 7, f = c = k = 1`: `q_fast = 6`, `q_cert = 5`,
`q_slow = 4`, `q_weak = 3`.
-/

namespace LeanDagTest

namespace Hydrozoan

open LeanDag LeanDag.Hydrozoan

set_option maxRecDepth 8192

/-- Thirty-two blocks over five rounds. Ids 0–6: genesis (creator = id).
Ids 7–13: round 1 — the equivocating pair 7/8 by Byzantine 0, then 9–13
by replicas 2–6; every round-1 block votes for genesis 2. Ids 14–19:
round 2 by replicas 0, 2, 3, 4, 5, 6, all referencing the same five
distinct-creator round-1 blocks — so each is a certificate for the slot-0
leader. Ids 20–25: round 3 by replicas 0, 2, 3, 4, 5, 6, each
referencing five round-2 blocks that **exclude id 17** (replica 4's, the
slot-2 candidate — hence the slot-2 skip) and **include id 15** (the
certificate the anchor reaches). Id 24 (creator 5 = slot 3's leader) is
the anchor. Ids 26–31: round 4 by replicas 0, 2, 3, 4, 5, 6, each
referencing id 24 — six votes, fast-committing slot 3 exactly at
quorum. Crashed replica 1 creators only its genesis block. -/
def lk3 : Fin 32 → Block (Fin 7) (Fin 32) := fun i =>
  if h : (i : ℕ) < 7 then
    { round := 0, creator := ⟨i, by omega⟩, refs := ∅, payload := () }
  else if (i : ℕ) = 7 then
    { round := 1, creator := 0, refs := {0, 1, 2, 3, 4}, payload := () }
  else if (i : ℕ) = 8 then
    { round := 1, creator := 0, refs := {0, 1, 2, 3, 5}, payload := () }
  else if h : (i : ℕ) < 14 then
    { round := 1, creator := ⟨(i : ℕ) - 7, by omega⟩, refs := {0, 1, 2, 3, 4}, payload := () }
  else if (i : ℕ) = 14 then
    { round := 2, creator := 0, refs := {7, 9, 10, 11, 12}, payload := () }
  else if h : (i : ℕ) < 20 then
    { round := 2, creator := ⟨(i : ℕ) - 13, by omega⟩, refs := {7, 9, 10, 11, 12}, payload := () }
  else if (i : ℕ) = 20 then
    { round := 3, creator := 0, refs := {14, 15, 16, 18, 19}, payload := () }
  else if h : (i : ℕ) < 26 then
    { round := 3, creator := ⟨(i : ℕ) - 19, by omega⟩, refs := {14, 15, 16, 18, 19}, payload := () }
  else if (i : ℕ) = 26 then
    { round := 4, creator := 0, refs := {20, 21, 22, 24, 25}, payload := () }
  else
    { round := 4, creator := ⟨(i : ℕ) - 25, by omega⟩, refs := {20, 21, 22, 24, 25}, payload := () }

/-- The five-round witness universe. -/
def U3 : BlockUniverse (Fin 7) (Fin 32) where
  ids := Finset.univ
  block := lk3
  complete := by decide
  valid := by decide
  no_equivocation := by decide

/-- The full view: every block delivered. -/
def Vfull3 : View U3 where
  ids := Finset.univ
  subset_ids := by decide
  complete := by decide

-- Anchor eligibility: slot 3 can anchor slot 0; slot 2 — only two
-- rounds ahead — cannot.
example : EligibleAt (Validator := Fin 7) 2 0 3 := by decide
example : ¬ EligibleAt (Validator := Fin 7) 2 0 2 := by decide

-- Slot 3's candidate is id 24, fast-committed by all six round-4 votes.
example : IsLeaderBlock U3 3 24 := by decide
example : FastCommitInView U3 Vfull3 24 3 := by decide

-- The anchor commits via the fast path.
example : Decided U3 Vfull3 3 (some 24) :=
  Decided.directCommit (by decide) (Or.inl (by decide))

-- Slot 2 is skipped: no round-3 block references its candidate id 17.
example : SkippedLeaderInView U3 Vfull3 2 := by decide
example : Decided U3 Vfull3 2 none :=
  Decided.directSkip (by decide)

-- Rung 1's test holds structurally: certificate 15 sits among the
-- anchor's refs.
example : LeanDag.Hydrozoan.CertifiedIn U3 24 2 0 :=
  ⟨15, by decide, Reaches.single (by decide)⟩

-- Rung 2's test also holds here (the rungs are not exclusive; the
-- grading orders them): q_weak anchor-linked votes exist, via the
-- history characterization.
example : WeakLinked U3 24 2 0 :=
  (weakLinked_iff_history (by decide)).mpr (by decide)

-- Negative rungs: the withheld equivocation id 8 gathers no votes at
-- all, so neither rung can ever fire for it.
example : ¬ LeanDag.Hydrozoan.CertifiedIn U3 24 8 1 := fun h =>
  absurd ((linkedVia_iff_history (by decide)).mp h) (by decide)
example : ¬ WeakLinked U3 24 8 1 := fun h =>
  absurd ((weakLinked_iff_history (by decide)).mp h) (by decide)

-- The end-to-end seam: slot 0 commits indirectly via rung 1, anchored
-- on slot 3. Slots 1 and 2 are not eligible for slot 0, so the
-- in-between premise is vacuous.
example : Decided U3 Vfull3 0 (some 2) :=
  Decided.indirectCommit (j := 3) (A := 24) (i := 0) (by omega) (by decide)
    (Decided.directCommit (by decide) (Or.inl (by decide)))
    (fun i h1 h2 h3 => by
      have hi : i = 1 ∨ i = 2 := by omega
      rcases hi with rfl | rfl
      · exact absurd h3 (by decide)
      · exact absurd h3 (by decide))
    (by decide) (fun _ h => absurd h (Nat.not_lt_zero _))
    (by decide)
    (show LeanDag.Hydrozoan.CertifiedIn U3 24 2 0 from ⟨15, by decide, Reaches.single (by decide)⟩)
    (fun _ _ _ h => h)

end Hydrozoan

end LeanDagTest
