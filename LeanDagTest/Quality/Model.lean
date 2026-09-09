import LeanDag.Properties.Arcs.Quality
import LeanDag.Mysticeti.Properties
import LeanDag.DoS.Density
import LeanDag.Mysticeti.Quantitative
import LeanDagTest.DoS.Exclusion
import LeanDagTest.Mysticeti.Quantitative
/-!
# Chain quality, witnessed

`chain-quality.md` §5, CQP0. Two models carry the whole story.

**`Ucens` — tightness and censorship in one universe.** Four validators
at `f = 1` (Byzantine `{0}`, so `Correct = {1,2,3}`); validators
`0, 1, 2` reference only each other, validator `3` builds validly —
self-parent plus two of the others — but is **never referenced by
anyone**. Slot 1 commits directly (leader block 13 at round 3, the full
certificate pattern present), and the committed cone misses author 3 at
**every** layer: `missingAt = {3}`, exactly `f` — CQ1's bound is tight —
and `coveredAt = {1,2}`, exactly `|Correct| − f`, which is still at
least half of `Correct` (CQ2 on data). Every validity, delivery and
liveness clause is satisfiable over this universe, and coverage
(`Synchronised`) fails at every round — commits recur while the same
correct validator is censored from every flush. Aggregate coverage is
not individual inclusion; this is why CQ6 needs `R`, exhibited.

**`Uexcl` — inclusion on data.** The synchronised model of the DoS arc:
CQ5 applied puts a correct round-1 block in the slot-1 commit's cone,
and the ledger membership is checked by `decide` against a concrete
verdict assignment.
-/

namespace LeanDag

open Properties Properties.Arcs MysticetiProperties

/-! ### From the former `Quality/Coverage.lean` -/

open LeanDag.Properties LeanDag.Properties.Arcs

variable {Validator : Type} [Fintype Validator] [DecidableEq Validator]
variable [F : Faults Validator]
variable {BlockId : Type} [DecidableEq BlockId] {Payload : Type}
variable {U : BlockUniverse Validator BlockId Payload}
variable {b L : BlockId} {δ : ℕ}

/-! The correct validators whose round-`δ` block a cone carries are
`Arcs.coveredAt` at the core's rule and reliability — the complement,
within `Correct`, of `missingAt` (`Arcs.coveredAt_eq_sdiff`). -/

/-- **CQ1, the count.** A valid block's cone covers all but at most `f`
of the correct validators, at every round below it. Purely structural:
density (D25) plus the partition. -/
theorem card_coveredAt_ge (hb : b ∈ U.ids) (hδ : δ < (U.block b).round) :
    (Correct : Finset Validator).card - F.f ≤ (Arcs.coveredAt (MysticetiProperties.mysticetiRule (Payload := Payload))
      (coreReliability Validator) U b δ).card :=
  Arcs.card_coveredAt_ge (R := MysticetiProperties.mysticetiRule)
    MysticetiProperties.quorate hb hδ

/-! ## Where the arc depends on the rule

Exactly one step: a committed block is a candidate at the slot's round,
which is `Properties.CommitsCandidate` (`Properties/Candidate.lean`).
Everything above is about valid DAGs alone. -/

section Decided

variable [S : Slots Validator]

/-- **The arc's one rule-dependent step**: a committed block is a block.
`Properties.CommitsCandidate` at the core. -/
theorem mem_ids_of_decided {V : View Validator BlockId Payload U}
    {k : ℕ} (h : Decided U V k (some L)) : L ∈ U.ids :=
  (MysticetiProperties.commitsCandidate (Payload := Payload) S U V k L h).1

/-- **CQ1.** A committed leader's flush covers all but at most `f` of
the correct validators at every round below it — any route, any view,
no synchrony. -/
theorem card_coveredAt_ge_of_decided {V : View Validator BlockId Payload U}
    {k : ℕ} (h : Decided U V k (some L)) (hδ : δ < (U.block L).round) :
    (Correct : Finset Validator).card - F.f ≤ (Arcs.coveredAt (MysticetiProperties.mysticetiRule (Payload := Payload))
      (coreReliability Validator) U L δ).card :=
  Arcs.card_coveredAt_ge_of_decided (R := MysticetiProperties.mysticetiRule)
    MysticetiProperties.quorate
    MysticetiProperties.commitsCandidate h hδ

/-- **CQ2 (the half, exactly).** Every commit carries, at every round
below it, blocks from at least half of the correct validators:
`|Correct| ≤ 2·|covered|`, since `|Correct| ≥ 2f + 1`. -/
theorem card_correct_le_two_mul_coveredAt_of_decided
    {V : View Validator BlockId Payload U} {k : ℕ}
    (h : Decided U V k (some L)) (hδ : δ < (U.block L).round) :
    (Correct : Finset Validator).card ≤ 2 * (Arcs.coveredAt (MysticetiProperties.mysticetiRule (Payload := Payload))
      (coreReliability Validator) U L δ).card :=
  Arcs.card_correct_le_two_mul_coveredAt_of_decided
    (R := MysticetiProperties.mysticetiRule) MysticetiProperties.quorate
    MysticetiProperties.commitsCandidate
    (by
      simp only [coreReliability_correct, coreReliability_slack]
      have := two_f_add_one_le_card_correct (Validator := Validator)
      omega) h hδ

/-- A cone block of a committed slot is in the ledger — the one
unfolding both CQ3 and CQ6 rest on. -/
theorem mem_ledgerSet_of_mem_history {g : ℕ → Option BlockId} {n k : ℕ}
    (hg : g k = some L) (hk : k < n) (hL : L ∈ U.ids)
    (hb : b ∈ history U L) : b ∈ ledgerSet U g n :=
  Arcs.mem_ledgerSetOf_of_mem_history (R := MysticetiProperties.mysticetiRule) hg hk hL hb

/-- **CQ3 (ledger coverage, cumulative).** For a verdict assignment `g`
of a view with a committed slot `k < n` whose leader sits at round `r`:
for every `δ < r`, at least `|Correct| − f` correct validators each
have a round-`δ` block in the ledger `ledgerSet U g n`. The set is
exhibited (`coveredAt`), so no choice and no decidability of the
ledger is needed; view-independence is `ledgerSet_agree`. -/
theorem ledger_coverage {V : View Validator BlockId Payload U}
    {g : ℕ → Option BlockId} {n k : ℕ}
    (hdec : Decided U V k (some L)) (hg : g k = some L) (hk : k < n)
    (hδ : δ < (U.block L).round) :
    ∃ S : Finset Validator, S ⊆ (Correct : Finset Validator) ∧
      (Correct : Finset Validator).card - F.f ≤ S.card ∧
      ∀ v ∈ S, ∃ i ∈ ledgerSet U g n,
        (U.block i).creator = v ∧ (U.block i).round = δ :=
  Arcs.ledger_coverage MysticetiProperties.quorate
    MysticetiProperties.commitsCandidate hdec hg hk hδ

end Decided

/-! ### From the former `Quality/Inclusion.lean` -/

variable {Validator : Type} [Fintype Validator] [DecidableEq Validator]
variable [F : Faults Validator]
variable {BlockId : Type} [DecidableEq BlockId] {Payload : Type}
variable {U : BlockUniverse Validator BlockId Payload}
variable [S : Slots Validator]
variable {T : Finset Validator} {b L : BlockId} {m : ℕ}

/-- **CQ5.** A correct block is in the cone of every committed leader
block by the same author at or above its round — any commit route, any
view, no synchrony. The self-parent chain does all the work. -/
theorem mem_history_of_decided_commit
    {V : View Validator BlockId Payload U} {k : ℕ}
    (hdec : Decided U V k (some L))
    (hLc : (U.block L).creator ∈ (Correct : Finset Validator))
    (hb : b ∈ U.ids) (hbc : (U.block b).creator = (U.block L).creator)
    (hle : (U.block b).round ≤ (U.block L).round) :
    b ∈ history U L :=
  Properties.Arcs.mem_history_of_decided_commit
    (R := MysticetiProperties.mysticetiRule) MysticetiProperties.selfParent
    MysticetiProperties.noEquiv MysticetiProperties.commitsCandidate hdec hLc hb hbc hle

/-- **A slot whose commit carries its leader's round-`m` block into the
ledger.** In any execution meeting the certification precondition at
slot `k`, the slot commits a leader block whose history contains every
round-`m` block by that leader, and every such block is in the agreed
ledger from any later position. Naming it keeps the quantifier order
visible — `k` is fixed by the schedule before an execution is named. -/
def IncludesAt (BlockId : Type) [DecidableEq BlockId] (Payload : Type)
    (T : Finset Validator) (m k : ℕ) : Prop :=
  ∀ (U : BlockUniverse Validator BlockId Payload) (V : View Validator BlockId Payload U),
    MysticetiProperties.certLive S V T k (k + 1) →
    ∃ L, Decided U V k (some L) ∧
      ∀ b ∈ U.ids, (U.block b).creator = S.leader k → (U.block b).round = m →
        b ∈ history U L ∧
        ∀ (g : ℕ → Option BlockId) (n : ℕ), g k = some L → k < n →
          b ∈ ledgerSet U g n

/-- A slot a member of `T` leads at or above round `m` includes that
member's round-`m` blocks. -/
theorem includesAt_of_leads (hT : T ⊆ (Correct : Finset Validator)) {k : ℕ}
    (hlead : S.leader k ∈ T) (hm : m ≤ S.slotRound k) :
    IncludesAt (Validator := Validator) BlockId Payload T m k :=
  fun U V hlive =>
    Properties.Arcs.includes_of_leads (R := MysticetiProperties.mysticetiRule)
      MysticetiProperties.selfParent MysticetiProperties.noEquiv
      MysticetiProperties.commitsCandidate MysticetiProperties.leaderCommits_cert S hT hlead hm
      U V hlive

/-- **CQ6 (inclusion liveness).** Under a schedule fair to each member
of `T`, for every round `m` and every `v ∈ T` there is a slot at or
above `m` that `v` leads, which any execution meeting the certification
precondition commits, and whose flush contains **every** round-`m`
block by `v`; hence every correct block is in the agreed ledger of any
verdict assignment covering its author's next committed slot.

The slot is produced *before* the universe is quantified: the schedule
fixes it, and any execution then commits it. -/
theorem committed_of_correct_block (hT : T ⊆ (Correct : Finset Validator))
    (fair : FairToEach T) (m : ℕ) {v : Validator} (hv : v ∈ T) :
    ∃ k', m ≤ S.slotRound k' ∧ S.leader k' = v ∧
      IncludesAt (Validator := Validator) BlockId Payload T m k' := by
  obtain ⟨k₀, hk₀⟩ := S.unbounded m
  obtain ⟨k', hk', hlead⟩ := fair v hv k₀
  have hm : m ≤ S.slotRound k' := le_trans hk₀ (S.mono hk')
  exact ⟨k', hm, hlead, includesAt_of_leads hT (by rw [hlead]; exact hv) hm⟩

/-- **CQ6 at `T := Correct`.** -/
theorem committed_of_correct_block_correct
    (fair : FairToEach (Correct : Finset Validator)) (m : ℕ) {v : Validator}
    (hv : v ∈ (Correct : Finset Validator)) :
    ∃ k', m ≤ S.slotRound k' ∧ S.leader k' = v ∧
      IncludesAt (Validator := Validator) BlockId Payload (Correct : Finset Validator) m k' :=
  committed_of_correct_block Finset.Subset.rfl fair m hv

/-! ### From the former `Quality/Capstone.lean` -/

variable {Validator : Type} [Fintype Validator] [DecidableEq Validator]
variable [F : Faults Validator]
variable {BlockId : Type} [DecidableEq BlockId] {Payload : Type}
variable [S : Slots Validator]
variable {T : Finset Validator} {w s R m : ℕ}

/-- The least slot at or above a round is monotone in the round. -/
theorem slotAt_le_slotAt {a b : ℕ} (h : a ≤ b) :
    slotAt Validator a ≤ slotAt Validator b :=
  Nat.find_min' _ (le_trans h (le_slotRound_slotAt (Validator := Validator) b))

/-- **Windowed fairness to each validator**: within any `w` consecutive
slots every member of `T` leads once. Round-robin over `n` validators
has it at `w = n`. -/
def FairToEachWithin (T : Finset Validator) (w : ℕ) : Prop :=
  ∀ v ∈ T, ∀ k, ∃ k', k ≤ k' ∧ k' < k + w ∧ S.leader k' = v

/-- **CQ7, windowed.** Under a schedule windowed-fair to each validator,
the committing slot for `v`'s round-`m` blocks lies within `w` slots of
the first slot at or above round `m`. -/
theorem committed_of_correct_block_within
    (hT : T ⊆ (Correct : Finset Validator))
    (fair : FairToEachWithin T w) (m : ℕ) {v : Validator} (hv : v ∈ T) :
    ∃ k', slotAt Validator m ≤ k' ∧ k' < slotAt Validator m + w ∧
      m ≤ S.slotRound k' ∧ S.leader k' = v ∧
      IncludesAt (Validator := Validator) BlockId Payload T m k' := by
  obtain ⟨k', hk₁, hk₂, hlead⟩ := fair v hv (slotAt Validator m)
  have hm : m ≤ S.slotRound k' :=
    le_trans (le_slotRound_slotAt (Validator := Validator) m) (S.mono hk₁)
  exact ⟨k', hk₁, hk₂, hm, hlead, includesAt_of_leads hT (by rw [hlead]; exact hv) hm⟩

/-- **CQ7, by round.** With bounded slot spacing, the committing slot's
round is within `s·w` rounds of the first slot at or above `m`: a
correct block is committed within a schedule-window of rounds of its
creation. -/
theorem committed_of_correct_block_by_round
    (hT : T ⊆ (Correct : Finset Validator))
    (fair : FairToEachWithin T w) (hs : BoundedSpacing (Validator := Validator) s)
    (m : ℕ) {v : Validator} (hv : v ∈ T) :
    ∃ k', m ≤ S.slotRound k' ∧
      S.slotRound k' ≤ S.slotRound (slotAt Validator m) + s * w ∧
      S.leader k' = v ∧
      IncludesAt (Validator := Validator) BlockId Payload T m k' := by
  obtain ⟨k', hk₁, hk₂, hm, hlead, hinc⟩ :=
    committed_of_correct_block_within (BlockId := BlockId) (Payload := Payload) hT fair m hv
  refine ⟨k', hm, ?_, hlead, hinc⟩
  have hd : k' - slotAt Validator m ≤ w := by omega
  have := slotRound_le_of_boundedSpacing hs (slotAt Validator m) (k' - slotAt Validator m)
  rw [Nat.add_sub_cancel' hk₁] at this
  calc S.slotRound k'
      ≤ S.slotRound (slotAt Validator m) + s * (k' - slotAt Validator m) := this
    _ ≤ S.slotRound (slotAt Validator m) + s * w :=
        Nat.add_le_add_left (Nat.mul_le_mul_left s hd) _

/-- **CQ7 (the capstone).** Chain quality in one statement, enforceable
or standard conditions only. Unconditionally: every commit's flush
covers at least half of the correct validators at every round below
it. Under a schedule fair to each member of `T`: every block by a member
of `T` is in the flush of a slot its author leads, fixed in advance by
the schedule. -/
theorem chain_quality (hT : T ⊆ (Correct : Finset Validator))
    (fair : FairToEach T) (m : ℕ) :
    (∀ (U : BlockUniverse Validator BlockId Payload)
        (V : View Validator BlockId Payload U) (k : ℕ) (L : BlockId)
        (δ : ℕ), Decided U V k (some L) → δ < (U.block L).round →
        (Correct : Finset Validator).card ≤
          2 * (Properties.Arcs.coveredAt (MysticetiProperties.mysticetiRule (Payload := Payload))
            (coreReliability Validator) U L δ).card) ∧
    ∀ v ∈ T, ∃ k', m ≤ S.slotRound k' ∧ S.leader k' = v ∧
      IncludesAt (Validator := Validator) BlockId Payload T m k' :=
  ⟨fun _ _ _ _ _ hdec hδ =>
    card_correct_le_two_mul_coveredAt_of_decided hdec hδ,
   fun v hv => committed_of_correct_block (BlockId := BlockId) (Payload := Payload) hT fair m hv⟩

/-- **The inclusion half, in a given execution** (CQ4′). `chain_quality`
conjoins the unconditional coverage bound with an inclusion statement whose
slot is fixed by the schedule ahead of any execution. This is the other
half read in a fixed universe: the certification precondition holds at
the slots `v` leads from round `m`, and the schedule supplies one whose
commit carries every round-`m` block by `v` into the ledger. -/
theorem chain_quality_of_run (hT : T ⊆ (Correct : Finset Validator))
    (fair : FairToEach T) (m : ℕ) {v : Validator} (hv : v ∈ T)
    (U : BlockUniverse Validator BlockId Payload)
    (hcert : ∀ k, S.leader k = v → m ≤ S.slotRound k →
      MysticetiProperties.certLive S (View.full U) T k (k + 1)) :
    ∃ k', m ≤ S.slotRound k' ∧ S.leader k' = v ∧
      ∃ L : BlockId, Decided U (View.full U) k' (some L) ∧
        ∀ b ∈ U.ids, (U.block b).creator = v → (U.block b).round = m →
          b ∈ history U L ∧
          ∀ (g : ℕ → Option BlockId) (n : ℕ), g k' = some L → k' < n →
            b ∈ ledgerSet U g n := by
  obtain ⟨k', hm, hlead, hinc⟩ :=
    committed_of_correct_block (BlockId := BlockId) (Payload := Payload) hT fair m hv
  obtain ⟨L, hdec, hb⟩ := hinc U (View.full U) (hcert k' hlead hm)
  exact ⟨k', hm, hlead, L, hdec, fun b hb' hbc hbr => hb b hb' (by rw [hlead]; exact hbc) hbr⟩

end LeanDag

namespace LeanDagTest

open LeanDag

/-! ## The censorship model -/

/-- Six rounds of four: `{0,1,2}` reference each other; `3` self-parents
and references two of the others; nobody references `3`. -/
def censBlk : Fin 24 → Block (Fin 4) (Fin 24) Unit := fun i =>
  { round := (i : ℕ) / 4,
    creator := ⟨(i : ℕ) % 4, by omega⟩,
    refs :=
      if (i : ℕ) / 4 = 0 then ∅
      else if (i : ℕ) % 4 = 3 then
        { ⟨4 * ((i : ℕ) / 4 - 1) + 3, by have := i.isLt; omega⟩,
          ⟨4 * ((i : ℕ) / 4 - 1), by have := i.isLt; omega⟩,
          ⟨4 * ((i : ℕ) / 4 - 1) + 1, by have := i.isLt; omega⟩ }
      else
        { ⟨4 * ((i : ℕ) / 4 - 1), by have := i.isLt; omega⟩,
          ⟨4 * ((i : ℕ) / 4 - 1) + 1, by have := i.isLt; omega⟩,
          ⟨4 * ((i : ℕ) / 4 - 1) + 2, by have := i.isLt; omega⟩ },
    payload := () }

def Ucens : BlockUniverse (Fin 4) (Fin 24) Unit where
  ids := Finset.univ
  block := censBlk
  complete := by decide
  valid := by decide
  no_equivocation := by decide

-- Slot 1 (round 3, leader 1): block 13, directly committed — the full
-- certificate pattern is present.
example : IsLeaderBlock Ucens 1 13 := by decide
example : DirectCommit Ucens 13 3 := by decide

theorem ucens_slot1 : Decided Ucens (View.full Ucens) 1 (some 13) :=
  Decided.directCommit (by decide) (by decide)

/-! ## CQ1/CQ2 on data — tight, and still half -/

-- The committed cone misses author 3 at every layer: exactly `f`.
example : missingAt Ucens 13 0 = {3} := by decide
example : missingAt Ucens 13 1 = {3} := by decide
example : missingAt Ucens 13 2 = {3} := by decide
example : (missingAt Ucens 13 0).card = Faults.f (Fin 4) := by decide

-- Covered: exactly `|Correct| − f = 2` of the three correct validators.
example : Properties.Arcs.coveredAt MysticetiProperties.mysticetiRule (coreReliability (Fin 4)) Ucens 13 1 = {1, 2} := by decide

-- CQ1 applied, and CQ2 applied: 3 ≤ 2·2.
example : (Correct : Finset (Fin 4)).card - Faults.f (Fin 4) ≤
    (Properties.Arcs.coveredAt MysticetiProperties.mysticetiRule (coreReliability (Fin 4)) Ucens 13 1).card :=
  card_coveredAt_ge_of_decided ucens_slot1 (by decide)

example : (Correct : Finset (Fin 4)).card ≤ 2 * (Properties.Arcs.coveredAt MysticetiProperties.mysticetiRule (coreReliability (Fin 4)) Ucens 13 1).card :=
  card_correct_le_two_mul_coveredAt_of_decided ucens_slot1 (by decide)

/-! ## The censorship, exhibited -/

-- No block of author 3 is in the committed cone…
example : ∀ i ∈ Ucens.ids, (Ucens.block i).creator = 3 →
    i ∉ history Ucens 13 := by decide

-- …and coverage fails at every round it could be tested: the round-3
-- block of author 1 does not reference author 3's round-2 block.
example : ¬ Synchronised Ucens 0 := by
  intro h
  exact absurd
    (h 2 (by omega) 13 (by decide) (by decide) (by decide)
      11 (by decide) (by decide) (by decide))
    (by decide)

example : ¬ Synchronised Ucens 2 := by
  intro h
  exact absurd
    (h 2 (by omega) 13 (by decide) (by decide) (by decide)
      11 (by decide) (by decide) (by decide))
    (by decide)

/-! ## The ledger, on data -/

/-- A concrete verdict assignment: slot 1 commits block 13. -/
def gcens : ℕ → Option (Fin 24) := fun k => if k = 1 then some 13 else none

-- A correct-authored cone block is in the ledger…
example : (5 : Fin 24) ∈ ledgerSet Ucens gcens 2 :=
  ⟨1, by omega, 13, rfl, (mem_history_iff (by decide)).mp (by decide)⟩

-- …and the censored validator's block is not.
example : (7 : Fin 24) ∉ ledgerSet Ucens gcens 2 := by
  rintro ⟨k, hk, L, hL, hr⟩
  interval_cases k
  · simp [gcens] at hL
  · rw [show L = 13 from ((by simpa [gcens] using hL : (13 : Fin 24) = L)).symm] at hr
    exact absurd ((mem_history_iff (by decide)).mpr hr) (by decide)

-- CQ3 applied: at least two correct validators have round-1 blocks in
-- the ledger.
example : ∃ S : Finset (Fin 4), S ⊆ (Correct : Finset (Fin 4)) ∧
    (Correct : Finset (Fin 4)).card - Faults.f (Fin 4) ≤ S.card ∧
    ∀ v ∈ S, ∃ i ∈ ledgerSet Ucens gcens 2,
      (Ucens.block i).creator = v ∧ (Ucens.block i).round = 1 :=
  ledger_coverage ucens_slot1 rfl (by omega) (by decide)

/-! ## CQ5/CQ6 on data — inclusion, from self-reference -/

theorem uexcl_slot1_commit : Decided Uexcl (View.full Uexcl) 1 (some 11) :=
  Decided.directCommit (by decide) (by decide)

-- CQ5 applied: every block by the slot-1 leader's author at or below its
-- round is in the commit's cone — and the same fact confirmed on the data.
example : ∀ b ∈ Uexcl.ids, (Uexcl.block b).creator = (Uexcl.block 11).creator →
    (Uexcl.block b).round ≤ (Uexcl.block 11).round → b ∈ history Uexcl 11 :=
  fun b hb hbc hle => mem_history_of_decided_commit uexcl_slot1_commit (by decide) hb hbc hle

example : ∀ b ∈ Uexcl.ids, (Uexcl.block b).creator = (Uexcl.block 11).creator →
    (Uexcl.block b).round ≤ (Uexcl.block 11).round → b ∈ history Uexcl 11 := by
  decide

-- CQ6's schedule side, instantiated: `fairSlots` returns to validator
-- `1` at every slot, and the theorem produces a slot `1` leads at or
-- above round 1.
example : ∃ k', 1 ≤ fairSlots.slotRound k' ∧ fairSlots.leader k' = 1 := by
  obtain ⟨k', hk', hlead, -⟩ :=
    committed_of_correct_block (S := fairSlots) (BlockId := Fin 20) (Payload := Unit)
      (T := {1}) (by decide)
      (fun v hv k => ⟨k, le_refl k, by rw [fairSlots_leader]; exact (Finset.mem_singleton.mp hv).symm⟩)
      1 (Finset.mem_singleton_self 1)
  exact ⟨k', hk', hlead⟩

/-! ## CQ7 on data — the windowed bound instantiated -/

/-- Round-robin over four validators is windowed-fair to each at `w = 4`. -/
theorem rrSlots_fairToEachWithin :
    FairToEachWithin (S := rrSlots) ({1, 2, 3} : Finset (Fin 4)) 4 := by
  intro v _ k
  have hv := v.isLt
  refine ⟨k + (v.val + 4 - k % 4) % 4, by omega, by omega, ?_⟩
  apply Fin.ext
  rw [rrSlots_leader_val]
  omega

-- Under the round-robin schedule, the committing slot for validator
-- `1`'s round-`1` blocks is pinned to a four-slot window.
example : ∃ k', slotAt (Fin 4) (S := rrSlots) 1 ≤ k' ∧
    k' < slotAt (Fin 4) (S := rrSlots) 1 + 4 := by
  obtain ⟨k', h1, h2, -⟩ :=
    committed_of_correct_block_within (S := rrSlots) (BlockId := Fin 20)
      (Payload := Unit) (by decide) rrSlots_fairToEachWithin 1 (v := 1) (by decide)
  exact ⟨k', h1, h2⟩

#print axioms chain_quality
#print axioms committed_of_correct_block_within
#print axioms committed_of_correct_block_by_round
#print axioms card_coveredAt_ge_of_decided
#print axioms card_correct_le_two_mul_coveredAt_of_decided
#print axioms ledger_coverage
#print axioms mem_history_of_decided_commit
#print axioms committed_of_correct_block

end LeanDagTest
