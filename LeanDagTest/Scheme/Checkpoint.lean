import LeanDagTest.Scheme.TryDecide
import LeanDag.Integration.SchemeCheckpoint
import LeanDag.Checkpoint.CarryProofs

/-!
# Checkpoints over the unified decider, witnessed

The generic checkpoint bridge at the scheme's carrier, on Mysticeti's
`U7` at the Mysticeti row with the least vote. Slot `1` commits block
`12` directly; slot `0` commits block `0` *indirectly* through that
anchor — the first checkpoint witness whose source commit is indirect.
Both commits carry both signing phases to a finality certificate, and
the two checkpoints chain: the VM appends the committed block to the
ledger prefix, so slot `0`'s history is a prefix of slot `1`'s.

The signing faults are concrete: quorum `3`, the non-Byzantine
validators reliable and available, both counting bounds by `decide`.
-/

namespace LeanDagTest

namespace Scheme

open LeanDag LeanDag.Scheme LeanDag.Checkpoint LeanDag.Integration LeanDag.Properties

/-- Quorum `3` of `4`; validator `0` is Byzantine, nobody crashes, no AbC. -/
def u7Signing : SigningFaults (Fin 4) where
  q := 3
  reliableSigner := {1, 2, 3}
  recoveryCorrect := {1, 2, 3}
  alive := {1, 2, 3}
  recoveryCorrect_subset_alive := Finset.Subset.rfl
  intersect := by decide
  reach := by decide

/-- The deterministic VM: the ledger prefix below the slot, then the
committed block. Slot-dependent and block-dependent. -/
def u7VM : DeterministicVM (BlockId := Fin 24) (Value := ℕ) where
  checkpointAfterCommit := fun k b => ⟨k + 1, 0, [(0 : ℕ), 12].take k ++ [b.val]⟩

/-- Slot `1` commits block `12` directly at the Mysticeti row. -/
theorem u7s_slot1 : (schemeAnchored myst σL).Decided U7 V7 1 (some 12) :=
  AnchoredRule.Decided.directCommit (by decide) (by decide)

/-- Slot `0` commits block `0` indirectly, anchored on slot `1`: the lone
certificate (block `8`) lies in the anchor's history. -/
theorem u7s_slot0 : (schemeAnchored myst σL).Decided U7 V7 0 (some 0) :=
  AnchoredRule.Decided.indirectCommit (i := 0) (j := 1) (A := 12)
    (by omega) (by decide) u7s_slot1
    (fun m h1 h2 _ => absurd h2 (by omega))
    (by decide) (fun i hi => absurd hi (Nat.not_lt_zero _))
    (by decide)
    (show myst.linkSize ≤ (creatorsOf U7.block
      (linkCerts myst σL U7 12 0 (Slots.slotRound (Fin 4) 0))).card by decide)
    (fun L' _ _ => Fin.not_lt_zero L')

/-- The row tolerates `U7`'s faults at the core quorum: one validator
outside the honest set, and the three-round inequalities at `q = 3`. -/
theorem u7Tolerates : myst.Tolerates (Correct : Finset (Fin 4)) 1 (quorumCard (Fin 4)) :=
  ⟨by decide, by decide,
    Or.inr (Or.inl ⟨rfl, by decide, rfl, by decide, by decide, by decide⟩)⟩

/-- In `U7` at this row, the only block-valued decisions on any view are
slot `0` committing block `0` and slot `1` committing block `12`: those
two by agreement against the concrete derivations, and no higher slot
because its candidate's round would exceed the universe's six rounds. -/
theorem u7s_decided_eq {V : View (Fin 4) (Fin 24) Unit U7} {s : ℕ} {b : Fin 24}
    (h : (schemeRule myst σL).Decided inferInstance V s (some b)) :
    (s = 0 ∧ b = 0) ∨ (s = 1 ∧ b = 12) := by
  have hL := AnchoredRule.isLeaderBlock_of_decided h
  have hround : ∀ c : Fin 24, (U7.block c).round ≤ 5 := by decide
  have hround := hround b
  have hs : s ≤ 1 := by
    have := hL.2.1
    simp at this
    omega
  interval_cases s
  · exact Or.inl ⟨rfl, Option.some.inj
      (Scheme.agree u7Tolerates _ V V7 0 _ _ h u7s_slot0)⟩
  · exact Or.inr ⟨rfl, Option.some.inj
      (Scheme.agree u7Tolerates _ V V7 1 _ _ h u7s_slot1)⟩

/-- The two committed checkpoints. -/
def u7Chk0 : CheckpointData ℕ := u7VM.checkpointAfterCommit 0 0
def u7Chk1 : CheckpointData ℕ := u7VM.checkpointAfterCommit 1 12

/-- Proposals follow the signing rule on `V7`; records store the two
committed checkpoints. -/
def u7Execution : u7Signing.Execution ℕ where
  genesis := fun _ => []
  localHistory := fun _ _ height => [(0 : ℕ), 12].take height
  emitted := fun message =>
    message.sender ∈ u7Signing.alive ∧
      ∃ slot block,
        (schemeRule myst σL).Decided inferInstance V7 slot (some block) ∧
        message.checkpoint = u7VM.checkpointAfterCommit slot block
  recorded := fun validator checkpoint =>
    validator ∈ u7Signing.recoveryCorrect ∧
      (checkpoint = u7Chk0 ∨ checkpoint = u7Chk1)
  genesis_prefix := by
    intro message _ _
    simp
  local_extension := by
    intro validator epoch h₁ h₂ _ le
    have h := List.take_prefix h₁ ([(0 : ℕ), 12].take h₂)
    rwa [List.take_take, Nat.min_eq_left le] at h
  emitted_from_state := by
    intro message hm _
    obtain ⟨-, slot, block, hdec, hc⟩ := hm
    rcases u7s_decided_eq hdec with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
      simp [hc, u7VM]
  local_height := by
    intro message hm _
    obtain ⟨-, slot, block, hdec, hc⟩ := hm
    rcases u7s_decided_eq hdec with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
      simp [hc, u7VM]

/-- Every proposal names one of the two committed checkpoints. -/
theorem u7Execution_emitted {message : ChkProp (Fin 4) ℕ}
    (h : u7Execution.emitted message) :
    message.checkpoint = u7Chk0 ∨ message.checkpoint = u7Chk1 := by
  obtain ⟨-, slot, block, hdec, hc⟩ := h
  rcases u7s_decided_eq hdec with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact Or.inl hc
  · exact Or.inr hc

/-- The signing rule on `U7`: every rule-following validator holds `V7`. -/
def u7Rule :
    SigningFaults.Execution.SigningRule u7Signing u7Execution
      (schemeRule myst σL) inferInstance U7 u7VM where
  quorum := by decide
  view := fun _ => V7
  proposes := fun v hv _ _ hdec => ⟨hv, _, _, hdec, rfl⟩
  witnesses := fun v hv _ he Q =>
    ⟨{ sender := v
       certificate := Q
       recorded := fun hv' => ⟨hv', u7Execution_emitted he⟩ },
     rfl⟩

/-- Every rule-following validator settled slot `0` and slot `1` on its own view. -/
theorem u7_all_decided (slot : ℕ) (hs : slot ≤ 1) :
    ∀ v ∈ u7Signing.alive,
      ∃ b, (schemeRule myst σL).Decided inferInstance (u7Rule.view v) slot (some b) := by
  intro v _
  interval_cases slot
  · exact ⟨0, u7s_slot0⟩
  · exact ⟨12, u7s_slot1⟩

/-- **The indirect commit reaches second-tier finality.** -/
theorem u7Finality0 :
    Nonempty (SigningFaults.Execution.FinalityQC u7Signing u7Execution u7Chk0) :=
  commitFinalized_scheme u7Signing u7Execution u7VM u7Tolerates _ u7Rule
    u7s_slot0 (u7_all_decided 0 (by omega))

/-- **And the direct one.** -/
theorem u7Finality1 :
    Nonempty (SigningFaults.Execution.FinalityQC u7Signing u7Execution u7Chk1) :=
  commitFinalized_scheme u7Signing u7Execution u7VM u7Tolerates _ u7Rule
    u7s_slot1 (u7_all_decided 1 le_rfl)

/-- The two finalized checkpoints chain: slot `0`'s history is a prefix
of slot `1`'s. -/
example : u7Chk0.history.IsPrefix u7Chk1.history := by decide

/-- Whatever block any view commits at slot `0`, the checkpoint content
is slot `0`'s: agreement, not the block value, closes the goal. -/
theorem u7_checkpoint_unique {V : View (Fin 4) (Fin 24) Unit U7} {block : Fin 24}
    (commit : (schemeRule myst σL).Decided inferInstance V 0 (some block)) :
    u7VM.checkpointAfterCommit 0 block = u7Chk0 :=
  checkpointUnique_scheme u7VM u7Tolerates _ commit u7s_slot0

/-! ## Liveness delivers the checkpoint, on `full4` at the Mahi-Mahi row

`full4` references every block of the round below, so production,
certification and coverage all hold by `decide`. No commit is supplied:
slot `1`, led by the correct validator `1`, reaches second-tier finality
from the hypotheses of `liveCommitFinalized_scheme` alone. -/

section Live

local instance liveSlots : Slots (Fin 4) :=
  Slots.uniformSingle 1 (by omega) (fun k => ⟨k % 4, by omega⟩)

/-- Slots `0`, `1`, `2` commit blocks `0`, `5`, `10` directly. -/
theorem full4_slot0 : (schemeAnchored mm4 σL).Decided full4 (View.full full4) 0 (some 0) :=
  AnchoredRule.Decided.directCommit (by decide) (by decide)

theorem full4_slot1 : (schemeAnchored mm4 σL).Decided full4 (View.full full4) 1 (some 5) :=
  AnchoredRule.Decided.directCommit (by decide) (by decide)

theorem full4_slot2 : (schemeAnchored mm4 σL).Decided full4 (View.full full4) 2 (some 10) :=
  AnchoredRule.Decided.directCommit (by decide) (by decide)

/-- The Mahi-Mahi row at wave four tolerates `full4`'s faults. -/
theorem mm4Tolerates : mm4.Tolerates (Correct : Finset (Fin 4)) 1 (quorumCard (Fin 4)) :=
  ⟨by decide, by decide,
    Or.inr (Or.inl ⟨rfl, by decide, rfl, by decide, by decide, by decide⟩)⟩

/-- In `full4` at this row, the only block-valued decisions are slots
`0`, `1`, `2` committing blocks `0`, `5`, `10`: those three by agreement
against the concrete derivations, and no higher slot because its decision
round or its anchor's candidate round would exceed the six rounds. -/
theorem full4_decided_eq {V : View (Fin 4) (Fin 24) Unit full4} {s : ℕ} {b : Fin 24}
    (h : (schemeRule mm4 σL).Decided inferInstance V s (some b)) :
    (s = 0 ∧ b = 0) ∨ (s = 1 ∧ b = 5) ∨ (s = 2 ∧ b = 10) := by
  have hL := AnchoredRule.isLeaderBlock_of_decided h
  have hround : ∀ c : Fin 24, (full4.block c).round ≤ 5 := by decide
  have hs : s ≤ 5 := by
    have hb := hround b
    have := hL.2.1
    simp at this
    omega
  have hdead : ∀ s', 3 ≤ s' → s' ≤ 5 → ∀ {V' : View (Fin 4) (Fin 24) Unit full4}
      {b' : Fin 24}, ¬ (schemeRule mm4 σL).Decided inferInstance V' s' (some b') := by
    intro s' h3 h5 V' b' h'
    have hw : mm4.waveLength = 4 := rfl
    cases h' with
    | directCommit hL' hc =>
      have hle := hc.le
      have hempty : ∀ c : Fin 24, ∀ r, 3 ≤ r →
          (creatorsOf full4.block (certsAt mm4 σL full4 c r)).card = 0 := by
        intro c r hr
        have : certsAt mm4 σL full4 c r = ∅ := by
          refine Finset.eq_empty_of_forall_notMem fun x hx => ?_
          obtain ⟨hx, -⟩ := Finset.mem_filter.mp hx
          obtain ⟨hxU, hxr⟩ := mem_blocksAt.mp hx
          rw [hw] at hxr
          have := hround x
          omega
        simp [this, creatorsOf]
      have hsr : Slots.slotRound (Fin 4) s' = s' := by simp
      have hct : mm4.commitThreshold = 3 := rfl
      have h0 := hempty b' (Slots.slotRound (Fin 4) s') (by omega)
      omega
    | @indirectCommit _ j A _ _ hlt helig hj _ _ _ _ _ _ =>
      have hA := (AnchoredRule.isLeaderBlock_of_decided hj).2.1
      have hAr := hround A
      have hwv : (schemeAnchored mm4 σL).waveAt (Slots.kind (Fin 4) s') = 3 := rfl
      have hel := ((schemeAnchored mm4 σL).eligible_iff).mp helig
      rw [hwv] at hel
      simp at hA hel
      omega
  interval_cases s
  · exact Or.inl ⟨rfl, Option.some.inj
      (Scheme.agree mm4Tolerates _ V (View.full full4) 0 _ _ h full4_slot0)⟩
  · exact Or.inr (Or.inl ⟨rfl, Option.some.inj
      (Scheme.agree mm4Tolerates _ V (View.full full4) 1 _ _ h full4_slot1)⟩)
  · exact Or.inr (Or.inr ⟨rfl, Option.some.inj
      (Scheme.agree mm4Tolerates _ V (View.full full4) 2 _ _ h full4_slot2)⟩)
  · exact absurd h (hdead 3 (by omega) (by omega))
  · exact absurd h (hdead 4 (by omega) (by omega))
  · exact absurd h (hdead 5 (by omega) (by omega))

/-- Quorum `3`; the non-Byzantine validators reliable and available. -/
def liveSigning : SigningFaults (Fin 4) where
  q := 3
  reliableSigner := {1, 2, 3}
  recoveryCorrect := {1, 2, 3}
  alive := {1, 2, 3}
  recoveryCorrect_subset_alive := Finset.Subset.rfl
  intersect := by decide
  reach := by decide

/-- The ledger prefix below the slot, then the committed block. -/
def liveVM : DeterministicVM (BlockId := Fin 24) (Value := ℕ) where
  checkpointAfterCommit := fun k b => ⟨k + 1, 0, [(0 : ℕ), 5, 10].take k ++ [b.val]⟩

/-- Proposals follow the signing rule on the full view. -/
def full4Execution : liveSigning.Execution ℕ where
  genesis := fun _ => []
  localHistory := fun _ _ height => [(0 : ℕ), 5, 10].take height
  emitted := fun message =>
    message.sender ∈ liveSigning.alive ∧
      ∃ slot block,
        (schemeRule mm4 σL).Decided inferInstance (View.full full4) slot (some block) ∧
        message.checkpoint = liveVM.checkpointAfterCommit slot block
  recorded := fun validator checkpoint =>
    validator ∈ liveSigning.recoveryCorrect ∧
      (checkpoint = liveVM.checkpointAfterCommit 0 0 ∨
        checkpoint = liveVM.checkpointAfterCommit 1 5 ∨
        checkpoint = liveVM.checkpointAfterCommit 2 10)
  genesis_prefix := by
    intro message _ _
    simp
  local_extension := by
    intro validator epoch h₁ h₂ _ le
    have h := List.take_prefix h₁ ([(0 : ℕ), 5, 10].take h₂)
    rwa [List.take_take, Nat.min_eq_left le] at h
  emitted_from_state := by
    intro message hm _
    obtain ⟨-, slot, block, hdec, hc⟩ := hm
    rcases full4_decided_eq hdec with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
      simp [hc, liveVM]
  local_height := by
    intro message hm _
    obtain ⟨-, slot, block, hdec, hc⟩ := hm
    rcases full4_decided_eq hdec with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
      simp [hc, liveVM]

/-- Certification at the family's support is the decider's `IsCert`,
which is decidable. -/
local instance : ∀ (U : (schemeRule mm4 σL).Universe) (c L : Fin 24),
    Decidable ((familySupport mm4 σL).Certifies U c L) := fun U c L =>
  inferInstanceAs (Decidable (IsCert mm4 σL U c L))

/-- Every candidate of slot `1` is certified by every available signer's
decision-round block. -/
theorem full4_certified : ∀ L : Fin 24,
    (schemeRule mm4 σL).IsCandidate inferInstance full4 1 L →
    (familySupport mm4 σL).certifiesAt full4 liveSigning.recoveryCorrect
      (Slots.slotRound (Fin 4) 1) (Slots.kind (Fin 4) 1) L := by
  decide

/-- The full view covers every round. -/
theorem full4_covers (N : ℕ) :
    Properties.CoversUpto (schemeRule mm4 σL) (View.full full4) N :=
  fun b hb _ => by
    change b ∈ (View.full full4).ids
    rw [View.full_ids]
    exact hb

/-- Every proposal names one of the three committed checkpoints. -/
theorem full4Execution_emitted {message : ChkProp (Fin 4) ℕ}
    (h : full4Execution.emitted message) :
    message.checkpoint = liveVM.checkpointAfterCommit 0 0 ∨
      message.checkpoint = liveVM.checkpointAfterCommit 1 5 ∨
      message.checkpoint = liveVM.checkpointAfterCommit 2 10 := by
  obtain ⟨-, slot, block, hdec, hc⟩ := h
  rcases full4_decided_eq hdec with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact Or.inl hc
  · exact Or.inr (Or.inl hc)
  · exact Or.inr (Or.inr hc)

/-- The signing rule on `full4`: every rule-following validator holds
the full view. -/
def full4Rule :
    SigningFaults.Execution.SigningRule liveSigning full4Execution
      (schemeRule mm4 σL) inferInstance full4 liveVM where
  quorum := by decide
  view := fun _ => View.full full4
  proposes := fun v hv _ _ hdec => ⟨hv, _, _, hdec, rfl⟩
  witnesses := fun v hv _ he Q =>
    ⟨{ sender := v
       certificate := Q
       recorded := fun hv' => ⟨hv', full4Execution_emitted he⟩ },
     rfl⟩

/-- **Liveness delivers the checkpoint**: production, certification,
coverage and a correct leader, no commit supplied. -/
theorem full4_live :
    ∃ L, (schemeRule mm4 σL).IsCandidate inferInstance full4 1 L ∧
      Nonempty (SigningFaults.Execution.FinalityQC liveSigning full4Execution
        (liveVM.checkpointAfterCommit 1 L)) :=
  liveCommitFinalized_scheme liveSigning full4Execution liveVM mm4Tolerates
    (rel := coreReliability (Fin 4)) (by decide) _ full4Rule
    (by decide) (fun n h1 h2 => by revert h1 h2; revert n; decide)
    full4_certified (fun v _ => full4_covers _) (by decide)

/-- The block liveness finds is slot `1`'s candidate, so the finalized
checkpoint is the committed one. -/
theorem full4_live_committed :
    Nonempty (SigningFaults.Execution.FinalityQC liveSigning full4Execution
      (liveVM.checkpointAfterCommit 1 5)) := by
  obtain ⟨L, hL, hF⟩ := full4_live
  have hall : ∀ L : Fin 24,
      (schemeRule mm4 σL).IsCandidate inferInstance full4 1 L → L = 5 := by decide
  obtain rfl := hall L hL
  exact hF

end Live

/-! ## Proposals carried in blocks, witnessed

`full4c` is `full4` with the checkpoint of slot `k` carried by the
round-`k+4` blocks; the content map is the identity. The chronology is
causal: at wave four, slot `k` is decided by the certificate blocks of
round `k+3`, so a validator observes the commit when it has those
blocks and carries the checkpoint in its next block, which references
them. Each validator's view is the record up to round `4`, on which
slots `0` and `1` are decided and slot `2` is not; rounds `4` and `5`
carry slots `0` and `1`. Emission is block authorship, so it is
decidable on the record, and the carried run finalizes the slot-`1`
commit through the derived execution and rule. -/

section Carried

local instance carrySlots : Slots (Fin 4) :=
  Slots.uniformSingle 1 (by omega) (fun k => ⟨k % 4, by omega⟩)

/-- The proposal for slot `k`, `k ≤ 2`: the ledger prefix through slot `k`. -/
def carryProp (k : ℕ) : Checkpoint.CheckpointData ℕ :=
  liveVM.checkpointAfterCommit k (if k = 0 then 0 else if k = 1 then 5 else 10)

/-- `full4`'s blocks, with the round-`k+4` blocks carrying slot `k`'s
checkpoint. -/
def full4cBlk : Fin 24 → Block (Fin 4) (Fin 24) (Option (Checkpoint.CheckpointData ℕ)) :=
  fun i =>
    let b := mmFullBlk i
    { round := b.round, creator := b.creator, refs := b.refs,
      payload := if 4 ≤ b.round then some (carryProp (b.round - 4)) else none }

def full4c : BlockUniverse (Fin 4) (Fin 24) (Option (Checkpoint.CheckpointData ℕ)) where
  ids := Finset.univ
  block := full4cBlk
  complete := by decide
  valid := by decide
  no_equivocation := by decide

/-- The least vote at the payload-carrying universe. -/
abbrev σC : VoteSel (Fin 4) (Fin 24) (Option (Checkpoint.CheckpointData ℕ))
    ValidWrt Correct := leastSel

theorem full4c_slot0 : (schemeAnchored mm4 σC).Decided full4c (View.full full4c) 0 (some 0) :=
  AnchoredRule.Decided.directCommit (by decide) (by decide)

theorem full4c_slot1 : (schemeAnchored mm4 σC).Decided full4c (View.full full4c) 1 (some 5) :=
  AnchoredRule.Decided.directCommit (by decide) (by decide)

theorem full4c_slot2 : (schemeAnchored mm4 σC).Decided full4c (View.full full4c) 2 (some 10) :=
  AnchoredRule.Decided.directCommit (by decide) (by decide)

/-- As `full4_decided_eq`, at the payload-carrying universe. -/
theorem full4c_decided_eq {V : View (Fin 4) (Fin 24) (Option (Checkpoint.CheckpointData ℕ))
    full4c} {s : ℕ} {b : Fin 24}
    (h : (schemeRule mm4 σC).Decided inferInstance V s (some b)) :
    (s = 0 ∧ b = 0) ∨ (s = 1 ∧ b = 5) ∨ (s = 2 ∧ b = 10) := by
  have hL := AnchoredRule.isLeaderBlock_of_decided h
  have hround : ∀ c : Fin 24, (full4c.block c).round ≤ 5 := by decide
  have hs : s ≤ 5 := by
    have hb := hround b
    have := hL.2.1
    simp at this
    omega
  have hdead : ∀ s', 3 ≤ s' → s' ≤ 5 →
      ∀ {V' : View (Fin 4) (Fin 24) (Option (Checkpoint.CheckpointData ℕ)) full4c}
      {b' : Fin 24}, ¬ (schemeRule mm4 σC).Decided inferInstance V' s' (some b') := by
    intro s' h3 h5 V' b' h'
    have hw : mm4.waveLength = 4 := rfl
    cases h' with
    | directCommit hL' hc =>
      have hle := hc.le
      have hempty : ∀ c : Fin 24, ∀ r, 3 ≤ r →
          (creatorsOf full4c.block (certsAt mm4 σC full4c c r)).card = 0 := by
        intro c r hr
        have : certsAt mm4 σC full4c c r = ∅ := by
          refine Finset.eq_empty_of_forall_notMem fun x hx => ?_
          obtain ⟨hx, -⟩ := Finset.mem_filter.mp hx
          obtain ⟨hxU, hxr⟩ := mem_blocksAt.mp hx
          rw [hw] at hxr
          have := hround x
          omega
        simp [this, creatorsOf]
      have hsr : Slots.slotRound (Fin 4) s' = s' := by simp
      have hct : mm4.commitThreshold = 3 := rfl
      have h0 := hempty b' (Slots.slotRound (Fin 4) s') (by omega)
      omega
    | @indirectCommit _ j A _ _ hlt helig hj _ _ _ _ _ _ =>
      have hA := (AnchoredRule.isLeaderBlock_of_decided hj).2.1
      have hAr := hround A
      have hwv : (schemeAnchored mm4 σC).waveAt (Slots.kind (Fin 4) s') = 3 := rfl
      have hel := ((schemeAnchored mm4 σC).eligible_iff).mp helig
      rw [hwv] at hel
      simp at hA hel
      omega
  interval_cases s
  · exact Or.inl ⟨rfl, Option.some.inj
      (Scheme.agree mm4Tolerates _ V (View.full full4c) 0 _ _ h full4c_slot0)⟩
  · exact Or.inr (Or.inl ⟨rfl, Option.some.inj
      (Scheme.agree mm4Tolerates _ V (View.full full4c) 1 _ _ h full4c_slot1)⟩)
  · exact Or.inr (Or.inr ⟨rfl, Option.some.inj
      (Scheme.agree mm4Tolerates _ V (View.full full4c) 2 _ _ h full4c_slot2)⟩)
  · exact absurd h (hdead 3 (by omega) (by omega))
  · exact absurd h (hdead 4 (by omega) (by omega))
  · exact absurd h (hdead 5 (by omega) (by omega))

/-- Each validator's view when it authors its round-`5` block: the
record up to round `4`. -/
def upto4 : View (Fin 4) (Fin 24) (Option (Checkpoint.CheckpointData ℕ)) full4c where
  ids := Finset.univ.filter fun b => (full4c.block b).round ≤ 4
  subset_ids := Finset.subset_univ _
  complete := by decide

/-- **Chronology.** A block carries a checkpoint only from round `4` on,
and the round-`k+4` block carries slot `k`'s; slot `k` is decided by the
round-`k+3` certificate blocks (`certsAt` at wave four), which the
carrying block references. -/
example : ∀ b : Fin 24, (full4c.block b).payload ≠ none ↔ 4 ≤ (full4c.block b).round := by
  decide
example : ∀ b : Fin 24, 4 ≤ (full4c.block b).round →
    (full4c.block b).payload = some (carryProp ((full4c.block b).round - 4)) := by
  decide
example : ∀ b : Fin 24, 4 ≤ (full4c.block b).round →
    ∀ c : Fin 24, (full4c.block c).round + 1 = (full4c.block b).round →
      c ∈ (full4c.block b).refs := by
  decide

/-- Slots `0` and `1` are decided on the view up to round `4`. -/
theorem upto4_slot0 : (schemeAnchored mm4 σC).Decided full4c upto4 0 (some 0) :=
  AnchoredRule.Decided.directCommit (by decide) (by decide)

theorem upto4_slot1 : (schemeAnchored mm4 σC).Decided full4c upto4 1 (some 5) :=
  AnchoredRule.Decided.directCommit (by decide) (by decide)

/-- On the view up to round `4`, slot `2` is not decided: its certificate
blocks are at round `5`, and no higher slot is decided to anchor it. -/
theorem upto4_decided_eq {s : ℕ} {b : Fin 24}
    (h : (schemeRule mm4 σC).Decided inferInstance upto4 s (some b)) :
    (s = 0 ∧ b = 0) ∨ (s = 1 ∧ b = 5) := by
  rcases full4c_decided_eq h with h0 | h1 | ⟨rfl, rfl⟩
  · exact Or.inl h0
  · exact Or.inr h1
  · exfalso
    cases h with
    | directCommit _ hc =>
      have hno : ¬ (schemeAnchored mm4 σC).Commit full4c upto4 10
          (Slots.slotRound (Fin 4) 2) (Slots.kind (Fin 4) 2) := by decide
      exact hno hc
    | @indirectCommit _ j _ _ _ hlt _ hj _ _ _ _ _ _ =>
      rcases full4c_decided_eq hj with ⟨rfl, -⟩ | ⟨rfl, -⟩ | ⟨rfl, -⟩ <;> omega

/-- The carried run: proposals ride in blocks, the identity content map
reads them off, every validator decides on the record up to round `4`,
and storage retains what a quorum of blocks carried. -/
def carriedRun :
    liveSigning.CarriedSigning (schemeRule mm4 σC) inferInstance full4c liveVM id where
  genesis := fun _ => []
  localHistory := fun _ _ height => [(0 : ℕ), 5, 10].take height
  recorded := fun v x =>
    v ∈ liveSigning.recoveryCorrect ∧
      ∃ S : Finset (Fin 4), liveSigning.q ≤ S.card ∧
        ∀ w ∈ S, ∃ b ∈ full4c.ids, (full4c.block b).creator = w ∧
          (full4c.block b).payload = some x
  view := fun _ => upto4
  quorum := by decide
  content_from_state := by decide
  local_extension := by
    intro v e h₁ h₂ _ le
    have h := List.take_prefix h₁ ([(0 : ℕ), 5, 10].take h₂)
    rwa [List.take_take, Nat.min_eq_left le] at h
  proposes := by
    intro v hv slot block hdec
    rcases upto4_decided_eq hdec with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
      (revert hv; revert v; decide)
  stores := by
    intro v hv x S hS hall _
    exact ⟨hv, S, hS, hall⟩

/-- **Emission is observable**: validator `1`'s round-`4` block (id `17`)
carries slot `0`'s checkpoint, as data. -/
example : carriedRun.execution.emitted ⟨1, liveVM.checkpointAfterCommit 0 0⟩ :=
  ⟨17, Finset.mem_univ _, rfl, rfl⟩

/-- **The carried run finalizes the slot-`1` commit** through the derived
execution and rule: no abstract emission anywhere in the hypotheses. -/
theorem carried_finality :
    Nonempty (SigningFaults.Execution.FinalityQC liveSigning carriedRun.execution
      (liveVM.checkpointAfterCommit 1 5)) :=
  carriedRun.commitFinalized (Scheme.agree mm4Tolerates) upto4_slot1
    (fun _ _ => ⟨5, upto4_slot1⟩)

end Carried

#print axioms u7Finality0
#print axioms u7Finality1
#print axioms full4_live_committed
#print axioms carried_finality
#print axioms LeanDag.Integration.commitFinalized_scheme
#print axioms LeanDag.Integration.liveCommitFinalized_scheme
#print axioms LeanDag.Integration.checkpointUnique_scheme
#print axioms LeanDag.Checkpoint.SigningFaults.CarriedSigning.commitFinalized

end Scheme

end LeanDagTest
