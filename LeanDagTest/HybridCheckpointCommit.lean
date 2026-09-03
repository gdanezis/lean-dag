import LeanDagTest.Hybrid
import LeanDag.Hybrid.Checkpoint.CommitProofs

/-!
# Commit-to-checkpoint bridge witnesses

Two models over the nine-validator hybrid instance `hyb9`.

`Uhyb9` (from `LeanDagTest/Hybrid.lean`) has a Byzantine leader at
slot `0` that nonetheless commits directly. Its execution follows the
signing rule by definition, the Byzantine validator emits a conflicting
checkpoint, and the concrete commit produces one checkpoint, a
first-phase quorum certificate, and a second-phase finality certificate.
The conflicting checkpoint has no certificate.

`Usync9` is a synchronised three-round universe with a correct leader at
slot `1`. It discharges every hypothesis of `LiveCommitFinalized`, so the
finalized checkpoint there is derived from production and coverage
without any commit being supplied.
-/

namespace LeanDagTest

open LeanDag LeanDag.Hybrid LeanDag.Hybrid.Checkpoint

/-- The bridge uses the secure base model without an additional AbC
population. -/
def bridgeFaults : Checkpoint.FlexibleFaults (Fin 9) ℕ where
  fabc := 0
  abc := ∅
  disjoint_byzantine := by simp
  disjoint_crash := by simp
  card_abc := by simp
  resilient := by decide

/-- The VM abstraction maps the committed leader deterministically to
the application checkpoint: height one, epoch zero, the block's id as
the sole history entry. -/
def natVM (n : ℕ) : DeterministicVM (BlockId := Fin n) (Value := ℕ) where
  checkpointAfterCommit := fun _ block =>
    { height := 1, epoch := 0, history := [block.val] }

/-- Distinct hypothetical committed blocks produce distinct application
checkpoints; determinism is not witnessed by a constant function. -/
example :
    (natVM 18).checkpointAfterCommit 0 0 ≠
      (natVM 18).checkpointAfterCommit 0 1 := by
  decide

/-! ## `Uhyb9`: a Byzantine-led commit, with a Byzantine fork attempt -/

/-- Deterministic application state after the `Uhyb9` commit of block `0`. -/
def committedCheckpoint : CheckpointData ℕ where
  height := 1
  epoch := 0
  history := [0]

/-- A second view of `Uhyb9`: it lacks the Byzantine twin (`17`) and
validator `7`'s round-1 block (`16`), so slot `0` has exactly `q = 7`
supporters in view. -/
def partialView : View (Fin 9) (Fin 18) Unit Uhyb9 where
  ids := (Finset.univ.erase 17).erase 16
  subset_ids := Finset.subset_univ _
  complete := by decide

example : partialView.ids ≠ (View.full Uhyb9).ids := by decide
example : (Hybrid.supportersIn Uhyb9 partialView 0 0).card = Hybrid.q (Fin 9) := by
  decide

/-- The partial view also commits slot `0`, at the tight quorum. -/
theorem uhyb9_slot0_partial :
    Hybrid.Decided 4 Uhyb9 partialView 0 (some 0) :=
  Decided.directCommit (by decide) (by decide)

/-- Validator `7` holds the partial view; everyone else holds the full
one. Views differ, decisions do not. -/
def bridgeView (v : Fin 9) : View (Fin 9) (Fin 18) Unit Uhyb9 :=
  if v = 7 then partialView else View.full Uhyb9

/-- `Uhyb9` has rounds `0` and `1` only. -/
theorem uhyb9_round_le (b : Fin 18) : (Uhyb9.block b).round ≤ 1 := by
  revert b; decide

/-- In `Uhyb9`, the only block-valued decision on any view is slot `0`
committing block `0`: slot `0` by base safety against `uhyb9_slot0`,
and no higher slot because its leader round or its anchor's leader
round would exceed the universe's two rounds. -/
theorem uhyb9_decided_eq {V : View (Fin 9) (Fin 18) Unit Uhyb9}
    {s : ℕ} {b : Fin 18} (h : Hybrid.Decided 4 Uhyb9 V s (some b)) :
    s = 0 ∧ b = 0 := by
  have hL := Hybrid.isLeaderBlock_of_decided h
  have hround := uhyb9_round_le b
  have hs : s ≤ 1 := by
    have := hL.2.1
    simp at this
    omega
  interval_cases s
  · exact ⟨rfl, Hybrid.safety (by decide) (by decide) h uhyb9_slot0⟩
  · exfalso
    cases h with
    | directCommit _ hdc =>
      have hempty : blocksAt Uhyb9 2 = ∅ := by decide
      have hfaults : HybridFaults.fb (Fin 9) + HybridFaults.fc (Fin 9) = 2 := rfl
      simp [Hybrid.DirectCommitIn, Hybrid.supportersIn, hempty,
        creatorsOf, Hybrid.q, hfaults] at hdc
    | @indirectCommit _ j A _ hlt _ hj _ _ _ _ =>
      have hA := (Hybrid.isLeaderBlock_of_decided hj).2.1
      have hAr := uhyb9_round_le A
      simp at hA
      omega

/-- A checkpoint the Byzantine validator proposes instead of the
committed one. -/
def forkedCheckpoint : CheckpointData ℕ where
  height := 1
  epoch := 0
  history := [5]

example : forkedCheckpoint ≠ committedCheckpoint := by decide

/-- Proposals are defined by the signing rule for the online correct
validators, and by adversarial choice for the Byzantine one: validator
`0` proposes `forkedCheckpoint`; the crashed validator `8` proposes
nothing. Records are durable storage of the committed checkpoint by
online correct validators, a predicate distinct from proposal. -/
def bridgeExecution : bridgeFaults.Execution ℕ where
  genesis := fun _ => []
  localHistory := fun _ _ height => List.replicate height 0
  emitted := fun message =>
    (message.sender ∈ bridgeFaults.RecoveryCorrect ∧
      ∃ slot block, Hybrid.Decided 4 Uhyb9 (bridgeView message.sender) slot (some block) ∧
        message.checkpoint = (natVM 18).checkpointAfterCommit slot block) ∨
    (message.sender = 0 ∧ message.checkpoint = forkedCheckpoint)
  recorded := fun validator checkpoint =>
    validator ∈ bridgeFaults.RecoveryCorrect ∧ checkpoint = committedCheckpoint
  genesis_prefix := by
    intro message _ _
    simp
  local_extension := by
    intro validator epoch h₁ h₂ _ le
    rw [List.prefix_iff_eq_take]
    simp [List.take_replicate, Nat.min_eq_left le]
  emitted_from_state := by
    intro message hm reliable
    rcases hm with ⟨_, slot, block, hdec, hc⟩ | ⟨h0, _⟩
    · obtain ⟨rfl, rfl⟩ := uhyb9_decided_eq hdec
      simp [hc, natVM]
    · rw [h0] at reliable
      exact absurd reliable (by decide)
  local_height := by
    intro message hm reliable
    rcases hm with ⟨_, slot, block, hdec, hc⟩ | ⟨h0, _⟩
    · obtain ⟨rfl, rfl⟩ := uhyb9_decided_eq hdec
      simp [hc, natVM]
    · rw [h0] at reliable
      exact absurd reliable (by decide)

/-- Every proposal from an online correct validator is the committed
checkpoint. -/
theorem bridgeExecution_emitted {message : ChkProp (Fin 9) ℕ}
    (h : bridgeExecution.emitted message)
    (hv : message.sender ∈ bridgeFaults.RecoveryCorrect) :
    message.checkpoint = committedCheckpoint := by
  rcases h with ⟨_, slot, block, hdec, hc⟩ | ⟨h0, _⟩
  · obtain ⟨rfl, rfl⟩ := uhyb9_decided_eq hdec
    exact hc
  · rw [h0] at hv
    exact absurd hv (by decide)

/-- The Byzantine validator proposes the fork; the crashed one proposes
nothing; validator `1` proposes the committed checkpoint because its
view committed slot `0`. -/
example : bridgeExecution.emitted ⟨0, forkedCheckpoint⟩ := Or.inr ⟨rfl, rfl⟩
example : ¬ bridgeExecution.emitted ⟨8, committedCheckpoint⟩ := by
  rintro (⟨h, -⟩ | ⟨h, -⟩)
  · exact absurd h (by decide)
  · exact absurd h (by decide)
example : bridgeExecution.emitted ⟨1, committedCheckpoint⟩ :=
  Or.inl ⟨by decide, 0, 0, uhyb9_slot0, rfl⟩

/-- The fork has no first-phase certificate: its only proposer is the
Byzantine validator, six signers short of the quorum. -/
example :
    IsEmpty (Checkpoint.FlexibleFaults.Execution.CheckpointQC bridgeFaults
      bridgeExecution forkedCheckpoint) := by
  refine ⟨fun Q => ?_⟩
  have hsub : Q.signers ⊆ {0} := by
    intro v hv
    rcases Q.messages v hv with ⟨_, slot, block, hdec, hc⟩ | ⟨h0, _⟩
    · obtain ⟨rfl, rfl⟩ := uhyb9_decided_eq hdec
      simp [forkedCheckpoint, natVM] at hc
    · exact Finset.mem_singleton.mpr h0
  have hcard := Finset.card_le_card hsub
  have hq := Q.quorum
  have h7 : Hybrid.q (Fin 9) = 7 := by decide
  simp at hcard
  omega

/-- The signing rule holds of this execution: proposals are its
definition, and a witness records what it proposed because every
online correct proposal is the committed checkpoint. -/
def bridgeRule :
    Checkpoint.FlexibleFaults.Execution.SigningRule bridgeFaults bridgeExecution
      Uhyb9 4 (natVM 18) where
  noAbC := rfl
  view := bridgeView
  proposes := by
    intro v hv slot block hdec
    exact Or.inl ⟨hv, slot, block, hdec, rfl⟩
  witnesses := by
    intro v hv checkpoint he Q
    exact
      { sender := v
        certificate := Q
        recorded := fun hv' => ⟨hv', bridgeExecution_emitted he hv⟩ }
  witnessSender := by
    intro v hv checkpoint he Q
    rfl

/-- The crash fault remains present and is not required to sign. -/
example : (8 : Fin 9) ∉ bridgeFaults.RecoveryCorrect := by decide

/-- Nevertheless the online base-correct validators form the required
checkpoint quorum by the inherited fault bound. -/
example : Hybrid.q (Fin 9) ≤ bridgeFaults.RecoveryCorrect.card :=
  Checkpoint.FlexibleFaults.Execution.recoveryCorrect_quorum
    bridgeFaults bridgeRule.noAbC

/-- Every online correct validator settled slot `0` on its own view. -/
theorem bridge_all_decided :
    ∀ v ∈ bridgeFaults.RecoveryCorrect,
      ∃ b, Hybrid.Decided 4 Uhyb9 (bridgeView v) 0 (some b) := by
  intro v _
  by_cases hv : v = 7
  · exact ⟨0, by rw [bridgeView, if_pos hv]; exact uhyb9_slot0_partial⟩
  · exact ⟨0, by rw [bridgeView, if_neg hv]; exact uhyb9_slot0⟩

/-- The real Hybrid commit reaches the end of checkpoint signing. -/
def committedCheckpointFinality :
    Checkpoint.FlexibleFaults.Execution.FinalityQC bridgeFaults bridgeExecution
      committedCheckpoint :=
  Checkpoint.FlexibleFaults.Execution.finalityQCOfDecided
    bridgeFaults bridgeExecution (natVM 18) bridgeRule (by decide) (by decide)
    uhyb9_slot0 bridge_all_decided

/-- The same commit also constructs the intermediate first-phase QC. -/
def committedCheckpointQC :
    Checkpoint.FlexibleFaults.Execution.CheckpointQC bridgeFaults bridgeExecution
      committedCheckpoint :=
  Checkpoint.FlexibleFaults.Execution.checkpointQCOfDecided
    bridgeFaults bridgeExecution (natVM 18) bridgeRule (by decide) (by decide)
    uhyb9_slot0 bridge_all_decided

/-- Whatever block any view commits at slot `0`, deterministic execution
reaches the checkpoint of the full-view commit: base safety, not the
concrete block value, closes the goal. -/
theorem slot0_checkpoint_unique {V : View (Fin 9) (Fin 18) Unit Uhyb9}
    {block : Fin 18} (commit : Hybrid.Decided 4 Uhyb9 V 0 (some block)) :
    (natVM 18).checkpointAfterCommit 0 block = committedCheckpoint :=
  Checkpoint.FlexibleFaults.Execution.checkpointAfterCommit_eq (natVM 18)
    (by decide) (by decide) commit uhyb9_slot0

example : (natVM 18).checkpointAfterCommit 0 0 = committedCheckpoint :=
  slot0_checkpoint_unique uhyb9_slot0_partial

/-! ## `Usync9`: a correct-led slot finalized from liveness alone

Rounds `0`, `1`, `2`, authored by the online correct validators `1`–`7`
only. Every non-genesis block references all seven blocks of the round
below, so the universe is synchronised over `RecoveryCorrect` from
round `1`. The Byzantine validator is silent here; the fork attempt
above already covers adversarial emission. -/

/-- Ids `7k`–`7k+6` are round `k`, creators `1`–`7`, referencing the
whole previous round. -/
def sync9Blk : Fin 21 → Block (Fin 9) (Fin 21) Unit := fun i =>
  if h : (i : ℕ) < 7 then
    { round := 0, creator := ⟨(i : ℕ) + 1, by omega⟩, refs := ∅, payload := () }
  else if h : (i : ℕ) < 14 then
    { round := 1, creator := ⟨(i : ℕ) - 6, by omega⟩,
      refs := {0, 1, 2, 3, 4, 5, 6}, payload := () }
  else
    { round := 2, creator := ⟨(i : ℕ) - 13, by have := i.isLt; omega⟩,
      refs := {7, 8, 9, 10, 11, 12, 13}, payload := () }

def Usync9 : BlockUniverse (Fin 9) (Fin 21) Unit where
  ids := Finset.univ
  block := sync9Blk
  complete := by decide
  valid := by decide
  no_equivocation := by decide

example : HonestNoEquiv Usync9 := by decide

/-- Slot `1`: leader `1`, a correct validator; its block is id `7`. -/
example : (hyb9Slots.leader 1 : Fin 9) = 1 := by decide
example : IsLeaderBlock Usync9 1 7 := by decide
example : (1 : Fin 9) ∈ bridgeFaults.RecoveryCorrect := by decide

/-- Deterministic application state after the `Usync9` commit of block `7`. -/
def syncCheckpoint : CheckpointData ℕ where
  height := 1
  epoch := 0
  history := [7]

/-- The direct commit that liveness will rediscover. -/
theorem usync9_slot1 :
    Hybrid.Decided 4 Usync9 (View.full Usync9) 1 (some 7) :=
  Decided.directCommit (by decide) (by decide)

/-- `Usync9` has rounds `0`, `1`, `2` only. -/
theorem usync9_round_le (b : Fin 21) : (Usync9.block b).round ≤ 2 := by
  revert b; decide

/-- In `Usync9`, the only block-valued decision on any view is slot `1`
committing block `7`: slot `0`'s leader is silent, slot `1` by base
safety against `usync9_slot1`, and slot `2` lacks a supporter round. -/
theorem usync9_decided_eq {V : View (Fin 9) (Fin 21) Unit Usync9}
    {s : ℕ} {b : Fin 21} (h : Hybrid.Decided 4 Usync9 V s (some b)) :
    s = 1 ∧ b = 7 := by
  have hL := Hybrid.isLeaderBlock_of_decided h
  have hround := usync9_round_le b
  have hs : s ≤ 2 := by
    have := hL.2.1
    simp at this
    omega
  interval_cases s
  · exfalso
    have hnone : ∀ L, ¬ IsLeaderBlock Usync9 0 L := by decide
    exact hnone b hL
  · exact ⟨rfl, Hybrid.safety (by decide) (by decide) h usync9_slot1⟩
  · exfalso
    cases h with
    | directCommit _ hdc =>
      have hempty : blocksAt Usync9 3 = ∅ := by decide
      have hfaults : HybridFaults.fb (Fin 9) + HybridFaults.fc (Fin 9) = 2 := rfl
      simp [Hybrid.DirectCommitIn, Hybrid.supportersIn, hempty,
        creatorsOf, Hybrid.q, hfaults] at hdc
    | @indirectCommit _ j A _ hlt _ hj _ _ _ _ =>
      have hA := (Hybrid.isLeaderBlock_of_decided hj).2.1
      have hAr := usync9_round_le A
      simp at hA
      omega

/-- Proposals follow the signing rule on the full view; records store
the committed checkpoint. -/
def syncExecution : bridgeFaults.Execution ℕ where
  genesis := fun _ => []
  localHistory := fun _ _ height => List.replicate height 7
  emitted := fun message =>
    message.sender ∈ bridgeFaults.RecoveryCorrect ∧
      ∃ slot block, Hybrid.Decided 4 Usync9 (View.full Usync9) slot (some block) ∧
        message.checkpoint = (natVM 21).checkpointAfterCommit slot block
  recorded := fun validator checkpoint =>
    validator ∈ bridgeFaults.RecoveryCorrect ∧ checkpoint = syncCheckpoint
  genesis_prefix := by
    intro message _ _
    simp
  local_extension := by
    intro validator epoch h₁ h₂ _ le
    rw [List.prefix_iff_eq_take]
    simp [List.take_replicate, Nat.min_eq_left le]
  emitted_from_state := by
    intro message ⟨_, slot, block, hdec, hc⟩ _
    obtain ⟨rfl, rfl⟩ := usync9_decided_eq hdec
    simp [hc, natVM]
  local_height := by
    intro message ⟨_, slot, block, hdec, hc⟩ _
    obtain ⟨rfl, rfl⟩ := usync9_decided_eq hdec
    simp [hc, natVM]

theorem syncExecution_emitted {message : ChkProp (Fin 9) ℕ}
    (h : syncExecution.emitted message) :
    message.checkpoint = syncCheckpoint := by
  obtain ⟨_, slot, block, hdec, hc⟩ := h
  obtain ⟨rfl, rfl⟩ := usync9_decided_eq hdec
  exact hc

def syncRule :
    Checkpoint.FlexibleFaults.Execution.SigningRule bridgeFaults syncExecution
      Usync9 4 (natVM 21) where
  noAbC := rfl
  view := fun _ => View.full Usync9
  proposes := by
    intro v hv slot block hdec
    exact ⟨hv, slot, block, hdec, rfl⟩
  witnesses := by
    intro v hv checkpoint he Q
    exact
      { sender := v
        certificate := Q
        recorded := fun hv' => ⟨hv', syncExecution_emitted he⟩ }
  witnessSender := by
    intro v hv checkpoint he Q
    rfl

/-- Coverage over the online correct validators from round `1`: the only
round pair at or above it is `(1, 2)`, and every round-2 block
references every round-1 block. -/
theorem usync9_synchronised :
    SynchronisedOn Usync9 bridgeFaults.RecoveryCorrect 1 := by
  intro n hn b hb hbr hbc a ha har hac
  have hn1 : n = 1 := by
    have := usync9_round_le b
    omega
  subst hn1
  revert b a
  decide

example : PopulatedOn Usync9 bridgeFaults.RecoveryCorrect 1 := by decide
example : PopulatedOn Usync9 bridgeFaults.RecoveryCorrect 2 := by decide

/-- **Liveness delivers the checkpoint.** No commit is supplied: the
hypotheses are the fault bound, production at rounds `1` and `2`,
coverage from round `1`, caught-up views, and a correct leader. -/
theorem usync9_live :
    ∃ L, IsLeaderBlock Usync9 1 L ∧
      Nonempty (Checkpoint.FlexibleFaults.Execution.FinalityQC bridgeFaults
        syncExecution ((natVM 21).checkpointAfterCommit 1 L)) :=
  Checkpoint.FlexibleFaults.Execution.liveCommitFinalized
    bridgeFaults syncExecution (natVM 21) syncRule (R := 1)
    (by decide) (by decide) usync9_synchronised (by decide) (by decide) (by decide)
    (fun _ _ => View.coversUpto_full _ _) (by decide)

/-- The block liveness finds is the leader block, so the finalized
checkpoint is the committed one. -/
theorem usync9_live_committed :
    Nonempty (Checkpoint.FlexibleFaults.Execution.FinalityQC bridgeFaults
      syncExecution syncCheckpoint) := by
  obtain ⟨L, hL, hF⟩ := usync9_live
  have hall : ∀ L, IsLeaderBlock Usync9 1 L → L = 7 := by decide
  obtain rfl := hall L hL
  exact hF

/-! ## Claims instantiated -/

example : Checkpoint.FlexibleFaults.Execution.CommitFinalized
    bridgeFaults bridgeExecution Unit (natVM 18) :=
  Checkpoint.FlexibleFaults.Execution.commitFinalized
    bridgeFaults bridgeExecution (natVM 18)

example : Checkpoint.FlexibleFaults.Execution.LiveCommitFinalized
    bridgeFaults syncExecution Unit (natVM 21) :=
  Checkpoint.FlexibleFaults.Execution.liveCommitFinalized
    bridgeFaults syncExecution (natVM 21)

example : Checkpoint.FlexibleFaults.Execution.CommitCheckpointUnique
    (Validator := Fin 9) Unit (natVM 18) :=
  Checkpoint.FlexibleFaults.Execution.checkpointAfterCommit_eq (natVM 18)

#print axioms slot0_checkpoint_unique
#print axioms committedCheckpointQC
#print axioms committedCheckpointFinality
#print axioms usync9_live_committed
#print axioms LeanDag.Hybrid.Checkpoint.FlexibleFaults.Execution.recoveryCorrect_quorum
#print axioms LeanDag.Hybrid.Checkpoint.FlexibleFaults.Execution.commitCertified
#print axioms LeanDag.Hybrid.Checkpoint.FlexibleFaults.Execution.commitFinalized
#print axioms LeanDag.Hybrid.Checkpoint.FlexibleFaults.Execution.liveCommitFinalized
#print axioms LeanDag.Hybrid.Checkpoint.FlexibleFaults.Execution.checkpointAfterCommit_eq

end LeanDagTest
