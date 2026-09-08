import LeanDag.Quality.Inclusion
import LeanDag.Mysticeti.Quantitative
/-!
# Chain quality: the capstone, and the quantitative bounds

`chain-quality.md` §4, CQP3 — **CQ7**: under a fair schedule over
reliable validators, every commit's flush covers at least half the
correct validators unconditionally, and post-`R` every correct block
lands in the flush of a committed slot fixed by the schedule in
advance. `committed_of_correct_block_within` / `…_by_round` give the
quantitative form of the second half, in slots or in rounds.
-/

namespace LeanDag

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
