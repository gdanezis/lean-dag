import LeanDag.Quality.Coverage
import LeanDag.DoS.Exclusion
import LeanDag.Mysticeti.Properties
/-!
# Chain quality: inclusion, from self-reference

`chain-quality.md` §4, CQP2 — **CQ5**, **CQ6**: the aggregate coverage
of `Coverage.lean` upgrades to an individual guarantee, that every
correct block enters the agreed ledger, with no synchrony. A correct
validator's self-referencing chain (P3′) reaches every earlier block of
its own, so its author's next committed leader block carries it, and a
schedule fair to each validator supplies that slot. The generic arc is
`Properties/Arcs/Quality.lean`; this file names the core's instance.
-/

namespace LeanDag

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

end LeanDag
