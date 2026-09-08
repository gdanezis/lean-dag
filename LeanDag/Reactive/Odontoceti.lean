import LeanDag.Reactive.Basic
import LeanDag.Odontoceti.Liveness
/-!
# Reactive Odontoceti

The two-round rule, run reactively. Odontoceti's direct commit counts
supporters at the round above the leader with no certificate stage, so
`ReactivePace`'s vote stage is the entire reactive protocol: a fast
slot crosses one reactive exit rather than Mysticeti's two, and its
latency is a single delivery plus processing.
-/

namespace LeanDag

namespace Odontoceti

variable {Validator : Type} [Fintype Validator] [DecidableEq Validator]
variable [F : Faults5 Validator]
variable {BlockId : Type} [LinearOrder BlockId] {Payload : Type}
variable {U : BlockUniverse Validator BlockId Payload}
variable [S : Slots Validator]
variable {T : Finset Validator} {N R : ℕ} {k : ℕ} {L : BlockId}

/-- **The reactive direct commit (Odontoceti)** — the shared counting
theorem (`directCommit_of_votesAt`) fed by the reactive vote supplier,
with the vote blocks from derived production. One application; the
argument lives with O7, once. -/
theorem reactive_directCommit (rc : ReactivePace U T N)
    (hT : T ⊆ (Correct : Finset Validator))
    (hcard : quorumCard Validator ≤ T.card)
    (hgst : rc.gst ≤ R)
    (hto : ∀ n, R ≤ n → 2 * rc.delay + rc.proc ≤ rc.timeout n)
    (hR : R ≤ S.slotRound k) (hN : S.slotRound k + 1 ≤ N)
    (hlead : S.leader k ∈ T) (hL : IsLeaderBlock U k L) :
    DirectCommit U L (S.slotRound k) :=
  directCommit_of_votesAt hcard
    (rc.toPaceCore.populatedOn hcard (S.slotRound k + 1) hN)
    (rc.votes hT hcard hgst hto hR hN hlead hL)

/-- **Reactive liveness (Odontoceti).** A reliable-led slot past GST is
committed by every view caught up to the horizon — the conclusion of
the two-round `decided_of_leader_mem`, from the single reactive wait
clause and the trunk's derived production. One delivery separates a
fast leader from its commit. -/
theorem reactive_decided (rc : ReactivePace U T N)
    (hT : T ⊆ (Correct : Finset Validator))
    (hcard : quorumCard Validator ≤ T.card)
    (hgst : rc.gst ≤ R)
    (hto : ∀ n, R ≤ n → 2 * rc.delay + rc.proc ≤ rc.timeout n)
    (hR : R ≤ S.slotRound k) (hN : S.slotRound k + 1 ≤ N)
    (V : View Validator BlockId Payload U) (hcov : V.CoversUpto N)
    (hlead : S.leader k ∈ T) :
    ∃ L, IsLeaderBlock U k L ∧ Decided U V k (some L) := by
  obtain ⟨L, hLmem, hLc, hLr⟩ :=
    rc.toPaceCore.populatedOn hcard (S.slotRound k) (by omega) (S.leader k) hlead
  have hL : IsLeaderBlock U k L := ⟨hLmem, hLr, hLc⟩
  exact ⟨L, hL, Decided.directCommit hL
    (directCommitIn_of_coversUpto
      (reactive_directCommit rc hT hcard hgst hto hR hN hlead hL)
      (hcov.mono hN))⟩

end Odontoceti

end LeanDag
