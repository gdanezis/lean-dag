import LeanDag.Reactive.Basic
/-!
# Reactive Mysticeti

The three-round rule, run reactively. The vote stage is `ReactivePace`'s;
`ReactiveM` adds the certificate stage, a validator that voted waits at
round `r + 2` only until it can certify, with the timeout as fallback
(`cert_or_wait`). The commit rule itself — `DirectCommit`, `Certifies`,
`Decided` — is untouched; only where the liveness hypotheses come from
changes, `SynchronisedOn` giving way to the two reactive wait clauses.
-/

namespace LeanDag

variable {Validator : Type} [Fintype Validator] [DecidableEq Validator]
variable [F : Faults Validator]
variable {BlockId : Type} [DecidableEq BlockId] {Payload : Type}
variable {U : BlockUniverse Validator BlockId Payload}
variable [S : Slots Validator]
variable {T : Finset Validator} {N R : ℕ} {k : ℕ} {L : BlockId}

/-- The reactive three-round schedule: `ReactivePace`'s vote stage,
plus the certificate wait, stated over any `T`-authored block. -/
structure ReactiveM (U : BlockUniverse Validator BlockId Payload)
    (T : Finset Validator) (N : ℕ) extends ReactivePace U T N where
  /-- **The certificate wait.** At two rounds above a reliable leader,
  any `T`-authored block either already certifies (the reactive exit —
  its references carry a quorum of votes), or its builder waited the
  full timeout and references every reliable vote it holds (the
  fallback). -/
  cert_or_wait : ∀ v ∈ T, ∀ k : ℕ, S.slotRound k + 2 ≤ N → S.leader k ∈ T →
    ∀ L, IsLeaderBlock U k L →
    ∀ c ∈ U.ids, (U.block c).creator = v → (U.block c).round = S.slotRound k + 2 →
    Certifies U c L ∨
      (built v (S.slotRound k + 1) + timeout (S.slotRound k + 1)
          ≤ built v (S.slotRound k + 2) ∧
        ∀ b ∈ U.ids, (U.block b).creator ∈ T →
          (U.block b).round = S.slotRound k + 1 →
          b ∈ holds v (built v (S.slotRound k + 2)) →
          L ∈ (U.block b).refs → b ∈ (U.block c).refs)

namespace ReactiveM

variable (rm : ReactiveM U T N)

/-- **Every reliable certificate block certifies.** By construction on
the reactive exit; on the fallback, every reliable vote has arrived
before the build (convergence and the collapsed drift), so the block
references all of `T`'s votes. -/
theorem certifies (hT : T ⊆ (Correct : Finset Validator))
    (hcard : quorumCard Validator ≤ T.card)
    (hgst : rm.gst ≤ R)
    (hto : ∀ n, R ≤ n → 2 * rm.delay + rm.proc ≤ rm.timeout n)
    (hR : R ≤ S.slotRound k) (hN : S.slotRound k + 2 ≤ N)
    (hlead : S.leader k ∈ T) (hL : IsLeaderBlock U k L) :
    CertifiesAt U T (S.slotRound k) L := by
  have hD := rm.driftOn_of_catchup hcard hgst
  intro v hv c hc hcc hcr
  rcases rm.cert_or_wait v hv k hN hlead L hL c hc hcc hcr with hcert | ⟨hwait, hincl⟩
  · exact hcert
  · -- the fallback block references every reliable vote; count them
    have hvotes := rm.toReactivePace.votes hT hcard hgst hto hR (by omega) hlead hL
    -- each `u ∈ T` has a vote block, by derived production
    have hpop := rm.toPaceCore.populatedOn hcard (S.slotRound k + 1) (by omega)
    refine le_trans hcard (Finset.card_le_card ?_)
    intro u hu
    obtain ⟨b, hb, hbc, hbr⟩ := hpop u hu
    have hvote : L ∈ (U.block b).refs := hvotes u hu b hb hbc hbr
    have harrive : b ∈ rm.holds v (rm.built v (S.slotRound k + 2)) := by
      have hown := rm.holds_own u hu (S.slotRound k + 1) (by omega) b hb hbc hbr
      have htopu : S.slotRound k + 1 ≤ rm.top u := by
        have := rm.le_top_of_built u hu b hb hbc
        omega
      have hgstu : rm.gst ≤ rm.built u (S.slotRound k + 1) :=
        le_trans (le_trans hgst (by omega)) (rm.le_built hu _ htopu)
      have hconv := rm.converges v hv u hu _ hgstu hown
      refine rm.holds_mono v _ _ ?_ hconv
      have hdrift := hD v hv u hu (S.slotRound k + 1) (by omega) (by omega)
      have := hto (S.slotRound k + 1) (by omega)
      omega
    refine mem_creatorsOf.mpr ⟨b, ?_, hbc⟩
    exact Finset.mem_filter.mpr ⟨hincl b hb (hbc ▸ hu) hbr harrive hvote, hvote⟩

/-- **The reactive direct commit** — the shared counting theorem
(`directCommit_of_certifiesAt`) fed by the reactive certificate
supplier, with the certificate blocks from derived production. One
application; the argument lives in `Liveness.lean`, once. -/
theorem directCommit (hT : T ⊆ (Correct : Finset Validator))
    (hcard : quorumCard Validator ≤ T.card)
    (hgst : rm.gst ≤ R)
    (hto : ∀ n, R ≤ n → 2 * rm.delay + rm.proc ≤ rm.timeout n)
    (hR : R ≤ S.slotRound k) (hN : S.slotRound k + 2 ≤ N)
    (hlead : S.leader k ∈ T) (hL : IsLeaderBlock U k L) :
    DirectCommit U L (S.slotRound k) :=
  directCommit_of_certifiesAt hcard
    (rm.toPaceCore.populatedOn hcard (S.slotRound k + 2) (by omega))
    (rm.certifies hT hcard hgst hto hR hN hlead hL)

/-- **Reactive liveness (Mysticeti).** A reliable-led slot past GST is
committed by every view — the conclusion of `decided_of_leader_mem`,
with reference coverage replaced by the two reactive wait clauses and
the leader block supplied by derived production. -/
theorem decided (hT : T ⊆ (Correct : Finset Validator))
    (hcard : quorumCard Validator ≤ T.card)
    (hgst : rm.gst ≤ R)
    (hto : ∀ n, R ≤ n → 2 * rm.delay + rm.proc ≤ rm.timeout n)
    (hR : R ≤ S.slotRound k) (hN : S.slotRound k + 2 ≤ N)
    (hlead : S.leader k ∈ T) :
    ∃ L, IsLeaderBlock U k L ∧ Decided U (View.full U) k (some L) := by
  obtain ⟨L, hLmem, hLc, hLr⟩ :=
    rm.toPaceCore.populatedOn hcard (S.slotRound k) (by omega) (S.leader k) hlead
  have hL : IsLeaderBlock U k L := ⟨hLmem, hLr, hLc⟩
  exact ⟨L, hL, Decided.directCommit hL
    (directCommitIn_full (rm.directCommit hT hcard hgst hto hR hN hlead hL))⟩

/-- **Reactive liveness is local too** (V18, reactive): every reliable
validator decides the slot on its own view, by the same explicit time as
the timed discipline, with `SynchronisedOn` needed nowhere. -/
theorem decided_local (hT : T ⊆ (Correct : Finset Validator))
    (hcard : quorumCard Validator ≤ T.card)
    (hgst : rm.gst ≤ R)
    (hto : ∀ n, R ≤ n → 2 * rm.delay + rm.proc ≤ rm.timeout n)
    (hR : R ≤ S.slotRound k) (hN : S.slotRound k + 2 ≤ N)
    (hlead : S.leader k ∈ T) :
    ∃ L, IsLeaderBlock U k L ∧ ∀ v ∈ T,
      Decided U (rm.viewAt v (rm.latest (S.slotRound k + 2) + rm.delay)) k (some L) := by
  obtain ⟨L, hLmem, hLc, hLr⟩ :=
    rm.toPaceCore.populatedOn hcard (S.slotRound k) (by omega) (S.leader k) hlead
  have hL : IsLeaderBlock U k L := ⟨hLmem, hLr, hLc⟩
  have hg : ∀ u ∈ T, rm.gst ≤ rm.built u (S.slotRound k + 2) := by
    intro u hu
    have htop := rm.toPaceCore.reached hcard (S.slotRound k + 2) hN u hu
    have := rm.le_built hu (S.slotRound k + 2) htop
    omega
  exact ⟨L, hL, rm.toPaceCore.decided_local_of_certifiesAt hcard hN hg hL
    (rm.certifies hT hcard hgst hto hR hN hlead hL)⟩

/-! ## Inclusion without coverage: the rotation backbone

Chain quality's per-round backbone (CQ5) needs `SynchronisedOn`, which
the reactive discipline gives up. Inclusion survives anyway: a correct
author's self-parent chain reaches every earlier block of its own
author, so once that author next leads a slot — guaranteed by
`FairToEach` — the whole chain enters the agreed ledger at once. The
reactive system trades inclusion latency, not the guarantee. -/

/-! **RS5 — reactive inclusion** is stated in `Reactive/MysticetiProperties.lean`
as `ReactiveM.committed_of_correct_block`, an instance of the generic
inclusion theorem (`Properties/Arcs/Quality.lean`) at the core's support:
the reactive precondition is certification, and the self-parent chain is
`SelfParent.reaches_of_creator`. -/

end ReactiveM

end LeanDag
