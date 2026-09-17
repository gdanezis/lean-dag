import LeanDag.Steelhead.Model.Reactive
import LeanDag.Steelhead.Helpers.Liveness
import LeanDag.MahiMahi.Helpers.Synchrony
/-!
# Helpers — the pacing disciplines

Generated lemma infrastructure for `Liveness/Statement.lean`'s two pacing claims; not part of the
audit surface. Both routes meet at the certifiers `shSupport_directCommitIn` asks for, and the
rest of the argument is the one SH6a already runs.

The reactive route supplies those certifiers itself. Above the wave of three they come from
reachability alone, since the vote round then sits two rounds or more below them; at the wave of
three they come from `ReactiveS.cert_or_wait`, counted as the core's reactive Mysticeti counts
them. The timed route instead discharges SH6a's `SynchronisedOn` from a `ViewPace` whose timeout
grows at a rate that clears the delay (`synchronisedOn_of_rate`), so it says nothing new about
the rule and everything about where the hypothesis comes from.
-/

namespace LeanDag

namespace Steelhead

variable {Validator : Type} [Fintype Validator] [DecidableEq Validator]
variable [F : Faults Validator]
variable {BlockId : Type} [LinearOrder BlockId] {Payload : Type}
variable [S : Slots Validator]

/-- **Every reliable block at the decision round certifies the candidate**, under the reactive
discipline. At a wave of four or more the votes of the round above the candidate reach the
certifier through the DAG; at the wave of three the certifier references them itself. -/
theorem reactive_certifies {U : BlockUniverse Validator BlockId Payload} {w : ℕ → ℕ}
    {T : Finset Validator} {N R k : ℕ} (rs : ReactiveS U T N w) (hw : ∀ r, 3 ≤ w r)
    (hT : T ⊆ (Correct : Finset Validator)) (hcard : quorumCard Validator ≤ T.card)
    (hgst : rs.gst ≤ R) (hto : ∀ n, R ≤ n → 2 * rs.delay + rs.proc ≤ rs.timeout n)
    (hR : R ≤ S.slotRound k) (hN : S.slotRound k + (w (S.slotRound k) - 1) ≤ N)
    (hlead : S.leader k ∈ T) {L : BlockId} (hL : IsLeaderBlock U k L)
    {v : Validator} (hv : v ∈ T) {c : BlockId} (hc : c ∈ U.ids)
    (hcc : (U.block c).creator = v)
    (hcr : (U.block c).round = S.slotRound k + (w (S.slotRound k) - 1)) :
    MahiMahi.Certifies U c L := by
  have hw3 := hw (S.slotRound k)
  have hLc : (U.block L).creator ∈ T := hL.2.2 ▸ hlead
  have hvotes := rs.toReactivePace.votes hT hcard hgst hto hR (by omega) hlead hL
  have hpop1 : PopulatedOn U T (S.slotRound k + 1) :=
    rs.toPaceCore.populatedOn hcard (S.slotRound k + 1) (by omega)
  rcases Nat.lt_or_ge (w (S.slotRound k)) 4 with hlt | hge
  · -- the wave of three: the certifier references the votes, or waited and holds them all
    have hw3' : w (S.slotRound k) = 3 := by omega
    have hcr2 : (U.block c).round = S.slotRound k + 2 := by rw [hcr, hw3']
    rcases rs.cert_or_wait v hv k hw3' (by omega) hlead L hL c hc hcc hcr2 with hcert | hwait
    · exact hcert
    · obtain ⟨hwaited, hincl⟩ := hwait
      have hD := rs.driftOn_of_catchup hcard hgst
      refine le_trans hcard (Finset.card_le_card ?_)
      intro u hu
      obtain ⟨b, hb, hbc, hbr⟩ := hpop1 u hu
      have hvote : L ∈ (U.block b).refs := hvotes u hu b hb hbc hbr
      have harrive : b ∈ rs.holds v (rs.built v (S.slotRound k + 2)) := by
        have hown := rs.holds_own u hu (S.slotRound k + 1) (by omega) b hb hbc hbr
        have htopu : S.slotRound k + 1 ≤ rs.top u := by
          have := rs.le_top_of_built u hu b hb hbc
          omega
        have hgstu : rs.gst ≤ rs.built u (S.slotRound k + 1) :=
          le_trans (le_trans hgst (by omega)) (rs.le_built hu _ htopu)
        have hconv := rs.converges v hv u hu _ hgstu hown
        refine rs.holds_mono v _ _ ?_ hconv
        have hdrift := hD v hv u hu (S.slotRound k + 1) (by omega) (by omega)
        have := hto (S.slotRound k + 1) (by omega)
        omega
      refine mem_creatorsOf.mpr ⟨b, ?_, hbc⟩
      refine Finset.mem_filter.mpr ⟨hincl b hb (hbc ▸ hu) hbr harrive hvote, ?_⟩
      exact MahiMahi.votes_of_reaches hb hL.1 (hT hLc) (Reaches.single hvote)
  · -- a wave of four or more: the votes reach the certifier through the DAG
    have hreach := MahiMahi.reaches_of_votes hT hcard hpop1 hL.1 hL.2.1 hLc
      fun q hq hqr hqc => hvotes _ hqc q hq rfl hqr
    refine MahiMahi.certifies_of_refs_reach (w := w (S.slotRound k)) (r := S.slotRound k)
      (by omega) hc (by unfold MahiMahi.decisionRoundAt; omega) hL.1 (hT hLc) ?_
    intro q hq
    have hqids := U.complete c hc q hq
    have hqr := U.round_of_mem_refs hc hq
    exact hreach q hqids (by omega)

/-- **SH6j.** A reliably led slot commits by the direct rule under the reactive discipline, in
every view holding its decision round: `shSupport_directCommitIn` at the certifiers above. -/
theorem reactive_commits {U : BlockUniverse Validator BlockId Payload} {w : ℕ → ℕ}
    {T : Finset Validator} {V : View Validator BlockId Payload U} {N R k : ℕ}
    (rs : ReactiveS U T N w) (hw : ∀ r, 3 ≤ w r) (hT : T ⊆ (Correct : Finset Validator))
    (hcard : quorumCard Validator ≤ T.card) (hgst : rs.gst ≤ R)
    (hto : ∀ n, R ≤ n → 2 * rs.delay + rs.proc ≤ rs.timeout n) (hR : R ≤ S.slotRound k)
    (hN : S.slotRound k + (w (S.slotRound k) - 1) ≤ N)
    (hV : V.CoversUpto (S.slotRound k + (w (S.slotRound k) - 1))) (hlead : S.leader k ∈ T) :
    ∃ L, IsLeaderBlock U k L ∧ Decided w U V k (some L) := by
  obtain ⟨L, hL, hin⟩ :=
    SteelheadProperties.shSupport_directCommitIn (fun r => by have := hw r; omega) S V hcard
      (fun n _ hn2 => rs.toPaceCore.populatedOn hcard n (by omega))
      (fun L' hL' v hv c hc hcc hcr =>
        reactive_certifies rs hw hT hcard hgst hto hR hN hlead hL' hv hc hcc hcr)
      hV hlead
  exact ⟨L, hL, Decided.directCommit hL hin⟩

/-- **SH6k.** The timed route: a `ViewPace` whose timeout clears the delay at a rate synchronises
the reliable set from `max (2Δ + proc, gst)` (`synchronisedOn_of_rate`), and SH6a takes it from
there. The claim is only as strong as `ViewPace` is inhabited, which is a question about the core
structure and not about this arc. -/
theorem timed_commits {U : BlockUniverse Validator BlockId Payload} {w : ℕ → ℕ}
    {T : Finset Validator} {V : View Validator BlockId Payload U} {N N' k : ℕ}
    (vp : ViewPace U T N) (hw : ∀ r, 3 ≤ w r) (hT : T ⊆ (Correct : Finset Validator))
    (hcard : quorumCard Validator ≤ T.card) (hrate : Rated vp.timeout)
    (hR : max (2 * vp.delay + vp.proc) vp.gst ≤ S.slotRound k)
    (hpop : ∀ r, max (2 * vp.delay + vp.proc) vp.gst ≤ r → r ≤ N' → PopulatedOn U T r)
    (hN : ∀ j, j ≤ k → (steelheadAnchored Validator BlockId Payload w).decisionRound j ≤ N')
    (hV : V.CoversUpto N') (hlead : S.leader k ∈ T) :
    ∃ L, IsLeaderBlock U k L ∧ Decided w U V k (some L) := by
  obtain ⟨L, hL, -, hdec⟩ := commitsOfSynchrony hw hT hcard
    (vp.synchronisedOn_of_rate hcard hrate) hpop hR hN hV hlead
  exact ⟨L, hL, hdec⟩

end Steelhead

end LeanDag
