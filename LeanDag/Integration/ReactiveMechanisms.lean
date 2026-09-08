import LeanDag.Properties.Arcs.GC
import LeanDag.Properties.Arcs.SafeSkip
import LeanDag.Integration.ReGenesis
import LeanDag.Reactive.MysticetiProperties
import LeanDag.Properties.Arcs.Liveness
import LeanDag.Mysticeti.Record
/-!
# The mechanisms over a reactive execution

A reactive execution has production but not coverage — a reactive
builder omits whatever had not arrived when its exit condition fired,
so `SynchronisedOn` is false in one by design (`Reactive/Basic.lean`).
Reactive Mysticeti's precondition is therefore guarded by a witness
rather than `Timed.OfCoverage`, but its commits still survive a
mechanism: the mechanism reads `CertifiesAt`, made of references, which
`Sustains` preserves regardless of coverage, and the reactive discipline
delivers `CertifiesAt` directly (`ReactiveM.certifies`). Three cells
follow, one per DAG-transforming mechanism, each the same two theorems
composed at a different `Sustains` witness.
-/

namespace LeanDag

namespace Integration

open LeanDag.MysticetiProperties
open LeanDag.Properties LeanDag.Properties.Arcs

variable {Validator : Type} [Fintype Validator] [DecidableEq Validator]
variable [F : Faults Validator]
variable {BlockId : Type} [DecidableEq BlockId] {Payload : Type}
variable [S : Slots Validator]
variable {U : BlockUniverse Validator BlockId Payload}
variable {T : Finset Validator} {N R k : ℕ} {L : BlockId}

/-! ## The precondition, across the three mechanisms: with
`Support.live_of_sustains` and `Support.live_of_truncates` the whole
window carries, and everything downstream applies in the transformed
universe with no further argument. -/

variable {V : View Validator BlockId Payload U} {lo K : ℕ}

/-- **The reactive precondition survives the cut**, as the support's,
at the re-indexed schedule. -/
theorem live_chop_reactive {G d : ℕ} (hd : G ≤ S.slotRound d)
    (h : MysticetiProperties.reactiveLive S (U := U) V T lo K) (hlo : d ≤ lo) (hK : lo < K) :
    MysticetiProperties.coreSupport.live (coreReliability Validator) (S.chop G d hd)
      (U := chop U G) (V.chop G) T (lo - d) (K - d) :=
  MysticetiProperties.coreSupport.live_of_truncates MysticetiProperties.coreSupport_local
    (MysticetiProperties.truncates_chop hd) (MysticetiProperties.coreSupport_live_of_reactiveLive h) hlo hK
    (fun _ hGN hc => coversUpto_of_truncates (MysticetiProperties.truncates_chop hd) MysticetiProperties.viewAgreeAbove_chop hGN hc)

/-- **And the fill**, on any view of it caught up as far as the old one. -/
theorem live_skipFill_reactive (sk : SkipMsg U) {V' : View Validator BlockId Payload sk.skipFill}
    (h : MysticetiProperties.reactiveLive S (U := U) V T lo K) (hr : sk.r + 1 ≤ S.slotRound lo)
    (hV' : ∀ N, V.CoversUpto N → V'.CoversUpto N) :
    MysticetiProperties.coreSupport.live (coreReliability Validator) S
      (U := sk.skipFill) V' T lo K :=
  MysticetiProperties.coreSupport.live_of_sustains MysticetiProperties.coreSupport_local
    (sustains_skipFill sk) (MysticetiProperties.coreSupport_live_of_reactiveLive h) hr hV'

/-- **And re-genesis.** -/
theorem live_addGenesis_reactive {v : Validator} {g : BlockId} {p : Payload}
    {hg : g ∉ U.ids} {hsev : ∀ b ∈ U.ids, (U.block b).creator ≠ v}
    {V' : View Validator BlockId Payload (addGenesis U v g p hg hsev)}
    (h : MysticetiProperties.reactiveLive S (U := U) V T lo K) (hone : 1 ≤ S.slotRound lo)
    (hV' : ∀ N, V.CoversUpto N → V'.CoversUpto N) :
    MysticetiProperties.coreSupport.live (coreReliability Validator) S
      (U := addGenesis U v g p hg hsev) V' T lo K :=
  MysticetiProperties.coreSupport.live_of_sustains MysticetiProperties.coreSupport_local
    sustains_addGenesis (MysticetiProperties.coreSupport_live_of_reactiveLive h) hone hV'

/-- **Anchored liveness after the cut, for a reactive execution**: a run
of `c` reliably-led slots in the truncation decides everything below it
there. -/
theorem decidedBelow_of_run_chop_reactive {G d c b : ℕ} (hd : G ≤ S.slotRound d) (hc : 0 < c)
    (hspans : (coreAnchored Validator BlockId Payload).SpansEligible (S := S.chop G d hd) c)
    (h : MysticetiProperties.reactiveLive S (U := U) V T (d + b) (d + b + c))
    (hlead : ∀ i, i < c → (S.chop G d hd).leader (b + i) ∈ T) :
    ∀ i, i < b → ∃ w, DecidedBelow (MysticetiProperties.mysticetiRule (Payload := Payload))
      (S.chop G d hd) (b + c) (V.chop G) i w :=
  MysticetiProperties.coreSupport.decidedBelow_of_run_truncates
    MysticetiProperties.coreSupport_local MysticetiProperties.coreSupport_commits hc
    (MysticetiProperties.descends hc hspans) (MysticetiProperties.truncates_chop hd) (V.chop G)
    (MysticetiProperties.coreSupport_live_of_reactiveLive h)
    (fun _ hGN hcov => coversUpto_of_truncates (MysticetiProperties.truncates_chop hd) MysticetiProperties.viewAgreeAbove_chop hGN hcov) hlead

end Integration

end LeanDag
