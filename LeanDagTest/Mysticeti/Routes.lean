import LeanDagTest.Quality.Model
import LeanDag

/-!
# Route compatibility: does every feature arc run off `ViewPace`?

An audit, machine-checked. Report §6.9 gives four routes to the two
conditions liveness consumes, and the report's main line is now the last of
them — `ViewPace`, where production is derived from genesis and the
pacemaker's progress rule rather than assumed as data. The question this
file settles is whether the feature arcs — Odontoceti, Hybrid, chain
quality, adaptive, DoS, GC — can be fed from that line, or whether each is
tied to a route of its own.

The answer is that they can, **at `T := Correct`**, and the reason they are
not tied is `CommitsAt`-style statement: each capstone takes production and
coverage as hypotheses rather than a structure, so any route supplying the
pair discharges it. Each `example` below is one such discharge.

One qualification, recorded rather than fixed here.

*The generality does not transfer.* The Mysticeti core asks production over
`T` and from the synchrony round on; every feature arc still asks it over
all of `Correct` and at *every* round below the horizon. `ViewPace` supplies
that at `T := Correct` — `populatedOn` runs from round `0` — so the arcs are
compatible, but they do not inherit the relativisation of report §6.9. A
feature capstone therefore cannot be run at a `T` that is a proper subset of
`Correct`, though the Mysticeti one can.
-/

namespace LeanDagTest.Routes

open LeanDag

variable {Validator : Type} [Fintype Validator] [DecidableEq Validator]
variable {BlockId : Type} [DecidableEq BlockId] {Payload : Type}
variable [S : Slots Validator]

section Mysticeti

variable [F : Faults Validator]

/-! ## The bridge

A `ViewPace` over `Correct` supplies both interface conditions, in the shape
the feature capstones ask for: production at *every* round below the
horizon, and coverage from the synchrony round on. -/

/-- Production in the feature arcs' shape: `Populated`, at every round. -/
theorem populated_of_viewPace {U : BlockUniverse Validator BlockId Payload} {N : ℕ}
    (vp : ViewPace U (Correct : Finset Validator) N) :
    ∀ r ≤ N, Populated U r :=
  vp.populatedOn card_correct

/-- Coverage in the feature arcs' shape: `Synchronised`, from `R` on —
the drift-free headline, with the quorum bound supplied by
`card_correct`. -/
theorem synchronised_of_viewPace {U : BlockUniverse Validator BlockId Payload} {N R : ℕ}
    (vp : ViewPace U (Correct : Finset Validator) N) (hgst : vp.gst ≤ R)
    (hbackoff : ∀ n, R ≤ n → 2 * vp.delay + vp.proc ≤ vp.timeout n) :
    Synchronised U R :=
  vp.synchronisedOn_of_converges card_correct hgst hbackoff

/-! ## The arcs, discharged

Each example takes a `ViewPace` and the two network-side side conditions
— GST and the backoff over `2Δ + proc` — and produces the arc's
conclusion. Nothing
else is supplied, which is the point: no `Live`, no `Delivery`, no
`DeliversQuorum`, no `Timing`, and no production assumption beyond what the
`ViewPace` derives. -/

section Arcs

variable {U : BlockUniverse Validator BlockId Payload} {N R : ℕ}

/-- **Mysticeti L10**, from a `ViewPace`. -/
example {c : ℕ} (hc : 0 < c) (hspan : (coreAnchored Validator BlockId Payload).SpansEligible c)
    (fair : FairRunOn (Correct : Finset Validator) c) (k : ℕ)
    (vp : ViewPace U (Correct : Finset Validator) N)
    (hgst : vp.gst ≤ R)
    (hbackoff : ∀ n, R ≤ n → 2 * vp.delay + vp.proc ≤ vp.timeout n) :
    ∃ b, k ≤ b ∧ R ≤ S.slotRound b ∧
      (S.slotRound (b + c - 1) + 2 ≤ N →
        ∀ i, i < b → ∃ v, Decided U (View.full U) i v) := by
  obtain ⟨b, hk, hR, hrest⟩ :=
    all_decided_below_of_fairRun (BlockId := BlockId) (Payload := Payload)
      hc Finset.Subset.rfl card_correct hspan fair R k
  exact ⟨b, hk, hR, fun hN =>
    hrest U N (fun r _ hr => populated_of_viewPace vp r hr)
      (synchronised_of_viewPace vp hgst hbackoff) hN⟩

/-- **Chain quality CQ6**, from the same `ViewPace`: every round-`m` block
by a correct validator enters the ledger of a slot that validator leads,
fixed in advance by the schedule. The pace supplies the timed
precondition, `certLive_of_coreLive` turns it into certification, and
the inclusion theorem never sees the synchrony. -/
example (m : ℕ) (hRm : R ≤ m)
    (fair : FairToEach (Correct : Finset Validator)) {v : Validator}
    (hv : v ∈ (Correct : Finset Validator))
    (vp : ViewPace U (Correct : Finset Validator) N)
    (hgst : vp.gst ≤ R)
    (hbackoff : ∀ n, R ≤ n → 2 * vp.delay + vp.proc ≤ vp.timeout n) :
    ∃ k', m ≤ S.slotRound k' ∧ S.leader k' = v ∧
      (S.slotRound k' + 2 ≤ N →
        ∃ L, Decided U (View.full U) k' (some L) ∧
          ∀ b ∈ U.ids, (U.block b).creator = v →
            (U.block b).round = m → b ∈ history U L ∧
            ∀ (g : ℕ → Option BlockId) (n : ℕ), g k' = some L → k' < n →
              b ∈ ledgerSet U g n) := by
  obtain ⟨k', hm, hlead, hinc⟩ :=
    committed_of_correct_block_correct (BlockId := BlockId) (Payload := Payload) fair m hv
  refine ⟨k', hm, hlead, fun hN => ?_⟩
  obtain ⟨L, hdec, hb⟩ := hinc U (View.full U)
    (MysticetiProperties.certLive_of_coreLive
      ⟨card_correct, R, N, synchronised_of_viewPace vp hgst hbackoff, le_trans hRm hm,
        fun r _ hr => populated_of_viewPace vp r hr, View.coversUpto_full U N,
        fun k hk => by have := S.mono (Nat.lt_succ_iff.mp hk); omega⟩)
  exact ⟨L, hdec, fun b hb' hbc hbr => hb b hb' (by rw [hlead]; exact hbc) hbr⟩

end Arcs

end Mysticeti

/-! ## Odontoceti

Its own fault model — `Faults5`, `n ≥ 5f+1` — so it needs a section of its
own, two `Faults` instances in one scope being ambiguous. Nothing else
changes: the decision rule differs (two rounds rather than three,
`ThickLink` rather than a certificate) and none of that reaches the
interface, so the same `ViewPace` discharges it. -/

section Odontoceti

variable [F5 : Faults5 Validator] [LinearOrder BlockId]
variable {U : BlockUniverse Validator BlockId Payload} {N R : ℕ}

/-- **Odontoceti O10**, from a `ViewPace`. -/
example {c : ℕ} (hc : 0 < c)
    (hspan : (Odontoceti.odontocetiAnchored Validator BlockId Payload).SpansEligible c)
    (fair : FairRunOn (Correct : Finset Validator) c) (k : ℕ)
    (vp : ViewPace U (Correct : Finset Validator) N)
    (hgst : vp.gst ≤ R)
    (hbackoff : ∀ n, R ≤ n → 2 * vp.delay + vp.proc ≤ vp.timeout n) :
    ∃ b, k ≤ b ∧ R ≤ S.slotRound b ∧
      (S.slotRound (b + c - 1) + 1 ≤ N →
        ∀ i, i < b → ∃ v, Odontoceti.Decided U (View.full U) i v) := by
  obtain ⟨b, hk, hR, hrest⟩ :=
    Odontoceti.all_decided_below_of_fairRun (BlockId := BlockId) (Payload := Payload)
      hc Finset.Subset.rfl card_correct hspan fair R k
  exact ⟨b, hk, hR, fun hN =>
    hrest U N (View.full U) (fun r _ hr => vp.populatedOn card_correct r hr)
      (vp.synchronisedOn_of_converges card_correct hgst hbackoff) hN
      (View.coversUpto_full U N)⟩

end Odontoceti

end LeanDagTest.Routes
