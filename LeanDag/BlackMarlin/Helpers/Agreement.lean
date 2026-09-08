import LeanDag.BlackMarlin.Helpers.Reactive
/-!
# Black Marlin — the agreement layer

Generated proof layer; not part of the audit surface. The local commit —
the run-of-two argument run inside a validator's own view rather than
inside the universe — and the agreement statement it yields with the
prefix result.
-/

namespace LeanDag

namespace BlackMarlin

variable {Validator : Type} [Fintype Validator] [DecidableEq Validator]
variable [F : Faults Validator] [Rot : Rotation Validator]
variable {BlockId : Type} [DecidableEq BlockId] {Payload : Type}
variable {U : BlockUniverse Validator BlockId Payload}
variable {T : Finset Validator} {N R r : ℕ}

namespace Pace

variable (pc : Pace U T N)

/-- Every build at a round past GST lies past GST: rounds advance real
time, so the round number itself bounds the build time from below. No
hypothesis beyond `gst ≤ R ≤ n` is needed. -/
theorem gst_le_built (hcard : quorumCard Validator ≤ T.card)
    (hgst : pc.gst ≤ R) {n : ℕ} (hRn : R ≤ n) (hn : n ≤ N) :
    ∀ u ∈ T, pc.gst ≤ pc.built u n := by
  intro u hu
  have := pc.le_built hu n (pc.reached hcard n hn u hu)
  omega

/-- **The two rounds the rule reads, in hand.** Past GST every reliable
validator holds every reliable block of rounds `r + 1` and `r + 2` by a
common time — the later of the two rounds' `latest`, plus one delivery. -/
theorem holds_two_rounds (hcard : quorumCard Validator ≤ T.card)
    (hgst : pc.gst ≤ R) (hR : R ≤ r) (hN : r + 2 ≤ N) :
    ∀ v ∈ T, ∀ n, r + 1 ≤ n → n ≤ r + 2 → ∀ b ∈ U.ids, (U.block b).creator ∈ T →
      (U.block b).round = n →
      b ∈ pc.holds v (max (pc.latest (r + 1)) (pc.latest (r + 2)) + pc.delay) := by
  intro v hv n h1 h2 b hb hbT hbr
  have hg := pc.gst_le_built hcard hgst (n := n) (by omega) (by omega)
  have hheld := pc.toPaceCore.holds_roundBlocks (n := n) (by omega) hg v hv b hb hbT hbr
  refine pc.holds_mono v _ _ ?_ hheld
  have hle : pc.latest n ≤ max (pc.latest (r + 1)) (pc.latest (r + 2)) := by
    rcases (show n = r + 1 ∨ n = r + 2 by omega) with rfl | rfl
    · exact le_max_left _ _
    · exact le_max_right _ _
  omega

/-- **The commit, on every reliable validator's own view.** A run of two
reliable anchors past GST is committed by each of them separately, at
the explicit time the two rounds' blocks have converged — the local
counterpart of `reactive_committed`, which states the same verdict over
the universe. -/
theorem committedIn_local (hT : T ⊆ (Correct : Finset Validator))
    (hcard : quorumCard Validator ≤ T.card) (hgst : pc.gst ≤ R)
    (hto : ∀ n, R ≤ n → 2 * pc.delay + pc.proc ≤ pc.timeout n)
    (hR : R ≤ r) (hN : r + 2 ≤ N)
    (hlead : Rot.anchor r ∈ T) (hlead1 : Rot.anchor (r + 1) ∈ T) :
    ∃ L, IsAnchor U r L ∧ Committed U L r ∧
      ∀ v ∈ T, CommittedIn U
        (pc.toPaceCore.viewAt v (max (pc.latest (r + 1)) (pc.latest (r + 2)) + pc.delay))
        L r := by
  set t := max (pc.latest (r + 1)) (pc.latest (r + 2)) + pc.delay with ht
  have hpop := pc.populatedOn hcard
  have hheld := pc.holds_two_rounds hcard hgst hR hN
  obtain ⟨L, hL, hLc, hLr⟩ := hpop r (by omega) (Rot.anchor r) hlead
  obtain ⟨L', hL', hL'c, hL'r⟩ := hpop (r + 1) (by omega) (Rot.anchor (r + 1)) hlead1
  have haL : IsAnchor U r L := ⟨hL, hLr, hLc⟩
  have haL' : IsAnchor U (r + 1) L' := ⟨hL', hL'r, hL'c⟩
  have hvL := pc.votes hT hcard hgst hto hR (by omega) hlead haL
  have hvL' := pc.votes hT hcard hgst hto (show R ≤ r + 1 by omega) (by omega) hlead1 haL'
  have hlink : L ∈ (U.block L').refs := hvL (Rot.anchor (r + 1)) hlead1 L' hL' hL'c hL'r
  -- the universe-level verdict, from the same two vote facts
  have hcomm : Committed U L r :=
    ⟨haL, supported_of_votesAt hcard (hpop (r + 1) (by omega)) hvL,
      ⟨L', mem_linkers.mpr ⟨haL', hlink,
        supported_of_votesAt hcard (hpop (r + 2) (by omega)) hvL'⟩⟩⟩
  refine ⟨L, haL, hcomm, fun v hv => ?_⟩
  -- support for `L`, counted inside `v`'s view
  have hsupp : ∀ (A : BlockId) (n : ℕ), r ≤ n → n < r + 2 → IsAnchor U n A →
      VotesAt U T n A → SupportedIn U (pc.toPaceCore.viewAt v t) A n := by
    intro A n hn1 hn2 hA hvA
    refine le_trans hcard (Finset.card_le_card ?_)
    intro u hu
    obtain ⟨c, hc, hcc, hcr⟩ := hpop (n + 1) (by omega) u hu
    refine mem_creatorsOf.mpr ⟨c, Finset.mem_inter.mpr ⟨?_, ?_⟩, hcc⟩
    · exact Finset.mem_filter.mpr ⟨mem_blocksAt.mpr ⟨hc, hcr⟩,
        hvA u hu c hc hcc hcr⟩
    · exact pc.mem_viewAt (hheld v hv (n + 1) (by omega) (by omega) c hc (hcc ▸ hu) hcr)
  refine ⟨haL, hsupp L r (by omega) (by omega) haL hvL, ⟨L', ?_⟩⟩
  refine Finset.mem_inter.mpr ⟨Finset.mem_filter.mpr ⟨mem_blocksAt.mpr ⟨hL', hL'r⟩,
    hL'c, hlink, hsupp L' (r + 1) (by omega) (by omega) haL' hvL'⟩, ?_⟩
  exact pc.mem_viewAt (hheld v hv (r + 1) (by omega) (by omega) L' hL' (hL'c ▸ hlead1) hL'r)

/-- **Agreement.** What one validator delivered with an anchor committed
at round `ρ`, every reliable validator delivers with the anchor they each
commit at any reliably anchored round `r ≥ ρ`: the prefix result composed
with the local commit above. -/
theorem agreement (hT : T ⊆ (Correct : Finset Validator))
    (hcard : quorumCard Validator ≤ T.card) (hgst : pc.gst ≤ R)
    (hto : ∀ n, R ≤ n → 2 * pc.delay + pc.proc ≤ pc.timeout n)
    (hR : R ≤ r) (hN : r + 2 ≤ N)
    (hlead : Rot.anchor r ∈ T) (hlead1 : Rot.anchor (r + 1) ∈ T)
    {V : View Validator BlockId Payload U} {A B : BlockId} {ρ : ℕ} (hρ : ρ ≤ r)
    (hA : CommittedIn U V A ρ) (hB : B ∈ history U A) :
    ∃ L, IsAnchor U r L ∧ B ∈ history U L ∧
      ∀ v ∈ T, CommittedIn U
        (pc.toPaceCore.viewAt v (max (pc.latest (r + 1)) (pc.latest (r + 2)) + pc.delay))
        L r := by
  obtain ⟨L, haL, hcomm, hloc⟩ :=
    pc.committedIn_local hT hcard hgst hto hR hN hlead hlead1
  exact ⟨L, haL,
    history_subset_of_committed (committed_of_committedIn hA) hcomm hρ hB, hloc⟩

end Pace

end BlackMarlin

end LeanDag
