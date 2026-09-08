import LeanDag.BlackMarlin.Model.Round
import LeanDag.BlackMarlin.Helpers.Liveness
/-!
# Black Marlin — the reactive layer

Generated proof layer; not part of the audit surface. The lemmas behind
`Reactive/Statement.lean`: the fallback route, which yields the votes the
commit rule counts, and the exit route, which bounds latency in the
actual delivery time with the timeout appearing nowhere.
-/

namespace LeanDag

namespace BlackMarlin

variable {Validator : Type} [Fintype Validator] [DecidableEq Validator]
variable [F : Faults Validator] [Rot : Rotation Validator]
variable {BlockId : Type} [DecidableEq BlockId] {Payload : Type}
variable {U : BlockUniverse Validator BlockId Payload}
variable {T : Finset Validator} {D N R r : ℕ} {A : BlockId}

namespace Pace

variable (pc : Pace U T N)

/-- Rounds advance real time, over the rounds a validator reached. -/
theorem le_built {v : Validator} (hv : v ∈ T) : ∀ n ≤ pc.top v, n ≤ pc.built v n := by
  intro n
  induction n with
  | zero => intro _; omega
  | succ n ih =>
      intro hn
      have := pc.built_lt v hv n (by omega)
      have := ih (by omega)
      omega

/-- Drift collapses here as it does under the timed discipline, from the
trunk's catch-up rule with `le_built` supplied by `built_lt`. -/
theorem driftOn_of_catchup (hcard : quorumCard Validator ≤ T.card)
    (hgst : pc.gst ≤ R) :
    DriftOn pc.built T R (pc.delay + pc.proc) N :=
  pc.toPaceCore.driftOn_of_catchup hcard hgst (fun u hu => pc.le_built hu)

/-- A reliable anchor reached its round: its block is in the universe,
and `le_top_of_built` reads the reach off it. -/
theorem anchor_le_top (hlead : Rot.anchor r ∈ T) (hA : IsAnchor U r A) :
    r ≤ pc.top (Rot.anchor r) := by
  have h1 := pc.le_top_of_built (Rot.anchor r) hlead A hA.1 hA.2.2
  have h2 := hA.2.1
  omega

/-! ## The fallback route -/

/-- **Every reliable block at the round above a reliable anchor
references it.** Past GST, with the timeout clearing `2Δ + proc`,
whether by the exit — which required holding the anchor — or the
fallback, whose convergence and drift bounds place the anchor's arrival
before the waiter's build. -/
theorem votes (hT : T ⊆ (Correct : Finset Validator))
    (hcard : quorumCard Validator ≤ T.card) (hgst : pc.gst ≤ R)
    (hto : ∀ n, R ≤ n → 2 * pc.delay + pc.proc ≤ pc.timeout n)
    (hR : R ≤ r) (hN : r + 1 ≤ N)
    (hlead : Rot.anchor r ∈ T) (hA : IsAnchor U r A) :
    VotesAt U T r A := by
  have hD := pc.driftOn_of_catchup hcard hgst
  intro v hv c hc hcc hcr
  rcases pc.anchor_or_wait v hv r hN hlead A hA c hc hcc hcr with hvote | ⟨hwait, hheld⟩
  · exact hvote
  · refine hheld ?_
    have hown := pc.holds_own _ hlead r (by omega) A hA.1 hA.2.2 hA.2.1
    have hgstA : pc.gst ≤ pc.built (Rot.anchor r) r :=
      le_trans (le_trans hgst hR) (pc.le_built hlead _ (pc.anchor_le_top hlead hA))
    have hconv := pc.converges v hv _ hlead _ hgstA hown
    refine pc.holds_mono v _ _ ?_ hconv
    have hdrift := hD v hv _ hlead r hR (by omega)
    have := hto r hR
    omega

/-- **Reactive liveness.** A run of two reliable anchors past GST is
committed, with no coverage hypothesis: the reactive discipline supplies
exactly the references the commit rule counts, and production comes off
the trunk. -/
theorem reactive_committed (hT : T ⊆ (Correct : Finset Validator))
    (hcard : quorumCard Validator ≤ T.card) (hgst : pc.gst ≤ R)
    (hto : ∀ n, R ≤ n → 2 * pc.delay + pc.proc ≤ pc.timeout n)
    (hR : R ≤ r) (hN : r + 2 ≤ N)
    (hlead : Rot.anchor r ∈ T) (hlead1 : Rot.anchor (r + 1) ∈ T) :
    ∃ L, IsAnchor U r L ∧ Committed U L r := by
  have hpop := pc.populatedOn hcard
  obtain ⟨L, hL, hLc, hLr⟩ := hpop r (by omega) (Rot.anchor r) hlead
  obtain ⟨L', hL', hL'c, hL'r⟩ := hpop (r + 1) (by omega) (Rot.anchor (r + 1)) hlead1
  have haL : IsAnchor U r L := ⟨hL, hLr, hLc⟩
  have haL' : IsAnchor U (r + 1) L' := ⟨hL', hL'r, hL'c⟩
  have hvL := pc.votes hT hcard hgst hto hR (by omega) hlead haL
  have hvL' := pc.votes hT hcard hgst hto (by omega) (by omega) hlead1 haL'
  refine ⟨L, haL, haL, ?_, ⟨L', mem_linkers.mpr ⟨haL', ?_, ?_⟩⟩⟩
  · exact supported_of_votesAt hcard (hpop (r + 1) (by omega)) hvL
  · exact hvL (Rot.anchor (r + 1)) hlead1 L' hL' hL'c hL'r
  · exact supported_of_votesAt hcard (hpop (r + 2) (by omega)) hvL'

/-! ## The exit route -/

/-- Holdings only grow, so the view they generate does. -/
theorem viewAt_ids_mono {v : Validator} {s t : ℕ} (hst : s ≤ t) :
    (pc.toPaceCore.viewAt v s).ids ⊆ (pc.toPaceCore.viewAt v t).ids := by
  intro i hi
  obtain ⟨a, ha, hia⟩ := Finset.mem_biUnion.mp hi
  exact Finset.mem_biUnion.mpr ⟨a, pc.holds_mono v _ _ hst ha, hia⟩

/-- **A supported anchor stays supported.** What the round rule checked
once it never has to check again, which is what makes the exit
incremental. -/
theorem suppAnchorIn_mono {v : Validator} {s t : ℕ} (hst : s ≤ t) {ρ : ℕ}
    (h : SuppAnchorIn U (pc.toPaceCore.viewAt v s) ρ) :
    SuppAnchorIn U (pc.toPaceCore.viewAt v t) ρ := by
  obtain ⟨A, hA, hsupp⟩ := h
  refine ⟨A, hA, le_trans hsupp (Finset.card_le_card ?_)⟩
  exact Finset.image_subset_image
    (Finset.inter_subset_inter (Finset.Subset.refl _) (pc.viewAt_ids_mono hst))

/-- **The exit fires.** A validator holding every reliable block of the
two rounds below `r + 2` can conclude round `r + 2`, given reliable
anchors at rounds `r`, `r + 1` and `r + 2` — three, where the commit
rule asks for two. -/
theorem concludesAt_of_holds {v : Validator} {t : ℕ}
    (hcard : quorumCard Validator ≤ T.card) (hv : v ∈ T) (hN : r + 2 ≤ N)
    (hheld : ∀ n, r + 1 ≤ n → n ≤ r + 2 → ∀ b ∈ U.ids, (U.block b).creator ∈ T →
      (U.block b).round = n → b ∈ pc.holds v t)
    (ha0 : Rot.anchor r ∈ T) (ha1 : Rot.anchor (r + 1) ∈ T)
    (ha2 : Rot.anchor (r + 2) ∈ T)
    (hvotes : ∀ n, r ≤ n → n < r + 2 → ∀ A, IsAnchor U n A → VotesAt U T n A) :
    ConcludesAt U (pc.toPaceCore.viewAt v t) (r + 2) := by
  have hpop := pc.populatedOn hcard
  have hview : ∀ n, r + 1 ≤ n → n ≤ r + 2 → ∀ b ∈ U.ids, (U.block b).creator ∈ T →
      (U.block b).round = n → b ∈ (pc.toPaceCore.viewAt v t).ids :=
    fun n h1 h2 b hb hbT hbr => pc.mem_viewAt (hheld n h1 h2 b hb hbT hbr)
  refine ⟨?_, ?_, ?_, ?_⟩
  · refine le_trans hcard (Finset.card_le_card ?_)
    intro u hu
    obtain ⟨b, hb, hbc, hbr⟩ := hpop (r + 2) hN u hu
    exact mem_authorsIn.mpr
      ⟨b, hview (r + 2) (by omega) (by omega) b hb (hbc ▸ hu) hbr, hbr, hbc⟩
  · obtain ⟨A, hA, hAc, hAr⟩ := hpop (r + 2) hN _ ha2
    exact ⟨A, hview (r + 2) (by omega) (by omega) A hA (hAc ▸ ha2) hAr, hA, hAr, hAc⟩
  · intro ρ hρ
    have hρ' : ρ = r + 1 := by omega
    rw [hρ']
    obtain ⟨A, hA, hAc, hAr⟩ := hpop (r + 1) (by omega) _ ha1
    refine ⟨A, ⟨hA, hAr, hAc⟩, le_trans hcard (Finset.card_le_card ?_)⟩
    intro u hu
    obtain ⟨c, hc, hcc, hcr⟩ := hpop (r + 2) (by omega) u hu
    refine mem_creatorsOf.mpr ⟨c, Finset.mem_inter.mpr ⟨?_, ?_⟩, hcc⟩
    · exact Finset.mem_filter.mpr ⟨mem_blocksAt.mpr ⟨hc, hcr⟩,
        hvotes (r + 1) (by omega) (by omega) A ⟨hA, hAr, hAc⟩ u hu c hc hcc hcr⟩
    · exact hview (r + 2) (by omega) (by omega) c hc (hcc ▸ hu) hcr
  · intro ρ hρ
    have hρ' : ρ = r := by omega
    rw [hρ']
    obtain ⟨A, hA, hAc, hAr⟩ := hpop r (by omega) _ ha0
    refine ⟨A, ⟨hA, hAr, hAc⟩, le_trans hcard (Finset.card_le_card ?_)⟩
    intro u hu
    obtain ⟨c, hc, hcc, hcr⟩ := hpop (r + 1) (by omega) u hu
    refine mem_creatorsOf.mpr ⟨c, Finset.mem_inter.mpr ⟨?_, ?_⟩, hcc⟩
    · exact Finset.mem_filter.mpr ⟨mem_blocksAt.mpr ⟨hc, hcr⟩,
        hvotes r (by omega) (by omega) A ⟨hA, hAr, hAc⟩ u hu c hc hcc hcr⟩
    · exact hview (r + 1) (by omega) (by omega) c hc (hcc ▸ hu) hcr

/-- **The exit, sustained.** A validator that already saw the round-`r`
anchor supported needs neither that anchor reliable nor the votes at
round `r`: the check it passed to conclude the previous round carries
forward. Entering the fast path costs a run of three reliable anchors;
staying on it costs one more per round. -/
theorem concludesAt_of_sustained {v : Validator} {t₀ t : ℕ}
    (hcard : quorumCard Validator ≤ T.card) (hv : v ∈ T) (hN : r + 2 ≤ N)
    (hheld : ∀ n, r + 1 ≤ n → n ≤ r + 2 → ∀ b ∈ U.ids, (U.block b).creator ∈ T →
      (U.block b).round = n → b ∈ pc.holds v t)
    (hprev : SuppAnchorIn U (pc.toPaceCore.viewAt v t₀) r) (ht : t₀ ≤ t)
    (ha1 : Rot.anchor (r + 1) ∈ T) (ha2 : Rot.anchor (r + 2) ∈ T)
    (hvotes : ∀ A, IsAnchor U (r + 1) A → VotesAt U T (r + 1) A) :
    ConcludesAt U (pc.toPaceCore.viewAt v t) (r + 2) := by
  have hpop := pc.populatedOn hcard
  have hview : ∀ n, r + 1 ≤ n → n ≤ r + 2 → ∀ b ∈ U.ids, (U.block b).creator ∈ T →
      (U.block b).round = n → b ∈ (pc.toPaceCore.viewAt v t).ids :=
    fun n h1 h2 b hb hbT hbr => pc.mem_viewAt (hheld n h1 h2 b hb hbT hbr)
  refine ⟨?_, ?_, ?_, ?_⟩
  · refine le_trans hcard (Finset.card_le_card ?_)
    intro u hu
    obtain ⟨b, hb, hbc, hbr⟩ := hpop (r + 2) hN u hu
    exact mem_authorsIn.mpr
      ⟨b, hview (r + 2) (by omega) (by omega) b hb (hbc ▸ hu) hbr, hbr, hbc⟩
  · obtain ⟨A, hA, hAc, hAr⟩ := hpop (r + 2) hN _ ha2
    exact ⟨A, hview (r + 2) (by omega) (by omega) A hA (hAc ▸ ha2) hAr, hA, hAr, hAc⟩
  · intro ρ hρ
    have hρ' : ρ = r + 1 := by omega
    rw [hρ']
    obtain ⟨A, hA, hAc, hAr⟩ := hpop (r + 1) (by omega) _ ha1
    refine ⟨A, ⟨hA, hAr, hAc⟩, le_trans hcard (Finset.card_le_card ?_)⟩
    intro u hu
    obtain ⟨c, hc, hcc, hcr⟩ := hpop (r + 2) (by omega) u hu
    refine mem_creatorsOf.mpr ⟨c, Finset.mem_inter.mpr ⟨?_, ?_⟩, hcc⟩
    · exact Finset.mem_filter.mpr ⟨mem_blocksAt.mpr ⟨hc, hcr⟩,
        hvotes A ⟨hA, hAr, hAc⟩ u hu c hc hcc hcr⟩
    · exact hview (r + 2) (by omega) (by omega) c hc (hcc ▸ hu) hcr
  · intro ρ hρ
    have hρ' : ρ = r := by omega
    rw [hρ']
    exact pc.suppAnchorIn_mono ht hprev

/-! ## Latency

`δ` is the *actual* per-block propagation bound of the execution — a
premise about this run, not an assumption about the network in general —
and the bounds degrade continuously as it approaches the timeout. -/

/-- **Latency tracks delivery.** When every reliable block of the two
rounds below reaches every reliable validator within `δ` of its build,
the next round is entered within `D + δ + proc` of round entry: drift to
the last builder, `δ` to arrive, `proc` to conclude. The timeout does not
appear. -/
theorem built_succ_le_of_fast {δ : ℕ} {v : Validator}
    (hcard : quorumCard Validator ≤ T.card) (hv : v ∈ T) (hN : r + 3 ≤ N)
    (hδ : ∀ n, r + 1 ≤ n → n ≤ r + 2 → ∀ b ∈ U.ids, (U.block b).creator ∈ T →
      (U.block b).round = n →
      b ∈ pc.holds v (pc.built ((U.block b).creator) n + δ))
    (hD : ∀ u ∈ T, ∀ w ∈ T, pc.built u (r + 2) ≤ pc.built w (r + 2) + D)
    (ha0 : Rot.anchor r ∈ T) (ha1 : Rot.anchor (r + 1) ∈ T)
    (ha2 : Rot.anchor (r + 2) ∈ T)
    (hvotes : ∀ n, r ≤ n → n < r + 2 → ∀ A, IsAnchor U n A → VotesAt U T n A) :
    pc.built v (r + 3) ≤ pc.built v (r + 2) + D + δ + pc.proc := by
  refine pc.prompt_conclude v hv (r + 2) (by omega) (pc.built v (r + 2) + D + δ)
    (by omega) ?_
  refine pc.concludesAt_of_holds hcard hv (by omega) ?_ ha0 ha1 ha2 hvotes
  intro n hn1 hn2 b hb hbT hbr
  refine pc.holds_mono v _ _ ?_ (hδ n hn1 hn2 b hb hbT hbr)
  have htop : r + 2 ≤ pc.top ((U.block b).creator) := pc.reached hcard (r + 2) (by omega) _ hbT
  have hstep : pc.built ((U.block b).creator) n
      ≤ pc.built ((U.block b).creator) (r + 2) := by
    have hn : n = r + 1 ∨ n = r + 2 := by omega
    rcases hn with rfl | rfl
    · exact le_of_lt (pc.built_lt _ hbT (r + 1) (by omega))
    · omega
  have := hD _ hbT v hv
  omega

/-- **The timeout never fires.** When delivery, drift and processing
together undercut the timeout, every reliable validator concludes the
round strictly before its deadline: the fallback branch of
`anchor_or_wait` is never taken, and the protocol runs at network
speed. -/
theorem no_timeout_of_fast {δ : ℕ} {v : Validator}
    (hcard : quorumCard Validator ≤ T.card) (hv : v ∈ T) (hN : r + 3 ≤ N)
    (hδ : ∀ n, r + 1 ≤ n → n ≤ r + 2 → ∀ b ∈ U.ids, (U.block b).creator ∈ T →
      (U.block b).round = n →
      b ∈ pc.holds v (pc.built ((U.block b).creator) n + δ))
    (hD : ∀ u ∈ T, ∀ w ∈ T, pc.built u (r + 2) ≤ pc.built w (r + 2) + D)
    (ha0 : Rot.anchor r ∈ T) (ha1 : Rot.anchor (r + 1) ∈ T)
    (ha2 : Rot.anchor (r + 2) ∈ T)
    (hvotes : ∀ n, r ≤ n → n < r + 2 → ∀ A, IsAnchor U n A → VotesAt U T n A)
    (hfast : D + δ + pc.proc < pc.timeout (r + 2)) :
    pc.built v (r + 3) < pc.built v (r + 2) + pc.timeout (r + 2) := by
  have := pc.built_succ_le_of_fast hcard hv hN hδ hD ha0 ha1 ha2 hvotes
  omega

/-- **Latency, in the deployment's own constants.** Past GST, with a
quorum reliable, the spread needs no supplying: catch-up collapses it to
`Δ + proc`, and the bound reads `Δ + δ + 2 * proc`. -/
theorem built_succ_le_of_fast_gst {δ : ℕ} {v : Validator}
    (hcard : quorumCard Validator ≤ T.card) (hv : v ∈ T) (hN : r + 3 ≤ N)
    (hgst : pc.gst ≤ R) (hR : R ≤ r + 2)
    (hδ : ∀ n, r + 1 ≤ n → n ≤ r + 2 → ∀ b ∈ U.ids, (U.block b).creator ∈ T →
      (U.block b).round = n →
      b ∈ pc.holds v (pc.built ((U.block b).creator) n + δ))
    (ha0 : Rot.anchor r ∈ T) (ha1 : Rot.anchor (r + 1) ∈ T)
    (ha2 : Rot.anchor (r + 2) ∈ T)
    (hvotes : ∀ n, r ≤ n → n < r + 2 → ∀ A, IsAnchor U n A → VotesAt U T n A) :
    pc.built v (r + 3) ≤ pc.built v (r + 2) + pc.delay + δ + 2 * pc.proc := by
  have hdrift := pc.driftOn_of_catchup hcard hgst
  have hD : ∀ u ∈ T, ∀ w ∈ T,
      pc.built u (r + 2) ≤ pc.built w (r + 2) + (pc.delay + pc.proc) :=
    fun u hu w hw => hdrift w hw u hu (r + 2) hR (by omega)
  have := pc.built_succ_le_of_fast hcard hv hN hδ hD ha0 ha1 ha2 hvotes
  omega

/-- **When the timeout never fires**, in the same constants. At the
minimal timeout `2Δ + proc` the hypothesis reads `δ + proc < Δ`. -/
theorem no_timeout_of_fast_gst {δ : ℕ} {v : Validator}
    (hcard : quorumCard Validator ≤ T.card) (hv : v ∈ T) (hN : r + 3 ≤ N)
    (hgst : pc.gst ≤ R) (hR : R ≤ r + 2)
    (hδ : ∀ n, r + 1 ≤ n → n ≤ r + 2 → ∀ b ∈ U.ids, (U.block b).creator ∈ T →
      (U.block b).round = n →
      b ∈ pc.holds v (pc.built ((U.block b).creator) n + δ))
    (ha0 : Rot.anchor r ∈ T) (ha1 : Rot.anchor (r + 1) ∈ T)
    (ha2 : Rot.anchor (r + 2) ∈ T)
    (hvotes : ∀ n, r ≤ n → n < r + 2 → ∀ A, IsAnchor U n A → VotesAt U T n A)
    (hfast : pc.delay + δ + 2 * pc.proc < pc.timeout (r + 2)) :
    pc.built v (r + 3) < pc.built v (r + 2) + pc.timeout (r + 2) := by
  have := pc.built_succ_le_of_fast_gst hcard hv hN hgst hR hδ ha0 ha1 ha2 hvotes
  omega

end Pace

end BlackMarlin

end LeanDag
