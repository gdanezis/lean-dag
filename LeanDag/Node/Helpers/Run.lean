import LeanDag.Node.Helpers.Wave
import LeanDag.Node.Helpers.Recover
import LeanDag.Scheme.Helpers.Reactive
/-!
# A run read on the run's record

`docs/validator.md` §4, V12. Over a trace, the honest nodes' decisions
before each event are nothing or one call of the scheme's loop on a view
of the run's record that the node holds (`commitInv_before`). Over a
timed trace meeting
the liveness assumptions, a window of rounds above every reliable node's
round at GST gives the scheme's `WaveFacts` (`waveFacts_of_run`), and on
a reliable node's view each slot of a reliably led run is decided, its
own committed to a leader block (`run_commits`).
-/

namespace LeanDag

namespace Node

open Scheme

variable {Validator BlockId Payload : Type} [Fintype Validator] [DecidableEq Validator]
variable [LinearOrder BlockId]
variable {cfg : Config Validator BlockId Payload} {H : Finset Validator}
variable {tr : Trace Validator BlockId Payload}

/-! ## Without timing -/

section Record

variable (hσ : cfg.σ = boundedSel) (hadm : cfg.Admissible) (hf : Hᶜ.card ≤ cfg.f)
  (htime : Converge.TimelyAuthentic cfg H tr) (hinj : Converge.HashInjective cfg H tr)
include hσ hadm hf htime hinj

/-- **The decisions before an event are the scheme's loop on a view the
node holds**, or nothing. -/
theorem commitInv_before {v : Validator} (hv : v ∈ H) (t : ℕ) :
    commitsOf (run (cfg.at v) (State.init (cfg.at v)) (inputsBefore tr t v)).2 = [] ∨
      ∃ (V : (globalRecord (hashInjective_of_trace hinj) (authentic_of_timely htime)).View)
        (N : ℕ), V.ids ⊆ (stateBefore cfg tr t v).disk.ids ∧
        commitsOf (run (cfg.at v) (State.init (cfg.at v)) (inputsBefore tr t v)).2 =
          Scheme.tryDecide (S := cfg.slots) cfg.p boundedSel
            (globalRecord (hashInjective_of_trace hinj) (authentic_of_timely htime)) V 0 N := by
  have hinjR := hashInjective_of_trace hinj
  have hauthR := authentic_of_timely htime
  haveI : Validity.Quorate (ValidAt (Validator := Validator) (BlockId := BlockId)
      (Payload := Payload) cfg.q Clause.none) cfg.q :=
    Validity.Quorate.of_validAt hadm.2.2.2.1 fun _ _ => Iff.rfl
  have ht : cfg.p.Tolerates H cfg.f cfg.q := ⟨hf, hadm.2.2.2.2, hadm.1⟩
  have h₀ : CommitInv (cfg.at v) (globalRecord hinjR hauthR) (State.init (cfg.at v)) [] :=
    ⟨rfl, Or.inl rfl⟩
  have h := CommitInv.run (cfg := cfg.at v) (U := globalRecord hinjR hauthR) (f := cfg.f)
    (q := cfg.q) (ground hinjR hauthR) hσ ht (inputsBefore tr t v) h₀ (isCut_init hinjR hauthR _)
    (fun _ h => absurd h List.not_mem_nil)
    (fun e he => ⟨v, hv, knownBefore_knownOf (t := t)
      (show e ∈ Converge.knownBefore cfg tr t v from List.mem_append_left _ he)⟩)
    (fun e he => ⟨v, hv, knownBefore_knownOf (t := t)
      (show e ∈ Converge.knownBefore cfg tr t v from List.mem_append_right _ he)⟩)
  rcases h.2 with h0 | ⟨V, N, hV, -, hcs⟩
  · exact Or.inl ((List.nil_append _).symm.trans h0)
  · exact Or.inr ⟨V, N, hV, (List.nil_append _).symm.trans hcs⟩

end Record

/-! ## Over a timed trace -/

section Timed

variable {T : Finset Validator} {time : ℕ → ℕ} {gst Δ Δₛ t₁ : ℕ}

/-- **A window of rounds gives the scheme's wave facts**: from a round
`n₀` above every reliable node's round at GST to a round `N` every
reliable node has reached by `t`, with `t + A` within the assumptions. -/
theorem waveFacts_of_run (hσ : cfg.σ = boundedSel) (hadm : cfg.Admissible)
    (hf : Hᶜ.card ≤ cfg.f) (htime : Converge.TimelyAuthentic cfg H tr)
    (hinj : Converge.HashInjective cfg H tr) (hTH : T ⊆ H) (hmono : Live.TimeMono tr time)
    (harr : Arrival cfg T tr time gst (Δ + Δₛ) t₁) (hq : 2 ≤ cfg.q)
    (hto : ∀ r, 2 * (Δ + Δₛ) < cfg.timeout r) (hwait : Live.TimersAfterSet cfg H tr time)
    (hid : Function.Injective cfg.idOf) (hstart : Live.StartedBy T tr time gst)
    (hTc : Fintype.card Validator - cfg.f - cfg.c ≤ T.card) {n₀ N t : ℕ}
    (hbelow : ∀ v ∈ T, topAt cfg tr time v gst < n₀)
    (hst : ∀ v ∈ T, (stateAt cfg tr time v t).top.isSome)
    (htop : ∀ v ∈ T, N ≤ topAt cfg tr time v t) (ht₁ : t + (Δ + Δₛ) ≤ t₁) :
    letI := cfg.slots
    Scheme.WaveFacts cfg.p (boundedSel (P := ValidAt cfg.q Clause.none) (honest := H))
      (globalRecord (hashInjective_of_trace hinj) (authentic_of_timely htime)) T N n₀ :=
  letI := cfg.slots
  { populated := fun n hn0 hnN w hw' => by
      obtain ⟨i, inp, e, hi, he, her, -, -⟩ :=
        built_of_top hmono (hst w hw') ((htop w hw').trans' hnN)
          (harr.no_jump hmono hw' ((hbelow w hw').trans_le hn0) (by omega))
      obtain ⟨h₁, h₂, h₃⟩ := built_mem hσ hadm hf htime hinj (hTH hw') hi he
      exact ⟨e.1, h₁, h₃, h₂.trans her⟩
    reach_or_refs := fun w hw' _ hRk hNk hlk L hL _ hm _ hc hcc hcr =>
      reach_or_refs_node hσ hadm hf htime hinj hTH hmono harr hbelow hst htop ht₁ hq hto hwait
        hid hstart hTc hw' hRk hlk hL hm (by omega) hc hcc hcr
    cert_or_refs := fun hvc w hw' _ hRk hNk hlk L hL _ hc hcc hcr =>
      cert_or_refs_node hσ hadm hf htime hinj hTH hmono harr hbelow hst htop ht₁ hq hto hwait
        hid hstart hTc hvc hw' hRk hlk hL hNk hc hcc hcr }

/-- **On a reliable node's view, a reliably led run is decided**, from a
round `n₀` above every reliable node's round at GST, `A` after every
reliable node reached the last slot's decision round: each slot of the
run commits a leader block, certified by the wave facts
(`WaveFacts.certifies`, `reliable_held`), and every slot below the run is
decided within it (`decidedWithin_below_of_committed_run`). The view
holds the node's disk. -/
theorem run_commits (hσ : cfg.σ = boundedSel) (hadm : cfg.Admissible)
    (hf : Hᶜ.card ≤ cfg.f) (hTH : T ⊆ H) (hqT : cfg.q ≤ T.card)
    (hTc : Fintype.card Validator - cfg.f - cfg.c ≤ T.card) (hq : 2 ≤ cfg.q)
    (hid : Function.Injective cfg.idOf) (hto : ∀ r, 2 * (Δ + Δₛ) < cfg.timeout r)
    (htime : Converge.TimelyAuthentic cfg H tr) (hinj : Converge.HashInjective cfg H tr)
    (hmono : Live.TimeMono tr time) (harr : Arrival cfg T tr time gst (Δ + Δₛ) t₁)
    (hwait : Live.TimersAfterSet cfg H tr time) (hstart : Live.StartedBy T tr time gst) :
    letI := cfg.slots
    ∀ {b c n₀ : ℕ}, 0 < c → (Scheme.schemeAnchored cfg.p
      (boundedSel (BlockId := BlockId) (Payload := Payload) (P := ValidAt cfg.q Clause.none)
        (honest := T))).SpansEligible c →
    (∀ i < c, cfg.slots.leader (b + i) ∈ T) → n₀ ≤ cfg.slots.slotRound b →
    (∀ v ∈ T, topAt cfg tr time v gst < n₀) → ∀ {t : ℕ},
    (∀ v ∈ T, cfg.slots.slotRound (b + c - 1) + (cfg.p.waveLength - 1) ≤
      topAt cfg tr time v t) → t + (Δ + Δₛ) ≤ t₁ → ∀ {v : Validator}, v ∈ T →
    ∃ V : (globalRecord (hashInjective_of_trace hinj) (authentic_of_timely htime)).View,
      (∀ i, i ∈ V.ids ↔ i ∈ (stateAt cfg tr time v (t + (Δ + Δₛ))).disk.ids) ∧
      (∀ j, j ≤ b + c - 1 → ∃ w, (Scheme.schemeAnchored cfg.p boundedSel).DecidedWithin
        (globalRecord (hashInjective_of_trace hinj) (authentic_of_timely htime)) V (b + c) j w) ∧
      ∀ j, b ≤ j → j ≤ b + c - 1 → ∃ L,
        IsLeaderBlock (globalRecord (hashInjective_of_trace hinj) (authentic_of_timely htime))
          j L ∧
        (Scheme.schemeAnchored cfg.p boundedSel).DecidedWithin
          (globalRecord (hashInjective_of_trace hinj) (authentic_of_timely htime)) V (b + c) j
          (some L) := by
  intro b c n₀ hc hspan hlead hn₀ hbelow t htop ht₁ v hv
  letI := cfg.slots
  haveI : Nonempty Validator := ⟨v⟩
  set U := globalRecord (hashInjective_of_trace hinj) (authentic_of_timely htime) with hU
  set N := cfg.slots.slotRound (b + c - 1) + (cfg.p.waveLength - 1) with hNdef
  have hw : 2 ≤ cfg.p.waveLength := hadm.2.1.1
  -- every reliable node has started by `t`
  have hst : ∀ w ∈ T, (stateAt cfg tr time w t).top.isSome := fun w hw' => by
    have := htop w hw'
    unfold topAt at this
    rcases h : (stateAt cfg tr time w t).top with _ | r
    · rw [h] at this; simp at this; omega
    · rfl
  have wf := waveFacts_of_run hσ hadm hf htime hinj hTH hmono harr hq hto hwait hid hstart hTc
    hbelow hst htop ht₁
  -- the view of the node's disk `A` later
  set E := eventsBy tr time (t + (Δ + Δₛ)) with hE
  have hcut := (cut_before hσ hadm hf htime hinj E v (hTH hv)).1
  obtain ⟨V, -, hiff⟩ := hcut.extend ⟨∅, Finset.empty_subset _, fun i hi => absurd hi
    (Finset.notMem_empty _)⟩ (fun i hi => absurd hi (Finset.notMem_empty _))
  -- each run slot commits on the view
  have hcm : cfg.p.commitThreshold ≤ T.card := hadm.2.2.1.trans hTc
  have hcommit : ∀ j, b ≤ j → j ≤ b + c - 1 →
      ∃ L, IsLeaderBlock U j L ∧
        (Scheme.schemeAnchored cfg.p boundedSel).DecidedWithin U V (b + c) j (some L) := by
    intro j hbj hjc
    have hlj' : cfg.slots.leader j ∈ T := by
      have := hlead (j - b) (by omega); rwa [Nat.add_sub_cancel' hbj] at this
    have hsr : n₀ ≤ cfg.slots.slotRound j := hn₀.trans (cfg.slots.mono hbj)
    have hsN : cfg.slots.slotRound j + (cfg.p.waveLength - 1) ≤ N := by
      have := cfg.slots.mono hjc; omega
    obtain ⟨L, hLU, hLc, hLr⟩ := wf.populated _ hsr (by omega) _ hlj'
    have hL : IsLeaderBlock U j L := ⟨hLU, hLr, hLc⟩
    refine ⟨L, hL, AnchoredRule.DecidedWithin.directCommit (by omega) hL
      (Scheme.commit_of_certified hcm (wf.populated _ (by omega) hsN) fun C hC hCT hCr => ⟨?_, ?_⟩)⟩
    · exact wf.certifies hw hadm.2.1.2 hTH hqT hsr hsN hlj' hL _ hCT C hC rfl hCr
    · exact (hiff C).mpr (reliable_held hσ hadm hf htime hinj hTH
        hmono harr hbelow hst htop ht₁ hCT hv (r := (U.block C).round) (by omega) (by omega)
        hC rfl rfl)
  refine ⟨V, hiff, fun j hj => ?_, hcommit⟩
  -- and every slot below the run is decided within it
  by_cases hb : b ≤ j
  · obtain ⟨L, -, hL⟩ := hcommit j hb hj
    exact ⟨_, hL⟩
  · exact AnchoredRule.decidedWithin_below_of_committed_run
      (fun _ h => AnchoredRule.exists_least_of_lt (fun _ _ => Iff.rfl) h)
      (b := b) (n := b + c - 1) (by omega) (by omega) (fun i hi => by exact hspan b i hi)
      (fun j h1 h2 => ⟨_, (hcommit j h1 h2).choose_spec.2⟩) j (by omega)

end Timed

end Node

end LeanDag
