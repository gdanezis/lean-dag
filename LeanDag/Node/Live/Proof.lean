import LeanDag.Node.Live.Statement
import LeanDag.Node.Helpers.Wave
import LeanDag.Node.Helpers.Recover
import LeanDag.Scheme.Helpers.Reactive
/-!
# The reliable nodes produce rounds and decide — proof

`docs/validator.md` §5.2–5.4 and §5.6.

**Production.** Past GST, let every reliable node be at round `n` or
above at `s`, and `v` reliable and at round `n` at `s + A`, for
`A = Δ + Δₛ`. Every reliable node's round-`n` block arrived by `s + A`
(`round_arrives`), so `v` holds a quorum of the round and has armed its
timer (`armed_before`), which fires by `s + A + timeout n` (`TopTimerBy`).
Suppose `v` is still at round `n` then. It is settled (`settled_before`),
the round's timer has fired and stays so (`fired_stays`), and it holds no
block with the identifier of its next one (`fresh_before`), so it builds
(`tryBuild_isSome`), against its being settled.

**Decision.** Let every reliable node be below a round `n₀` at GST. An
honest node that armed a round's timer from `n₀` on held a quorum of the
round past GST, whose `f + 1` reliable authors bring every reliable node
to the round within `A` (`catches_up`); their blocks reach every reliable
node `A` after, before the timer fired (`waited_holds`). An honest block
that did not pass the tests was built on such a timer, or behind an
earlier such block, so every reliable block of the round below had
reached every reliable node by then (`held_before`), and a reliable one
references them (`refs_all`). Each reliable block therefore reaches or certifies the
leader block, or references what it needs (`reach_or_refs_node`,
`cert_or_refs_node`), and the run gives the scheme's `WaveFacts`, whose
reliable decision-round blocks certify each reliable leader's block
(`WaveFacts.certifies`). `A` after every reliable node reached the last
slot's decision round, each holds those blocks (`reliable_held`), so on
its view each slot of the run from its next undecided one commits, and
every slot below the run is decided within the run
(`decidedWithin_below_of_committed_run`). Its next undecided slot is then
output by its scan (`tryDecide_within`), against its being settled.

**The time bound.** The reliable nodes gain a round every `timeout + A`
(`produces`), so they reach the last slot's decision round within the sum,
and decide `A` later.

The argument reads the run through arrival within `A` (`Arrival`) and the
armed top round's timer (`TopTimerBy`). Without crashes the assumptions
give them at GST (`progresses`); with crashes up to `t_r`, at
`max t_r gst + W` (`recovers`, `Helpers/Recover.lean`).
-/

namespace LeanDag

namespace Node

namespace Live

variable {Validator BlockId Payload : Type} [Fintype Validator] [DecidableEq Validator]
variable [LinearOrder BlockId]

/-- **Production**: past GST, the reliable nodes are above round `n` a
timeout and `A` after all were at `n` or above. -/
theorem produces {cfg : Config Validator BlockId Payload} {H T : Finset Validator}
    {tr : Trace Validator BlockId Payload} {time : ℕ → ℕ} {gst Δ Δₛ t₁ : ℕ}
    (hσ : cfg.σ = boundedSel) (hadm : cfg.Admissible)
    (hf : Hᶜ.card ≤ cfg.f) (hTH : T ⊆ H) (hqT : cfg.q ≤ T.card) (hq : 2 ≤ cfg.q)
    (hid : Function.Injective cfg.idOf)
    (htime : Converge.TimelyAuthentic cfg H tr) (hinj : Converge.HashInjective cfg H tr)
    (hmono : TimeMono tr time) (harr : Arrival cfg T tr time gst (Δ + Δₛ) t₁)
    (htop : TopTimerBy cfg T tr time gst t₁)
    (hstart : StartedBy T tr time gst) : Produces cfg T tr time gst (Δ + Δₛ) t₁ := by
  intro s n hgs hst₁ hall v hv
  have hstarted : ∀ w ∈ T, (stateAt cfg tr time w s).top.isSome := fun w hw =>
    started_at hadm hid htime hTH hmono hstart hw hgs
  by_contra hlt
  have hle : topAt cfg tr time v (s + (Δ + Δₛ) + cfg.timeout n) ≤ n := by omega
  set τ := s + (Δ + Δₛ) with hτ
  set E := eventsBy tr time (τ + cfg.timeout n) with hE
  have hsτ : eventsBy tr time s ≤ eventsBy tr time τ := eventsBy_mono (by omega)
  have hτE : eventsBy tr time τ ≤ E := eventsBy_mono (by omega)
  -- `v` is at round `n` from `s` to `τ + timeout n`
  have hZt : (stateBefore cfg tr E v).top = some n := by
    have hZs : (stateBefore cfg tr E v).top.isSome :=
      (rises_before (cfg := cfg) v (hsτ.trans hτE)).2.1 (hstarted v hv)
    have hZge : n ≤ (stateBefore cfg tr E v).top.getD 0 :=
      (hall v hv).trans (rises_before (cfg := cfg) v (hsτ.trans hτE)).1
    obtain ⟨t, ht⟩ := Option.isSome_iff_exists.mp hZs
    change (stateBefore cfg tr E v).top.getD 0 ≤ n at hle
    rw [ht] at hZge hle ⊢
    simp only [Option.getD_some] at hZge hle
    rw [show t = n by omega]
  have hτt : (stateAt cfg tr time v τ).top = some n :=
    top_between hτE ((rises_before (cfg := cfg) v hsτ).2.1 (hstarted v hv))
      ((hall v hv).trans (rises_before (cfg := cfg) v hsτ).1) hZt
  -- it holds a quorum of round `n` at `τ`, so it armed the round's timer
  obtain ⟨j₀, hj₀, hj₀i, hj₀r, hj₀c⟩ :=
    ownTop_before (cfg := cfg) (tr := tr) (v := v) (eventsBy tr time τ) n hτt
  have hauth : T ⊆ authorsIn (stateAt cfg tr time v τ).disk.toRecord
      (stateAt cfg tr time v τ).disk.ids n := by
    intro w hw
    rw [mem_authorsIn]
    by_cases hwv : w = v
    · subst hwv
      exact ⟨j₀, hj₀i, hj₀r, hj₀c⟩
    · exact round_arrives htime hinj hTH hmono harr hw hv hwv hgs (hstarted w hw) (hall w hw)
        le_rfl (by omega)
  have hcard : cfg.q ≤ ((stateAt cfg tr time v τ).disk.authorsAt n).card := by
    rw [Store.authorsAt_eq]
    exact hqT.trans (Finset.card_le_card hauth)
  have harm := armed_before (cfg := cfg) (tr := tr) v (eventsBy tr time τ) n hτt (by
    rw [(stateBefore cfg tr (eventsBy tr time τ) v).mirrors.authorsAt_eq
      ((Converge.floor_before hτt).trans (Nat.sub_le _ _))]
    exact hcard)
  obtain ⟨f, hfe, htf⟩ := htop v hv τ n (by omega) (by omega) hτt harm
  have hfl : f < tr.length := (List.getElem?_eq_some_iff.mp hfe).1
  have hfE : f < E := (lt_eventsBy hmono hfl).mpr htf
  -- at `τ + timeout n` its round's timer has fired, with the quorum held
  have hfired : n ∈ (stateBefore cfg tr E v).fired :=
    fired_stays hfe E hfE (by rw [hZt]; rfl)
  have hcardE : cfg.q ≤ (authorsIn (stateBefore cfg tr E v).disk.toRecord
      (stateBefore cfg tr E v).disk.ids n).card := by
    rw [← Store.authorsAt_eq]
    exact hcard.trans (Finset.card_le_card (Grows.authorsAt (grows_before v hτE) n))
  obtain ⟨j₁, hj₁, hj₁i, hj₁r, hj₁c⟩ := ownTop_before (cfg := cfg) (tr := tr) (v := v) E n hZt
  -- so it builds, against its being settled
  have hsome := tryBuild_isSome (cfg := cfg.at v) hZt (Or.inl hfired) hcardE
    (fun j hj => by rw [hj₁] at hj; cases hj; exact ⟨hj₁i, hj₁r, hj₁c⟩)
    (fun R => fresh_before hid htime (hTH hv) hZt R)
    ((Converge.floor_before hZt).trans (Nat.sub_le _ _))
  rcases settled_before (cfg := cfg) hq v E with h | h
  · rw [hZt] at h; cases h
  · rw [h.build] at hsome; cases hsome

/-- **Decision**: from a round `n₀` above every reliable node's round
at GST, once every reliable node is at the decision round of the last of
`c` reliably led slots spanning the rule's eligibility, `A` later every
reliable node has output the decisions of every slot below them. -/
theorem decides {cfg : Config Validator BlockId Payload} {H T : Finset Validator}
    {tr : Trace Validator BlockId Payload} {time : ℕ → ℕ} {gst Δ Δₛ t₁ : ℕ}
    (hσ : cfg.σ = boundedSel) (hadm : cfg.Admissible)
    (hf : Hᶜ.card ≤ cfg.f) (hTH : T ⊆ H) (hqT : cfg.q ≤ T.card)
    (hcT : Fintype.card Validator - cfg.f - cfg.c ≤ T.card) (hq : 2 ≤ cfg.q)
    (hid : Function.Injective cfg.idOf) (hto : ∀ r, 2 * (Δ + Δₛ) < cfg.timeout r)
    (htime : Converge.TimelyAuthentic cfg H tr) (hinj : Converge.HashInjective cfg H tr)
    (hmono : TimeMono tr time) (harr : Arrival cfg T tr time gst (Δ + Δₛ) t₁)
    (hwait : TimersAfterSet cfg H tr time) (hstart : StartedBy T tr time gst) :
    Decides cfg T tr time gst (Δ + Δₛ) t₁ := by
  letI := cfg.slots
  intro b c n₀ hc hspan hlead hn₀ hbelow t htop ht₁ v hv
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
  -- the node's wave facts
  let wf : Scheme.WaveFacts cfg.p (boundedSel (P := ValidAt cfg.q Clause.none) (honest := H)) U T
      N n₀ :=
    { populated := fun n _ hnN w hw' => by
        obtain ⟨i, inp, e, hi, he, her, -, -⟩ :=
          built_of_top hmono (hst w hw') ((htop w hw').trans' hnN)
        obtain ⟨h₁, h₂, h₃⟩ := built_mem hσ hadm hf htime hinj (hTH hw') hi he
        exact ⟨e.1, h₁, h₃, h₂.trans her⟩
      reach_or_refs := fun w hw' _ hRk hNk hlk L hL _ hm _ hc hcc hcr =>
        reach_or_refs_node hσ hadm hf htime hinj hTH hmono harr hbelow hst htop ht₁ hq hto hwait
          hid hstart hcT hw' hRk hlk hL hm (by omega) hc hcc hcr
      cert_or_refs := fun hvc w hw' _ hRk hNk hlk L hL _ hc hcc hcr =>
        cert_or_refs_node hσ hadm hf htime hinj hTH hmono harr hbelow hst htop ht₁ hq hto hwait
          hid hstart hcT hvc hw' hRk hlk hL hNk hc hcc hcr }
  -- `v` at `t + A`, settled
  set E := eventsBy tr time (t + (Δ + Δₛ)) with hE
  obtain ⟨h₁, h₂, -⟩ := rises_before (cfg := cfg) v
    (eventsBy_mono (tr := tr) (time := time) (show t ≤ t + (Δ + Δₛ) by omega))
  obtain ⟨t', ht'⟩ := Option.isSome_iff_exists.mp (h₂ (hst v hv))
  change (stateBefore cfg tr E v).top = some t' at ht'
  have hNt' : N ≤ t' := by
    have := (htop v hv).trans h₁
    change N ≤ (stateBefore cfg tr E v).top.getD 0 at this
    rw [ht'] at this
    exact this
  rw [decisionsBy_length]
  change b + c ≤ (stateBefore cfg tr E v).lo
  set Z := stateBefore cfg tr E v with hZ
  by_contra hlo
  have hSet : Settled (cfg.at v) Z := by
    rcases settled_before (cfg := cfg) hq v E with h | h
    · rw [ht'] at h; cases h
    · exact h
  have hcut := (cut_before hσ hadm hf htime hinj E v (hTH hv)).1
  obtain ⟨V, -, hiff⟩ := hcut.extend ⟨∅, Finset.empty_subset _, fun i hi => absurd hi
    (Finset.notMem_empty _)⟩ (fun i hi => absurd hi (Finset.notMem_empty _))
  have hva := ViewsAbove.of_store hiff fun i hi => (hcut i hi).2
  -- each run slot from `lo` on commits on the view
  have hcm : cfg.p.commitThreshold ≤ T.card := hadm.2.2.1.trans hcT
  have hcommit : ∀ j, b ≤ j → j ≤ b + c - 1 →
      ∃ L, (Scheme.schemeAnchored cfg.p boundedSel).DecidedWithin U V (b + c) j (some L) := by
    intro j hbj hjc
    have hlj' : cfg.slots.leader j ∈ T := by
      have := hlead (j - b) (by omega); rwa [Nat.add_sub_cancel' hbj] at this
    have hsr : n₀ ≤ cfg.slots.slotRound j := hn₀.trans (cfg.slots.mono hbj)
    have hsN : cfg.slots.slotRound j + (cfg.p.waveLength - 1) ≤ N := by
      have := cfg.slots.mono hjc; omega
    obtain ⟨L, hLU, hLc, hLr⟩ := wf.populated _ hsr (by omega) _ hlj'
    have hL : IsLeaderBlock U j L := ⟨hLU, hLr, hLc⟩
    refine ⟨L, AnchoredRule.DecidedWithin.directCommit (by omega) hL
      (Scheme.commit_of_certified hcm (wf.populated _ (by omega) hsN) fun C hC hCT hCr => ⟨?_, ?_⟩)⟩
    · exact wf.certifies hw hadm.2.1.2 hTH hqT hsr hsN hlj' hL _ hCT C hC rfl hCr
    · exact (hiff C).mpr (reliable_held hσ hadm hf htime hinj hTH
        hmono harr hbelow hst htop ht₁ hCT hv (r := (U.block C).round) (by omega) (by omega)
        hC rfl rfl)
  -- so does slot `lo`
  have hlow : ∃ w, (Scheme.schemeAnchored cfg.p boundedSel).DecidedWithin U V (b + c) Z.lo w := by
    by_cases hb : b ≤ Z.lo
    · obtain ⟨L, hL⟩ := hcommit Z.lo hb (by omega)
      exact ⟨_, hL⟩
    · exact AnchoredRule.decidedWithin_below_of_committed_run
        (fun _ h => AnchoredRule.exists_least_of_lt (fun _ _ => Iff.rfl) h)
        (b := b) (n := b + c - 1) (by omega) (by omega) (fun i hi => by exact hspan b i hi)
        (fun j h1 h2 => hcommit j h1 h2) Z.lo (by omega)
  -- and the scan reaches it
  obtain ⟨o, -, hoi, hor, -⟩ := ownTop_before (cfg := cfg) (tr := tr) (v := v) E t' ht'
  have hoi' : o ∈ Z.disk.ids := hoi
  have hor' : (Z.disk.blk o).round = t' := hor
  have hdec : b + c ≤ decidable cfg Z.disk.topRound := by
    have hle : (Z.disk.blk o).round ≤ Z.disk.topRound := Z.disk.topRound_eq ▸
      Finset.le_sup (f := fun i => (Z.disk.blk i).round) hoi'
    have := lt_decidable (cfg := cfg) (k := b + c - 1) (R := Z.disk.topRound) (by omega)
    omega
  haveI : Validity.Quorate (ValidAt (Validator := Validator) (BlockId := BlockId)
      (Payload := Payload) cfg.q Clause.none) cfg.q :=
    Validity.Quorate.of_validAt hadm.2.2.2.1 fun _ _ => Iff.rfl
  have ht : cfg.p.Tolerates H cfg.f cfg.q := ⟨hf, hadm.2.2.2.2, hadm.1⟩
  obtain ⟨hls, hcms, hcs, hlaws⟩ := Scheme.coveredLaws (boundedSel (P := ValidAt cfg.q Clause.none)
    (honest := H) (Validator := Validator) (BlockId := BlockId) (Payload := Payload)) ht
  obtain ⟨w, hwd⟩ := hlow
  have hmem := Scheme.tryDecide_within hls hcms hcs hlaws trivial (lo := Z.lo) (k := Z.lo)
    (B := b + c) (N := decidable cfg Z.disk.topRound - 1) le_rfl (by omega) (by omega)
    (fun m h1 h2 => ⟨w, by rwa [show m = Z.lo by omega]⟩) w hwd.toDecided
  have hfZ : Z.floor ≤ cfg.slots.slotRound Z.lo := Converge.floor_lo_before (cfg := cfg) E v
  have hempty := hSet.decided (show Z.lo < decidable cfg Z.disk.topRound by omega) hfZ
  have heq : Scheme.tryDecide (S := cfg.slots) cfg.p boundedSel Z.disk.toRecord Z.disk.view Z.lo
      (decidable cfg Z.disk.topRound - 1) =
      Scheme.tryDecide cfg.p boundedSel U V Z.lo (decidable cfg Z.disk.topRound - 1) :=
    hva.tryDecide_eq cfg.p hw _ (Nat.zero_le _)
  change Scheme.tryDecide (S := cfg.slots) cfg.p cfg.σ (Z.memory.window (cfg.slots.slotRound Z.lo))
    (Z.memory.windowView (cfg.slots.slotRound Z.lo)) Z.lo
    (decidable cfg Z.disk.topRound - 1) = [] at hempty
  rw [tryDecide_memory (cfg := cfg) hσ hw Z hfZ, heq] at hempty
  rw [hempty] at hmem
  simp at hmem

/-- **Decision by a time bound**: the reliable nodes gain a round every
timeout and `A` (`produces`), so they reach the last slot's decision round
within the sum, and decide `A` after (`decides`). -/
theorem decidesBy {cfg : Config Validator BlockId Payload} {T : Finset Validator}
    {tr : Trace Validator BlockId Payload} {time : ℕ → ℕ} {gst D t₁ : ℕ}
    (hp : Produces cfg T tr time gst D t₁) (hd : Decides cfg T tr time gst D t₁) :
    DecidesBy cfg T tr time gst D t₁ := by
  letI := cfg.slots
  intro b c n₀ n₁ s hc hspan hlead hn₀ hbelow hgs hall ht₁
  set N := cfg.slots.slotRound (b + c - 1) + (cfg.p.waveLength - 1) with hN
  -- a round every timeout and `D`
  have key : ∀ k, n₁ + k ≤ N → ∀ v ∈ T,
      n₁ + k ≤ topAt cfg tr time v (s + ∑ r ∈ Finset.Ico n₁ (n₁ + k), (cfg.timeout r + D)) := by
    intro k
    induction k with
    | zero => intro _ v hv; simpa using hall v hv
    | succ k ih =>
      intro hk v hv
      have hsum : ∑ r ∈ Finset.Ico n₁ (n₁ + (k + 1)), (cfg.timeout r + D) =
          ∑ r ∈ Finset.Ico n₁ (n₁ + k), (cfg.timeout r + D) + (cfg.timeout (n₁ + k) + D) :=
        Finset.sum_Ico_succ_top (show n₁ ≤ n₁ + k by omega) _
      have hsub : ∑ r ∈ Finset.Ico n₁ (n₁ + (k + 1)), (cfg.timeout r + D) ≤
          ∑ r ∈ Finset.Ico n₁ N, (cfg.timeout r + D) :=
        Finset.sum_le_sum_of_subset (Finset.Ico_subset_Ico_right hk)
      have := hp (s + ∑ r ∈ Finset.Ico n₁ (n₁ + k), (cfg.timeout r + D)) (n₁ + k) (by omega)
        (by omega) (ih (by omega)) v hv
      rw [hsum, show s + (∑ r ∈ Finset.Ico n₁ (n₁ + k), (cfg.timeout r + D) +
        (cfg.timeout (n₁ + k) + D)) = s + ∑ r ∈ Finset.Ico n₁ (n₁ + k), (cfg.timeout r + D) +
          D + cfg.timeout (n₁ + k) by omega]
      exact this
  have hall' : ∀ v ∈ T, N ≤ topAt cfg tr time v
      (s + ∑ r ∈ Finset.Ico n₁ N, (cfg.timeout r + D)) := by
    by_cases hn₁N : n₁ ≤ N
    · have := key (N - n₁) (by omega)
      rwa [Nat.add_sub_cancel' hn₁N] at this
    · intro v hv
      rw [Finset.Ico_eq_empty (by omega), Finset.sum_empty, Nat.add_zero]
      exact (show N ≤ n₁ by omega).trans (hall v hv)
  exact hd b c n₀ hc hspan hlead hn₀ hbelow _ hall' ht₁

/-- **The reliable nodes produce rounds and decide.** -/
theorem progresses : Progresses := by
  intro Validator BlockId Payload _ _ _ cfg H T tr time gst Δ Δₛ t₁ hσ hadm hf hTH hqT hcT
    hq hid hto htime hinj hmono hdel hfire hwait hsync hstart
  have harr := arrival_of_delivered hσ hadm hf htime hinj hTH hmono hdel hsync
  have hp := produces hσ hadm hf hTH hqT hq hid htime hinj hmono harr
    (TopTimerBy.of_fire hmono hfire) hstart
  have hd := decides hσ hadm hf hTH hqT hcT hq hid hto htime hinj hmono harr hwait hstart
  exact ⟨hp, hd, decidesBy hp hd⟩

/-- **The reliable nodes recover from crashes**: past `G = max t_r gst + W`
blocks arrive within `A` (`arrival_of_recovered`) and the armed top
round's timer fires within its timeout (`topTimerBy_of_up`), so
production and decision hold from `G`. -/
theorem recovers : Recovers := by
  intro Validator BlockId Payload _ _ _ cfg H T tr time gst Δ Δₛ t_r t₁ hσ hadm hf hTH hqT
    hcT hq hid hto htime hinj hmono hdel hfire hwait hsync hup hstart
  intro G
  have hrG : t_r ≤ G := (le_max_left _ _).trans (Nat.le_add_right _ _)
  have hgG : gst ≤ G := (le_max_right _ _).trans (Nat.le_add_right _ _)
  have harr := arrival_of_recovered hσ hadm hf hid htime hinj hTH hmono hdel hsync hup hfire hstart
  have hstart' : StartedBy T tr time G := fun v hv => by
    obtain ⟨i, hi, hit⟩ := hstart v hv
    exact ⟨i, hi, hit.trans hgG⟩
  have hp := produces hσ hadm hf hTH hqT hq hid htime hinj hmono harr
    (topTimerBy_of_up hmono hup hfire hrG) hstart'
  have hd := decides hσ hadm hf hTH hqT hcT hq hid hto htime hinj hmono harr hwait hstart'
  exact ⟨hp, hd, decidesBy hp hd⟩

/-- **The reliable nodes' liveness**, without crashes and with them. -/
theorem holds : Statement := ⟨progresses, recovers⟩

end Live

end Node

end LeanDag
