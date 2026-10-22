import LeanDag.Node.Live.Statement
import LeanDag.Node.Helpers.Wave
import LeanDag.Scheme.Helpers.Reactive
/-!
# The reliable nodes produce rounds and decide — proof

`docs/validator.md` §5.2–5.4.

**Production.** Past GST, let every reliable node be at round `n` or
above at `s`, and `v` reliable. `v` built its round-`n` block by `s`,
with the round's timer, which fires by `s + timeout n`. Suppose `v` is
still at round `n` then. It is settled (`settled_before`), and the
round's timer has fired and stays so (`fired_stays`). Every reliable
node's round-`n` block arrived within `A = Δ + Δₛ` of `s`, less than the
timeout (`round_arrives`): the block reached `v` within `Δ`, and its
history within `Δₛ` after it (`arrives`). So `v` holds a quorum of
authors at round `n`, its own block included, and no block with the
identifier of its next one (`fresh_before`), and builds
(`tryBuild_isSome`), against its being settled.

**Decision.** From a round `n₀` the reliable nodes built within `A` of
each other past GST, they build every later round within `A` of each
other (`drift`): a node behind a peer's round-`n + 1` block holds it `A`
later, with a quorum of round `n`, and passes the tests with the
references it lends, or its own timer of round `n` has fired
(`catches_up`). So a node that waited the timeout holds every reliable
block of the round (`waited_holds`), and with the build rule's wait
clauses (`reach_or_wait_node`, `cert_or_wait_node`) the run gives the
scheme's `WaveFacts`, whose reliable decision-round blocks certify each
reliable leader's block (`WaveFacts.certifies`). `A` after every
reliable node reached the last slot's decision round, each holds those
blocks (`reliable_held`), so on its view each slot of the run from its
next undecided one commits, and every slot below the run is decided
within the run (`decidedWithin_below_of_committed_run`). Its next
undecided slot is then output by its scan (`tryDecide_within`), against
its being settled.

**The time bound.** From the synchronisation point the reliable nodes
gain a round a timeout (`produces`), so they reach the last slot's
decision round within the sum of the timeouts, and decide `A` later.
-/

namespace LeanDag

namespace Node

namespace Live

variable {Validator BlockId Payload : Type} [Fintype Validator] [DecidableEq Validator]
variable [LinearOrder BlockId]

/-- **Production**: past GST, the reliable nodes are above round `n` a
timeout after all were at `n` or above. -/
theorem produces {cfg : Config Validator BlockId Payload} {H T : Finset Validator}
    {tr : Trace Validator BlockId Payload} {time : ℕ → ℕ} {gst Δ Δₛ t₁ : ℕ}
    (hσ : cfg.σ = boundedSel) (hadm : cfg.Admissible)
    (hf : Hᶜ.card ≤ cfg.f) (hTH : T ⊆ H) (hqT : cfg.q ≤ T.card)
    (hto : ∀ r, 2 * (Δ + Δₛ) < cfg.timeout r) (hq : 2 ≤ cfg.q)
    (hid : Function.Injective cfg.idOf)
    (htime : Converge.TimelyAuthentic cfg H tr) (hinj : Converge.HashInjective cfg H tr)
    (hmono : TimeMono tr time) (harr : Arrival cfg T tr time gst (Δ + Δₛ) t₁)
    (htop : TopTimerBy cfg T tr time gst t₁)
    (hstart : StartedBy T tr time gst) : Produces cfg T tr time gst t₁ := by
  intro s n hgs hst₁ hall v hv
  have hτ := hto n
  have hstarted : ∀ w ∈ T, (stateAt cfg tr time w s).top.isSome := fun w hw =>
    started_at hadm hid htime hTH hmono hstart hw hgs
  by_contra hlt
  have hle : topAt cfg tr time v (s + cfg.timeout n) ≤ n := by omega
  set E := eventsBy tr time (s + cfg.timeout n) with hE
  have hsE : eventsBy tr time s ≤ E := eventsBy_mono (by omega)
  -- `v` is at round `n` at `s`, and the round's timer fires by `s + timeout n`
  have hts : (stateAt cfg tr time v s).top = some n := by
    obtain ⟨t, ht⟩ := Option.isSome_iff_exists.mp (hstarted v hv)
    have h₁ := hall v hv
    have h₂ := (rises_before (cfg := cfg) (tr := tr) v hsE).1
    change n ≤ (stateBefore cfg tr (eventsBy tr time s) v).top.getD 0 at h₁
    change (stateBefore cfg tr (eventsBy tr time s) v).top = some t at ht
    change (stateBefore cfg tr E v).top.getD 0 ≤ n at hle
    rw [ht] at h₁ h₂
    simp only [Option.getD_some] at h₁ h₂
    change (stateBefore cfg tr (eventsBy tr time s) v).top = some n
    rw [ht, show t = n by omega]
  obtain ⟨f, hfe, htf⟩ := htop v hv s n hgs hst₁ hts
  have hfl : f < tr.length := (List.getElem?_eq_some_iff.mp hfe).1
  have hfE : f < eventsBy tr time (s + cfg.timeout n) := (lt_eventsBy hmono hfl).mpr (by omega)
  -- at `s + timeout n`, `v` is at round `n`
  have hZs : (stateBefore cfg tr E v).top.isSome :=
    (rises_before (cfg := cfg) v hsE).2.1 (hstarted v hv)
  have hZge : n ≤ (stateBefore cfg tr E v).top.getD 0 :=
    (hall v hv).trans (rises_before (cfg := cfg) v hsE).1
  have hZle : (stateBefore cfg tr E v).top.getD 0 ≤ n := hle
  have hZt : (stateBefore cfg tr E v).top = some n := by
    obtain ⟨t, ht⟩ := Option.isSome_iff_exists.mp hZs
    rw [ht] at hZge hZle ⊢
    simp only [Option.getD_some] at hZge hZle
    rw [show t = n by omega]
  -- its round's timer has fired
  have hfired : n ∈ (stateBefore cfg tr E v).fired := fired_stays hfe E hfE
  -- it holds a quorum of round `n`
  obtain ⟨j₀, hj₀, hj₀i, hj₀r, hj₀c⟩ := ownTop_before (cfg := cfg) (tr := tr) (v := v) E n hZt
  have hauth : T ⊆ authorsIn (stateBefore cfg tr E v).store.toRecord
      (stateBefore cfg tr E v).store.ids n := by
    intro w hw
    rw [mem_authorsIn]
    by_cases hwv : w = v
    · subst hwv
      exact ⟨j₀, hj₀i, hj₀r, hj₀c⟩
    · exact round_arrives (τ := s + cfg.timeout n) htime hinj hTH hmono harr hw hv hwv hgs
        (hstarted w hw) (hall w hw) (by omega) hst₁
  have hcard : cfg.q ≤ (authorsIn (stateBefore cfg tr E v).store.toRecord
      (stateBefore cfg tr E v).store.ids n).card :=
    hqT.trans (Finset.card_le_card hauth)
  -- so it builds, against its being settled
  have hsome := tryBuild_isSome (cfg := cfg.at v) hZt (Or.inl hfired) hcard
    (fun j hj => by rw [hj₀] at hj; cases hj; exact ⟨hj₀i, hj₀r, hj₀c⟩)
    (fun R => fresh_before hid htime (hTH hv) hZt R)
  rcases settled_before (cfg := cfg) hq v E with h | h
  · rw [hZt] at h; cases h
  · rw [h.build] at hsome; cases hsome

/-- **Decision**: past a synchronisation point, once every reliable node is
at the decision round of the last of `c` reliably led slots spanning the
rule's eligibility, `A` later every reliable node has output the
decisions of every slot below them. -/
theorem decides {cfg : Config Validator BlockId Payload} {H T : Finset Validator}
    {tr : Trace Validator BlockId Payload} {time : ℕ → ℕ} {gst Δ Δₛ t₁ : ℕ}
    (hσ : cfg.σ = boundedSel) (hadm : cfg.Admissible)
    (hf : Hᶜ.card ≤ cfg.f) (hTH : T ⊆ H) (hqT : cfg.q ≤ T.card)
    (hcT : Fintype.card Validator - cfg.f - cfg.c ≤ T.card) (hq : 2 ≤ cfg.q)
    (hid : Function.Injective cfg.idOf) (hto : ∀ r, 2 * (Δ + Δₛ) < cfg.timeout r)
    (htime : Converge.TimelyAuthentic cfg H tr) (hinj : Converge.HashInjective cfg H tr)
    (hmono : TimeMono tr time) (harr : Arrival cfg T tr time gst (Δ + Δₛ) t₁)
    (hwait : TimersAfterSet cfg T tr time) (hfire : TimersFireFrom cfg T tr time gst t₁)
    (hstart : StartedBy T tr time gst) : Decides cfg T tr time gst (Δ + Δₛ) t₁ := by
  letI := cfg.slots
  intro b c n₀ s hc hspan hlead hn₀ hgs hall t htop ht₁ v hv
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
  have hDs := drift hq hσ hadm hf hid htime hinj hTH hmono harr hwait hfire
    hstart hgs (fun w hw' => ⟨(hall w hw').2.1, (hall w hw').2.2⟩) hst htop ht₁
  have hD : ∀ n, n₀ ≤ n → n ≤ N → ∀ u ∈ T, ∀ w ∈ T, gst ≤ builtAt cfg tr time u n ∧
      builtAt cfg tr time u n ≤ builtAt cfg tr time w n + (Δ + Δₛ) :=
    fun n h₁ h₂ u hu w hw => ⟨hgs.trans (hDs n h₁ h₂ u hu w hw).1, (hDs n h₁ h₂ u hu w hw).2⟩
  -- the node's wave facts
  let wf : Scheme.WaveFacts cfg.p (boundedSel (P := ValidAt cfg.q Clause.none) (honest := H)) U T
      N n₀ :=
    { built := builtAt cfg tr time
      timeout := cfg.timeout
      holds := heldBefore cfg tr time
      populated := fun n _ hnN w hw' => by
        obtain ⟨i, inp, e, hi, he, her, -, -⟩ :=
          built_of_top hmono (hst w hw') ((htop w hw').trans' hnN)
        obtain ⟨h₁, h₂, h₃⟩ := built_mem hσ hadm hf htime hinj (hTH hw') hi he
        exact ⟨e.1, h₁, h₃, h₂.trans her⟩
      arrives := fun w hw' u hu n hn₀ hnN c hc hcu hcr hwait =>
        waited_holds hσ hadm hf htime hinj hTH hmono harr
          hD hst htop ht₁ hto hu hw' hn₀ hnN hc hcu hcr hwait
      reach_or_wait := fun w hw' _ _ hlk L hL _ hm _ hc hcc hcr =>
        reach_or_wait_node time hσ hadm hf htime hinj hmono hTH hwait hw'
          hlk hL hm hc hcc hcr
      cert_or_wait := fun hvc w hw' _ _ hlk L hL _ hc hcc hcr =>
        (cert_or_wait_node time hσ hadm hf htime hinj hmono hTH hwait hvc hw'
          hlk hL hc hcc hcr).imp id
          fun h => ⟨h.1, fun b hb hbc hbr hbh _ => h.2 b hb hbc hbr hbh⟩ }
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
        hmono harr hD hst htop ht₁ hCT hv (r := (U.block C).round) (by omega) (by omega)
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
  have hoi' : o ∈ Z.store.ids := hoi
  have hor' : (Z.store.blk o).round = t' := hor
  have hdec : b + c ≤ decidable cfg Z.store.topRound := by
    have hle : (Z.store.blk o).round ≤ Z.store.topRound := Z.store.topRound_eq ▸
      Finset.le_sup (f := fun i => (Z.store.blk i).round) hoi'
    have := lt_decidable (cfg := cfg) (k := b + c - 1) (R := Z.store.topRound) (by omega)
    omega
  haveI : Validity.Quorate (ValidAt (Validator := Validator) (BlockId := BlockId)
      (Payload := Payload) cfg.q Clause.none) cfg.q :=
    Validity.Quorate.of_validAt hadm.2.2.2.1 fun _ _ => Iff.rfl
  have ht : cfg.p.Tolerates H cfg.f cfg.q := ⟨hf, hadm.2.2.2.2, hadm.1⟩
  obtain ⟨hls, hcms, hcs, hlaws⟩ := Scheme.coveredLaws (boundedSel (P := ValidAt cfg.q Clause.none)
    (honest := H) (Validator := Validator) (BlockId := BlockId) (Payload := Payload)) ht
  obtain ⟨w, hwd⟩ := hlow
  have hmem := Scheme.tryDecide_within hls hcms hcs hlaws trivial (lo := Z.lo) (k := Z.lo)
    (B := b + c) (N := decidable cfg Z.store.topRound - 1) le_rfl (by omega) (by omega)
    (fun m h1 h2 => ⟨w, by rwa [show m = Z.lo by omega]⟩) w hwd.toDecided
  have hempty := hSet.decided (show Z.lo < decidable cfg Z.store.topRound by omega)
  have heq : Scheme.tryDecide (S := cfg.slots) cfg.p cfg.σ Z.store.toRecord Z.store.view Z.lo
      (decidable cfg Z.store.topRound - 1) =
      Scheme.tryDecide cfg.p boundedSel U V Z.lo (decidable cfg Z.store.topRound - 1) := by
    rw [hσ]
    exact hva.tryDecide_eq cfg.p hw _ (Nat.zero_le _)
  change Scheme.tryDecide (S := cfg.slots) cfg.p cfg.σ (Z.store.window (cfg.slots.slotRound Z.lo))
    (Z.store.windowView (cfg.slots.slotRound Z.lo)) Z.lo
    (decidable cfg Z.store.topRound - 1) = [] at hempty
  rw [tryDecide_window cfg hσ hw, heq] at hempty
  rw [hempty] at hmem
  simp at hmem

/-- **Decision by a time bound**: from the synchronisation point, the
reliable nodes reach the last slot's decision round a timeout a round
(`produces`), and decide `A` after (`decides`). -/
theorem decidesBy {cfg : Config Validator BlockId Payload} {T : Finset Validator}
    {tr : Trace Validator BlockId Payload} {time : ℕ → ℕ} {gst D t₁ : ℕ}
    (hp : Produces cfg T tr time gst t₁) (hd : Decides cfg T tr time gst D t₁) :
    DecidesBy cfg T tr time gst D t₁ := by
  letI := cfg.slots
  intro b c n₀ s hc hspan hlead hn₀ hgs hall ht₁
  set N := cfg.slots.slotRound (b + c - 1) + (cfg.p.waveLength - 1) with hN
  have hn₀N : n₀ ≤ N := hn₀.trans ((cfg.slots.mono (by omega : b ≤ b + c - 1)).trans
    (Nat.le_add_right _ _))
  -- a round a timeout
  have key : ∀ k, n₀ + k ≤ N → ∀ v ∈ T,
      n₀ + k ≤ topAt cfg tr time v (s + D + ∑ r ∈ Finset.Ico n₀ (n₀ + k), cfg.timeout r) := by
    intro k
    induction k with
    | zero => intro _ v hv; simpa using (hall v hv).1
    | succ k ih =>
      intro hk v hv
      have hsum : ∑ r ∈ Finset.Ico n₀ (n₀ + (k + 1)), cfg.timeout r =
          ∑ r ∈ Finset.Ico n₀ (n₀ + k), cfg.timeout r + cfg.timeout (n₀ + k) :=
        Finset.sum_Ico_succ_top (show n₀ ≤ n₀ + k by omega) _
      have hsub : ∑ r ∈ Finset.Ico n₀ (n₀ + (k + 1)), cfg.timeout r ≤
          ∑ r ∈ Finset.Ico n₀ N, cfg.timeout r :=
        Finset.sum_le_sum_of_subset (Finset.Ico_subset_Ico_right hk)
      have := hp (s + D + ∑ r ∈ Finset.Ico n₀ (n₀ + k), cfg.timeout r) (n₀ + k) (by omega)
        (by omega) (ih (by omega)) v hv
      rw [hsum, ← Nat.add_assoc (s + D)]
      exact this
  have hall' := key (N - n₀) (by omega)
  rw [Nat.add_sub_cancel' hn₀N] at hall'
  exact hd b c n₀ s hc hspan hlead hn₀ hgs hall _ hall' ht₁

/-- **The reliable nodes produce rounds and decide.** -/
theorem holds : Statement := by
  intro Validator BlockId Payload _ _ _ cfg H T tr time gst Δ Δₛ t₁ hσ hadm hf hTH hqT hcT
    hq hid hto htime hinj hmono hdel htimer hsync hstart
  have harr := arrival_of_delivered hσ hadm hf htime hinj hTH hmono hdel hsync
  have hp := produces hσ hadm hf hTH hqT hto hq hid htime hinj hmono harr
    (TopTimerBy.of_fire hmono htimer.1) hstart
  have hd := decides hσ hadm hf hTH hqT hcT hq hid hto htime hinj hmono harr htimer.2
    (TimersFireFrom.of_fire htimer.1) hstart
  exact ⟨hp, hd, decidesBy hp hd⟩

end Live

end Node

end LeanDag
