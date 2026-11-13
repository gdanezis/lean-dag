import LeanDag.Scheme.AtomicBroadcast.Statement
import LeanDag.Scheme.Helpers.Deliver
import LeanDag.Scheme.Loop.Proof
import LeanDag.Scheme.Helpers.Validity
import LeanDag.Scheme.Reactive.Proof
import LeanDag.Steelhead.Helpers.Liveness
import LeanDag.Barnacle.Helpers.Skips
/-!
# Byzantine atomic broadcast — proof

The safety properties are the loop's prefix comparability and resumption
(`Loop.prefixComparable`, `Loop.resume`) carried through `deliverOf`,
which preserves prefixes and keeps one block per round and author
(`Helpers/Deliver.lean`). Agreement is eventual delivery among the
reliable validators: the view of one is eventually inside the view of
another, whose delivered sequence then extends the first one's.

Validity commits a slot whose leader block reaches the block, on the
author's own view, with every slot below decided; the loop then outputs
that slot (`Loop.outputComplete`) and agreement carries the delivery to
every reliable validator. Under partial synchrony the slot is one the
author leads past GST, certified by every reliable block
(`ReactiveRun.certifies`), and the slots below it are decided by the run
of reliably-led slots after it; its leader block reaches the author's
earlier blocks by self-reference. Under asynchrony a block of safe coins
commits a slot from round `r + 2`, whose leader block reaches every
reliable block of round `r + 1` by quorum intersection, and so the
author's on-time block; the draws with no such block are Steelhead's
count (`Steelhead.no_good_block_prob_le`).
-/

namespace LeanDag

namespace Scheme

namespace AtomicBroadcast

theorem grows : Grows := by
  intro Validator BlockId Payload _ _ _ P _ q _ honest f p σ S U V₁ V₂ N₁ N₂ ht hV hN
  exact deliverOf_prefix ⟨_, Loop.resume Validator BlockId Payload P q honest f p σ U V₁ V₂ 0 N₁ N₂
    ht hV hN⟩

theorem runGrows : RunGrows := by
  intro Validator BlockId Payload _ _ _ P _ q _ honest f p σ S U T N qp ap M ht v hv t t' htt
  exact grows Validator BlockId Payload P q honest f p σ U _ _ M M ht
    (ap.holds_mono v t t' htt) le_rfl

theorem integrity : Integrity := by
  intro Validator BlockId Payload _ _ _ P honest p σ S U V N r P_k
  refine length_filter_le_one (roundAuthor U) (deliverOf_nodup_roundAuthor _) _ ?_
  intro a c ha hc
  simp only [decide_eq_true_eq] at ha hc
  simp [roundAuthor, ha.1, ha.2, hc.1, hc.2]

theorem integritySD : IntegritySD := by
  intro Validator BlockId Payload _ _ _ P honest p σ S U V N
  exact ⟨deliverOf_nodup _, fun b hb => (mem_deliverOf hb).1⟩

/-- Two delivered sequences are prefix-comparable at the rows the
inequalities cover. -/
theorem deliverSeq_comparable {Validator BlockId Payload : Type} [Fintype Validator]
    [DecidableEq Validator] [LinearOrder BlockId] {P : Validity Validator BlockId Payload}
    [P.Mechanised] {q : ℕ} [P.Quorate q] {honest : Finset Validator} {f : ℕ} {p : Params}
    (σ : VoteSel Validator BlockId Payload P honest) [S : Slots Validator]
    (U : BlockRecord Validator BlockId Payload P honest) (V₁ V₂ : U.View) (N₁ N₂ : ℕ)
    (ht : p.Tolerates honest f q) :
    deliverSeq p σ U V₁ N₁ <+: deliverSeq p σ U V₂ N₂ ∨
      deliverSeq p σ U V₂ N₂ <+: deliverSeq p σ U V₁ N₁ :=
  (Loop.prefixComparable Validator BlockId Payload P q honest f p σ U V₁ V₂ 0 N₁ N₂ ht
    (Nat.zero_le _) (Nat.zero_le _)).imp deliverOf_prefix deliverOf_prefix

theorem totalOrder : TotalOrder := by
  intro Validator BlockId Payload _ _ _ P _ q _ honest f p σ S U V_i V_j N_i N_j x y ht h
  exact h.not_swap (deliverSeq_comparable σ U V_i V_j N_i N_j ht) (deliverOf_nodup _)
    (deliverOf_nodup _)

theorem totalOrderSD : TotalOrderSD := by
  intro Validator BlockId Payload _ _ _ P _ q _ honest f p σ S U V_i V_j N_i N_j x y ht h hy
  exact h.of_comparable (deliverSeq_comparable σ U V_i V_j N_i N_j ht) (deliverOf_nodup _) hy

theorem agreement : Agreement := by
  intro Validator BlockId Payload _ _ _ P _ q _ honest f p σ S U T N qp ap M ht P_i hi t b hb
    P_j hj
  obtain ⟨d, hd⟩ := ap.converges P_j hj P_i hi t
  refine ⟨t + d, fun t'' ht'' => ?_⟩
  have hsub : (ap.viewAt hi t).ids ⊆ (ap.viewAt hj t'').ids :=
    hd.trans (ap.holds_mono P_j _ _ ht'')
  exact (grows Validator BlockId Payload P q honest f p σ U _ _ M M ht hsub le_rfl).subset hb

/-- **One delivery spreads**: a block in a reliable validator's delivered
sequence at time `t` at every scan from `N₀` on is eventually delivered by
every reliable validator. -/
theorem delivers_of_mem {Validator BlockId Payload : Type} [Fintype Validator]
    [DecidableEq Validator] [LinearOrder BlockId] {P : Validity Validator BlockId Payload}
    [P.Mechanised] {q : ℕ} [P.Quorate q] {honest : Finset Validator} {f : ℕ} {p : Params}
    (σ : VoteSel Validator BlockId Payload P honest) [S : Slots Validator]
    {U : BlockRecord Validator BlockId Payload P honest} {T : Finset Validator} {N qp : ℕ}
    (ap : AsyncPace qp U T N) (ht : p.Tolerates honest f q) {v : Validator} (hv : v ∈ T)
    {t N₀ : ℕ} {m : BlockId} (h : ∀ M, N₀ ≤ M → m ∈ ap.deliverAt p σ hv M t) {w : Validator}
    (hw : w ∈ T) : ap.Delivers p σ hw m :=
  ⟨N₀, fun M hM => agreement Validator BlockId Payload P q honest f p σ U T N qp ap M ht v hv t m
    (h M hM) w hw⟩

attribute [local instance] noFaults in
/-- **A reliably led slot past GST commits** on every view holding the
reliable blocks, when its decision round lies within the run's waits. -/
theorem reliable_commits {Validator BlockId Payload : Type} [Fintype Validator]
    [DecidableEq Validator] [Nonempty Validator] [LinearOrder BlockId]
    {P : Validity Validator BlockId Payload} [P.Mechanised] {q : ℕ} [P.Quorate q]
    {honest : Finset Validator} {p : Params} (σ : VoteSel Validator BlockId Payload P honest)
    [S : Slots Validator] {U : BlockRecord Validator BlockId Payload P honest}
    {T : Finset Validator} {N R qr : ℕ} (rs : SchemeReactive qr p σ U T N) (hcf : p.CertFits qr)
    (hcm : p.commitThreshold ≤ T.card) (hTh : T ⊆ honest) (hqr : qr ≤ T.card)
    (hgst : rs.gst ≤ R) (htime : ∀ n, R ≤ n → 2 * rs.delay + rs.proc ≤ rs.timeout n) :
    ∀ j, S.leader j ∈ T → R ≤ S.slotRound j →
      S.slotRound j + (p.waveLength - 1) ≤ rs.waits →
      ∃ L, IsLeaderBlock U j L ∧ ∀ V : U.View,
        (∀ b ∈ U.ids, (U.block b).creator ∈ T → b ∈ V.ids) →
        (schemeAnchored p σ).Decided U V j (some L) := by
  intro j hjT hRj hjN
  have hW := rs.waits_le
  obtain ⟨L, hL, hLc, hLr⟩ := rs.toAsyncPace.populated hqr (S.slotRound j) (by omega)
    (S.leader j) hjT
  have hLB : IsLeaderBlock U j L := ⟨hL, hLr, hLc⟩
  refine ⟨L, hLB, fun V hV => decided_of_certified σ hcm
    (rs.toAsyncPace.populated hqr _ (by omega)) hLB ?_ hV⟩
  intro C hC hCT hCr
  exact ReactiveRun.certifies Validator BlockId Payload P honest p σ U T N R qr rs j L hcf hTh hqr
    hgst htime hRj hjN hjT hLB _ hCT C hC rfl hCr

theorem validityPS : ValidityPS := by
  intro Validator BlockId Payload _ _ _ _ P _ q _ honest f p σ S U T N R qr d rs ht hcf hcm hTh
    hqr hgst htime hP hd hspan P_k m k b₀ hk hm hmc hlead hRk hmk hkb hrun hN P_j hj
  set ap := rs.toAsyncPace
  obtain ⟨t, hdel⟩ := ap.delivered
  have hW := rs.waits_le
  have hcommit := reliable_commits σ rs hcf hcm hTh hqr hgst htime
  have hlast : ∀ j, j ≤ b₀ + d - 1 → S.slotRound j + (p.waveLength - 1) ≤ rs.waits :=
    fun j hj => by
    have := S.mono hj; omega
  set V := ap.viewAt hk t
  have hV : ∀ b ∈ U.ids, (U.block b).creator ∈ T → b ∈ V.ids := fun b hb hbT =>
    hdel t le_rfl P_k hk b hb hbT
  have hbelow : ∀ i, i < b₀ → ∃ v, (schemeAnchored p σ).Decided U V i v :=
    AnchoredRule.decided_below_of_run
      (fun _ h => AnchoredRule.exists_least_of_lt (fun _ _ => Iff.rfl) h) hd hspan
      (b := b₀) (Led := fun j => S.leader j ∈ T) hrun fun j h1 h2 hjT => by
        have := S.mono (show k ≤ j by omega)
        obtain ⟨L, -, hL⟩ := hcommit j hjT (by omega) (hlast j h2)
        exact ⟨L, hL V hV⟩
  obtain ⟨L, hLB, hL⟩ := hcommit k (hlead ▸ hk) hRk (hlast k (by omega))
  have hmh : (U.block m).creator ∈ honest := by rw [hmc]; exact hTh hk
  have hreach : Reaches U L m := reaches_own hP hm hLB.1 hmh (hLB.2.2.trans (hlead.trans hmc.symm))
    (by rw [hLB.2.1]; exact hmk)
  obtain ⟨N₀, hN₀⟩ := mem_deliverSeq_of_decided σ ht (fun i hi => hbelow i (by omega)) (hL V hV)
    hm hreach hmh
  exact delivers_of_mem σ ap ht hk (t := t) hN₀ hj

theorem livenessPS : LivenessPS := by
  intro Validator BlockId Payload _ _ _ _ P _ q _ honest f p σ S U T N R qr d rs ht hcf hcm hTh
    hqr hgst htime hP hd hspan P_k hk m k b₀ hm hmc hlead hRk hmk hkb hrun hN
  exact validityPS Validator BlockId Payload P q honest f p σ U T N R qr d rs ht hcf hcm hTh hqr
    hgst htime hP hd hspan P_k m k b₀ hk hm hmc hlead hRk hmk hkb hrun hN P_k hk

/-- **Round-robin repeats every rotation**: a run of `c` reliably-led
slots exists within a rotation past any slot. -/
theorem roundRobin_run_within {n : ℕ} [NeZero n] {T : Finset (Fin n)} {c : ℕ}
    (h : c * (n - T.card) < n) (a : ℕ) :
    ∃ b, a ≤ b ∧ b < a + n ∧ ∀ i, i < c → (roundRobinSlots n).leader (b + i) ∈ T := by
  have hn := NeZero.pos n
  obtain ⟨k', hk', hrun⟩ := Steelhead.roundRobin_fairRun hn h a
  refine ⟨a + (k' - a) % n, by omega, by have := Nat.mod_lt (k' - a) hn; omega, fun i hi => ?_⟩
  have hmod : (a + (k' - a) % n + i) % n = (k' + i) % n := by
    have := ((Nat.mod_modEq (k' - a) n).add_left a).add_right i
    rw [show a + (k' - a) = k' by omega] at this
    exact this
  have := hrun i hi
  have heq : (roundRobinSlots n).leader (a + (k' - a) % n + i) =
      (⟨(k' + i) % n, Nat.mod_lt _ hn⟩ : Fin n) := Fin.ext hmod
  rw [heq]
  exact this

theorem validityRoundRobin : ValidityRoundRobin := by
  intro n _ BlockId Payload _ P _ q _ honest f p σ U T N R qr rs ht hcf hcm hTh hqr hgst htime hP
    hfair P_k m hk hm hmc hN P_j hj
  letI S : Slots (Fin n) := roundRobinSlots n
  have hn := NeZero.pos n
  have hw := hcf.1
  set K := max R (U.block m).round
  have hkl : S.leader (n * K + P_k.val) = P_k := by
    apply Fin.ext
    change (n * K + P_k.val) % n = P_k.val
    rw [Nat.mul_add_mod, Nat.mod_eq_of_lt P_k.isLt]
  have hKk : K ≤ n * K + P_k.val := le_trans (Nat.le_mul_of_pos_left K hn) (Nat.le_add_right _ _)
  obtain ⟨b₀, hb₁, hb₂, hrun⟩ := roundRobin_run_within hfair (n * K + P_k.val + 1)
  have hspan : (schemeAnchored p σ).SpansEligible (S := S) p.waveLength := by
    have := AnchoredRule.spansEligible_of_identity (R := schemeAnchored p σ) (S := S)
      (fun _ => rfl) (w := p.waveLength - 1) (fun _ => le_rfl)
    rwa [show p.waveLength - 1 + 1 = p.waveLength by omega] at this
  have hPk := P_k.isLt
  exact validityPS (Fin n) BlockId Payload P q honest f p σ U T N R qr p.waveLength rs ht hcf hcm
    hTh hqr hgst htime hP (by omega) hspan P_k m (n * K + P_k.val) b₀ hk hm hmc hkl
    (le_trans (le_max_left _ _) hKk) (le_trans (le_max_right _ _) hKk) (by omega) hrun
    (by change b₀ + p.waveLength - 1 + (p.waveLength - 1) ≤ rs.waits
        have : n * (K + 2) = n * K + 2 * n := by ring
        omega) P_j hj

theorem validityRoundRobinSilent : ValidityRoundRobinSilent := by
  intro n _ BlockId Payload _ P _ q _ honest f p σ U T Z N R qr fb rs ht hcf hcm hsk hv hTh hqr
    hgst htime hP hsil hZ hfb P_k m hk hm hmc hN P_j hj
  letI S : Slots (Fin n) := roundRobinSlots n
  have hn := NeZero.pos n
  have hw := hcf.1
  have hTn : T.card ≤ n := by simpa using Finset.card_le_univ T
  set g := p.waveLength
  set K := max R (U.block m).round
  set k := n * K + P_k.val
  have hkl : S.leader k = P_k := by
    apply Fin.ext
    change (n * K + P_k.val) % n = P_k.val
    rw [Nat.mul_add_mod, Nat.mod_eq_of_lt P_k.isLt]
  have hKk : K ≤ k := le_trans (Nat.le_mul_of_pos_left K hn) (Nat.le_add_right _ _)
  have hPk := P_k.isLt
  -- a window of `g` slots above `k`, its last leader in `T`, the others in `T ∪ Z`
  obtain ⟨x, hxT, hxD⟩ := Barnacle.exists_run_perm_roundRobin hn (Equiv.refl _) T (T ∪ Z)
    (n - T.card) fb g (k + g) (by omega) (by omega) hZ (by omega)
  have hx := x.isLt
  set t := k + g + x
  have hleadT : S.leader t ∈ T := hxT
  have hleadD : ∀ j, t + 1 - g ≤ j → j < t → S.leader j ∈ T ∪ Z := fun j h1 h2 => by
    have := hxD ⟨t - 1 - j, by omega⟩
    rwa [show k + g + ↑x - ((t - 1 - j : ℕ) + 1) = j by omega] at this
  set ap := rs.toAsyncPace
  obtain ⟨t₀, hdel⟩ := ap.delivered
  have hW := rs.waits_le
  have hround : ∀ j, S.slotRound j = j := fun _ => rfl
  have hlast : ∀ j, j ≤ t → S.slotRound j + (g - 1) ≤ rs.waits := fun j hj => by
    rw [hround]
    have : n * (K + 2) = n * K + 2 * n := by ring
    omega
  have hcommit := reliable_commits σ rs hcf hcm hTh hqr hgst htime
  set V := ap.viewAt hk t₀
  have hV : ∀ b ∈ U.ids, (U.block b).creator ∈ T → b ∈ V.ids := fun b hb hbT =>
    hdel t₀ le_rfl P_k hk b hb hbT
  -- a silent leader's slot is skipped directly
  have hskip : ∀ j, R ≤ j → j + 1 ≤ N → S.leader j ∈ Z →
      (schemeAnchored p σ).Decided U V j none := by
    intro j hRj hjN hjZ
    refine Scheme.skipsUnsupported (σ := σ) hv S U V T j hsk (fun v hvT => ?_)
      (fun c _ _ _ L hL _ => ?_)
    · obtain ⟨b, hb, hbc, hbr⟩ := ap.populated hqr (S.slotRound j + 1) (by rw [hround]; omega)
        v hvT
      exact ⟨b, hV b hb (by rw [hbc]; exact hvT), hbc, hbr⟩
    · obtain ⟨hLU, hLr, hLc⟩ := hL
      have hLc' : (U.block L).creator = S.leader j := hLc
      have hLr' : (U.block L).round = S.slotRound j := hLr
      have := hsil L hLU (by rw [hLc']; exact hjZ)
      rw [hLr', hround] at this
      omega
  have hspan : (schemeAnchored p σ).SpansEligible (S := S) g := by
    have := AnchoredRule.spansEligible_of_identity (R := schemeAnchored p σ) (S := S)
      (fun _ => rfl) (w := g - 1) (fun _ => le_rfl)
    rwa [show g - 1 + 1 = g by omega] at this
  have hbelow : ∀ i, i < t + 1 - g → ∃ v, (schemeAnchored p σ).Decided U V i v := by
    refine AnchoredRule.decided_below_of_window
      (fun _ h => AnchoredRule.exists_least_of_lt (fun _ _ => Iff.rfl) h) (b := t + 1 - g)
      (n := t) (by omega) (fun i hi => by
        have := hspan (t + 1 - g) i hi
        rwa [show t + 1 - g + g - 1 = t by omega] at this) ?_ (fun j h1 h2 => ?_)
    · obtain ⟨L, -, hL⟩ := hcommit t hleadT (by rw [hround]; omega) (hlast t le_rfl)
      exact ⟨L, hL V hV⟩
    · rcases Nat.lt_or_eq_of_le h2 with hlt | rfl
      · rcases Finset.mem_union.mp (hleadD j h1 hlt) with hjT | hjZ
        · obtain ⟨L, -, hL⟩ := hcommit j hjT (by rw [hround]; omega) (hlast j h2)
          exact ⟨some L, hL V hV⟩
        · exact ⟨none, hskip j (by omega) (by have := hlast j h2; rw [hround] at this; omega)
            hjZ⟩
      · obtain ⟨L, -, hL⟩ := hcommit _ hleadT (by rw [hround]; omega) (hlast _ le_rfl)
        exact ⟨some L, hL V hV⟩
  obtain ⟨L, hLB, hL⟩ := hcommit k (hkl ▸ hk) (by rw [hround]; omega) (hlast k (by omega))
  have hmh : (U.block m).creator ∈ honest := by rw [hmc]; exact hTh hk
  have hmk : (U.block m).round ≤ S.slotRound k := by
    rw [hround]; exact le_trans (le_max_right _ _) hKk
  have hreach : Reaches U L m := reaches_own hP hm hLB.1 hmh (hLB.2.2.trans (hkl.trans hmc.symm))
    (by rw [hLB.2.1]; exact hmk)
  obtain ⟨N₀, hN₀⟩ := mem_deliverSeq_of_decided σ ht (fun i hi => hbelow i (by omega)) (hL V hV)
    hm hreach hmh
  exact delivers_of_mem σ ap ht hk (t := t₀) hN₀ hj

theorem validityAsync : ValidityAsync := by
  intro Validator BlockId Payload _ _ _ _ P _ q _ honest f p σ U T N qp ap S₀ hS dflt s₀ d M c
    ht hcf hcm hqp hTh hqT hd hspan hN hfloor hP P_k m x r hk hm hmc hmr hx hxc hxr hon hr2
  letI : Faults Validator := noFaults
  set G : Fin M → Fin d → Finset Validator :=
    fun j i => safeAt p U (S₀.slotRound (s₀ + j * d + i))
  have hG : ∀ j i, c ≤ (G j i).card := fun j i => by
    have hj := j.isLt
    have hi := i.isLt
    have : (j : ℕ) * d + i < M * d := by
      have := Nat.mul_le_mul_right d (show (j : ℕ) + 1 ≤ M by omega)
      rw [Nat.add_mul, one_mul] at this; omega
    exact hfloor _ (by omega) (by omega)
  have hmh : (U.block m).creator ∈ honest := by rw [hmc]; exact hTh hk
  have hxm : Reaches U x m := reaches_own hP hm hx hmh (hxc.trans hmc.symm) (by rw [hxr]; exact hmr)
  have hsub : {g : Fin M → Fin d → Validator | ¬ ∀ (P_j : Validator) (hj : P_j ∈ T),
        ap.Delivers (S := coinSlots S₀ hS (Steelhead.coinOfBlocksFrom s₀ g dflt)) p σ hj m} ⊆
      {g | ∀ j ∈ (Finset.univ : Finset (Fin M)), ∃ i, g j i ∉ G j i} := by
    intro g hg j _
    by_contra hall
    push Not at hall
    apply hg
    intro P_j hj
    letI S' := coinSlots S₀ hS (Steelhead.coinOfBlocksFrom s₀ g dflt)
    obtain ⟨L, hLB, t, hev⟩ := eventually_committed_of_good_block σ ap S₀ hS dflt g hcf hcm hqp hd
      hspan hN j hall
    obtain ⟨hdec, hall'⟩ := hev t le_rfl P_k hk
    have hLr : r + 2 ≤ (U.block L).round := by
      rw [hLB.2.1]
      exact le_trans hr2 (S₀.mono (by omega))
    have hreach : Reaches U L m :=
      (reaches_of_onTime hqT (x := x) (r := r)
        (fun c hc hcT hcr => Reaches.single (hon c hc hcT hcr))
        L hLB.1 hLr).trans hxm
    obtain ⟨N₀, hN₀⟩ := mem_deliverSeq_of_decided σ ht hall' hdec hm hreach hmh
    exact delivers_of_mem σ ap ht hk (t := t) hN₀ hj
  refine le_trans (MeasureTheory.measure_mono hsub) ?_
  have := Steelhead.no_good_block_prob_le (Finset.univ : Finset (Fin M)) G hG
  rwa [Finset.card_univ, Fintype.card_fin] at this

theorem livenessAsync : LivenessAsync := by
  intro Validator BlockId Payload _ _ _ _ P _ q _ honest f p σ U T N qp ap S₀ hS dflt s₀ d M c
    ht hcf hcm hqp hTh hqT hd hspan hN hfloor hP P_k hk m x r hm hmc hmr hx hxc hxr hon hr2
  refine le_trans (MeasureTheory.measure_mono ?_) (validityAsync Validator BlockId Payload P q
    honest f p σ U T N qp ap S₀ hS dflt s₀ d M c ht hcf hcm hqp hTh hqT hd hspan hN hfloor hP P_k m
    x r hk hm hmc hmr hx hxc hxr hon hr2)
  intro g hg hall
  exact hg (hall P_k hk)

theorem holds : Statement :=
  ⟨grows, runGrows, integrity, integritySD, totalOrder, totalOrderSD, agreement, validityPS,
    livenessPS, validityRoundRobin, validityRoundRobinSilent, validityAsync, livenessAsync⟩

end AtomicBroadcast

end Scheme

end LeanDag
