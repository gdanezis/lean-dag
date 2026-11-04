import LeanDag.Node.Helpers.Jump
/-!
# An infinite run, read through its prefixes

`docs/dos-bounds.md` Phase 3.2 item 4.3. A node's state after `k` events is
the same on every prefix of a run that holds them (`stateBefore_prefixOf`),
so its top and next undecided slot only rise along the run
(`rises_prefixOf`). Over a run meeting the assumptions of `Live.Eventually`
on its prefixes (`RunMeets`), every honest node starts (`started_run`), and
once an honest node is past a slot every honest node is, each slot taking a
request for its proof and a reply (`moves_up`, `catchup_run`).
-/

namespace LeanDag

namespace Node

open Live

variable {Validator BlockId Payload : Type} [Fintype Validator] [DecidableEq Validator]
variable [LinearOrder BlockId]
variable {cfg : Config Validator BlockId Payload}
  {ev : ℕ → Validator × Input Validator BlockId Payload}

omit [Fintype Validator] [DecidableEq Validator] [LinearOrder BlockId] in
theorem prefixOf_length (N : ℕ) : (prefixOf ev N).length = N := by simp [prefixOf]

omit [Fintype Validator] [DecidableEq Validator] [LinearOrder BlockId] in
theorem prefixOf_getElem? {N i : ℕ} (h : i < N) : (prefixOf ev N)[i]? = some (ev i) := by
  simp [prefixOf, h]

omit [Fintype Validator] [DecidableEq Validator] [LinearOrder BlockId] in
theorem take_prefixOf {k N : ℕ} (h : k ≤ N) : (prefixOf ev N).take k = prefixOf ev k := by
  unfold prefixOf
  rw [← List.map_take, List.take_range, min_eq_left h]

/-- **A node's state after `k` events is that of every prefix holding
them.** -/
theorem stateBefore_prefixOf {k N : ℕ} (h : k ≤ N) (v : Validator) :
    stateBefore cfg (prefixOf ev N) k v = stateBefore cfg (prefixOf ev k) k v := by
  unfold stateBefore inputsBefore
  rw [take_prefixOf h, List.take_of_length_le (by rw [prefixOf_length])]

/-- **Along a run, a node's top and next undecided slot only rise.** -/
theorem rises_prefixOf {n n' : ℕ} (h : n ≤ n') (v : Validator) :
    Rises (stateBefore cfg (prefixOf ev n) n v) (stateBefore cfg (prefixOf ev n') n' v) := by
  have h₁ := rises_before (cfg := cfg) (tr := prefixOf ev n') v h
  have h₂ := stateBefore_prefixOf (cfg := cfg) (ev := ev) h v
  rw [h₂] at h₁
  exact h₁

/-- **A bounded rising sequence settles.** -/
theorem settles {f : ℕ → ℕ} (hf : Monotone f) {K : ℕ} (hK : ∀ n, f n ≤ K) :
    ∃ n₀, ∀ n, n₀ ≤ n → f n = f n₀ := by
  suffices h : ∀ d m, K - f m ≤ d → ∃ n₀, ∀ n, n₀ ≤ n → f n = f n₀ from
    h K 0 (Nat.sub_le _ _)
  intro d
  induction d with
  | zero =>
    intro m hm
    exact ⟨m, fun n hn => le_antisymm (by have := hK n; omega) (hf hn)⟩
  | succ d ih =>
    intro m hm
    by_cases h : ∀ n, m ≤ n → f n = f m
    · exact ⟨m, h⟩
    · push Not at h
      obtain ⟨n, hmn, hne⟩ := h
      have : f m < f n := lt_of_le_of_ne (hf hmn) (Ne.symm hne)
      exact ih n (by have := hK n; omega)

omit [Fintype Validator] [DecidableEq Validator] [LinearOrder BlockId] in
/-- **A property rising along `ℕ` that each node of a finite set reaches,
all reach at once.** -/
theorem exists_forall_of_mono {P : Validator → ℕ → Prop}
    (hP : ∀ u n n', n ≤ n' → P u n → P u n') (H : Finset Validator)
    (h : ∀ u ∈ H, ∃ n, P u n) : ∃ n, ∀ u ∈ H, P u n := by
  classical
  induction H using Finset.induction_on with
  | empty => exact ⟨0, fun u hu => absurd hu (Finset.notMem_empty u)⟩
  | insert a s _ ih =>
    obtain ⟨na, hna⟩ := h a (Finset.mem_insert_self a s)
    obtain ⟨ns, hns⟩ := ih fun u hu => h u (Finset.mem_insert_of_mem hu)
    refine ⟨max na ns, fun u hu => ?_⟩
    rcases Finset.mem_insert.mp hu with rfl | hu
    · exact hP _ _ _ (le_max_left _ _) hna
    · exact hP _ _ _ (le_max_right _ _) (hns u hu)

omit [Fintype Validator] [DecidableEq Validator] [LinearOrder BlockId] in
/-- **The events by a time before a prefix's end are those of every longer
prefix.** -/
theorem eventsBy_prefixOf {time : ℕ → ℕ} (hmono : Monotone time) {N N' T : ℕ}
    (hT : T < time N) (hN : N ≤ N') :
    eventsBy (prefixOf ev N') time T = eventsBy (prefixOf ev N) time T := by
  have hm : ∀ M, TimeMono (prefixOf ev M) time := fun _ _ _ hij _ => hmono hij
  have h₁ : eventsBy (prefixOf ev N') time T ≤ N := by
    by_contra h
    have hl := eventsBy_le_length (tr := prefixOf ev N') (time := time) T
    rw [prefixOf_length] at hl
    have := (lt_eventsBy (t := T) (hm N') (show N < (prefixOf ev N').length by
      rw [prefixOf_length]; omega)).mp (by omega)
    omega
  have h₂ : eventsBy (prefixOf ev N) time T ≤ N := by
    have := eventsBy_le_length (tr := prefixOf ev N) (time := time) T
    rwa [prefixOf_length] at this
  have hiff : ∀ i < N, i < eventsBy (prefixOf ev N') time T ↔ i < eventsBy (prefixOf ev N) time T :=
    fun i hi => (lt_eventsBy (hm N') (by rw [prefixOf_length]; omega)).trans
      (lt_eventsBy (hm N) (by rw [prefixOf_length]; omega)).symm
  rcases lt_trichotomy (eventsBy (prefixOf ev N') time T) (eventsBy (prefixOf ev N) time T)
    with h | h | h
  · exact absurd ((hiff _ (by omega)).mpr h) (lt_irrefl _)
  · exact h
  · exact absurd ((hiff _ (by omega)).mp h) (lt_irrefl _)

/-- **A node's state at a time before a prefix's end is its state on every
longer prefix.** -/
theorem stateAt_prefixOf {time : ℕ → ℕ} (hmono : Monotone time) {N N' T : ℕ}
    (hT : T < time N) (hN : N ≤ N') (v : Validator) :
    stateAt cfg (prefixOf ev N') time v T = stateAt cfg (prefixOf ev N) time v T := by
  unfold stateAt
  rw [eventsBy_prefixOf hmono hT hN]
  have h₂ : eventsBy (prefixOf ev N) time T ≤ N := by
    have := eventsBy_le_length (tr := prefixOf ev N) (time := time) T
    rwa [prefixOf_length] at this
  rw [stateBefore_prefixOf (h₂.trans hN), stateBefore_prefixOf h₂]

variable (cfg) in
/-- **A run meeting the assumptions of `Live.Eventually`** on its prefixes. -/
structure RunMeets (H : Finset Validator) (ev : ℕ → Validator × Input Validator BlockId Payload)
    (time : ℕ → ℕ) (gst Δ Δₛ : ℕ) (D : Finset Validator) (nE : ℕ) : Prop where
  mono : Monotone time
  unbounded : ∀ t, ∃ N, t < time N
  timeless : ∀ N, Converge.TimelyAuthentic cfg H (prefixOf ev N) ∧
    Converge.HashInjective cfg H (prefixOf ev N) ∧
    Converge.EvidenceAuthentic cfg H (prefixOf ev N) ∧ Spread cfg H (prefixOf ev N) D nE ∧
    TimersAfterSet cfg H (prefixOf ev N) time
  timed : ∀ N t₁, t₁ < time N → DeliveredWithin cfg H (prefixOf ev N) time gst Δ t₁ ∧
    TimersFire cfg H (prefixOf ev N) time t₁ ∧ SyncedHeld cfg H (prefixOf ev N) time gst Δₛ t₁ ∧
    UpFrom H (prefixOf ev N) time 0 t₁
  started : ∀ N, gst < time N → StartedBy H (prefixOf ev N) time gst ∧
    ∀ v ∈ H, max 1 nE ≤ topAt cfg (prefixOf ev N) time v gst

section Run

variable {H : Finset Validator} {time : ℕ → ℕ} {gst Δ Δₛ : ℕ} {D : Finset Validator} {nE : ℕ}

omit [Fintype Validator] [DecidableEq Validator] [LinearOrder BlockId] in
theorem timeMono_prefixOf (hmono : Monotone time) (N : ℕ) : TimeMono (prefixOf ev N) time :=
  fun _ _ hij _ => hmono hij

omit [Fintype Validator] [DecidableEq Validator] [LinearOrder BlockId] in
/-- **The events of a prefix by a time before its end are those of the run.** -/
theorem lt_of_time_lt (hmono : Monotone time) {N i : ℕ} {t : ℕ} (hN : t < time N)
    (hi : time i ≤ t) : i < N := by
  by_contra h
  have := hmono (show N ≤ i by omega)
  omega

/-- **Every honest node starts**: past the event that starts it, its top is
set. -/
theorem started_run (hrun : RunMeets cfg H ev time gst Δ Δₛ D nE) (hadm : cfg.Admissible)
    (hfa : cfg.Faithful) (hid : Function.Injective cfg.idOf) {v : Validator} (hv : v ∈ H) :
    ∃ n₀, ∀ n, n₀ ≤ n → (stateBefore cfg (prefixOf ev n) n v).top.isSome := by
  obtain ⟨N, hN⟩ := hrun.unbounded gst
  obtain ⟨st, hst, hstg⟩ := (hrun.started N hN).1 v hv
  have hstN : st < N := (List.getElem?_eq_some_iff.mp hst).1.trans_eq (prefixOf_length N)
  have h₁ := started_after hadm hfa hid (hrun.timeless N).1 hv hst
  rw [stateBefore_prefixOf hstN] at h₁
  exact ⟨st + 1, fun n hn => (rises_prefixOf hn v).2.1 h₁⟩

/-- **Along a run, once an honest node is past slot `k`, every honest node
is**, at a node that drops: from an event at which the node has started,
each slot takes a request for its proof and a reply (`moves_up`). -/
theorem catchup_run (hrun : RunMeets cfg H ev time gst Δ Δₛ D nE) (hσ : cfg.σ = boundedSel)
    (hadm : cfg.Admissible) (hfa : cfg.Faithful) (hf : Hᶜ.card ≤ cfg.f)
    (hid : Function.Injective cfg.idOf) (hdr : cfg.drops = true) {u v : Validator}
    (hu : u ∈ H) (hv : v ∈ H) {k n : ℕ} (hk : k < (stateBefore cfg (prefixOf ev n) n v).lo) :
    ∃ n', k < (stateBefore cfg (prefixOf ev n') n' u).lo := by
  haveI : Validity.Quorate (ValidAt (Validator := Validator) (BlockId := BlockId)
      (Payload := Payload) cfg.q Clause.none) cfg.q :=
    Validity.Quorate.of_validAt hadm.2.2.2.1 fun _ _ => Iff.rfl
  have htol : cfg.p.Tolerates H cfg.f cfg.q := ⟨hf, hadm.2.2.2.2, hadm.1⟩
  have hw : 2 ≤ cfg.p.waveLength := by
    rcases htol.2.2 with ⟨-, hw, -⟩ | ⟨-, hw, -⟩ | ⟨-, hw, -⟩ | ⟨-, hw, -⟩ <;> omega
  obtain ⟨hl, hcm, hcv, -⟩ := Scheme.coveredLaws (boundedSel (P := ValidAt
    (Validator := Validator) (BlockId := BlockId) (Payload := Payload) cfg.q Clause.none)
    (honest := H)) htol
  by_cases huv : v = u
  · subst huv; exact ⟨n, hk⟩
  obtain ⟨n₀, hn₀⟩ := started_run hrun hadm hfa hid hu
  suffices h : ∀ g E, max n n₀ ≤ E →
      k + 1 - (stateBefore cfg (prefixOf ev E) E u).lo = g →
      ∃ n', k < (stateBefore cfg (prefixOf ev n') n' u).lo from h _ _ le_rfl rfl
  intro g
  induction g using Nat.strong_induction_on with
  | _ g ih =>
  intro E hE hg
  by_cases hkE : k < (stateBefore cfg (prefixOf ev E) E u).lo
  · exact ⟨E, hkE⟩
  obtain ⟨m, hm⟩ := Option.isSome_iff_exists.mp (hn₀ E (le_of_max_le_right hE))
  obtain ⟨N, hN⟩ := hrun.unbounded (max (time E + askDelay cfg k m) gst + 2 * Δ)
  have hEN : E < N := lt_of_time_lt hrun.mono hN (by omega)
  obtain ⟨htime, -, hev, -, -⟩ := hrun.timeless N
  obtain ⟨hdel, hfire, -, hup⟩ := hrun.timed N _ hN
  have hvk : k < (stateBefore cfg (prefixOf ev N) E v).lo := by
    rw [stateBefore_prefixOf hEN.le]
    exact lt_of_lt_of_le hk (rises_prefixOf (le_of_max_le_left hE) v).2.2
  obtain ⟨j, hEj, hjN, -, hj⟩ := moves_up hσ hw hl hcm hcv hid hdr htime hev
    (Finset.Subset.refl H) (timeMono_prefixOf hrun.mono N) hdel hup
    (fun i w inp hi hw' r a ha ht _ => hfire i w inp hi hw' r a ha ht) hu hv huv
    (by rw [stateBefore_prefixOf hEN.le]; exact hm)
    (by rw [stateBefore_prefixOf hEN.le]; omega) hvk (fun a ha _ => hrun.mono ha.le) le_rfl
  rw [prefixOf_length] at hjN
  rw [stateBefore_prefixOf hEN.le, stateBefore_prefixOf (show j + 1 ≤ N by omega)] at hj
  exact ih _ (by omega) (j + 1) (by omega) rfl

/-- **If no honest node passes slot `K`, the honest nodes' next undecided
slots settle at one slot `L`**, at a node that drops: the highest settles,
and every honest node catches up with it (`catchup_run`). -/
theorem stable_run (hrun : RunMeets cfg H ev time gst Δ Δₛ D nE) (hσ : cfg.σ = boundedSel)
    (hadm : cfg.Admissible) (hfa : cfg.Faithful) (hf : Hᶜ.card ≤ cfg.f)
    (hid : Function.Injective cfg.idOf) (hdr : cfg.drops = true) (hH : H.Nonempty) {K : ℕ}
    (hK : ∀ n, ∀ v ∈ H, (stateBefore cfg (prefixOf ev n) n v).lo ≤ K) :
    ∃ n₁ L, (∀ v ∈ H, ∀ n, (stateBefore cfg (prefixOf ev n) n v).lo ≤ L) ∧
      ∀ v ∈ H, ∀ n, n₁ ≤ n → (stateBefore cfg (prefixOf ev n) n v).lo = L := by
  set F : ℕ → ℕ := fun n => H.sup fun v => (stateBefore cfg (prefixOf ev n) n v).lo with hF
  have hFm : Monotone F := fun n n' h => Finset.sup_mono_fun fun v _ => (rises_prefixOf h v).2.2
  obtain ⟨n₀, hn₀⟩ := settles hFm (K := K) fun n => Finset.sup_le fun v hv => hK n v hv
  have hle : ∀ v ∈ H, ∀ n, (stateBefore cfg (prefixOf ev n) n v).lo ≤ F n₀ := fun v hv n => by
    have h₁ := (rises_prefixOf (cfg := cfg) (ev := ev) (le_max_left n n₀) v).2.2.trans
      (Finset.le_sup (f := fun v => (stateBefore cfg (prefixOf ev (max n n₀)) (max n n₀) v).lo) hv)
    have h₂ := hn₀ _ (le_max_right n n₀)
    simp only [hF] at h₂
    rw [h₂] at h₁
    exact h₁
  rcases Nat.eq_zero_or_pos (F n₀) with hL0 | hLpos
  · exact ⟨0, F n₀, hle, fun v hv n _ => le_antisymm (hle v hv n) (by omega)⟩
  obtain ⟨v₀, hv₀, hv₀L⟩ := Finset.exists_mem_eq_sup H hH
    (fun v => (stateBefore cfg (prefixOf ev n₀) n₀ v).lo)
  obtain ⟨n, hn⟩ := exists_forall_of_mono
    (P := fun u n => F n₀ - 1 < (stateBefore cfg (prefixOf ev n) n u).lo)
    (fun u n n' h hp => lt_of_lt_of_le hp (rises_prefixOf h u).2.2) H
    (fun u hu => catchup_run hrun hσ hadm hfa hf hid hdr hu hv₀ (k := F n₀ - 1) (n := n₀)
      (by simp only [hF] at hLpos ⊢; rw [hv₀L] at hLpos ⊢; omega))
  exact ⟨n, F n₀, hle, fun v hv n' hn' => le_antisymm (hle v hv n')
    (by have := lt_of_lt_of_le (hn v hv) (rises_prefixOf hn' v).2.2; omega)⟩

/-- **When every honest node's next undecided slot stays at `L`, from some
event on every honest node is at the floor at `L` or above**, at a node that
drops: it has started, is above `nE` past GST, and is at or above its floor
(`floor_le_top_before`). -/
theorem floor_run [Infinite BlockId] (hrun : RunMeets cfg H ev time gst Δ Δₛ D nE)
    (hσ : cfg.σ = boundedSel) (hadm : cfg.Admissible) (hfa : cfg.Faithful)
    (hf : Hᶜ.card ≤ cfg.f) (hid : Function.Injective cfg.idOf) (hq : 2 ≤ cfg.q)
    (hdr : cfg.drops = true) (hsk : cfg.f < cfg.p.skipThreshold)
    (hcm : cfg.f < cfg.p.commitThreshold) {L n₁ : ℕ}
    (hle : ∀ v ∈ H, ∀ n, (stateBefore cfg (prefixOf ev n) n v).lo ≤ L)
    (heq : ∀ v ∈ H, ∀ n, n₁ ≤ n → (stateBefore cfg (prefixOf ev n) n v).lo = L) :
    ∃ n₂, n₁ ≤ n₂ ∧ ∀ v ∈ H, ∀ n, n₂ ≤ n →
      (stateBefore cfg (prefixOf ev n) n v).top.isSome ∧
        floorAt cfg L ≤ (stateBefore cfg (prefixOf ev n) n v).top.getD 0 := by
  obtain ⟨Ng, hNg⟩ := hrun.unbounded gst
  have hegN : eventsBy (prefixOf ev Ng) time gst ≤ Ng := by
    have := eventsBy_le_length (tr := prefixOf ev Ng) (time := time) gst
    rwa [prefixOf_length] at this
  set eg := eventsBy (prefixOf ev Ng) time gst with heg
  obtain ⟨ns, hns⟩ := exists_forall_of_mono
    (P := fun u n => (stateBefore cfg (prefixOf ev n) n u).top.isSome)
    (fun u n n' h hp => (rises_prefixOf h u).2.1 hp) H
    (fun u hu => by
      obtain ⟨n₀, h⟩ := started_run hrun hadm hfa hid hu
      exact ⟨n₀, h n₀ le_rfl⟩)
  refine ⟨max n₁ (max ns eg), le_max_left _ _, fun v hv n hn => ?_⟩
  have hs : (stateBefore cfg (prefixOf ev n) n v).top.isSome :=
    (rises_prefixOf (show ns ≤ n by omega) v).2.1 (hns v hv)
  refine ⟨hs, ?_⟩
  obtain ⟨t, ht⟩ := Option.isSome_iff_exists.mp hs
  rw [ht]
  simp only [Option.getD_some]
  rcases Nat.eq_zero_or_pos L with hL0 | hLpos
  · rw [hL0, floorAt_zero]; exact Nat.zero_le _
  -- the node is above `nE` past GST
  have hnE : nE ≤ t := by
    have h₁ := (hrun.started Ng hNg).2 v hv
    have h₂ : topAt cfg (prefixOf ev Ng) time v gst =
        (stateBefore cfg (prefixOf ev eg) eg v).top.getD 0 := by
      unfold topAt stateAt
      rw [← heg, stateBefore_prefixOf hegN]
    have h₃ := (rises_prefixOf (cfg := cfg) (ev := ev) (show eg ≤ n by omega) v).1
    rw [ht] at h₃
    simp only [Option.getD_some] at h₃
    omega
  obtain ⟨htime, hinj, -, hsp, -⟩ := hrun.timeless n
  have hlo := heq v hv n (by omega)
  have h := floor_le_top_before hσ hadm hfa hf hid htime hinj hq hdr hsk hcm hsp hv ht hnE
    (by rw [hlo]; exact hLpos) (fun w hw k hk => by
      rw [stateBefore_prefixOf hk, hlo]; exact hle w hw k)
  rw [floor_eq_before hdr v n, hlo] at h
  exact h

end Run

end Node

end LeanDag
