import LeanDag.Node.Helpers.Drift
/-!
# The wave facts of a node's timed run

`docs/validator.md` §13.3. Past a synchronisation point, with drift
within `A = 3Δ + Δₛ` (`drift`) and `2A < timeout`, a reliable node that
waited the timeout at a round holds every reliable block of it before it
builds the next (`waited_holds`): its own stays stored, and another's
arrives `A` after it was built, before the node's timer fired. By `A`
after every reliable node reached a round, each holds every reliable
block up to it at or above its horizon (`reliable_held`).
-/

namespace LeanDag

namespace Node

open Scheme

variable {Validator BlockId Payload : Type} [Fintype Validator] [DecidableEq Validator]
variable [LinearOrder BlockId]
variable {cfg : Config Validator BlockId Payload} {H : Finset Validator}

/-! ## Holdings -/

section Holds

variable {T : Finset Validator} {tr : Trace Validator BlockId Payload} {time : ℕ → ℕ}
  {gst Δ Δₛ t₁ : ℕ}

omit [Fintype Validator] [DecidableEq Validator] [LinearOrder BlockId] in
/-- Under nondecreasing times, the events strictly before `t` are those at
times below it. -/
theorem lt_eventsBefore (hmono : Live.TimeMono tr time) {i t : ℕ} (hi : i < tr.length) :
    i < eventsBefore tr time t ↔ time i < t := by
  rcases Nat.eq_zero_or_pos t with rfl | ht
  · have : eventsBefore tr time 0 = 0 := by
      unfold eventsBefore
      simp
    rw [this]; omega
  · have heq : eventsBefore tr time t = eventsBy tr time (t - 1) := by
      unfold eventsBefore eventsBy
      congr 1
      exact List.filter_congr fun j _ => by simp only [decide_eq_decide]; omega
    rw [heq, lt_eventsBy hmono hi]
    omega

/-- **A node is at round `n` before it builds round `n + 1`**: at an
index past an event building round `n`, before every event at or after
the first build of round `n + 1`. -/
theorem top_eq_between {v : Validator} (hnv : Steady cfg tr v)
    (hmono : Live.TimeMono tr time) {E n i₀ : ℕ} {inp : Input Validator BlockId Payload}
    (hi₀ : tr[i₀]? = some (v, inp)) {e : BlockId × Block Validator BlockId Payload}
    (he : e ∈ persists (outputsAt cfg tr i₀)) (her : e.2.round = n) (hi₀E : i₀ < E)
    (hlt : ∀ k < E, k < tr.length → time k < builtAt cfg tr time v (n + 1)) :
    (stateBefore cfg tr E v).top = some n := by
  obtain ⟨t₀, ht₀, hrt₀⟩ := built_le_top hi₀ he
  obtain ⟨h₁, h₂, -, -⟩ := rises_before (cfg := cfg) hnv (show i₀ + 1 ≤ E by omega)
  rw [ht₀] at h₁ h₂
  obtain ⟨t', ht'⟩ := Option.isSome_iff_exists.mp (h₂ rfl)
  rw [ht'] at h₁ ⊢
  simp only [Option.getD_some] at h₁
  by_contra hne
  have hge : n + 1 ≤ t' := by
    have : t' ≠ n := fun h => hne (by rw [h])
    omega
  obtain ⟨k, hkE, hkv, e', he', her'⟩ := built_by hnv E (by rw [ht']; rfl)
    (show n + 1 ≤ _ by rw [ht']; exact hge)
  obtain ⟨i', hi'k, hbt', -⟩ := builtAt_first (cfg := cfg) time hkv ⟨e', he', her'⟩
  obtain ⟨_inpk, hk⟩ := Converge.event_of_map hkv
  have hkl : k < tr.length := (List.getElem?_eq_some_iff.mp hk).1
  have := hlt k hkE hkl
  have := hmono i' k hi'k hkl
  omega

variable {N n₀ t : ℕ} (hq : 2 ≤ cfg.q) (hσ : cfg.σ = boundedSel)
  (hadm : cfg.Admissible) (hf : Hᶜ.card ≤ cfg.f) (htime : Converge.TimelyAuthentic cfg H tr)
  (hcert : Boot.TimelyCerts cfg H tr)
  (hinj : Converge.HashInjective cfg H tr) (hchain : Boot.ChainInjective cfg H tr)
  (hTH : T ⊆ H) (hnr : ∀ v ∈ T, Steady cfg tr v) (hmono : Live.TimeMono tr time)
  (hdel : Live.DeliveredWithin cfg T tr time gst Δ t₁)
  (hsync : Live.SyncedWithin cfg H T tr time gst Δₛ t₁)
  (hcmp : ∀ u ∈ T, ∀ v ∈ T, ∀ i j, (stateBefore cfg tr i u).decided.reverse <+:
    (stateBefore cfg tr j v).decided.reverse ∨
      (stateBefore cfg tr j v).decided.reverse <+: (stateBefore cfg tr i u).decided.reverse)
  (hD : ∀ n, n₀ ≤ n → n ≤ N → ∀ u ∈ T, ∀ w ∈ T, gst ≤ builtAt cfg tr time u n ∧
    builtAt cfg tr time u n ≤ builtAt cfg tr time w n + (3 * Δ + Δₛ))
  (hst : ∀ v ∈ T, (stateAt cfg tr time v t).top.isSome)
  (hN : ∀ v ∈ T, N ≤ topAt cfg tr time v t) (ht₁ : t + (3 * Δ + Δₛ) ≤ t₁)
include hq hσ hadm hf htime hcert hinj hchain hTH hnr hmono hdel hsync hcmp hD hst hN ht₁

/-- **A reliable node that waited the timeout holds the reliable blocks of
the round**, before it builds the next, when `2A < timeout`. -/
theorem waited_holds (hto : ∀ r, 2 * (3 * Δ + Δₛ) < cfg.timeout r) {u v : Validator} (hu : u ∈ T)
    (hv : v ∈ T) {n : ℕ} (hn₀ : n₀ ≤ n) (hnN : n + 1 ≤ N) {c : BlockId}
    (hcU : c ∈ (globalRecord (hashInjective_of_trace hinj) (authentic_of_timely htime)).ids)
    (hcu : ((globalRecord (hashInjective_of_trace hinj) (authentic_of_timely htime)).block
      c).creator = u)
    (hcr : ((globalRecord (hashInjective_of_trace hinj) (authentic_of_timely htime)).block
      c).round = n)
    (hwait : builtAt cfg tr time v n + cfg.timeout n ≤ builtAt cfg tr time v (n + 1)) :
    c ∈ heldBefore cfg tr time v (builtAt cfg tr time v (n + 1)) := by
  have hnv : Steady cfg tr v := hnr v hv
  have hτ := hto n
  obtain ⟨i₁, -, e₁, hi₁, -, -, hbt₁, hi₁t⟩ :=
    built_of_top hnv hmono (hst v hv) ((hN v hv).trans' hnN)
  obtain ⟨i₀, _inp₀, e₀, hi₀, he₀, he₀r, hbt₀, -⟩ :=
    built_of_top hnv hmono (hst v hv) ((hN v hv).trans' (by omega : n ≤ N))
  set Eb := eventsBefore tr time (time i₁) with hEbdef
  have hlt : ∀ k < Eb, k < tr.length → time k < builtAt cfg tr time v (n + 1) := fun k hk hkl => by
    rw [hbt₁]; exact (lt_eventsBefore hmono hkl).mp hk
  have hi₀l : i₀ < tr.length := (List.getElem?_eq_some_iff.mp hi₀).1
  have hi₀E : i₀ < Eb := (lt_eventsBefore hmono hi₀l).mpr (by omega)
  have hEt := top_eq_between hnv hmono hi₀ he₀ he₀r hi₀E hlt
  have hEb : (stateBefore cfg tr Eb v).store.base ≤ n :=
    (base_le_top_sub hnv Eb hEt).trans (by omega)
  unfold heldBefore
  rw [hbt₁, ← hEbdef]
  -- the block's build
  obtain ⟨i, inp, e, hi, he, rfl, her, hbt⟩ :=
    event_of_mem (time := time) hinj htime (hTH hu) hcU hcu
  rw [hcr] at her hbt
  have hil : i < tr.length := (List.getElem?_eq_some_iff.mp hi).1
  obtain ⟨hgu, hdu⟩ := hD n hn₀ (by omega) u hu v hv
  obtain ⟨-, hdv⟩ := hD n hn₀ (by omega) v hv u hu
  by_cases huv : u = v
  · subst huv
    exact own_held hnv hi he ((lt_eventsBefore hmono hil).mpr (by omega)) (by omega)
  -- another's, arrived `A` after it was built
  set τ := time i + (3 * Δ + Δₛ) with hτdef
  have hτE : eventsBy tr time τ ≤ Eb := by
    by_contra h
    have hk : Eb < tr.length := lt_of_lt_of_le (not_le.mp h) (eventsBy_le_length τ)
    have h₁ := (lt_eventsBy hmono hk).mp (not_le.mp h)
    have h₂ := (lt_eventsBefore hmono hk).not.mp (lt_irrefl _)
    omega
  have hZt : (stateAt cfg tr time v τ).top = some n :=
    top_eq_between hnv hmono hi₀ he₀ he₀r ((lt_eventsBy hmono hi₀l).mpr (by omega))
      fun k hk hkl => hlt k (by omega) hkl
  have hZb : (stateAt cfg tr time v τ).store.base ≤ e.2.round := by
    have := (grows_before (cfg := cfg) (tr := tr) v hτE).1
    change (stateBefore cfg tr (eventsBy tr time τ) v).store.base ≤ _
    omega
  obtain ⟨hin, hinr, -, -⟩ := block_arrives hq hσ hadm hf htime hcert hinj hchain hTH
    hnr hmono hdel hsync hcmp hu hv huv hi he (s := time i) le_rfl (τ := τ)
    (by rw [max_eq_left (by omega)]; omega) (by omega) hZt (by omega) hZb
  have hinr' : ((stateBefore cfg tr (eventsBy tr time τ) v).store.blk e.1).round = e.2.round :=
    hinr
  exact (retains_before (cfg := cfg) hnv hτE e.1 hin (by rw [hinr']; omega)).1

/-- **By `A` after every reliable node reached a round, each holds every
reliable block up to it** at or above its horizon. -/
theorem reliable_held {u v : Validator} (hu : u ∈ T) (hv : v ∈ T) {r : ℕ} (hr₀ : n₀ ≤ r)
    (hrN : r ≤ N) {c : BlockId}
    (hcU : c ∈ (globalRecord (hashInjective_of_trace hinj) (authentic_of_timely htime)).ids)
    (hcu : ((globalRecord (hashInjective_of_trace hinj) (authentic_of_timely htime)).block
      c).creator = u)
    (hcr : ((globalRecord (hashInjective_of_trace hinj) (authentic_of_timely htime)).block
      c).round = r)
    (hb : (stateAt cfg tr time v (t + (3 * Δ + Δₛ))).store.base ≤ r) :
    c ∈ (stateAt cfg tr time v (t + (3 * Δ + Δₛ))).store.ids := by
  have hnu : Steady cfg tr u := hnr u hu
  have hnv : Steady cfg tr v := hnr v hv
  obtain ⟨i, inp, e, hi, he, rfl, her, hbt⟩ :=
    event_of_mem (time := time) hinj htime (hTH hu) hcU hcu
  rw [hcr] at her hbt
  have hil : i < tr.length := (List.getElem?_eq_some_iff.mp hi).1
  have hit : time i ≤ t := hbt ▸ builtAt_le_of_top hnu hmono (hst u hu) ((hN u hu).trans' hrN)
  have hgi : gst ≤ time i := hbt ▸ (hD r hr₀ hrN u hu u hu).1
  by_cases huv : u = v
  · subst huv
    exact own_held hnv hi he ((lt_eventsBy hmono hil).mpr (by omega)) (by rw [her]; exact hb)
  obtain ⟨h₁, h₂, -, -⟩ := rises_before (cfg := cfg) hnv
    (eventsBy_mono (tr := tr) (time := time) (show t ≤ t + (3 * Δ + Δₛ) by omega))
  obtain ⟨t', ht'⟩ := Option.isSome_iff_exists.mp (h₂ (hst v hv))
  have hNt' : N ≤ t' := by
    have := (hN v hv).trans h₁
    change N ≤ (stateBefore cfg tr (eventsBy tr time (t + (3 * Δ + Δₛ))) v).top.getD 0 at this
    rw [ht'] at this
    exact this
  exact (block_arrives hq hσ hadm hf htime hcert hinj hchain hTH hnr hmono hdel hsync
    hcmp hu hv huv hi he (s := time i) le_rfl (τ := t + (3 * Δ + Δₛ))
    (by rw [max_eq_left hgi]; omega) ht₁ ht' (by omega) (by rw [her]; exact hb)).1

end Holds

section Outputs

variable {tr : Trace Validator BlockId Payload} {time : ℕ → ℕ}

/-- **The decisions a node output number its next undecided slot.** -/
theorem decisionsBy_length (v : Validator) (τ : ℕ) :
    (decisionsBy cfg tr time v τ).length = (stateAt cfg tr time v τ).lo := by
  obtain ⟨ha, hL⟩ := run_appends (cfg := cfg.at v) (inputsBefore tr (eventsBy tr time τ) v)
    Ledger.init
  have h := congrArg List.length ha.1
  have h₀ : (State.init (cfg.at v)).decided = [] := rfl
  rw [h₀, List.reverse_nil, List.nil_append, List.length_reverse] at h
  unfold decisionsBy
  rw [← h]
  exact hL.length

omit [Fintype Validator] in
/-- Every slot at a round at most `R` is below `decidable R`. -/
theorem lt_decidable {k R : ℕ} (hk : cfg.slots.slotRound k ≤ R) : k < decidable cfg R := by
  change cfg.per * (k / cfg.m) ≤ R at hk
  unfold decidable
  have h₁ : k / cfg.m ≤ R / cfg.per :=
    (Nat.le_div_iff_mul_le cfg.per_pos).mpr (by rw [Nat.mul_comm]; exact hk)
  exact lt_of_lt_of_le (Nat.lt_mul_div_succ k cfg.m_pos)
    (Nat.mul_le_mul_left _ (by omega))

end Outputs

end Node

end LeanDag
