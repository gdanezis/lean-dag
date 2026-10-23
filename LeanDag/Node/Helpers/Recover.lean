import LeanDag.Node.Helpers.Catch
/-!
# Recovery from crashes

`docs/validator.md` §5.6. A reliable node sends again a block at its
round at `t₀` or above within `W` (`sends_again`), so past the recovery a
reliable block at its author's round at `G` or above arrives
(`arrival_of_recovered`); its retry timer fires by then, so it no longer
recovers (`recovered_by`).
-/

namespace LeanDag

namespace Node

variable {Validator BlockId Payload : Type} [Fintype Validator] [DecidableEq Validator]
variable [LinearOrder BlockId]
variable {cfg : Config Validator BlockId Payload} {tr : Trace Validator BlockId Payload}

/-! ## Timers past the last restart -/

section Timers

variable {T : Finset Validator} {time : ℕ → ℕ} {t_r t₁ : ℕ}

omit [Fintype Validator] in
/-- Resending sets the retry timer. -/
theorem setTimer_mem_resend {s : State Validator BlockId Payload} {n : ℕ} {j : BlockId}
    (ht : s.top = some n) (ho : s.own = some j) :
    Output.setTimer (n - 1) (2 * cfg.timeout (n - 1)) ∈ Node.resend cfg s := by
  simp [Node.resend, ht, ho]

omit [Fintype Validator] in
/-- Resending broadcasts the node's own block at its top. -/
theorem broadcast_mem_resend {s : State Validator BlockId Payload} {n : ℕ} {j : BlockId}
    (ht : s.top = some n) (ho : s.own = some j) :
    Output.broadcast j (s.disk.blk j) ∈ Node.resend cfg s := by
  simp [Node.resend, ht, ho]

open Classical in
/-- **The retry timer is set past the last restart**: a reliable node at
round `n` at `s ≥ t_r` set the timer of round `n - 1` at a last event
before `s`, its build of round `n`, a restart or a resend, and that timer
fires twice the round's timeout later. -/
theorem retry_last (hmono : Live.TimeMono tr time) (hup : Live.UpFrom T tr time t_r t₁)
    (hfire : Live.TimersFireUp cfg T tr time t₁) {v : Validator} (hv : v ∈ T) {s n : ℕ}
    (hrs : t_r ≤ s) (hts : (stateAt cfg tr time v s).top = some n)
    (ht₁ : s + 2 * cfg.timeout (n - 1) ≤ t₁) :
    ∃ a f, a < eventsBy tr time s ∧ (tr[a]?.map Prod.fst) = some v ∧
      Output.setTimer (n - 1) (2 * cfg.timeout (n - 1)) ∈ outputsAt cfg tr a ∧
      (∀ a', a < a' → a' < eventsBy tr time s → (tr[a']?.map Prod.fst) = some v →
        Output.setTimer (n - 1) (2 * cfg.timeout (n - 1)) ∉ outputsAt cfg tr a') ∧
      (∀ k, a < k → k ≤ eventsBy tr time s → (stateBefore cfg tr k v).top = some n) ∧
      a < f ∧ tr[f]? = some (v, .timer (n - 1)) ∧ time f = time a + 2 * cfg.timeout (n - 1) := by
  set E := eventsBy tr time s with hE
  change (stateBefore cfg tr E v).top = some n at hts
  let P : ℕ → Prop := fun a =>
    (tr[a]?.map Prod.fst) = some v ∧
      Output.setTimer (n - 1) (2 * cfg.timeout (n - 1)) ∈ outputsAt cfg tr a
  -- the build of round `n` set the timer
  obtain ⟨b, hbE, hbv, e, hep, her⟩ := built_top (cfg := cfg) (tr := tr) E (by rw [hts]; rfl)
  simp only [hts, Option.getD_some] at her
  obtain ⟨inpb, hb⟩ := Converge.event_of_map hbv
  have hPb : P b := ⟨hbv, by have := timer_of_persist hb hep; rwa [her] at this⟩
  -- the last event before `E` that set it
  set a := Nat.findGreatest P (E - 1) with ha
  have hPa : P a := Nat.findGreatest_spec (P := P) (m := b) (by omega) hPb
  have hba : b ≤ a := Nat.le_findGreatest (by omega) hPb
  have haE : a < E := lt_of_le_of_lt (Nat.findGreatest_le (E - 1)) (by omega)
  have hmax : ∀ a', a < a' → a' < E → ¬ P a' := fun a' h₁ h₂ =>
    Nat.findGreatest_is_greatest h₁ (by omega)
  obtain ⟨inpa, hai⟩ := Converge.event_of_map hPa.1
  have hal : a < tr.length := (List.getElem?_eq_some_iff.mp hai).1
  have hta : time a ≤ s := (lt_eventsBy hmono hal).mp haE
  -- the node is at round `n` from it to `E`
  obtain ⟨t₀, ht₀, hbt₀⟩ := built_le_top hb hep
  have hat : ∀ k, b < k → k ≤ E → (stateBefore cfg tr k v).top = some n := by
    intro k hbk hkE
    have hr := rises_before (cfg := cfg) (tr := tr) v (show b + 1 ≤ k by omega)
    refine top_between (cfg := cfg) hkE (hr.2.1 (by rw [ht₀]; rfl)) ?_ hts
    have := hr.1
    rw [ht₀] at this; simp only [Option.getD_some] at this; omega
  -- no restart after it
  have hnr : ∀ k, a < k → time k ≤ time a + 2 * cfg.timeout (n - 1) →
      tr[k]? ≠ some (v, .restart) := by
    intro k hak hkt hk
    have hkl : k < tr.length := (List.getElem?_eq_some_iff.mp hk).1
    by_cases hkE : k < E
    · -- a restart before `E` would set the timer again
      have htk := hat k (by omega) (by omega)
      obtain ⟨j, hj, -⟩ := ownTop_before (cfg := cfg) (tr := tr) (v := v) k n htk
      refine hmax k hak hkE ⟨by rw [hk]; rfl, ?_⟩
      rw [outputsAt_eq hk]
      exact List.mem_append_left _
        (List.mem_append_left _ (setTimer_mem_resend (cfg := cfg.at v) htk hj))
    · have := hup k v hk hv (by omega)
      have := (lt_eventsBy hmono hkl).not.mp hkE
      omega
  obtain ⟨f, haf, hf, htf⟩ :=
    hfire a v inpa hai hv (n - 1) (2 * cfg.timeout (n - 1)) hPa.2 (by omega) hnr
  exact ⟨a, f, haE, hPa.1, hPa.2, fun a' h₁ h₂ h₃ h₄ => hmax a' h₁ h₂ ⟨h₃, h₄⟩,
    fun k hak hkE => hat k (by omega) hkE, haf, hf, htf⟩

/-- **A reliable node sends one of its blocks again past the last
restart**: at round `m` at `t₀ ≥ t_r`, it broadcasts a block of its own of
round `m` or above after `t₀` and within twice the timeout of round
`m - 1`. When the retry timer fires, it builds above `m`, or resends its round-`m`
block, or it built above `m` before. -/
theorem sends_again (hmono : Live.TimeMono tr time) (hup : Live.UpFrom T tr time t_r t₁)
    (hfire : Live.TimersFireUp cfg T tr time t₁) {u : Validator} (hu : u ∈ T) {t₀ m : ℕ}
    (hrt : t_r ≤ t₀) (hts : (stateAt cfg tr time u t₀).top = some m)
    (ht₁ : t₀ + 2 * cfg.timeout (m - 1) ≤ t₁) :
    ∃ k inp y, tr[k]? = some (u, inp) ∧ t₀ < time k ∧ time k ≤ t₀ + 2 * cfg.timeout (m - 1) ∧
      y ∈ broadcasts (outputsAt cfg tr k) ∧ m ≤ y.2.round ∧ y.2.creator = u := by
  obtain ⟨a, f, haE, -, -, hmax, hat, haf, hf, htf⟩ := retry_last hmono hup hfire hu hrt hts ht₁
  set E := eventsBy tr time t₀ with hE
  have hal : a < tr.length := lt_of_lt_of_le haE (eventsBy_le_length t₀)
  have hta : time a ≤ t₀ := (lt_eventsBy hmono hal).mp haE
  have hfl : f < tr.length := (List.getElem?_eq_some_iff.mp hf).1
  change (stateBefore cfg tr E u).top = some m at hts
  -- the node after its timer's event
  have hsucc : stateBefore cfg tr (f + 1) u =
      (Node.step (cfg.at u) (stateBefore cfg tr f u) (.timer (m - 1))).1 := by
    rw [stateBefore_succ hf, if_pos rfl]
  -- the step of the timer, when the node stays at `m`, resends
  have hres : (stateBefore cfg tr f u).top = some m → (stateBefore cfg tr (f + 1) u).top = some m →
      (∃ j, (stateBefore cfg tr (f + 1) u).own = some j ∧
        ((stateBefore cfg tr (f + 1) u).disk.blk j).round = m ∧
        ((stateBefore cfg tr (f + 1) u).disk.blk j).creator = u ∧
        Output.setTimer (m - 1) (2 * cfg.timeout (m - 1)) ∈ outputsAt cfg tr f ∧
        Output.broadcast j ((stateBefore cfg tr (f + 1) u).disk.blk j) ∈ outputsAt cfg tr f) := by
    intro h₁ h₂
    obtain ⟨j, hj, -, hjr, hjc⟩ := ownTop_before (cfg := cfg) (tr := tr) (v := u) (f + 1) m h₂
    have h₂' := h₂
    rw [hsucc, step_timer_fst] at h₂'
    have hout : outputsAt cfg tr f =
        (Node.settle (cfg.at u) { stateBefore cfg tr f u with
          fired := fire (stateBefore cfg tr f u) (m - 1), recovering := false }).2 ++
        Node.resend (cfg.at u) (Node.settle (cfg.at u) { stateBefore cfg tr f u with
          fired := fire (stateBefore cfg tr f u) (m - 1), recovering := false }).1 := by
      have hm : (stateBefore cfg tr f u).top = some (m - 1) ∨
          (stateBefore cfg tr f u).top = some (m - 1 + 1) := by
        rcases Nat.eq_zero_or_pos m with h0 | hpos
        · left; rw [h₁, h0]
        · right; rw [h₁, Nat.sub_add_cancel hpos]
      rw [outputsAt_eq hf]
      simp only [Node.step]
      rw [if_pos ⟨h₂'.trans h₁.symm, hm⟩]
    have hsame : stateBefore cfg tr (f + 1) u = (Node.settle (cfg.at u)
        { stateBefore cfg tr f u with
          fired := fire (stateBefore cfg tr f u) (m - 1), recovering := false }).1 := by
      rw [hsucc, step_timer_fst]
    refine ⟨j, hj, hjr, hjc, ?_, ?_⟩
    · rw [hout]
      refine List.mem_append_right _ ?_
      rw [← hsame]
      exact setTimer_mem_resend (cfg := cfg.at u) h₂ hj
    · rw [hout]
      refine List.mem_append_right _ ?_
      rw [← hsame]
      exact broadcast_mem_resend (cfg := cfg.at u) h₂ hj
  -- the timer fires after `t₀`: before, the node would have set it again
  have hfE : E ≤ f := by
    by_contra hlt
    have h₁ := hat f haf (by omega)
    have h₂ := hat (f + 1) (by omega) (by omega)
    obtain ⟨-, -, -, -, hset, -⟩ := hres h₁ h₂
    exact hmax f haf (by omega) (by rw [hf]; rfl) hset
  have htf₀ : t₀ < time f := by
    by_contra h
    have : f < E := (lt_eventsBy hmono hfl).mpr (by omega)
    omega
  have hfle : time f ≤ t₀ + 2 * cfg.timeout (m - 1) := by omega
  -- the node at the timer's event is at `m` or above
  have hsf : (stateBefore cfg tr f u).top.isSome ∧ m ≤ (stateBefore cfg tr f u).top.getD 0 := by
    obtain ⟨h₁, h₂, -⟩ := rises_before (cfg := cfg) (tr := tr) u hfE
    rw [hts] at h₁ h₂
    exact ⟨h₂ rfl, by simpa using h₁⟩
  have hcre : ∀ {k inp} {y : BlockId × Block Validator BlockId Payload},
      tr[k]? = some (u, inp) → y ∈ persists (outputsAt cfg tr k) → y.2.creator = u :=
    fun hk hy => (Local.authored _ _ _ (cfg.at u) _ _ (persists_of_event hk hy)).2
  by_cases hfm : (stateBefore cfg tr f u).top = some m
  · by_cases hstay : (stateBefore cfg tr (f + 1) u).top = some m
    · -- it resends its round-`m` block
      obtain ⟨j, -, hjr, hjc, -, hb⟩ := hres hfm hstay
      exact ⟨f, _, (j, (stateBefore cfg tr (f + 1) u).disk.blk j), hf, htf₀, hfle,
        mem_broadcasts.mpr hb, by simp [hjr], hjc⟩
    · -- it builds above `m`
      obtain ⟨h₁, h₂, -⟩ := rises_before (cfg := cfg) (tr := tr) u (show f ≤ f + 1 by omega)
      rw [hfm] at h₁ h₂
      obtain ⟨t, ht⟩ := Option.isSome_iff_exists.mp (h₂ rfl)
      have hmt : m + 1 ≤ t := by
        have := h₁; rw [ht] at this; simp only [Option.getD_some] at this
        have : t ≠ m := fun h => hstay (by rw [ht, h])
        omega
      rw [hsucc] at ht
      obtain ⟨e, hep, her⟩ := step_every (cfg := cfg.at u) (s := stateBefore cfg tr f u)
        (inp := .timer (m - 1)) (by simp) (Or.inr ⟨_, rfl⟩) (by rw [ht]; rfl) (m + 1)
        (Or.inr (by rw [hfm]; simp))
        (by rw [ht]; simpa using hmt)
      rw [← outputsAt_eq hf] at hep
      exact ⟨f, _, e, hf, htf₀, hfle, broadcasts_of_persists hep, by omega, hcre hf hep⟩
  · -- it built above `m` after `t₀`, before its timer fired
    have hmf : m + 1 ≤ (stateBefore cfg tr f u).top.getD 0 := by
      obtain ⟨t, ht⟩ := Option.isSome_iff_exists.mp hsf.1
      have h₂ := hsf.2
      rw [ht] at h₂ ⊢
      simp only [Option.getD_some] at h₂ ⊢
      have : t ≠ m := fun h => hfm (by rw [ht, h])
      omega
    obtain ⟨b', hb'f, hb'u, e, hep, her⟩ := built_top (cfg := cfg) (tr := tr) f hsf.1
    obtain ⟨inpb, hb'⟩ := Converge.event_of_map hb'u
    have hb'l : b' < tr.length := (List.getElem?_eq_some_iff.mp hb').1
    have hEb : E ≤ b' := by
      by_contra hlt
      obtain ⟨t, ht, het⟩ := built_le_top hb' hep
      have hr := (rises_before (cfg := cfg) (tr := tr) u (show b' + 1 ≤ E by omega)).1
      rw [ht, hts] at hr
      simp only [Option.getD_some] at hr
      omega
    have htb : t₀ < time b' := by
      by_contra h
      have : b' < E := (lt_eventsBy hmono hb'l).mpr (by omega)
      omega
    have := hmono b' f hb'f.le hfl
    exact ⟨b', _, e, hb', htb, by omega, broadcasts_of_persists hep, by omega, hcre hb' hep⟩

end Timers

/-! ## Arrival past the recovery -/

section Arrival

variable {P : Validity Validator BlockId Payload} {H T : Finset Validator} {time : ℕ → ℕ}
  {gst Δ Δₛ t_r t₁ : ℕ}

/-- **Reliable blocks arrive past the recovery**: with the reliable nodes
up from `t_r` on, a reliable block built at `s` is held by every other
reliable node by `max s G + Δ + Δₛ`, for `G = max t_r gst + W` and `W`
twice the largest timeout of the round below the one a reliable node is
at by `max t_r gst`, if its round is its author's round at `G` or above.
A block built from `t_r` on is delivered and synchronised as before; one
built earlier is then its author's block of its round at `t₀`, which its
author sends again within `W` (`sends_again`), delivered and
synchronised. -/
theorem arrives_recovered (hσ : cfg.σ = boundedSel) (hadm : cfg.Admissible)
    (hf : Hᶜ.card ≤ cfg.f) (hid : Function.Injective cfg.idOf)
    (htime : Converge.TimelyAuthentic cfg H tr) (hinj : Converge.HashInjective cfg H tr)
    (hTH : T ⊆ H) (hmono : Live.TimeMono tr time)
    (hdel : Live.DeliveredFrom cfg T tr time gst Δ t_r t₁)
    (hsync : Live.SyncedFrom cfg H T tr time gst Δₛ t_r t₁) (hup : Live.UpFrom T tr time t_r t₁)
    (hfire : Live.TimersFireUp cfg T tr time t₁) (hstart : Live.StartedBy T tr time gst) :
    ∀ u ∈ T, ∀ v ∈ T, u ≠ v → ∀ b inp, tr[b]? = some (u, inp) →
      ∀ e ∈ persists (outputsAt cfg tr b),
        topAt cfg tr time u
          (max t_r gst + T.sup fun u => 2 * cfg.timeout (topAt cfg tr time u (max t_r gst) - 1))
          ≤ e.2.round →
      ∀ s τ, time b ≤ s →
        max s (max t_r gst +
          T.sup fun u => 2 * cfg.timeout (topAt cfg tr time u (max t_r gst) - 1)) + (Δ + Δₛ) ≤ τ →
        τ ≤ t₁ → e.1 ∈ (stateAt cfg tr time v τ).disk.ids := by
  intro u hu v hv huv b inp hb e hep hGe s τ htb hτ ht₁
  set t₀ := max t_r gst with ht₀
  set W := T.sup fun u => 2 * cfg.timeout (topAt cfg tr time u t₀ - 1) with hW
  have hbl : b < tr.length := (List.getElem?_eq_some_iff.mp hb).1
  -- a block of `u` delivered to `v` at `j`, from `t_r` on, is held by `τ`
  have hheld : ∀ {q k j : ℕ} {inpq : Input Validator BlockId Payload}
      {y : BlockId × Block Validator BlockId Payload},
      tr[q]? = some (u, inpq) → y ∈ persists (outputsAt cfg tr q) →
      tr[j]? = some (v, .deliver y.1 y.2) → k < j → t_r ≤ time k →
      max (time j) gst + Δₛ ≤ τ → y.1 ∈ (stateAt cfg tr time v τ).disk.ids := by
    intro q k j inpq y hq hyq hj hkj hrk hjτ
    have hjl : j < tr.length := (List.getElem?_eq_some_iff.mp hj).1
    have hjr : t_r ≤ time j := hrk.trans (hmono k j hkj.le hjl)
    have hgood := ((Converge.inv_before (cfg := cfg) (tr := tr) (q + 1) u).good y
      (persists_of_event hq hyq)).2.1
    by_cases hn0 : y.2.round = 0
    · exact arrives_zero hinj hTH hmono hu hv huv (by rw [hq]; rfl) hyq hgood hn0 hj (by omega)
    · obtain ⟨x, y', o, hx, hxb, heo, -⟩ := build_witness hσ hadm hf htime hinj (hTH hu) hq hyq hn0
      exact arrives hinj htime hTH hmono hsync hu hv huv hq hyq hx hxb heo hj hjr hjτ (by omega)
  have hsend : ∀ {k : ℕ} {inpk : Input Validator BlockId Payload}
      {y : BlockId × Block Validator BlockId Payload}, tr[k]? = some (u, inpk) →
      y ∈ broadcasts (outputsAt cfg tr k) → t_r ≤ time k → max (time k) gst + Δ ≤ t₁ →
      ∃ j, k < j ∧ tr[j]? = some (v, .deliver y.1 y.2) ∧ time j ≤ max (time k) gst + Δ :=
    fun hk hy hrk ht => hdel _ u _ hk hu hrk (v, .deliver _ _)
      ⟨.broadcast _ _, mem_broadcasts.mp hy, Ne.symm huv, rfl⟩ hv ht
  by_cases hbr : t_r ≤ time b
  · -- built from `t_r` on: delivered and synchronised
    obtain ⟨j, hbj, hj, htj⟩ := hsend hb (broadcasts_of_persists hep) hbr (by omega)
    exact hheld hb hep hj hbj hbr (by omega)
  · -- built before: at `u`'s round at `t₀`, the block `u` sends again
    have hus : (stateAt cfg tr time u t₀).top.isSome :=
      started_at hadm hid htime hTH hmono hstart hu (le_max_right _ _)
    obtain ⟨m, hm⟩ := Option.isSome_iff_exists.mp hus
    have htm : topAt cfg tr time u t₀ = m := by unfold topAt; rw [hm]; rfl
    have hem : e.2.round ≤ m := by
      have := (top_of_built hmono hb hep (τ := t₀) (by omega)).2
      rw [htm] at this; exact this
    have hmW : 2 * cfg.timeout (m - 1) ≤ W := by
      rw [← htm]
      exact Finset.le_sup (f := fun u => 2 * cfg.timeout (topAt cfg tr time u t₀ - 1)) hu
    obtain ⟨k, inpk, y, hk, htk, hkle, hyb, hym, -⟩ :=
      sends_again hmono hup hfire hu (le_max_left _ _) hm (by omega)
    obtain ⟨q, hqk, inpq, hq, hyq⟩ := Converge.persists_of_broadcasts hk hyb
    have hql : q < tr.length := (List.getElem?_eq_some_iff.mp hq).1
    have hkl : k < tr.length := (List.getElem?_eq_some_iff.mp hk).1
    -- it is `u`'s block of `e`'s round, so it is `e`
    have hyG : y.2.round ≤ topAt cfg tr time u (t₀ + W) :=
      (top_of_built hmono hq hyq (τ := t₀ + W) ((hmono q k hqk hkl).trans (by omega))).2
    have hye : y = e := eq_of_persists u
      (mem_persists_iff.mpr (mem_outputs_of_event hq (mem_persists_iff.mp hyq)))
      (mem_persists_iff.mpr (mem_outputs_of_event hb (mem_persists_iff.mp hep))) (by omega)
    obtain ⟨j, hkj, hj, htj⟩ := hsend hk hyb (by omega) (by omega)
    rw [← hye]
    exact hheld hq hyq hj hkj (by omega) (by omega)

/-- **The reliable nodes have recovered by `G`**: a reliable node restarts
before `t_r` at its round at `t₀`, so the retry timer the restart sets
fires within `W`, before `G`, and a timer ends the recovery. -/
theorem recovered_by (hadm : cfg.Admissible) (hid : Function.Injective cfg.idOf)
    (htime : Converge.TimelyAuthentic cfg H tr) (hTH : T ⊆ H) (hmono : Live.TimeMono tr time)
    (hup : Live.UpFrom T tr time t_r t₁) (hfire : Live.TimersFireUp cfg T tr time t₁)
    (hstart : Live.StartedBy T tr time gst)
    (hG : max t_r gst + T.sup (fun u => 2 * cfg.timeout (topAt cfg tr time u (max t_r gst) - 1))
      ≤ t₁) {v : Validator} (hv : v ∈ T) {k : ℕ}
    (hk : eventsBy tr time (max t_r gst +
      T.sup fun u => 2 * cfg.timeout (topAt cfg tr time u (max t_r gst) - 1)) ≤ k)
    (hk₁ : k ≤ eventsBy tr time t₁) :
    (stateBefore cfg tr k v).recovering = false := by
  set t₀ := max t_r gst with ht₀
  set W := T.sup fun u => 2 * cfg.timeout (topAt cfg tr time u t₀ - 1) with hW
  cases hrec : (stateBefore cfg tr k v).recovering
  · rfl
  exfalso
  obtain ⟨j, hjk, hj, hno, htop⟩ := recovering_restart (cfg := cfg) (tr := tr) (v := v) k hrec
  have hjl : j < tr.length := (List.getElem?_eq_some_iff.mp hj).1
  have htj : time j < t_r := hup j v hj hv ((lt_eventsBy hmono hjl).mp (by omega))
  -- the node is at a round `m` from `j` to `k`, so at `t₀`
  have hE₀k : eventsBy tr time t₀ ≤ k := (eventsBy_mono (by omega)).trans hk
  have hks : (stateBefore cfg tr k v).top.isSome :=
    (rises_before (cfg := cfg) (tr := tr) v ((eventsBy_mono (le_max_right t_r gst)).trans hE₀k)).2.1
      (started_at hadm hid htime hTH hmono hstart hv le_rfl)
  rw [htop] at hks
  obtain ⟨m, hm⟩ := Option.isSome_iff_exists.mp hks
  have hjE : j + 1 ≤ eventsBy tr time t₀ := (lt_eventsBy hmono hjl).mpr (by omega)
  have hm₀ : topAt cfg tr time v t₀ = m := by
    have h₁ := (rises_before (cfg := cfg) (tr := tr) v (show j ≤ eventsBy tr time t₀ by omega)).1
    have h₂ := (rises_before (cfg := cfg) (tr := tr) v hE₀k).1
    rw [htop, hm] at h₂
    rw [hm] at h₁
    simp only [Option.getD_some] at h₁ h₂
    change (stateBefore cfg tr (eventsBy tr time t₀) v).top.getD 0 = m
    omega
  -- the restart set the retry timer of the round below `m`
  obtain ⟨o, hoo, -⟩ := ownTop_before (cfg := cfg) (tr := tr) (v := v) j m hm
  have hset : Output.setTimer (m - 1) (2 * cfg.timeout (m - 1)) ∈ outputsAt cfg tr j := by
    rw [outputsAt_eq hj]
    change _ ∈ Node.resend (cfg.at v) _ ++ Node.rearm (cfg.at v) _ ++ _
    exact List.mem_append_left _ (List.mem_append_left _ (setTimer_mem_resend hm hoo))
  have hmW : 2 * cfg.timeout (m - 1) ≤ W := by
    rw [← hm₀]
    exact Finset.le_sup (f := fun u => 2 * cfg.timeout (topAt cfg tr time u t₀ - 1)) hv
  -- it fires before `G`, after `j` and before `k`
  have hafter : ∀ k', eventsBy tr time (t₀ + W) ≤ k' → k' < tr.length → t₀ + W < time k' :=
    fun k' hk' hk'l => by
      by_contra h
      have := (lt_eventsBy hmono hk'l).mpr (show time k' ≤ t₀ + W by omega)
      omega
  obtain ⟨f, hjf, hf, htf⟩ := hfire j v .restart hj hv (m - 1) _ hset (by omega)
    (fun k' hjk' hk't hk' => by
      have hk'l : k' < tr.length := (List.getElem?_eq_some_iff.mp hk').1
      by_cases hk'k : k' < k
      · exact (hno k' .restart hjk' hk'k hk').1 rfl
      · have := hafter k' (by omega) hk'l
        omega)
  have hfl : f < tr.length := (List.getElem?_eq_some_iff.mp hf).1
  have hfk : f < k := by
    by_contra h
    have := hafter f (by omega) hfl
    omega
  exact (hno f _ hjf hfk hf).2 (m - 1) rfl

/-- **The run past the recovery**: reliable blocks at their author's round
at `G` arrive (`arrives_recovered`), no reliable node recovers from `G`
on (`recovered_by`), and none restarts past `t_r`. -/
theorem arrival_of_recovered (hσ : cfg.σ = boundedSel) (hadm : cfg.Admissible)
    (hf : Hᶜ.card ≤ cfg.f) (hid : Function.Injective cfg.idOf)
    (htime : Converge.TimelyAuthentic cfg H tr) (hinj : Converge.HashInjective cfg H tr)
    (hTH : T ⊆ H) (hmono : Live.TimeMono tr time)
    (hdel : Live.DeliveredFrom cfg T tr time gst Δ t_r t₁)
    (hsync : Live.SyncedFrom cfg H T tr time gst Δₛ t_r t₁)
    (hup : Live.UpFrom T tr time t_r t₁) (hfire : Live.TimersFireUp cfg T tr time t₁)
    (hstart : Live.StartedBy T tr time gst) :
    Arrival cfg T tr time
      (max t_r gst + T.sup fun u => 2 * cfg.timeout (topAt cfg tr time u (max t_r gst) - 1))
      (Δ + Δₛ) t₁ :=
  ⟨arrives_recovered hσ hadm hf hid htime hinj hTH hmono hdel hsync hup hfire hstart,
    fun hG _ hv _ hk hk₁ => recovered_by hadm hid htime hTH hmono hup hfire hstart hG hv hk hk₁,
    fun v hv k inp hk hGk hk₁ h => by
      subst h
      have := hup k v hk hv hk₁
      omega⟩

end Arrival

end Node

end LeanDag
