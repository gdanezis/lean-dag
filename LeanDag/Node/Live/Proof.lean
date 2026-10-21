import LeanDag.Node.Live.Statement
import LeanDag.Node.Helpers.Arrive
/-!
# The reliable nodes produce rounds — proof

`docs/validator.md` §13.2. Past GST, let every reliable node be at round
`n` or above at `s`, and `v` reliable. `v` built its round-`n` block by
`s`, with the round's timer, which fires by `s + timeout n`. Suppose `v`
is still at round `n` then. It is settled (`settled_before`), the
round's timer has fired and stays so (`fired_stays`), and it holds a
round at least `n` (`held_after_timer`). Every reliable node's round-`n`
block arrived within `3Δ + Δₛ` of `s`, less than the timeout
(`round_arrives`): the certificate the author last announced with its
horizon reached `v` (`cert_catches`), so `v`'s horizon reached the
author's (`base_le_after`), and the block's history arrived after the
block (`arrives`). So `v` holds a quorum of round `n`, its own block
included, and no block with the identifier of its next one
(`fresh_before`), and builds (`tryBuild_isSome`), against its being
settled.
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
    (hσ : cfg.σ = boundedSel) (hadm : cfg.Admissible) (hl : cfg.limit = none)
    (hf : Hᶜ.card ≤ cfg.f) (hTH : T ⊆ H) (hqT : cfg.q ≤ T.card)
    (hto : ∀ r, 2 * (3 * Δ + Δₛ) < cfg.timeout r) (hq : 2 ≤ cfg.q)
    (hid : Function.Injective cfg.idOf)
    (htime : Converge.TimelyAuthentic cfg H tr) (hoff : Boot.TimelyOffers cfg H tr)
    (hcert : Boot.TimelyCerts cfg H tr) (hinj : Converge.HashInjective cfg H tr)
    (hchain : Boot.ChainInjective cfg H tr) (hnr : Converge.NoRestart T tr)
    (hmono : TimeMono tr time) (hdel : DeliveredWithin cfg T tr time gst Δ t₁)
    (htimer : TimersOnTime cfg T tr time t₁) (hsync : SyncedWithin cfg T tr time gst Δₛ t₁)
    (hstart : StartedBy T tr time gst) : Produces cfg T tr time gst t₁ := by
  intro s n hgs hst₁ hall v hv
  have hcmp : ∀ u ∈ T, ∀ w ∈ T, ∀ i j, (stateBefore cfg tr i u).decided.reverse <+:
      (stateBefore cfg tr j w).decided.reverse ∨
        (stateBefore cfg tr j w).decided.reverse <+: (stateBefore cfg tr i u).decided.reverse :=
    fun u hu w hw i j => decided_comparable hσ hadm hf htime hoff hcert hinj hchain
      (hTH hu) (hTH hw) i j
  have hnv : ∀ k : ℕ, tr[k]? ≠ some (v, Input.restart) := fun k => hnr k v hv
  have hτ := hto n
  -- every reliable node has started by `s`
  have hstarted : ∀ w ∈ T, (stateAt cfg tr time w s).top.isSome := by
    intro w hw
    obtain ⟨st, hst, htst⟩ := hstart w hw
    have hstl : st < tr.length := (List.getElem?_eq_some_iff.mp hst).1
    have hstE : st + 1 ≤ eventsBy tr time s := (lt_eventsBy hmono hstl).mpr (by omega)
    exact (rises_before (cfg := cfg) (fun k => hnr k w hw) hstE).2.1
      (started_after hadm hid htime (hTH hw) hst)
  by_contra hlt
  have hle : topAt cfg tr time v (s + cfg.timeout n) ≤ n := by omega
  -- `v` built its round-`n` block by `s`, and the round's timer fires by `s + timeout n`
  obtain ⟨b, hbs, hbv, e, hep, her⟩ := built_by hnv (eventsBy tr time s) (hstarted v hv)
    (hall v hv)
  obtain ⟨inp, hb⟩ := Converge.event_of_map hbv
  have hbl : b < tr.length := (List.getElem?_eq_some_iff.mp hb).1
  have htb : time b ≤ s := (lt_eventsBy hmono hbl).mp hbs
  have hset := timer_of_persist hnv hb hep
  rw [her] at hset
  obtain ⟨f, hbf, hf, htf⟩ := htimer.1 b v inp hb hv n (cfg.timeout n) hset (by omega)
  have hfl : f < tr.length := (List.getElem?_eq_some_iff.mp hf).1
  have hfE : f < eventsBy tr time (s + cfg.timeout n) := (lt_eventsBy hmono hfl).mpr (by omega)
  -- at `s + timeout n`, `v` is at round `n`
  set E := eventsBy tr time (s + cfg.timeout n) with hE
  have hsE : eventsBy tr time s ≤ E := eventsBy_mono (by omega)
  have hZs : (stateBefore cfg tr E v).top.isSome :=
    (rises_before (cfg := cfg) hnv hsE).2.1 (hstarted v hv)
  have hZge : n ≤ (stateBefore cfg tr E v).top.getD 0 :=
    (hall v hv).trans (rises_before (cfg := cfg) hnv hsE).1
  have hZle : (stateBefore cfg tr E v).top.getD 0 ≤ n := hle
  have hZt : (stateBefore cfg tr E v).top = some n := by
    obtain ⟨t, ht⟩ := Option.isSome_iff_exists.mp hZs
    rw [ht] at hZge hZle ⊢
    simp only [Option.getD_some] at hZge hZle
    rw [show t = n by omega]
  -- its round's timer has fired, it holds round `n`, and its horizon lies at or below
  have hfired : n ∈ (stateBefore cfg tr E v).fired :=
    fired_stays hnv hf E hfE (by rw [hZt]; simp)
  have hheld : n ≤ (stateBefore cfg tr E v).held := by
    obtain ⟨t', ht', hnt'⟩ := built_le_top hb hep
    rw [her] at hnt'
    have h₁ := (rises_before (cfg := cfg) hnv (show b + 1 ≤ f by omega)).1
    rw [ht'] at h₁
    simp only [Option.getD_some] at h₁
    exact le_trans (by omega) (held_after_timer hnv hf E hfE)
  have hbn : (stateBefore cfg tr E v).store.base ≤ n := by
    rcases (Converge.inv_before (cfg := cfg) (tr := tr) E v).rounds with ⟨h, -, -⟩ | ⟨t, ht, hbt, -⟩
    · rw [hZt] at h; cases h
    · rw [hZt] at ht; cases ht; exact hbt
  -- it holds a quorum of round `n`
  have hown := ownTop_before (cfg := cfg) hnv E n hZt
  obtain ⟨j₀, hj₀, hj₀i, hj₀r, hj₀c⟩ := hown
  have hauth : T ⊆ authorsIn (stateBefore cfg tr E v).store.toRecord
      (stateBefore cfg tr E v).store.ids n := by
    intro w hw
    rw [mem_authorsIn]
    by_cases hwv : w = v
    · subst hwv
      exact ⟨j₀, hj₀i, hj₀r, hj₀c⟩
    · exact round_arrives (τ := s + cfg.timeout n) hq hl hinj htime hTH hnr hmono hdel hsync
        hcmp hw hv hwv hgs (hstarted w hw) (hall w hw) (by omega) hst₁ hZt le_rfl hheld hbn
  have hcard : cfg.q ≤ (authorsIn (stateBefore cfg tr E v).store.toRecord
      (stateBefore cfg tr E v).store.ids n).card := hqT.trans (Finset.card_le_card hauth)
  -- so it builds, against its being settled
  have hsome := tryBuild_isSome (cfg := cfg.at v) hZt hfired hcard
    (fun j hj => by rw [hj₀] at hj; cases hj; exact ⟨hj₀i, hj₀r, hj₀c⟩) hbn
    (fun R => fresh_before hid htime (hTH hv) hZt R)
  rcases settled_before (cfg := cfg) hq hnv E with h | h
  · rw [hZt] at h; cases h
  · rw [h.build] at hsome; cases hsome

end Live

end Node

end LeanDag
