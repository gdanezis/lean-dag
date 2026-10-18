import LeanDag.Node.Converge.Statement
import LeanDag.Node.Helpers.Converge
/-!
# Fetching makes the honest nodes converge — proof

Suppose honest `v` lacks a block of the history of a block `h` honest `u`
broadcast. Then `h` is pending at `v`, and below it a chain of pending
blocks leads to a block `z` that `v` lacks (`chain`). The last of the
chain's pending blocks to arrive arrived after `u` broadcast `h`, when the
rest were pending; its walk reached `z` (`walk_reaches`), so `v` asked for
`z` on its account, for the first time; `u`, which holds `h`'s history
since it broadcast `h`, answered; and `z` arrived, after which it stays
pending or stored, which it is not.
-/

namespace LeanDag

namespace Node

namespace Converge

theorem converges : Converges := by
  intro Validator BlockId Payload _ _ _ cfg H tr hdel htime hinj hbase i u hu huH e he y hy v hv
  obtain ⟨inp, hi⟩ := event_of_map hu
  set L := tr.length
  -- `h`'s history, as the trace reads it, held by `u` from event `i + 1` on
  obtain ⟨hst₁, hval₁⟩ := bcast_stored hbase huH hi he
  have hiL : i < L := (List.getElem?_eq_some_iff.mp hi).1
  have hgr := grows_before (cfg := cfg) (tr := tr) u (show i + 1 ≤ L by omega)
  have hb₁ : (stateBefore cfg tr L u).store.base = (stateBefore cfg tr (i + 1) u).store.base := by
    rw [base_before hbase huH, base_before hbase huH]
  rw [hist_eq hinj hbase huH ((hgr.2 hb₁).1 hst₁)] at hy
  -- the content of a block of the history, as `u` stored it
  set st := (stateBefore cfg tr (i + 1) u).store with hst
  let raw : BlockId → Block Validator BlockId Payload := fun j => st.map.getD j st.junk
  have hHsub := hist_sub hinj hbase huH hst₁
  have hrawk : ∀ j ∈ historyFrom (gT cfg H tr) e.1, (j, raw j) ∈ knownIn cfg H tr :=
    fun j hj => stored_known huH (hHsub hj)
  have hfits : ∀ j ∈ historyFrom (gT cfg H tr) e.1, Fits (cfg.at v) (gT cfg H tr) (j, raw j) :=
    fun j hj => fits_stored hinj hbase huH (hHsub hj) v
  set fin := stateBefore cfg tr L v
  -- a block of the history pending or stored at some time is so at the end
  have hlast : ∀ j ∈ historyFrom (gT cfg H tr) e.1, ∀ t,
      ((j, raw j) ∈ (stateBefore cfg tr t v).pending ∨ j ∈ (stateBefore cfg tr t v).store.ids) →
      t ≤ L → (j, raw j) ∈ fin.pending ∨ j ∈ fin.store.ids := fun j hj t ht htL =>
    keeps_after hinj hbase hv (hfits j hj) ht L htL
  by_contra hyv
  -- `v` lacks `h`, since it would hold its history with it
  have hhv : e.1 ∉ fin.store.ids := fun h' => hyv (hist_sub hinj hbase hv h' hy)
  have hvu : v ≠ u := by rintro rfl; exact hhv ((hgr.2 hb₁).1 hst₁)
  have heH : e.1 ∈ historyFrom (gT cfg H tr) e.1 := mem_historyFrom_self
  have hraw₀ : raw e.1 = e.2 := hval₁
  have hek : e ∈ knownIn cfg H tr := Or.inr ⟨i, u, hu, huH, he⟩
  have hecr : e.2.creator = u :=
    (Local.authored _ _ _ (cfg.at u) (inputsBefore tr (i + 1) u) e (broadcasts_of_event hi he)).2
  -- a block of the history delivered to `v` ends pending or stored there
  have hdeliv : ∀ j ∈ historyFrom (gT cfg H tr) e.1, ∀ t, t < L →
      tr[t]? = some (v, .deliver j (raw j)) → (raw j).creator ≠ v →
      (j, raw j) ∈ fin.pending ∨ j ∈ fin.store.ids := by
    intro j hj t htL ht hcr
    by_cases hc : Admits (cfg.at v) (stateBefore cfg tr t v) j (raw j)
    · exact hlast j hj (t + 1) (admit_after hinj hbase hv ht hc (hfits j hj)) (by omega)
    · have hid : j = cfg.idOf (raw j) := id_of_knownIn (hrawk j hj)
      have hb0 : (stateBefore cfg tr t v).store.base ≤ (raw j).round := by
        rw [base_before hbase hv]; exact Nat.zero_le _
      by_cases hs : j ∈ (stateBefore cfg tr t v).store.ids
      · exact hlast j hj t (Or.inr hs) (by omega)
      · by_cases hp : j ∈ (stateBefore cfg tr t v).pending.map Prod.fst
        · obtain ⟨p, hp, hpj⟩ := List.mem_map.mp hp
          have hpk := knownBefore_sub hv t ((inv_before (cfg := cfg) t v).pend p hp)
          have hpe : p = (j, raw j) := Prod.ext hpj (content_eq hinj hpk (hrawk j hj) hpj)
          exact hlast j hj t (Or.inl (hpe ▸ hp)) (by omega)
        · exact absurd ⟨hid, hcr, hb0, hs, hp⟩ hc
  -- `h` reaches `v`, and ends pending there
  obtain ⟨o, ho, hoe⟩ := List.mem_filterMap.mp he
  have hob : o = .broadcast e.1 e.2 := by
    cases o with
    | broadcast id b =>
      simp only [Option.some.injEq] at hoe
      rw [← hoe]
    | _ => exact absurd hoe (by simp)
  obtain ⟨j₀, hj₀, htj₀⟩ := hdel i u inp hi huH (v, .deliver e.1 e.2) ⟨o, ho, by
    rw [hob]; exact ⟨hvu, rfl⟩⟩ hv
  have hj₀L : j₀ < L := (List.getElem?_eq_some_iff.mp htj₀).1
  have hhp : (e.1, raw e.1) ∈ fin.pending := by
    rcases hdeliv e.1 heH j₀ hj₀L (by rw [hraw₀]; exact htj₀) (by rw [hraw₀, hecr]; exact hvu.symm)
      with h' | h'
    · exact h'
    · exact absurd h' hhv
  -- below `h`, a chain of pending blocks leads to a block `v` lacks
  obtain ⟨len, x, hlen, hx0, hxH, hxc, hxl⟩ :=
    chain hinj hbase huH hv hst₁ raw (fun _ => rfl) (raw e.1).round e.1 heH rfl hhp hhv
  have hround : ∀ k₁ d, k₁ + d + 1 ≤ len →
      (raw (x (k₁ + d + 1))).round < (raw (x k₁)).round := by
    intro k₁ d
    induction d with
    | zero => intro h₂; simp only [Nat.add_zero]; have := (hxc k₁ (by omega)).2.2; omega
    | succ d ih =>
      intro h₂
      have h₃ := (hxc (k₁ + d + 1) (by omega)).2.2
      have h₄ := ih (by omega)
      rw [show k₁ + (d + 1) + 1 = k₁ + d + 1 + 1 by omega]
      omega
  have hxinj : ∀ k₁ k₂, k₁ ≤ len → k₂ ≤ len → x k₁ = x k₂ → k₁ = k₂ := by
    intro k₁ k₂ h₁ h₂ he'
    by_contra hne
    rcases Nat.lt_or_gt_of_ne hne with h | h
    · have := hround k₁ (k₂ - k₁ - 1) (by omega)
      rw [show k₁ + (k₂ - k₁ - 1) + 1 = k₂ by omega, he'] at this; omega
    · have := hround k₂ (k₁ - k₂ - 1) (by omega)
      rw [show k₂ + (k₁ - k₂ - 1) + 1 = k₁ by omega, he'] at this; omega
  -- each pending block of the chain entered once and stayed
  have hent : ∀ k : Fin len, ∃ a < L, (x k, raw (x k)) ∉ (stateBefore cfg tr a v).pending ∧
      ∀ t, a < t → t ≤ L → (x k, raw (x k)) ∈ (stateBefore cfg tr t v).pending :=
    fun k => entry_time (hxc k k.2).1
  choose A hAL hA1 hA2 using hent
  have hentry : ∀ k : Fin len, tr[A k]? = some (v, .deliver (x k) (raw (x k))) ∧
      Admits (cfg.at v) (stateBefore cfg tr (A k) v) (x k) (raw (x k)) := fun k =>
    entry_before (hA1 k) (hA2 k (A k + 1) (by omega) (by have := hAL k; omega))
  -- the last of them to arrive
  obtain ⟨m, -, hmax⟩ := Finset.exists_max_image Finset.univ A ⟨⟨0, hlen⟩, Finset.mem_univ _⟩
  have hAlt : ∀ k : Fin len, m.1 < k.1 → A k < A m := by
    intro k hk
    refine lt_of_le_of_ne (hmax k (Finset.mem_univ _)) fun hAe => ?_
    have h₁ := (hentry k).1
    have h₂ := (hentry m).1
    rw [hAe, h₂] at h₁
    simp only [Option.some.injEq, Prod.mk.injEq, Input.deliver.injEq] at h₁
    have := hxinj k m (by omega) (by omega) h₁.2.1.symm
    omega
  -- the delivery of the last arrival, and the state its walk ran on
  obtain ⟨htm, hcm⟩ := hentry m
  have hAmL : A m < L := hAL m
  set Sm := stateBefore cfg tr (A m) v
  let s₁ := afterFlush (cfg := cfg.at v) Sm (x m) (raw (x m))
  have hstepm := step_before (cfg := cfg) htm
  rw [step_deliver hcm] at hstepm
  have hRm := reads_before hinj hbase hv (A m)
  have hxmk : (x m, raw (x m)) ∈ knownIn cfg H tr := hrawk _ (hxH m (by omega)).1
  have hpbm : ∀ q ∈ (x m, raw (x m)) :: Sm.pending, gT cfg H tr q.1 = atBase 0 q.2 := by
    intro q hq
    rcases List.mem_cons.mp hq with rfl | hq
    · exact gT_of_known hinj hxmk
    · exact pend_before hinj hv (A m) q hq
  have hknm : ∀ q ∈ (x m, raw (x m)) :: Sm.pending, q ∈ knownIn cfg H tr := by
    intro q hq
    rcases List.mem_cons.mp hq with rfl | hq
    · exact hxmk
    · exact knownBefore_sub hv (A m) ((inv_before (cfg := cfg) (A m) v).pend q hq)
  -- `s₁`'s store grows into the end's
  have hg₁ : Grows s₁.store (stateBefore cfg tr (A m + 1) v).store := by
    rw [hstepm]; exact Grows.settle_of _ rfl
  have hb₁' : (stateBefore cfg tr (A m + 1) v).store.base = s₁.store.base := by
    rw [base_before hbase hv]
    exact ((flush_base (cfg := cfg.at v) _ _ _).trans (base_before hbase hv (A m))).symm
  have hgend := grows_before (cfg := cfg) (tr := tr) v (show A m + 1 ≤ L by omega)
  have hbend : fin.store.base = (stateBefore cfg tr (A m + 1) v).store.base := by
    rw [base_before hbase hv, base_before hbase hv]
  have hs₁fin : ∀ j ∈ s₁.store.ids, j ∈ fin.store.ids := fun j hj =>
    (hgend.2 hbend).1 ((hg₁.2 hb₁').1 hj)
  -- the later blocks of the chain are pending in `s₁`
  have hF1 : ∀ k : Fin len, m.1 < k.1 → (x k, raw (x k)) ∈ s₁.pending := by
    intro k hk
    have hin := hA2 k (A m) (hAlt k hk) (by omega)
    rcases flush_keeps (cfg := cfg.at v) (Sm.pending.length + 1) hRm hpbm (hfits _ (hxH k (by omega)).1)
      (List.mem_cons_of_mem _ hin) with h' | h'
    · exact h'
    · exact absurd (hs₁fin _ h') (hxH k (by omega)).2
  -- the block `v` lacks is neither stored nor pending in `s₁`
  have hF2 : x len ∉ s₁.store.ids := fun h' => (hxH len le_rfl).2 (hs₁fin _ h')
  have hF3 : x len ∉ s₁.pending.map Prod.fst := by
    intro h'
    obtain ⟨q, hq, hqx⟩ := List.mem_map.mp h'
    have hqk := hknm q (flush_pending_sub (cfg := cfg.at v) _ _ _ q hq)
    have hqe : q = (x len, raw (x len)) :=
      Prod.ext hqx (content_eq hinj hqk (hrawk _ (hxH len le_rfl).1) hqx)
    have hR₁ : ReadsAs (gT cfg H tr) (stateBefore cfg tr (A m + 1) v).store :=
      reads_before hinj hbase hv _
    rw [hstepm] at hR₁
    have hk := settle_keeps (cfg := cfg.at v) hR₁ (by rw [← hstepm]; exact hb₁')
      (ReadsAs.flush (cfg := cfg.at v) _ hRm hpbm).2 (hfits _ (hxH len le_rfl).1)
      (Or.inl (hqe ▸ hq))
    rw [← hstepm] at hk
    rcases hlast _ (hxH len le_rfl).1 (A m + 1) hk (by omega) with h'' | h''
    · exact hxl (List.mem_map.mpr ⟨_, h'', rfl⟩)
    · exact (hxH len le_rfl).2 h''
  -- the walk from the last arrival reaches the block `v` lacks
  have hs₁b : s₁.store.base = 0 := (flush_base (cfg := cfg.at v) _ _ _).trans
    (base_before hbase hv (A m))
  have hmlen : m.1 < len := m.2
  set n := len - m.1 - 1 with hn
  let y : ℕ → BlockId × ℕ := fun k => (x (m.1 + 1 + k), (raw (x (m.1 + k))).round - 1)
  have hexp : ∀ k, m.1 < k → k < len → ∀ q ∈ (raw (x k)).refs,
      (q, (raw (x k)).round - 1) ∈ expand s₁ (x k) := by
    intro k hmk hkl q hq
    have hp := hF1 ⟨k, hkl⟩ hmk
    rcases hfind : s₁.pending.find? (fun e => decide (e.1 = x k)) with _ | ⟨p', b'⟩
    · exact absurd (List.find?_eq_none.mp hfind _ hp) (by simp)
    · have hm' := List.mem_of_find?_eq_some hfind
      have hid := List.find?_some hfind
      simp only [decide_eq_true_eq] at hid
      have hb' : b' = raw (x k) := content_eq hinj
        (hknm _ (flush_pending_sub (cfg := cfg.at v) _ _ _ _ hm')) (hrawk _ (hxH k (by omega)).1) hid
      simp only [expand, hfind, hb']
      exact List.mem_map.mpr ⟨q, (Finset.mem_sort _).mpr hq, rfl⟩
  have hdist : n ≤ s₁.pending.length := by
    have hsub : (Finset.range n).image (fun k => x (m.1 + 1 + k)) ⊆
        (s₁.pending.map Prod.fst).toFinset := by
      intro j hj
      obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp hj
      rw [Finset.mem_range] at hk
      exact List.mem_toFinset.mpr (List.mem_map.mpr ⟨_, hF1 ⟨m.1 + 1 + k, by omega⟩ (show m.1 < m.1 + 1 + k by omega), rfl⟩)
    have hcard := Finset.card_le_card hsub
    rw [Finset.card_image_of_injOn (fun k₁ hk₁ k₂ hk₂ he' => by
      have := hxinj _ _ (by simp at hk₁; omega) (by simp at hk₂; omega) he'; omega),
      Finset.card_range] at hcard
    exact hcard.trans ((List.toFinset_card_le _).trans (by simp))
  obtain ⟨w, hw, hwx⟩ := walk_reaches (s := s₁) (fuel := s₁.pending.length + 2)
    (((raw (x m)).refs.sort (· ≤ ·)).map fun j => (j, (raw (x m)).round - 1)) (n := n) y
    (List.mem_map.mpr ⟨x (m.1 + 1), (Finset.mem_sort _).mpr (by
      simpa using (hxc m (by omega)).2.1), by simp [y]⟩)
    (fun k hk => ⟨by rw [hs₁b]; exact Nat.zero_le _, fun h' =>
      (hxH (m.1 + 1 + k) (by omega)).2 (hs₁fin _ h')⟩)
    (fun k hk => List.mem_map.mpr ⟨_, hF1 ⟨m.1 + 1 + k, by omega⟩ (show m.1 < m.1 + 1 + k by omega), rfl⟩)
    (fun k hk => by
      have := hexp (m.1 + 1 + k) (by omega) (by omega) (x (m.1 + 1 + (k + 1)))
        (by have := (hxc (m.1 + 1 + k) (by omega)).2.1; rwa [show m.1 + 1 + k + 1 =
          m.1 + 1 + (k + 1) by omega] at this)
      simpa [y, show m.1 + (k + 1) = m.1 + 1 + k by omega] using this)
    (by simpa [y, show m.1 + 1 + n = len by omega] using hF3) (by omega)
  have hwx' : w.1 = x len := by rw [hwx]; simp [y, show m.1 + 1 + n = len by omega]
  -- `v` had not asked for it on the last arrival's account
  have hnreq : (w.1, x m) ∉ s₁.requested.map fun q => (q.1, q.2.1) := by
    intro h'
    obtain ⟨q, hq, hqe⟩ := List.mem_map.mp h'
    simp only [Prod.mk.injEq] at hqe
    obtain ⟨a', ha', b, hab, hca⟩ := requested_before (cfg := cfg) (tr := tr) v (A m) q hq
    rw [hqe.2] at hab hca
    have hbk : (x m, b) ∈ knownIn cfg H tr := Or.inl ⟨a', v, hab, hv, hca.1⟩
    have hbe : b = raw (x m) := content_eq hinj hbk hxmk rfl
    rw [hbe] at hab hca
    have hk := admit_after hinj hbase hv hab hca (hfits _ (hxH m (by omega)).1)
    rcases keeps_after hinj hbase hv (hfits _ (hxH m (by omega)).1) hk (A m) (by omega) with
      h'' | h''
    · exact hA1 m h''
    · exact (hxH m (by omega)).2 ((grows_before (cfg := cfg) (tr := tr) v (show A m ≤ L by omega)).2
        (by rw [base_before hbase hv, base_before hbase hv]) |>.1 h'')
  -- so it asked for it at the last arrival, and `u` got the request
  set miss := missing s₁ (x m) (raw (x m))
  have hwm : w ∈ miss := List.mem_filter.mpr ⟨hw, by simpa using hnreq⟩
  have hout : outputsAt cfg tr (A m) = (if miss.isEmpty then [] else [.fetch (miss.map Prod.fst)]) ++
      (Node.settle (cfg.at v) { s₁ with
        requested := s₁.requested ++ miss.map fun q => (q.1, x m, q.2) }).2 := by
    rw [outputsAt_eq htm, step_deliver hcm]
  have hne : miss.isEmpty = false := by
    rw [List.isEmpty_eq_false_iff]; exact List.ne_nil_of_mem hwm
  obtain ⟨k, hkm, htk⟩ := hdel (A m) v _ htm hv (u, .fetchRequest v (miss.map Prod.fst))
    ⟨.fetch (miss.map Prod.fst), by rw [hout, hne]; simp, ⟨hvu.symm, rfl⟩⟩ huH
  have hkL : k < L := (List.getElem?_eq_some_iff.mp htk).1
  -- `u` broadcast `h` before it reached `v`, so holds its history by `k`
  have h0 : (0 : ℕ) < len := hlen
  obtain ⟨ht0, -⟩ := hentry ⟨0, h0⟩
  simp only [hx0] at ht0
  obtain ⟨i', hi'A, hi'u, hi'b⟩ := htime (A ⟨0, h0⟩) v e.1 (raw e.1) ht0 hv
    (by rw [hraw₀, hecr]; exact huH) (id_of_knownIn (hrawk _ heH))
  rw [hraw₀, hecr] at hi'u
  obtain ⟨inp', hi'⟩ := event_of_map hi'u
  have hst' := (bcast_stored hbase huH hi' (by rw [hraw₀] at hi'b; exact hi'b)).1
  have hA0 : A ⟨0, h0⟩ ≤ A m := hmax ⟨0, h0⟩ (Finset.mem_univ _)
  have hgk := grows_before (cfg := cfg) (tr := tr) u (show i' + 1 ≤ k by omega)
  have hzk : x len ∈ (stateBefore cfg tr k u).store.ids :=
    (hgk.2 (by rw [base_before hbase huH, base_before hbase huH])).1
      (hist_sub hinj hbase huH hst' (hxH len le_rfl).1)
  -- `u` answers, and the block reaches `v`
  set rk := (stateBefore cfg tr k u).store.map.getD (x len) (stateBefore cfg tr k u).store.junk
  have hans : Output.send v (x len) rk ∈ outputsAt cfg tr k := by
    rw [outputsAt_eq htk]
    change Output.send v (x len) rk ∈ answer _ v (miss.map Prod.fst)
    unfold answer
    exact List.mem_map.mpr ⟨x len, List.mem_filter.mpr ⟨List.mem_map.mpr ⟨w, hwm, hwx'⟩,
      by simpa using hzk⟩, rfl⟩
  obtain ⟨k', hk'k, htk'⟩ := hdel k u _ htk huH (v, .deliver (x len) rk) ⟨_, hans, rfl, rfl⟩ hv
  have hk'L : k' < L := (List.getElem?_eq_some_iff.mp htk').1
  have hrk : rk = raw (x len) :=
    content_eq hinj (stored_known huH hzk) (hrawk _ (hxH len le_rfl).1) rfl
  rw [hrk] at htk'
  -- `v` acts on it, so it ends pending or stored there, which it does not
  have hcr : (raw (x len)).creator ≠ v := by
    intro hc
    rcases hrawk _ (hxH len le_rfl).1 with ⟨j, w', hj, hw', hid⟩ | ⟨j, w', hj, hw', hb⟩
    · obtain ⟨i'', -, hi''v, hi''b⟩ := htime j w' _ _ hj hw' (by rw [hc]; exact hv) hid
      rw [hc] at hi''v
      obtain ⟨inp'', hi''⟩ := event_of_map hi''v
      have := (bcast_stored hbase hv hi'' hi''b).1
      exact (hxH len le_rfl).2 ((grows_before (cfg := cfg) (tr := tr) v
        (show i'' + 1 ≤ L by have := (List.getElem?_eq_some_iff.mp hi'').1; omega)).2
        (by rw [base_before hbase hv, base_before hbase hv]) |>.1 this)
    · obtain ⟨inp'', hj'⟩ := event_of_map hj
      have hcw := (Local.authored _ _ _ (cfg.at w') (inputsBefore tr (j + 1) w') _
        (broadcasts_of_event hj' hb)).2
      change (raw (x len)).creator = w' at hcw
      have hwv : w' = v := hcw.symm.trans hc
      subst hwv
      have := (bcast_stored hbase hv hj' hb).1
      exact (hxH len le_rfl).2 ((grows_before (cfg := cfg) (tr := tr) w'
        (show j + 1 ≤ L by have := (List.getElem?_eq_some_iff.mp hj').1; omega)).2
        (by rw [base_before hbase hv, base_before hbase hv]) |>.1 this)
  rcases hdeliv (x len) (hxH len le_rfl).1 k' hk'L htk' hcr with h' | h'
  · exact hxl (List.mem_map.mpr ⟨_, h', rfl⟩)
  · exact (hxH len le_rfl).2 h'

theorem holds : Statement := converges

end Converge

end Node

end LeanDag
