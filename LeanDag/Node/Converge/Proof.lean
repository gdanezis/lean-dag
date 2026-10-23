import LeanDag.Node.Converge.Statement
import LeanDag.Node.Helpers.Converge
import LeanDag.Node.Helpers.Agree
import LeanDag.Node.Helpers.Held
/-!
# Fetching makes the honest nodes converge — proof

Suppose honest `v` lacks a block of the history of a block `h` honest `u`
broadcast. Then `h` is pending at `v`, and below it a chain of pending
blocks leads to a block `z` that `v` lacks (`chain`). The last of the
chain's pending blocks to arrive arrived after `u` broadcast `h`, when the
rest were pending; its walk reached `z` (`walk_reaches`), so `v` asked for
`z` on its account, for the first time, from its round `r`; `u`, which
holds `h`'s history since it broadcast `h`, answered; and `z` arrived,
after which it stays pending or stored, which it is not.

The answer leaves out what a block of `v`'s core reaches. If a block of
the chain below the asked one has round-`(r − 1)` blocks of at least
`n − q + f + 1` authors reaching it in `u`'s store (`mem_coreSets`), at
least `n − q + 1` of these authors are honest. At round `r`, `v` held
round-`(r − 1)` blocks of `q` authors (`Quorate`), so one of them is such
an honest author, whose one block of that round (`eq_of_persists`) `v`
then holds, with `z` in its history. Otherwise the pruned history of the
asked block contains `z` (`pruned_chain`), and `u` sends it.
-/

namespace LeanDag

namespace Node

namespace Converge


theorem converges : Converges := by
  intro Validator BlockId Payload _ _ _ cfg H tr hf hdel htime hinj i u hu huH e he y hy v hv
  obtain ⟨inp, hi⟩ := event_of_map hu
  set L := tr.length
  -- `h`'s history, as the trace reads it, held by `u` from event `i + 1` on
  obtain ⟨hst₁, hval₁⟩ := broadcast_stored hi he
  have hiL : i < L := (List.getElem?_eq_some_iff.mp hi).1
  have hgr := grows_before (cfg := cfg) (tr := tr) u (show i + 1 ≤ L by omega)
  rw [hist_eq hinj huH (hgr.1 hst₁)] at hy
  -- the content of a block of the history, as `u` stored it
  set st := (stateBefore cfg tr (i + 1) u).disk with hst
  let raw : BlockId → Block Validator BlockId Payload := fun j => st.blk j
  have hHsub := hist_sub hinj huH hst₁
  have hrawk : ∀ j ∈ historyFrom (gT cfg H tr) e.1, (j, raw j) ∈ knownIn cfg H tr :=
    fun j hj => stored_known huH (hHsub hj)
  have hfits : ∀ j ∈ historyFrom (gT cfg H tr) e.1, Fits (cfg.at v) (gT cfg H tr) (j, raw j) :=
    fun j hj => fits_stored hinj huH (hHsub hj) v
  set fin := stateBefore cfg tr L v
  -- a block of the history pending or stored at some time is so at the end
  have hlast : ∀ j ∈ historyFrom (gT cfg H tr) e.1, ∀ t,
      ((j, raw j) ∈ (stateBefore cfg tr t v).pending ∨ j ∈ (stateBefore cfg tr t v).disk.ids) →
      t ≤ L → (j, raw j) ∈ fin.pending ∨ j ∈ fin.disk.ids := fun j hj t ht htL =>
    keeps_after hinj hv (hfits j hj) ht L htL
  by_contra hyv
  -- `v` lacks `h`, since it would hold its history with it
  have hhv : e.1 ∉ fin.disk.ids := fun h' => hyv (hist_sub hinj hv h' hy)
  have hvu : v ≠ u := by rintro rfl; exact hhv (hgr.1 hst₁)
  have heH : e.1 ∈ historyFrom (gT cfg H tr) e.1 := mem_historyFrom_self
  have hraw₀ : raw e.1 = e.2 := hval₁
  have hecr : e.2.creator = u := by
    obtain ⟨j, -, inp', hj', hje⟩ := persists_of_broadcasts hi he
    exact (Local.authored _ _ _ (cfg.at u) (inputsBefore tr (j + 1) u) e
      (persists_of_event hj' hje)).2
  -- a block of the history delivered to `v` ends pending or stored there
  have hdeliv : ∀ j ∈ historyFrom (gT cfg H tr) e.1, ∀ t, t < L →
      tr[t]? = some (v, .deliver j (raw j)) → (raw j).creator ≠ v →
      (j, raw j) ∈ fin.pending ∨ j ∈ fin.disk.ids := by
    intro j hj t htL ht hcr
    by_cases hc : Admits (cfg.at v) (stateBefore cfg tr t v) j (raw j)
    · exact hlast j hj (t + 1) (admit_after hinj hv ht hc (hfits j hj)) (by omega)
    · have hid : j = cfg.idOf (raw j) := id_of_knownIn (hrawk j hj)
      by_cases hs : j ∈ (stateBefore cfg tr t v).disk.ids
      · exact hlast j hj t (Or.inr hs) (by omega)
      · by_cases hp : j ∈ (stateBefore cfg tr t v).pending.map Prod.fst
        · obtain ⟨p, hp, hpj⟩ := List.mem_map.mp hp
          have hpk := knownBefore_sub hv t ((inv_before (cfg := cfg) t v).pend p hp)
          have hpe : p = (j, raw j) := Prod.ext hpj (content_eq hinj hpk (hrawk j hj) hpj)
          exact hlast j hj t (Or.inl (hpe ▸ hp)) (by omega)
        · exact absurd ⟨hid, hcr, hs, hp⟩ hc
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
    chain hinj huH hv hst₁ raw (fun _ => rfl) (raw e.1).round e.1 heH rfl hhp hhv
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
  -- `h` entered pending once and stayed; its arrival is the anchor
  have hent : ∀ k : Fin len, ∃ a < L, (x k, raw (x k)) ∉ (stateBefore cfg tr a v).pending ∧
      ∀ t, a < t → t ≤ L → (x k, raw (x k)) ∈ (stateBefore cfg tr t v).pending :=
    fun k => entry_time (hxc k k.2).1
  choose A hAL hA1 hA2 using hent
  have hentry : ∀ k : Fin len, tr[A k]? = some (v, .deliver (x k) (raw (x k))) ∧
      Admits (cfg.at v) (stateBefore cfg tr (A k) v) (x k) (raw (x k)) := fun k =>
    entry_before (hA1 k) (hA2 k (A k + 1) (by omega) (by have := hAL k; omega))
  set m : Fin len := ⟨0, hlen⟩ with hm
  -- the delivery of `h`, and the state its walk ran on
  obtain ⟨htm, hcm⟩ := hentry m
  have hAmL : A m < L := hAL m
  set Sm := stateBefore cfg tr (A m) v
  let s₁ := afterFlush (cfg := cfg.at v) Sm (x m) (raw (x m))
  have hs₁p : s₁.pending = (flushOn (cfg.at v) (Sm.pending.length + 1) Sm.disk
      ((x m, raw (x m)) :: Sm.pending)).2 := afterFlush_pending _ _ _
  have hstepm : stateBefore cfg tr (A m + 1) v = (settle (cfg.at v) s₁).1 := by
    rw [step_before (cfg := cfg) htm, step_deliver hcm]
  have hRm := reads_before hinj hv (A m)
  have hxmk : (x m, raw (x m)) ∈ knownIn cfg H tr := hrawk _ (hxH m (by omega)).1
  have hpbm : ∀ q ∈ (x m, raw (x m)) :: Sm.pending, gT cfg H tr q.1 = q.2 := by
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
  have hg₁ : Grows s₁.disk (stateBefore cfg tr (A m + 1) v).disk := by
    rw [hstepm]; exact Grows.settle_of _ rfl
  have hgend := grows_before (cfg := cfg) (tr := tr) v (show A m + 1 ≤ L by omega)
  have hs₁fin : ∀ j ∈ s₁.disk.ids, j ∈ fin.disk.ids := fun j hj => hgend.1 (hg₁.1 hj)
  -- the block `v` lacks is neither stored nor pending in `s₁`
  have hF2 : x len ∉ s₁.disk.ids := fun h' => (hxH len le_rfl).2 (hs₁fin _ h')
  have hF3 : x len ∉ s₁.pending.map Prod.fst := by
    intro h'
    obtain ⟨q, hq, hqx⟩ := List.mem_map.mp h'
    have hqk := hknm q (flush_pending_sub (cfg := cfg.at v) _ _ _ q (hs₁p ▸ hq))
    have hqe : q = (x len, raw (x len)) :=
      Prod.ext hqx (content_eq hinj hqk (hrawk _ (hxH len le_rfl).1) hqx)
    have hR₁ : ReadsAs (gT cfg H tr) (stateBefore cfg tr (A m + 1) v).disk :=
      reads_before hinj hv _
    rw [hstepm] at hR₁
    have hp₁ : ∀ q ∈ s₁.pending, gT cfg H tr q.1 = q.2 := by
      rw [hs₁p]; exact (ReadsAs.flush (cfg := cfg.at v) _ hRm hpbm).2
    have hq' : (x len, raw (x len)) ∈ s₁.pending := hqe ▸ hq
    have hk := settle_keeps (cfg := cfg.at v) hR₁ hp₁ (hfits _ (hxH len le_rfl).1) (Or.inl hq')
    rw [← hstepm] at hk
    rcases hlast _ (hxH len le_rfl).1 (A m + 1) hk (by omega) with h'' | h''
    · exact hxl (List.mem_map.mpr ⟨_, h'', rfl⟩)
    · exact (hxH len le_rfl).2 h''
  -- the first block of the chain below `h` not pending in `s₁`
  have hP : ∃ j, m.1 < j ∧ j ≤ len ∧ x j ∉ s₁.pending.map Prod.fst :=
    ⟨len, hlen, le_rfl, hF3⟩
  classical
  set K := Nat.find hP with hK
  obtain ⟨hmK, hKlen, hKp⟩ : m.1 < K ∧ K ≤ len ∧ x K ∉ s₁.pending.map Prod.fst :=
    Nat.find_spec hP
  have hF1 : ∀ j, m.1 < j → j < K → (x j, raw (x j)) ∈ s₁.pending := by
    intro j hmj hjK
    have hj : x j ∈ s₁.pending.map Prod.fst := by
      by_contra hn; exact Nat.find_min hP hjK ⟨hmj, by omega, hn⟩
    obtain ⟨q, hq, hqx⟩ := List.mem_map.mp hj
    have hqk := hknm q (flush_pending_sub (cfg := cfg.at v) _ _ _ q (hs₁p ▸ hq))
    rwa [show q = (x j, raw (x j)) from
      Prod.ext hqx (content_eq hinj hqk (hrawk _ (hxH j (by omega)).1) hqx)] at hq
  -- the walk from `h` reaches it
  have hmlen : m.1 < len := m.2
  set n := K - m.1 - 1 with hn
  let y : ℕ → BlockId := fun k => x (m.1 + 1 + k)
  have hexp : ∀ k, m.1 < k → k < K → ∀ q ∈ (raw (x k)).refs, q ∈ expand s₁ (x k) := by
    intro k hmk hkl q hq
    have hp := hF1 k hmk hkl
    rcases hfind : s₁.pending.find? (fun e => decide (e.1 = x k)) with _ | ⟨p', b'⟩
    · exact absurd (List.find?_eq_none.mp hfind _ hp) (by simp)
    · have hm' := List.mem_of_find?_eq_some hfind
      have hid := List.find?_some hfind
      simp only [decide_eq_true_eq] at hid
      have hb' : b' = raw (x k) := content_eq hinj
        (hknm _ (flush_pending_sub (cfg := cfg.at v) _ _ _ _ (hs₁p ▸ hm')))
        (hrawk _ (hxH k (by omega)).1) hid
      simp only [expand, hfind, hb']
      exact (Finset.mem_sort _).mpr hq
  have hdist : n ≤ s₁.pending.length := by
    have hsub : (Finset.range n).image (fun k => x (m.1 + 1 + k)) ⊆
        (s₁.pending.map Prod.fst).toFinset := by
      intro j hj
      obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp hj
      rw [Finset.mem_range] at hk
      exact List.mem_toFinset.mpr
        (List.mem_map.mpr ⟨_, hF1 (m.1 + 1 + k) (by omega) (by omega), rfl⟩)
    have hcard := Finset.card_le_card hsub
    rw [Finset.card_image_of_injOn (fun k₁ hk₁ k₂ hk₂ he' => by
      have := hxinj _ _ (by simp at hk₁; omega) (by simp at hk₂; omega) he'; omega),
      Finset.card_range] at hcard
    exact hcard.trans ((List.toFinset_card_le _).trans (by simp))
  have hw := walk_reaches (s := s₁) (fuel := s₁.pending.length + 2)
    ((raw (x m)).refs.sort (· ≤ ·)) (n := n) y
    ((Finset.mem_sort _).mpr (by simpa [y] using (hxc m (by omega)).2.1))
    (fun k hk h' => (hxH (m.1 + 1 + k) (by omega)).2 (hs₁fin _ h'))
    (fun k hk => List.mem_map.mpr ⟨_, hF1 (m.1 + 1 + k) (by omega) (by omega), rfl⟩)
    (fun k hk => by
      have := hexp (m.1 + 1 + k) (by omega) (by omega) (x (m.1 + 1 + (k + 1)))
        (by have := (hxc (m.1 + 1 + k) (by omega)).2.1; rwa [show m.1 + 1 + k + 1 =
          m.1 + 1 + (k + 1) by omega] at this)
      simpa [y] using this)
    (by simpa [y, show m.1 + 1 + n = K by omega] using hKp) (by omega)
  have hwx' : y n = x K := by simp [y, show m.1 + 1 + n = K by omega]
  rw [hwx'] at hw
  -- so it asked `h`'s author `u` for it at `h`'s arrival, from its round `r`
  set miss := missing s₁ (raw (x m))
  set r := Sm.top.getD 0 with hr
  have hwm : x K ∈ miss := hw
  obtain ⟨rest, hout⟩ : ∃ rest, outputsAt cfg tr (A m) =
      (if miss.isEmpty then [] else [.fetch (raw (x m)).creator r miss]) ++ rest :=
    ⟨_, by rw [outputsAt_eq htm, step_deliver hcm]⟩
  have hne : miss.isEmpty = false := by
    rw [List.isEmpty_eq_false_iff]; exact List.ne_nil_of_mem hwm
  clear_value miss
  have hxm0 : x m = e.1 := hx0
  have hcrm : (raw (x m)).creator = u := by rw [hxm0, hraw₀, hecr]
  obtain ⟨k, hkm, htk⟩ := hdel (A m) v _ htm hv (u, .fetchRequest v r miss)
    ⟨.fetch (raw (x m)).creator r miss, by rw [hout, hne]; simp, ⟨hcrm.symm, rfl⟩⟩ huH
  have hkL : k < L := (List.getElem?_eq_some_iff.mp htk).1
  -- `u` broadcast `h` before it reached `v`, so holds its history by `k`
  have h0 : (0 : ℕ) < len := hlen
  obtain ⟨ht0, -⟩ := hentry ⟨0, h0⟩
  simp only [hx0] at ht0
  have hid₀ : e.1 = (cfg.at v).idOf (raw e.1) := id_of_knownIn (hrawk _ heH)
  obtain ⟨i', hi'A, hi'u, hi'b⟩ := htime (A ⟨0, h0⟩) v _ ht0 hv (e.1, raw e.1)
    (by simp [delivered, ← hid₀]) (by rw [hraw₀, hecr]; exact huH)
  rw [hraw₀, hecr] at hi'u
  obtain ⟨inp', hi'⟩ := event_of_map hi'u
  have hst' := (broadcast_stored hi' (by rw [hraw₀] at hi'b; exact hi'b)).1
  have hA0 : A ⟨0, h0⟩ ≤ A m := le_rfl
  have hgk := grows_before (cfg := cfg) (tr := tr) u (show i' + 1 ≤ k by omega)
  have hzk : x len ∈ (stateBefore cfg tr k u).disk.ids :=
    hgk.1 (hist_sub hinj huH hst' (hxH len le_rfl).1)
  have hKk : x K ∈ (stateBefore cfg tr k u).disk.ids :=
    hgk.1 (hist_sub hinj huH hst' (hxH K hKlen).1)
  -- the chain from `x K` down, as `u` reads it at `k`
  set stk := (stateBefore cfg tr k u).disk
  have hRk := reads_before hinj huH k
  have hblkk : ∀ k₀, k₀ ≤ len → stk.blk (x k₀) = raw (x k₀) := fun k₀ hk₀ =>
    (hRk _ (hgk.1 (hist_sub hinj huH hst' (hxH k₀ hk₀).1))).trans
      (gT_of_known hinj (hrawk _ (hxH k₀ hk₀).1))
  have hreach : ∀ k₀ d, k₀ + d ≤ len → ReachesFrom stk.blk (x k₀) (x (k₀ + d)) := by
    intro k₀ d
    induction d with
    | zero => intro _; exact ReachesFrom.refl
    | succ d ih =>
      intro hd
      have hr' : (x (k₀ + (d + 1))) ∈ (stk.blk (x (k₀ + d))).refs := by
        rw [hblkk _ (by omega)]; exact (hxc (k₀ + d) (by omega)).2.1
      exact (ih (by omega)).trans (ReachesFrom.single hr')
  have hrounds : ∀ d, K + d ≤ len → (raw (x (K + d))).round + d = (raw (x K)).round := by
    intro d
    induction d with
    | zero => intro _; rfl
    | succ d ih =>
      intro hd
      have := (hxc (K + d) (by omega)).2.2
      rw [show K + d + 1 = K + (d + 1) by omega] at this
      have := ih (by omega)
      omega
  -- `u` answers with `x len`: no block of the chain below `x K` is in the
  -- asker's core, since `v` holds what such a block reaches
  have hsent : x len ∈ historyUptoFrom (pruned (cfg.at u) stk r)
      ((stk.blk (x K)).round + 1) (x K) := by
    by_cases hnc : ∀ k', K < k' → k' ≤ len →
        ¬ coreThreshold (cfg.at u) ≤ ((coreSets (cfg.at u) stk r).getD (x k') ∅).card
    · have hd := pruned_chain (cfg.at u) stk (r := r) (K := K) (len := len) (x := x)
        (fun k' _ h₂ => by rw [hblkk k' (by omega)]; exact (hxc k' h₂).2.1) hnc (len - K)
        (by omega)
      rw [show len - (len - K) = K by omega] at hd
      refine historyUptoFrom_mono ?_ _ hd
      have := hrounds (len - K) (by omega)
      rw [hblkk K hKlen]
      omega
    · exfalso
      push Not at hnc
      obtain ⟨k', hKk', hk'len, hcore⟩ := hnc
      -- the round is positive, since the sweep records nothing at round 0
      have hr0 : r ≠ 0 := by
        intro h0
        rw [h0] at hcore
        unfold coreSets at hcore
        simp [coreThreshold] at hcore
      obtain ⟨r', hr'⟩ : ∃ r', Sm.top = some r' := by
        rcases h : Sm.top with _ | r'
        · exact absurd (by rw [hr, h]; rfl) hr0
        · exact ⟨r', rfl⟩
      have hrr : r = r' := by rw [hr, hr']; rfl
      -- `v` held blocks of a quorum `Q` of round-`(r − 1)` authors
      have hQ : cfg.q ≤ (authorsIn Sm.disk.toRecord Sm.disk.ids (r - 1)).card := by
        have := Quorate.run (cfg := cfg.at v) (inputsBefore tr (A m) v) Quorate.init r' hr'
          (by omega)
        rw [hrr]; exact this
      -- an honest author lies in both `Q` and the core set of `x k'`
      set C := (coreSets (cfg.at u) stk r).getD (x k') ∅
      set Q := authorsIn Sm.disk.toRecord Sm.disk.ids (r - 1)
      have hCH : (C \ H).card ≤ cfg.f :=
        (Finset.card_le_card fun a ha => Finset.mem_compl.mpr (Finset.mem_sdiff.mp ha).2).trans hf
      have h₁ := Finset.card_inter_add_card_sdiff C H
      have h₂ := Finset.card_union_add_card_inter Q (C ∩ H)
      have h₃ : (Q ∪ (C ∩ H)).card ≤ Fintype.card Validator := Finset.card_le_univ _
      have h₄ : Q.card ≤ Fintype.card Validator := Finset.card_le_univ _
      have hthr : coreThreshold (cfg.at u) = Fintype.card Validator - cfg.q + cfg.f + 1 := rfl
      obtain ⟨a, ha⟩ : (Q ∩ (C ∩ H)).Nonempty := Finset.card_pos.mp (by omega)
      obtain ⟨haQ, haC, haH⟩ : a ∈ Q ∧ a ∈ C ∧ a ∈ H := by
        simp only [Finset.mem_inter] at ha; exact ⟨ha.1, ha.2.1, ha.2.2⟩
      obtain ⟨yv, hyv, hyvr, hyvc⟩ := mem_authorsIn.mp haQ
      obtain ⟨yu, hyu, hyur, hyuc, hyureach⟩ := mem_coreSets (cfg.at u) stk haC
      have hyvr' : (Sm.disk.blk yv).round = r - 1 := hyvr
      have hyvc' : (Sm.disk.blk yv).creator = a := hyvc
      -- an honest author has one block a round, so `v` held the one `u` reads
      have hinjR := hashInjective_of_trace hinj
      have hauthR := authentic_of_timely htime
      have hkv : (yv, Sm.disk.blk yv) ∈ knownAll cfg H tr :=
        ⟨v, hv, knownBefore_knownOf ((inv_before (cfg := cfg) (A m) v).known yv hyv)⟩
      have hku : (yu, stk.blk yu) ∈ knownAll cfg H tr :=
        ⟨u, huH, knownBefore_knownOf ((inv_before (cfg := cfg) k u).known yu hyu)⟩
      have hpv := mem_persists_of_known hinjR hauthR hkv (by dsimp only; rw [hyvc']; exact haH)
      have hpu := mem_persists_of_known hinjR hauthR hku (by dsimp only; rw [hyuc]; exact haH)
      dsimp only at hpv hpu
      rw [hyvc'] at hpv
      rw [hyuc] at hpu
      have hyy : yv = yu :=
        congrArg Prod.fst (eq_of_persists a hpv hpu (by dsimp only; rw [hyvr', hyur]))
      subst hyy
      -- the block reaches `x len`, which `v` then holds
      have hyl : ReachesFrom stk.blk yv (x len) := by
        have := hreach k' (len - k') (by omega)
        rw [show k' + (len - k') = len by omega] at this
        exact hyureach.trans this
      have hyH : x len ∈ historyFrom (gT cfg H tr) yv := by
        rw [← hist_eq hinj huH hyu]
        exact ((causal_store k u).mem_history_iff hyu).mpr hyl
      have hyfin : yv ∈ fin.disk.ids :=
        (grows_before (cfg := cfg) (tr := tr) v (show A m ≤ L by omega)).1 hyv
      exact (hxH len le_rfl).2 (hist_sub hinj hv hyfin hyH)
  set rk := stk.blk (x len)
  have hans : Output.send v (x len) rk ∈ outputsAt cfg tr k := by
    rw [outputsAt_eq htk]
    change Output.send v (x len) rk ∈ answer _ _ v r miss
    unfold answer answerIds
    refine List.mem_map.mpr ⟨x len, List.mem_dedup.mpr (List.mem_append_right _
      (List.mem_flatMap.mpr ⟨x K, List.mem_filter.mpr ⟨hwm, by simpa using hKk⟩, ?_⟩)), rfl⟩
    rw [Finset.mem_sort, Finset.mem_filter]
    exact ⟨hsent, by simpa using hzk⟩
  obtain ⟨k', hk'k, htk'⟩ := hdel k u _ htk huH (v, .deliver (x len) rk)
    ⟨Output.send v (x len) rk, hans, ⟨rfl, rfl⟩⟩ hv
  have hk'L : k' < L := (List.getElem?_eq_some_iff.mp htk').1
  have hrk : rk = raw (x len) :=
    content_eq hinj (stored_known huH hzk) (hrawk _ (hxH len le_rfl).1) rfl
  rw [hrk] at htk'
  -- `v` acts on it, so it ends pending or stored there, which it does not
  have hcr : (raw (x len)).creator ≠ v := by
    intro hc
    rcases hrawk _ (hxH len le_rfl).1 with ⟨j, w', inp, hj₀, hw', hdl⟩ | ⟨j, w', hj, hw', hb⟩
    · obtain ⟨hj, hid⟩ := deliver_of_delivered hj₀ hdl
      have hid' : x len = (cfg.at w').idOf (raw (x len)) := hid
      obtain ⟨i'', -, hi''v, hi''b⟩ := htime j w' _ hj hw' (x len, raw (x len))
        (by simp [delivered, ← hid']) (by rw [hc]; exact hv)
      rw [hc] at hi''v
      obtain ⟨inp'', hi''⟩ := event_of_map hi''v
      have := (broadcast_stored hi'' hi''b).1
      exact (hxH len le_rfl).2 ((grows_before (cfg := cfg) (tr := tr) v
        (show i'' + 1 ≤ L by have := (List.getElem?_eq_some_iff.mp hi'').1; omega)).1 this)
    · obtain ⟨inp'', hj'⟩ := event_of_map hj
      have hcw := (Local.authored _ _ _ (cfg.at w') (inputsBefore tr (j + 1) w') _
        (persists_of_event hj' hb)).2
      change (raw (x len)).creator = w' at hcw
      have hwv : w' = v := hcw.symm.trans hc
      subst hwv
      have := (persist_stored hj' hb).1
      exact (hxH len le_rfl).2 ((grows_before (cfg := cfg) (tr := tr) w'
        (show j + 1 ≤ L by have := (List.getElem?_eq_some_iff.mp hj').1; omega)).1 this)
  rcases hdeliv (x len) (hxH len le_rfl).1 k' hk'L htk' hcr with h' | h'
  · exact hxl (List.mem_map.mpr ⟨_, h', rfl⟩)
  · exact (hxH len le_rfl).2 h'

theorem holds : Statement := converges

end Converge

end Node

end LeanDag
