import LeanDagTest.Steelhead.RotatingStall
/-!
# Steelhead witnesses: the failover fires, and the stalled output recovers

The scan's failover (SH10e) and output liveness under it (SH14) on `rtDag N`, the rotating stall
of `RotatingStall.lean`, with the coin naming validator `2` at every round and the interval `8`:

* **every round chain-commits** (`rt_chain_decided`): by two rounds up every block reaches
  validator `2`'s block of a round, since the omissions spare validator `0`'s and the round's
  known leader's blocks, so the whole of round `r + 3` votes for it and the whole of round `r + 4`
  certifies it;
* **the failover fires at interval `1`** (`rt_failover`, SH10e on data): interval `0`'s anchor is
  round `0`, whose history decides nothing above it; interval `1`'s is round `9`, whose history
  commits no slot at round `1` or above, the synchronous slots having no certificate (SH8's
  hypotheses, asked at the slots the history can decide) and slot `3` being undecided there, so
  the agreed output's last commit stays at `0` and `0 + 8 < 9`: interval `2` runs at period `1`
  whatever the replay answers, which is `4` (`rt_update_four`);
* **the stalled slot is decided** (`rt_recovers`, SH14 on data): the scan derives the periods `4`,
  `4`, `1`, `1` over the first four intervals, interval `2` finds its anchor at round `17`, the
  coin names a committed candidate at rounds `25` to `29`, and a view holding round `33` decides
  slot `3` at the adaptive wavelength of that sequence.

The horizon `N` is a parameter throughout: the chain commit is proved from the DAG's structure,
not by evaluation, which a wave of five on a hundred blocks does not admit.
-/

namespace LeanDagTest

open LeanDag LeanDag.Steelhead

/-- The coin names validator `2` at every round. -/
def rtCoin : ℕ → Fin 4 := fun _ => 2

/-- The sequence the scan derives: `4` on intervals `0` and `1`, `1` from interval `2` on. -/
def rtPer : ℕ → ℕ := fun j => if j ≤ 1 then 4 else 1

/-- The adaptive schedule of that sequence: the known leader on the first two intervals'
synchronous rounds, the coin elsewhere. -/
abbrev rtSlots : Slots (Fin 4) := adaptiveSlots rtCoin rtKnown 8 rtPer

-- The schedule is named explicitly throughout; the local instance keeps projections such as
-- `h.decided` from synthesising the sibling files' global one.
attribute [local instance] rtSlots

/-- Its adaptive wavelength. -/
abbrev rtW : ℕ → ℕ := adaptiveWave 3 5 8 rtPer

/-! ## Every round chain-commits -/

/-- A block of `rtDag N` references a block of the round below unless the latter is the known
leader's and the former is neither validator `0`'s nor the leader's own. -/
theorem rt_mem_refs {N b i : ℕ} (hi : 4 * (b / 4) - 4 ≤ i ∧ i < 4 * (b / 4))
    (hc : b % 4 = 0 ∨ b % 4 = (b / 4 - 1) % 4 ∨ i % 4 ≠ (b / 4 - 1) % 4) :
    i ∈ ((rtDag N).block b).refs := by
  change i ∈ rtRefs b
  simp only [rtRefs, growRefs, Finset.mem_filter, Finset.mem_Ico]
  exact ⟨hi, hc⟩

/-- A block id lies in `rtDag N` once it is below the horizon's blocks. -/
theorem rt_mem_ids {N b : ℕ} (hb : b < 4 * (N + 1)) : b ∈ (rtDag N).ids := by
  change b ∈ Finset.range (4 * (N + 1))
  exact Finset.mem_range.mpr hb

/-- Every block three rounds above round `r` reaches validator `2`'s block of round `r`: through
the block of round `r`'s known leader at round `r + 1`, which references all of round `r`, and
the block of round `r + 1`'s known leader at round `r + 2`, which every block above references. -/
theorem rt_reaches_coin {N r q : ℕ} (hqr : q / 4 = r + 3) : Reaches (rtDag N) q (4 * r + 2) := by
  -- the residues are named, since `omega` does not read a remainder inside a remainder
  obtain ⟨m, hm, hm4⟩ : ∃ m, (r + 1) % 4 = m ∧ m < 4 := ⟨_, rfl, Nat.mod_lt _ (by omega)⟩
  obtain ⟨k, hk, hk4⟩ : ∃ k, r % 4 = k ∧ k < 4 := ⟨_, rfl, Nat.mod_lt _ (by omega)⟩
  have e1 : (4 * (r + 2) + m) / 4 = r + 2 := by
    rw [Nat.mul_add_div (by decide), Nat.div_eq_of_lt hm4]
  have e2 : (4 * (r + 2) + m) % 4 = m := by
    rw [Nat.mul_add_mod, Nat.mod_eq_of_lt hm4]
  have e3 : (4 * (r + 1) + k) / 4 = r + 1 := by
    rw [Nat.mul_add_div (by decide), Nat.div_eq_of_lt hk4]
  have e4 : (4 * (r + 1) + k) % 4 = k := by
    rw [Nat.mul_add_mod, Nat.mod_eq_of_lt hk4]
  have h1 : 4 * (r + 2) + m ∈ ((rtDag N).block q).refs :=
    rt_mem_refs (by omega) (by omega)
  have hi2 : 4 * ((4 * (r + 2) + m) / 4) - 4 ≤ 4 * (r + 1) + k ∧
      4 * (r + 1) + k < 4 * ((4 * (r + 2) + m) / 4) := by
    rw [e1]
    omega
  have hc2 : (4 * (r + 2) + m) % 4 = 0 ∨ (4 * (r + 2) + m) % 4 = ((4 * (r + 2) + m) / 4 - 1) % 4 ∨
      (4 * (r + 1) + k) % 4 ≠ ((4 * (r + 2) + m) / 4 - 1) % 4 := by
    rw [e1, e2]
    right; left
    omega
  have h2 : 4 * (r + 1) + k ∈ ((rtDag N).block (4 * (r + 2) + m)).refs :=
    rt_mem_refs hi2 hc2
  have hi3 : 4 * ((4 * (r + 1) + k) / 4) - 4 ≤ 4 * r + 2 ∧
      4 * r + 2 < 4 * ((4 * (r + 1) + k) / 4) := by
    rw [e3]
    omega
  have hc3 : (4 * (r + 1) + k) % 4 = 0 ∨ (4 * (r + 1) + k) % 4 = ((4 * (r + 1) + k) / 4 - 1) % 4 ∨
      (4 * r + 2) % 4 ≠ ((4 * (r + 1) + k) / 4 - 1) % 4 := by
    rw [e3, e4]
    right; left
    omega
  have h3 : 4 * r + 2 ∈ ((rtDag N).block (4 * (r + 1) + k)).refs :=
    rt_mem_refs hi3 hc3
  exact Reaches.trans (Reaches.single h1) (Reaches.trans (Reaches.single h2) (Reaches.single h3))

/-- Validator `2`'s block of round `r` is its only block there. -/
theorem rt_coin_unique {N r L' : ℕ} (_hL' : L' ∈ (rtDag N).ids)
    (hr : ((rtDag N).block L').round = ((rtDag N).block (4 * r + 2)).round)
    (hc : ((rtDag N).block L').creator = ((rtDag N).block (4 * r + 2)).creator) :
    L' = 4 * r + 2 := by
  change L' / 4 = (4 * r + 2) / 4 at hr
  have hcv : L' % 4 = (4 * r + 2) % 4 := congrArg Fin.val hc
  omega

/-- Every block three rounds up votes for validator `2`'s block of round `r`. -/
theorem rt_votes_coin {N r q : ℕ} (hq : q ∈ (rtDag N).ids) (hqr : q / 4 = r + 3) :
    MahiMahi.Votes (rtDag N) q (4 * r + 2) := by
  have hqN : q < 4 * (N + 1) := Finset.mem_range.mp hq
  exact votes_of_reaches_of_unique hq (rt_mem_ids (by omega))
    (fun L' hL' hr hc => rt_coin_unique hL' hr hc) (rt_reaches_coin hqr)

/-- Every block four rounds up certifies it: it references the blocks of at least three
validators of round `r + 3`, and all of them vote. -/
theorem rt_certifies_coin {N r C : ℕ} (hC : C ∈ (rtDag N).ids) (hCr : C / 4 = r + 4) :
    C ∈ MahiMahi.certificates (rtDag N) 5 (4 * r + 2) r := by
  have hCN : C < 4 * (N + 1) := Finset.mem_range.mp hC
  refine mem_certificatesAt.mpr ⟨hC, ?_, ?_⟩
  · change C / 4 = r + 5 - 1
    omega
  · change 3 ≤ (creatorsOf (rtDag N).block (MahiMahi.votesIn (rtDag N) C (4 * r + 2))).card
    have hs : Finset.univ.erase (rtKnown (r + 3)) ⊆
        creatorsOf (rtDag N).block (MahiMahi.votesIn (rtDag N) C (4 * r + 2)) := by
      intro v hv
      have hv4 := v.isLt
      have hn : v.val ≠ (r + 3) % 4 := fun h => (Finset.mem_erase.mp hv).1 (Fin.ext h)
      refine mem_creatorsOf.mpr ⟨4 * (r + 3) + v.val, ?_, ?_⟩
      · refine mem_carriedVotes.mpr ⟨rt_mem_refs (by omega) (by omega), ?_⟩
        exact rt_votes_coin (rt_mem_ids (by omega)) (by omega)
      · apply Fin.ext
        change (4 * (r + 3) + v.val) % 4 = v.val
        omega
    have hc : (Finset.univ.erase (rtKnown (r + 3))).card = 3 := by
      rw [Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, Fintype.card_fin]
    have := Finset.card_le_card hs
    omega

/-- **Every round chain-commits**: the four blocks of round `r + 4` certify validator `2`'s block
of round `r`, so it is directly committed at wave `5` once the record holds that round. -/
theorem rt_chain_commit (N r : ℕ) (hr : r + 4 ≤ N) :
    MahiMahi.DirectCommit (rtDag N) 5 (4 * r + 2) r := by
  change 3 ≤ (creatorsOf (rtDag N).block (MahiMahi.certificates (rtDag N) 5 (4 * r + 2) r)).card
  have hs : (Finset.univ : Finset (Fin 4)) ⊆
      creatorsOf (rtDag N).block (MahiMahi.certificates (rtDag N) 5 (4 * r + 2) r) := by
    intro v _
    have hv4 := v.isLt
    refine mem_creatorsOf.mpr ⟨4 * (r + 4) + v.val, rt_certifies_coin (rt_mem_ids (by omega))
      (by omega), ?_⟩
    apply Fin.ext
    change (4 * (r + 4) + v.val) % 4 = v.val
    omega
  have := Finset.card_le_card hs
  rw [Finset.card_univ, Fintype.card_fin] at this
  omega

/-- The same, as a chain verdict in the full view. -/
theorem rt_chain_decided (N r : ℕ) (hr : r + 4 ≤ N) :
    ChainDecided 5 rtCoin (rtDag N) (View.full (rtDag N)) r (some (4 * r + 2)) :=
  AnchoredRule.Decided.directCommit (S := chainSlots rtCoin)
    ⟨rt_mem_ids (by omega), by change (4 * r + 2) / 4 = r; omega,
      by apply Fin.ext; change (4 * r + 2) % 4 = 2; omega⟩
    (MahiMahiProperties.directCommitIn_of_coversUpto (rt_chain_commit N r hr)
      (View.coversUpto_full _ _))

/-! ## The anchors -/

/-- Interval `0`'s anchor is the chain commit at round `0`, block `2`. -/
theorem rt_anchor0 (N : ℕ) (hN : 4 ≤ N) :
    IntervalAnchor 8 5 rtCoin (rtDag N) (View.full (rtDag N)) 0 0 2 where
  mem := by decide
  commit := rt_chain_decided N 0 (by omega)
  below := fun _ _ h => absurd h (Nat.not_lt_zero _)

/-- Interval `j ≥ 1`'s anchor is the chain commit at its first round `8j + 1`. -/
theorem rt_anchor (N j : ℕ) (hj : 0 < j) (hN : 8 * j + 5 ≤ N) :
    IntervalAnchor 8 5 rtCoin (rtDag N) (View.full (rtDag N)) j (8 * j + 1)
      (4 * (8 * j + 1) + 2) where
  mem := by unfold intervalOf; omega
  commit := rt_chain_decided N (8 * j + 1) (by omega)
  below := by
    intro r' hr' hlt
    unfold intervalOf at hr'
    omega

/-! ## The stall inside an anchor's history

Every verdict of the history of an anchor at round `17` or below lies at a slot below round `17`,
where the adaptive wavelength of `rtPer` is the periodic one at period `4` and the schedule names
the known leader at the synchronous rounds; SH8 then applies with its hypotheses asked at those
slots alone, and no synchronous slot there commits. -/

/-- Below round `17` the adaptive wavelength is the periodic one at period `4`. -/
theorem rtW_eq_periodic {r : ℕ} (hr : r ≤ 16) : rtW r = periodic 3 5 4 r := by
  have h : rtPer (intervalOf 8 r) = 4 := by
    unfold rtPer intervalOf
    rw [if_pos (by omega)]
  change periodic 3 5 (rtPer (intervalOf 8 r)) r = periodic 3 5 4 r
  rw [h]

/-- Every wavelength of `rtW` is at least three rounds. -/
theorem rtW_ge_three (r : ℕ) : 3 ≤ rtW r := by
  unfold rtW adaptiveWave periodic
  split <;> omega

/-- Below round `17` the schedule names the known leader at a synchronous round. -/
theorem rtSlots_leader_sync {r : ℕ} (hr : r ≤ 16) (hs : ¬ IsAsync 4 r) :
    rtSlots.leader r = rtKnown r := by
  have h : rtPer (intervalOf 8 r) = 4 := by
    unfold rtPer intervalOf
    rw [if_pos (by omega)]
  change (if IsAsync (rtPer (intervalOf 8 r)) r then rtCoin r else rtKnown r) = rtKnown r
  rw [h, if_neg hs]

/-- No synchronous candidate below round `17` is certified, on the schedule of `rtPer`. -/
theorem rt_hcert16 (N : ℕ) : ∀ (j : ℕ) (L : ℕ), j ≤ 16 → ¬ IsAsync 4 j →
    IsLeaderBlock (S := rtSlots) (rtDag N) j L → MahiMahi.certificates (rtDag N) 3 L j = ∅ := by
  intro j L hj hs hL
  have hround : L / 4 = j := hL.2.1
  have hc := hL.2.2
  rw [rtSlots_leader_sync hj hs] at hc
  have hcv : L % 4 = j % 4 := congrArg Fin.val hc
  have : L = 4 * j + j % 4 := by omega
  rw [this]
  exact rt_certificates_empty N j

/-- No synchronous slot below round `17` is directly skipped in any view, on the schedule of
`rtPer`. -/
theorem rt_hskip16 (N : ℕ) (V : View (Fin 4) ℕ Unit (rtDag N)) : ∀ j, j ≤ 16 → ¬ IsAsync 4 j →
    ¬ MahiMahi.DirectSkipIn (rtDag N) V 3 (rtSlots.leader j) j := by
  intro j hj hs
  rw [rtSlots_leader_sync hj hs]
  exact rt_no_skip N j hs V

/-- Every verdict of the history of an anchor at round `17` or below lies at a slot below round
`17`, at either wavelength. -/
theorem rt_history_slot_le {N A : ℕ} (hA : A ∈ (rtDag N).ids)
    (hρ : ((rtDag N).block A).round ≤ 17) {w : ℕ → ℕ} (hw : ∀ r, 3 ≤ w r) {j : ℕ}
    {v : Option ℕ} (hd : Decided (S := rtSlots) w (rtDag N) ((rtDag N).historyView A hA) j v) :
    j ≤ 16 := by
  have := voteRound_le_of_decided_historyView (S := rtSlots) (fun r => by have := hw r; omega)
    hA hd
  change j + w j - 2 ≤ ((rtDag N).block A).round at this
  have := hw j
  omega

/-- **Slot `3` is undecided in the history of every anchor at round `17` or below.** -/
theorem rt_stall_history {N A : ℕ} (hA : A ∈ (rtDag N).ids)
    (hρ : ((rtDag N).block A).round ≤ 17) (v : Option ℕ) :
    ¬ Decided (S := rtSlots) rtW (rtDag N) ((rtDag N).historyView A hA) 3 v := by
  intro hd
  have hd' : Decided (S := rtSlots) (periodic 3 5 4) (rtDag N) ((rtDag N).historyView A hA) 3 v :=
    decided_congr_of_decided
      (fun r u hr => rtW_eq_periodic (rt_history_slot_le hA hρ rtW_ge_three hr)) hd
  exact stall_of_pred (S := rtSlots) (by decide) (by decide) (fun _ => rfl) (Q := fun j => j ≤ 16)
    (fun j u hj => rt_history_slot_le hA hρ (fun r => by unfold periodic; split <;> omega) hj)
    (rt_hcert16 N) (rt_hskip16 N _) (by decide) hd'

/-- **No synchronous slot below round `17` commits in such a history.** -/
theorem rt_sync_no_commit_history {N A : ℕ} (hA : A ∈ (rtDag N).ids)
    (hρ : ((rtDag N).block A).round ≤ 17) {s : ℕ} (hs : s ≤ 16) (hsync : ¬ IsAsync 4 s) (L : ℕ) :
    ¬ Decided (S := rtSlots) rtW (rtDag N) ((rtDag N).historyView A hA) s (some L) := by
  intro hd
  have hd' : Decided (S := rtSlots) (periodic 3 5 4) (rtDag N) ((rtDag N).historyView A hA) s
      (some L) :=
    decided_congr_of_decided
      (fun r u hr => rtW_eq_periodic (rt_history_slot_le hA hρ rtW_ge_three hr)) hd
  exact not_commit_sync_of_pred (S := rtSlots) (fun _ => rfl) (Q := fun j => j ≤ 16) (rt_hcert16 N)
    hs hsync hd'

/-! ## The advances -/

/-- The advance over interval `0`'s anchor stays put: a round-`0` block's history decides nothing
at round `1` or above. -/
theorem rt_advance0 {N : ℕ} (h2 : 2 ∈ (rtDag N).ids) {next' last' : ℕ}
    (h : AgreedAdvance (S := rtSlots) (rtDag N) rtW 2 h2 1 next' 0 last') :
    next' = 1 ∧ last' = 0 := by
  have hnone : ∀ s v, 1 ≤ s →
      ¬ Decided (S := rtSlots) rtW (rtDag N) ((rtDag N).historyView 2 h2) s v := by
    intro s v hs hd
    have := slotRound_le_of_decided_historyView (S := rtSlots)
      (fun r => by have := rtW_ge_three r; omega) h2 hd
    change s ≤ 2 / 4 at this
    omega
  have hnext : next' = 1 := by
    rcases Nat.lt_or_ge 1 next' with hlt | hge
    · obtain ⟨v, hv⟩ := h.decided 1 le_rfl hlt
      exact absurd hv (hnone 1 v le_rfl)
    · have := h.le
      omega
  refine ⟨hnext, ?_⟩
  rcases h.last_mem with hl | ⟨s, L, hs1, hs2, hd, -⟩
  · exact hl
  · exact absurd hd (hnone s _ hs1)

/-- **An advance below the stall consumes no commit**: with the cursor between slots `1` and `3`
and the anchor at round `17` or below, the cursor stays at or below `3` and the last commit is
the old one. -/
theorem rt_advance_stalled {N A : ℕ} (hA : A ∈ (rtDag N).ids)
    (hρ : ((rtDag N).block A).round ≤ 17) {next next' last last' : ℕ} (h1 : 1 ≤ next)
    (hnext : next ≤ 3)
    (h : AgreedAdvance (S := rtSlots) (rtDag N) rtW A hA next next' last last') :
    1 ≤ next' ∧ next' ≤ 3 ∧ last' = last := by
  have hn : next' ≤ 3 := by
    by_contra hgt
    obtain ⟨v, hv⟩ := h.decided 3 hnext (by omega)
    exact rt_stall_history hA hρ v hv
  refine ⟨le_trans h1 h.le, hn, ?_⟩
  rcases h.last_mem with hl | ⟨s, L, hs1, hs2, hd, -⟩
  · exact hl
  · exact absurd hd (rt_sync_no_commit_history hA hρ (by omega) (by unfold IsAsync; omega) L)

/-! ## The failover fires -/

/-- **The failover fires at interval `1`** (SH10e on data): interval `1` runs at the replay's
answer `4`, and interval `2` at period `1`, the agreed output's cursor at slot `1`, `2` or `3`
and its last commit still at round `0`. -/
theorem rt_failover (N : ℕ) (hN : 13 ≤ N) :
    PeriodAt (S := rtSlots) 8 5 rtCoin (rtUpd N) 4 (rtDag N) (View.full (rtDag N)) rtW 1
        ⟨4, 1, 0⟩ ∧
      ∃ next', 1 ≤ next' ∧ next' ≤ 3 ∧
        PeriodAt (S := rtSlots) 8 5 rtCoin (rtUpd N) 4 (rtDag N) (View.full (rtDag N)) rtW 2
          ⟨1, next', 0⟩ := by
  have hw2 : ∀ r, 2 ≤ rtW r := fun r => by have := rtW_ge_three r; omega
  have h2 : 2 ∈ (rtDag N).ids := rt_mem_ids (by omega)
  have h38 : 38 ∈ (rtDag N).ids := rt_mem_ids (by omega)
  -- interval 0: the anchor at round 0, over whose history the advance stays put
  obtain ⟨n₀, l₀, hadv₀⟩ := AgreedAdvance.exists (S := rtSlots) (U := rtDag N) (w := rtW) hw2 h2 1 0
  obtain ⟨rfl, rfl⟩ := rt_advance0 h2 hadv₀
  have hp1 : PeriodAt (S := rtSlots) 8 5 rtCoin (rtUpd N) 4 (rtDag N) (View.full (rtDag N)) rtW 1
      ⟨4, 1, 0⟩ := by
    have hp : PeriodAt (S := rtSlots) 8 5 rtCoin (rtUpd N) 4 (rtDag N) (View.full (rtDag N)) rtW 1
        ⟨if 0 + 8 < 0 then 1 else rtUpd N 2 (⟨4, 1, 0⟩ : ScanState).period, 1, 0⟩ :=
      PeriodAt.anchor PeriodAt.zero (rt_anchor0 N (by omega)) hadv₀
    simpa [rt_update_four] using hp
  -- interval 1: the anchor at round 9, over whose history the advance consumes no commit
  obtain ⟨n₁, l₁, hadv₁⟩ :=
    AgreedAdvance.exists (S := rtSlots) (U := rtDag N) (w := rtW) hw2 h38 1 0
  obtain ⟨hn₁, hn₃, rfl⟩ := rt_advance_stalled h38 (by change 38 / 4 ≤ 17; omega) le_rfl (by omega)
    hadv₁
  exact ⟨hp1, n₁, hn₁, hn₃,
    periodAt_one_of_anchor hp1 (rt_anchor N 1 (by omega) (by omega)) hadv₁ (by omega)⟩

/-! ## The stalled slot is decided -/

/-- **Slot `3` is decided once the coin runs** (SH14 on data): the view derives the states of
the first four intervals at the periods `4`, `4`, `1`, `1`, and decides slot `3` at the adaptive
wavelength of that sequence. -/
theorem rt_recovers (N : ℕ) (hN : 33 ≤ N) :
    (∀ j, j ≤ 3 → ∃ st,
      PeriodAt (S := rtSlots) 8 5 rtCoin (rtUpd N) 4 (rtDag N) (View.full (rtDag N)) rtW j st ∧
        rtPer j = st.period) ∧
      ∃ v, Decided (S := rtSlots) rtW (rtDag N) (View.full (rtDag N)) 3 v := by
  have hw2 : ∀ r, 2 ≤ rtW r := fun r => by have := rtW_ge_three r; omega
  have h70 : 70 ∈ (rtDag N).ids := rt_mem_ids (by omega)
  obtain ⟨hp1, n₂, hn₂, hn₂', hp2⟩ := rt_failover N (by omega)
  -- interval 2: the anchor at round 17, over whose history the advance consumes no commit
  obtain ⟨n₃, l₃, hadv₃⟩ :=
    AgreedAdvance.exists (S := rtSlots) (U := rtDag N) (w := rtW) hw2 h70 n₂ 0
  obtain ⟨-, -, rfl⟩ := rt_advance_stalled h70 (by change 70 / 4 ≤ 17; omega) hn₂ hn₂' hadv₃
  have hp3 := periodAt_one_of_anchor hp2 (rt_anchor N 2 (by omega) (by omega)) hadv₃ (by omega)
  have hstates : ∀ j, j ≤ 3 → ∃ st,
      PeriodAt (S := rtSlots) 8 5 rtCoin (rtUpd N) 4 (rtDag N) (View.full (rtDag N)) rtW j st ∧
        rtPer j = st.period := by
    intro j hj
    interval_cases j
    · exact ⟨_, PeriodAt.zero, rfl⟩
    · exact ⟨_, hp1, rfl⟩
    · exact ⟨_, hp2, rfl⟩
    · exact ⟨_, hp3, rfl⟩
  refine ⟨hstates, ?_⟩
  -- SH14: the anchored interval 2 lies two past slot 3's, and the coin runs at rounds 25 to 29
  refine output_liveness (S := rtSlots) (by decide) (by decide) (by decide) (fun _ => rfl)
    (by decide) (b := 25) (fun j hj => hstates j (by unfold intervalOf at hj; omega)) ?_
    (s := 3) (by decide) (by decide) (rt_anchor N 2 (by omega) (by omega)) (by decide) ?_
    (View.coversUpto_full _ _)
  · intro r hr
    change (if IsAsync (rtPer (intervalOf 8 r)) r then rtCoin r else rtKnown r) = rtCoin r
    rw [if_pos hr]
  · intro i hi
    exact MahiMahi.mem_goodAt.mpr ⟨4 * (25 + i) + 2, rt_mem_ids (by omega),
      by change (4 * (25 + i) + 2) / 4 = 25 + i; omega,
      by apply Fin.ext; change (4 * (25 + i) + 2) % 4 = 2; omega,
      rt_chain_commit N (25 + i) (by omega)⟩

#print axioms rt_chain_commit
#print axioms rt_failover
#print axioms rt_recovers

end LeanDagTest
