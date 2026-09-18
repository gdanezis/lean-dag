import LeanDagTest.Steelhead.RotatingStall
/-!
# Steelhead witnesses: the failover fires, and the stalled output recovers

The scan's failover (SH10e) and output liveness under it (SH14) on `rtDag N`, the rotating stall
of `RotatingStall.lean`, with the coin naming validator `2` at every round, the interval `8` and
the period bound `4`:

* **every control slot commits** (`rt_control_decided`): by two rounds up every block reaches
  validator `2`'s block of a round, since the omissions spare validator `0`'s and the round's
  known leader's blocks, so the whole of round `r + 3` votes for it and the whole of round `r + 4`
  certifies it, at whichever scan's schedule the round is a slot of;
* **the failover fires at interval `1`** (`rt_failover`, SH10e on data): interval `0`'s anchor is
  its first control round at period `4`, round `4`, whose history commits no slot at round `1` or
  above, and the warm-up keeps period `4` (SH10n on data); interval `1`'s anchor is its first
  control round at period `4`, round `12`, whose history commits no slot at round `1` or above
  either, the synchronous slots having no certificate (SH8's hypotheses, asked at the slots the
  history can decide) and slot `3` being undecided there, so the agreed output's last commit
  stays at `0` and `0 + 8 < 12`: interval `2` runs at period `1` whatever the replay answers,
  which is `4` (`rt_update_four`);
* **the stalled slot is decided** (`rt_recovers`, SH14 on data): the scan derives the periods `4`,
  `4`, `1`, `1` over the first four intervals, interval `2` finds its anchor at round `17`, its
  first control round at period `1`, the coin names a committed candidate at rounds `25` to `29`,
  and a view holding round `33` decides slot `3` on the schedule whose kinds that sequence
  names.

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

/-- The wavelength of the pair, read at that schedule's kinds. -/
abbrev rtW : ℕ → ℕ := wavelength 3 5

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

/-- The same, as the coin's membership in the round's committed set. -/
theorem rt_good (N r : ℕ) (hr : r + 4 ≤ N) : rtCoin r ∈ MahiMahi.goodAt (rtDag N) 5 r :=
  MahiMahi.mem_goodAt.mpr ⟨4 * r + 2, rt_mem_ids (by omega),
    by change (4 * r + 2) / 4 = r; omega, by apply Fin.ext; change (4 * r + 2) % 4 = 2; omega,
    rt_chain_commit N r hr⟩

/-- **Every control slot commits**, in the scan of any interval at any period: the control
verdict of slot `i` commits validator `2`'s block of the slot's round, in the full view of a
record holding that round's wave. -/
theorem rt_control_decided (N j k i : ℕ) (hr : controlRound 8 4 j k i + 4 ≤ N) :
    ControlDecided 8 4 5 rtCoin j k (rtDag N) (View.full (rtDag N)) i
      (some (4 * controlRound 8 4 j k i + 2)) :=
  AnchoredRule.Decided.directCommit (S := controlSlots rtCoin 8 4 j k)
    ⟨rt_mem_ids (by omega),
      by change (4 * controlRound 8 4 j k i + 2) / 4 = controlRound 8 4 j k i; omega,
      by apply Fin.ext; change (4 * controlRound 8 4 j k i + 2) % 4 = 2; omega⟩
    (MahiMahiProperties.directCommitIn_of_coversUpto (rt_chain_commit N _ hr)
      (View.coversUpto_full _ _))

/-! ## The anchors

Each interval's anchor is its first control round at the period the scan runs at: round `4` for
interval `0` at period `4`, slot `1` of that scan's schedule; round `12` for interval `1` at
period `4`, slot `3`, the slots below lying in interval `0`; round `17` for interval `2` at
period `1`, slot `17`, every round up to the boundary being a slot there. -/

/-- Interval `0`'s anchor at period `4`: slot `1`, round `4`, block `18`. -/
theorem rt_anchor0 (N : ℕ) (hN : 8 ≤ N) :
    IntervalAnchor 8 4 5 rtCoin (rtDag N) (View.full (rtDag N)) 0 4 1 18 where
  pos := by decide
  mem := by decide
  commit := by
    rw [show (18 : ℕ) = 4 * controlRound 8 4 0 4 1 + 2 by decide]
    exact rt_control_decided N 0 4 1 (by
      have h : controlRound 8 4 0 4 1 = 4 := by decide
      omega)
  below := fun i' h1 _ h => by
    interval_cases i'
    exact absurd h1 (by decide)

/-- Interval `1`'s anchor at period `4`: slot `3`, round `12`, block `50`. -/
theorem rt_anchor1 (N : ℕ) (hN : 16 ≤ N) :
    IntervalAnchor 8 4 5 rtCoin (rtDag N) (View.full (rtDag N)) 1 4 3 50 where
  pos := by decide
  mem := by decide
  commit := by
    rw [show (50 : ℕ) = 4 * controlRound 8 4 1 4 3 + 2 by decide]
    exact rt_control_decided N 1 4 3 (by
      have h : controlRound 8 4 1 4 3 = 12 := by decide
      omega)
  below := fun i' _ hmem h => by
    interval_cases i' <;> exact absurd hmem (by decide)

/-- Interval `2`'s anchor at period `1`: slot `17`, round `17`, block `70`. -/
theorem rt_anchor2 (N : ℕ) (hN : 21 ≤ N) :
    IntervalAnchor 8 4 5 rtCoin (rtDag N) (View.full (rtDag N)) 2 1 17 70 where
  pos := by decide
  mem := by decide
  commit := by
    rw [show (70 : ℕ) = 4 * controlRound 8 4 2 1 17 + 2 by decide]
    exact rt_control_decided N 2 1 17 (by
      have h : controlRound 8 4 2 1 17 = 17 := by decide
      omega)
  below := fun i' _ hmem h => by
    interval_cases i' <;> exact absurd hmem (by decide)

/-! ## The stall inside an anchor's history

Every verdict of the history of an anchor at round `17` or below lies at a slot below round `17`,
where the schedule of `rtPer` carries the kinds of period `4` and names the known leader at the
synchronous rounds; SH8 then applies with its hypotheses asked at those slots alone, and no
synchronous slot there commits. -/

/-- Below round `17` the schedule assigns the kinds of period `4`. -/
theorem rtSlots_kind {r : ℕ} (hr : r ≤ 16) : rtSlots.kind r = periodicKind 4 r := by
  have h : rtPer (intervalOf 8 r) = 4 := by
    unfold rtPer intervalOf
    rw [if_pos (by omega)]
  change periodicKind (rtPer (intervalOf 8 r)) r = periodicKind 4 r
  rw [h]

/-- A synchronous slot below round `17` sits at a round that is not a multiple of `4`. -/
theorem rt_not_async16 {r : ℕ} (hr : r ≤ 16) (hk : rtSlots.kind r = 0) : ¬ IsAsync 4 r := by
  intro ha
  rw [rtSlots_kind hr, periodicKind_eq_one_iff.mpr ha] at hk
  exact absurd hk (by decide)

/-- Every wavelength of `rtW` is at least three rounds. -/
theorem rtW_ge_three (κ : ℕ) : 3 ≤ rtW κ := wavelength_three_le (by decide) (by decide) κ

/-- Below round `17` the schedule names the known leader at a synchronous round. -/
theorem rtSlots_leader_sync {r : ℕ} (hr : r ≤ 16) (hs : ¬ IsAsync 4 r) :
    rtSlots.leader r = rtKnown r := by
  change (if adaptiveKind 8 rtPer r = 1 then rtCoin r else rtKnown r) = rtKnown r
  rw [if_neg (fun h => hs (periodicKind_eq_one_iff.mp (by rw [← rtSlots_kind hr]; exact h)))]

/-- No synchronous candidate below round `17` is certified, on the schedule of `rtPer`. -/
theorem rt_hcert16 (N : ℕ) : ∀ (j : ℕ) (L : ℕ), j ≤ 16 → rtSlots.kind j = 0 →
    IsLeaderBlock (S := rtSlots) (rtDag N) j L → MahiMahi.certificates (rtDag N) 3 L j = ∅ := by
  intro j L hj hk hL
  have hround : L / 4 = j := hL.2.1
  have hc := hL.2.2
  rw [rtSlots_leader_sync hj (rt_not_async16 hj hk)] at hc
  have hcv : L % 4 = j % 4 := congrArg Fin.val hc
  have : L = 4 * j + j % 4 := by omega
  rw [this]
  exact rt_certificates_empty N j

/-- No synchronous slot below round `17` is directly skipped in any view, on the schedule of
`rtPer`. -/
theorem rt_hskip16 (N : ℕ) (V : View (Fin 4) ℕ Unit (rtDag N)) : ∀ j, j ≤ 16 →
    rtSlots.kind j = 0 → ¬ MahiMahi.DirectSkipIn (rtDag N) V 3 (rtSlots.leader j) j := by
  intro j hj hk
  have hs := rt_not_async16 hj hk
  rw [rtSlots_leader_sync hj hs]
  exact rt_no_skip N j hs V

/-- Every verdict of the history of an anchor at round `17` or below lies at a slot below round
`17`, at any wavelength function of three rounds or more. -/
theorem rt_history_slot_le {N A : ℕ} (hA : A ∈ (rtDag N).ids)
    (hρ : ((rtDag N).block A).round ≤ 17) {w : ℕ → ℕ} (hw : ∀ κ, 3 ≤ w κ) {j : ℕ}
    {v : Option ℕ} (hd : Decided (S := rtSlots) w (rtDag N) ((rtDag N).historyView A hA) j v) :
    j ≤ 16 := by
  have := voteRound_le_of_decided_historyView (S := rtSlots) (fun κ => by have := hw κ; omega)
    hA hd
  change j + w (rtSlots.kind j) - 2 ≤ ((rtDag N).block A).round at this
  have := hw (rtSlots.kind j)
  omega

/-- **Slot `3` is undecided in the history of every anchor at round `17` or below.** -/
theorem rt_stall_history {N A : ℕ} (hA : A ∈ (rtDag N).ids)
    (hρ : ((rtDag N).block A).round ≤ 17) (v : Option ℕ) :
    ¬ Decided (S := rtSlots) rtW (rtDag N) ((rtDag N).historyView A hA) 3 v :=
  fun hd => stall_of_pred (S := rtSlots) (by decide) (by decide) (fun _ => rfl)
    (Q := fun j => j ≤ 16) (fun j hj => rtSlots_kind hj)
    (fun j u hj => rt_history_slot_le hA hρ rtW_ge_three hj)
    (rt_hcert16 N) (rt_hskip16 N _) (by decide) hd

/-- **No synchronous slot below round `17` commits in such a history.** -/
theorem rt_sync_no_commit_history {N A : ℕ} (hA : A ∈ (rtDag N).ids) {s : ℕ} (hs : s ≤ 16)
    (hsync : ¬ IsAsync 4 s) (L : ℕ) :
    ¬ Decided (S := rtSlots) rtW (rtDag N) ((rtDag N).historyView A hA) s (some L) :=
  fun hd => not_commit_sync_of_pred (S := rtSlots) (fun _ => rfl) (Q := fun j => j ≤ 16)
    (rt_hcert16 N) hs
    (by
      rw [rtSlots_kind hs]
      exact periodicKind_eq_zero_of_ne_one fun h => hsync (periodicKind_eq_one_iff.mp h)) hd

/-! ## The advances -/

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
  · exact absurd hd (rt_sync_no_commit_history hA (by omega) (by unfold IsAsync; omega) L)

/-! ## The failover fires -/

/-- **The failover fires at interval `1`** (SH10e on data): interval `1` keeps period `4`, the
warm-up (SH10n on data), and interval `2` runs at period `1`, the agreed output's cursor at slot
`1`, `2` or `3` throughout and its last commit still at round `0`. -/
theorem rt_failover (N : ℕ) (hN : 16 ≤ N) :
    (∃ next', 1 ≤ next' ∧ next' ≤ 3 ∧
      PeriodAt (S := rtSlots) 8 4 5 rtCoin (rtUpd N) 4 (rtDag N) (View.full (rtDag N)) rtW 1
        ⟨4, next', 0⟩) ∧
      ∃ next', 1 ≤ next' ∧ next' ≤ 3 ∧
        PeriodAt (S := rtSlots) 8 4 5 rtCoin (rtUpd N) 4 (rtDag N) (View.full (rtDag N)) rtW 2
          ⟨1, next', 0⟩ := by
  have hw2 : ∀ κ, 2 ≤ rtW κ := fun κ => by have := rtW_ge_three κ; omega
  have h18 : 18 ∈ (rtDag N).ids := rt_mem_ids (by omega)
  have h50 : 50 ∈ (rtDag N).ids := rt_mem_ids (by omega)
  -- interval 0: the anchor at round 4, over whose history the advance consumes no commit; the
  -- warm-up keeps the period
  obtain ⟨n₀, l₀, hadv₀⟩ :=
    AgreedAdvance.exists (S := rtSlots) (U := rtDag N) (w := rtW) hw2 h18 1 0
  obtain ⟨hn₀, hn₀', rfl⟩ := rt_advance_stalled h18 (by change 18 / 4 ≤ 17; omega) le_rfl
    (by omega) hadv₀
  have hp1 : PeriodAt (S := rtSlots) 8 4 5 rtCoin (rtUpd N) 4 (rtDag N) (View.full (rtDag N)) rtW 1
      ⟨4, n₀, 0⟩ :=
    periodAt_warmUp (by decide) PeriodAt.zero (rt_anchor0 N (by omega)) hadv₀
  -- interval 1: the anchor at round 12, over whose history the advance consumes no commit, and
  -- 0 + 8 < 12
  obtain ⟨n₁, l₁, hadv₁⟩ :=
    AgreedAdvance.exists (S := rtSlots) (U := rtDag N) (w := rtW) hw2 h50 n₀ 0
  obtain ⟨hn₁, hn₁', rfl⟩ := rt_advance_stalled h50 (by change 50 / 4 ≤ 17; omega) hn₀ hn₀'
    hadv₁
  exact ⟨⟨n₀, hn₀, hn₀', hp1⟩, n₁, hn₁, hn₁',
    periodAt_one_of_anchor hp1 (rt_anchor1 N (by omega)) hadv₁
      (by change 0 + 8 < controlRound 8 4 1 4 3; decide)⟩

/-! ## The stalled slot is decided -/

/-- **Slot `3` is decided once the coin runs** (SH14 on data): the view derives the states of
the first four intervals at the periods `4`, `4`, `1`, `1`, and decides slot `3` at the adaptive
wavelength of that sequence. -/
theorem rt_recovers (N : ℕ) (hN : 33 ≤ N) :
    (∀ j, j ≤ 3 → ∃ st,
      PeriodAt (S := rtSlots) 8 4 5 rtCoin (rtUpd N) 4 (rtDag N) (View.full (rtDag N)) rtW j st ∧
        rtPer j = st.period) ∧
      ∃ v, Decided (S := rtSlots) rtW (rtDag N) (View.full (rtDag N)) 3 v := by
  have hw2 : ∀ κ, 2 ≤ rtW κ := fun κ => by have := rtW_ge_three κ; omega
  have h70 : 70 ∈ (rtDag N).ids := rt_mem_ids (by omega)
  obtain ⟨⟨n₁, hn₁, hn₁', hp1⟩, n₂, hn₂, hn₂', hp2⟩ := rt_failover N (by omega)
  -- interval 2: the anchor at round 17, over whose history the advance consumes no commit
  obtain ⟨n₃, l₃, hadv₃⟩ :=
    AgreedAdvance.exists (S := rtSlots) (U := rtDag N) (w := rtW) hw2 h70 n₂ 0
  obtain ⟨-, -, rfl⟩ := rt_advance_stalled h70 (by change 70 / 4 ≤ 17; omega) hn₂ hn₂' hadv₃
  have hp3 := periodAt_one_of_anchor hp2 (rt_anchor2 N (by omega)) hadv₃
    (by change 0 + 8 < controlRound 8 4 2 1 17; decide)
  have hstates : ∀ j, j ≤ 3 → ∃ st,
      PeriodAt (S := rtSlots) 8 4 5 rtCoin (rtUpd N) 4 (rtDag N) (View.full (rtDag N)) rtW j st ∧
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
    (fun _ => rfl) (by decide) (b := 25) (fun j hj => hstates j (by unfold intervalOf at hj; omega))
    ?_ (s := 3) (by decide) (by decide) (rt_anchor2 N (by omega)) (by decide)
    (fun i hi => rt_good N (25 + i) (by omega)) (View.coversUpto_full _ _)
  intro r hr
  change (if adaptiveKind 8 rtPer r = 1 then rtCoin r else rtKnown r) = rtCoin r
  exact if_pos (show adaptiveKind 8 rtPer r = 1 from hr)

#print axioms rt_chain_commit
#print axioms rt_failover
#print axioms rt_recovers

end LeanDagTest
