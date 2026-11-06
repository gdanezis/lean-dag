import LeanDag.KPartialDag.Reactive.Proof
import LeanDag.KPartialDag.Close.Proof
import LeanDag.KPartialDag.Helpers.Bounds
/-!
# Reactive nodes in time — a timed witness

Four validators, of which `3` is Byzantine and silent, with leaders in
rotation, at `δ = 1`, `γ = 2`, `τ = 4`, `μ = 1` and `G = 3`. Each correct
validator builds a block a round: `δ + γ` after the round below when the
leaders of the round and of the round below are correct, and `δ + τ` after
it otherwise. Validator `2` restarts at time `2` and keeps only its disk.
The timeline is a reactive run from round `2`, keeps histories on disk and
builds above the disk, and `Reactive.Commits` decides slot `5` by time `27`.
With every block declaring the channel closed, `Close.Closes` applies.
-/

namespace LeanDagTest

namespace KPartialDag

namespace Timed

open LeanDag LeanDag.KPartialDag

instance tFaults : Faults (Fin 4) where
  f := 1
  byzantine := {3}
  card_validators := by decide
  card_byzantine := by decide

instance tSlots : Slots (Fin 4) := Slots.identity fun k => ⟨k % 4, Nat.mod_lt _ (by omega)⟩

theorem leader_val (k : ℕ) : (tSlots.leader k).val = k % 4 := rfl

theorem slotRound_eq (k : ℕ) : tSlots.slotRound k = k := rfl

theorem quorum_four : quorumCard (Fin 4) = 3 := rfl

theorem mem_three {w : Fin 4} : w ∈ ({0, 1, 2} : Finset (Fin 4)) ↔ w ≠ 3 := by
  revert w; decide

theorem mem_correct_four {w : Fin 4} : w ∈ (Correct : Finset (Fin 4)) ↔ w ≠ 3 := by
  revert w; decide

theorem correct_four : (Correct : Finset (Fin 4)) = {0, 1, 2} := by decide

theorem ne_three_iff {w : Fin 4} : w ≠ 3 ↔ w.val ≠ 3 := by
  revert w; decide

/-- A block id: a round and an author. -/
abbrev Id := ℕ × Fin 4

/-- Block `(r, v)` references the blocks of the correct validators at round
`r − 1`. -/
def tBlock (b : Id) : Block (Fin 4) Id Unit :=
  ⟨b.1, b.2, if b.1 = 0 then ∅ else ({0, 1, 2} : Finset (Fin 4)).image fun w => (b.1 - 1, w),
    ()⟩

theorem mem_tRefs {b j : Id} :
    j ∈ (tBlock b).refs ↔ 0 < b.1 ∧ j.1 + 1 = b.1 ∧ j.2 ≠ 3 := by
  obtain ⟨r, v⟩ := b
  obtain ⟨s, w⟩ := j
  simp only [tBlock]
  split_ifs with h
  · simp [h]
  · simp only [Finset.mem_image, mem_three, Prod.mk.injEq]
    constructor
    · rintro ⟨x, hx, rfl, rfl⟩; exact ⟨by omega, by omega, hx⟩
    · rintro ⟨-, hs, hw⟩; exact ⟨w, hw, by omega, rfl⟩

/-- The blocks of the correct validators at rounds `0` to `N`. -/
def tIds (N : ℕ) : Finset Id := Finset.range (N + 1) ×ˢ {0, 1, 2}

theorem mem_tIds {N : ℕ} {b : Id} : b ∈ tIds N ↔ b.1 ≤ N ∧ b.2 ≠ 3 := by
  simp only [tIds, Finset.mem_product, Finset.mem_range, mem_three]; omega

theorem creatorsOf_tRefs {b : Id} (hb : 0 < b.1) :
    creatorsOf tBlock (tBlock b).refs = {0, 1, 2} := by
  ext w
  simp only [mem_creatorsOf, mem_tRefs, mem_three]
  constructor
  · rintro ⟨j, ⟨-, -, hj⟩, rfl⟩; exact hj
  · intro hw; exact ⟨(b.1 - 1, w), ⟨hb, by simp; omega, hw⟩, rfl⟩

/-- **The record**: every correct validator has a block at every round up to
`N`. -/
def tRec (N : ℕ) : KRecord (Fin 4) Id Unit where
  ids := tIds N
  block := tBlock
  complete i hi j hj := by
    rw [mem_tRefs] at hj
    rw [mem_tIds] at hi ⊢
    omega
  valid i _ := by
    refine ⟨fun j hj => ?_, fun h0 => ?_, fun j hj k hk hjk => ?_⟩
    · rw [mem_tRefs] at hj; exact hj.2.1
    · change quorumCard (Fin 4) ≤ (creatorsOf tBlock (tBlock i).refs).card
      rw [creatorsOf_tRefs h0]; rfl
    · rw [mem_tRefs] at hj hk
      exact Prod.ext (by omega) hjk
  no_equivocation i _ j _ _ hc hr := Prod.ext hr hc

/-! ## The timeline -/

/-- The wait above round `r`: `γ = 2` when the leaders of round `r` and of the
round below are correct, `τ = 4` otherwise. -/
def gap (r : ℕ) : ℕ := if r % 4 ≠ 3 ∧ (r + 3) % 4 ≠ 3 then 2 else 4

/-- The time the blocks of round `r` are built: rounds `0` and `1` before
`G`, round `2` at `G + τ`, and each round after `δ` and the wait. -/
def bt : ℕ → ℕ
  | 0 => 0
  | 1 => 1
  | 2 => 7
  | r + 3 => bt (r + 2) + 1 + gap (r + 2)

theorem bt_step {r : ℕ} (hr : 2 ≤ r) : bt (r + 1) = bt r + 1 + gap r := by
  obtain ⟨s, rfl⟩ : ∃ s, r = s + 2 := ⟨r - 2, by omega⟩
  rfl

theorem gap_le (r : ℕ) : gap r = 2 ∨ gap r = 4 := by
  unfold gap; split_ifs <;> simp

theorem bt_succ (r : ℕ) : bt r + 1 ≤ bt (r + 1) := by
  rcases r with _ | _ | r
  · decide
  · decide
  · change bt (r + 2) + 1 ≤ bt (r + 2 + 1)
    rw [bt_step (r := r + 2) (by omega)]; omega

theorem bt_strictMono : StrictMono bt := strictMono_nat_of_lt_succ fun r => bt_succ r

theorem bt_ge {r : ℕ} (hr : 2 ≤ r) : 7 ≤ bt r := by
  have := bt_strictMono.monotone hr
  exact this

/-- What validator `v` holds at time `t`, up: its own blocks once built,
every other block `δ = 1` after. -/
def normal (N : ℕ) (v : Fin 4) (t : ℕ) : Finset Id :=
  (tIds N).filter fun b => (b.2 = v ∧ bt b.1 ≤ t) ∨ bt b.1 + 1 ≤ t

/-- What validator `v` keeps on disk at time `t`: its own blocks once built,
and the rounds below its last. -/
def tDisk (N : ℕ) (v : Fin 4) (t : ℕ) : Finset Id :=
  (tIds N).filter fun b => (b.2 = v ∧ bt b.1 ≤ t) ∨ bt (b.1 + 1) ≤ t

/-- Validator `2` restarts at time `2` and holds only its disk. -/
def tHeld (N : ℕ) (v : Fin 4) (t : ℕ) : Finset Id :=
  if v = 2 ∧ t = 2 then tDisk N v t else normal N v t

/-- **The timeline.** -/
def tl (N : ℕ) : Timeline (Fin 4) Id := ⟨tHeld N, tDisk N, fun b => bt b.1⟩

theorem mem_normal {N : ℕ} {v : Fin 4} {t : ℕ} {b : Id} :
    b ∈ normal N v t ↔ b ∈ tIds N ∧ ((b.2 = v ∧ bt b.1 ≤ t) ∨ bt b.1 + 1 ≤ t) :=
  Finset.mem_filter

theorem mem_tDisk {N : ℕ} {v : Fin 4} {t : ℕ} {b : Id} :
    b ∈ tDisk N v t ↔ b ∈ tIds N ∧ ((b.2 = v ∧ bt b.1 ≤ t) ∨ bt (b.1 + 1) ≤ t) :=
  Finset.mem_filter

theorem tDisk_subset {N : ℕ} {v : Fin 4} {t : ℕ} : tDisk N v t ⊆ normal N v t := by
  intro b hb
  obtain ⟨hb, h⟩ := mem_tDisk.mp hb
  have := bt_succ b.1
  exact mem_normal.mpr ⟨hb, by omega⟩

theorem tHeld_subset {N : ℕ} {v : Fin 4} {t : ℕ} : tHeld N v t ⊆ normal N v t := by
  unfold tHeld; split_ifs
  · exact tDisk_subset
  · exact subset_rfl

theorem tHeld_of_ge {N : ℕ} {v : Fin 4} {t : ℕ} (ht : 3 ≤ t) :
    tHeld N v t = normal N v t := by
  unfold tHeld; rw [if_neg (by omega)]

/-- A block held is built by then. -/
theorem bt_le_of_held {N : ℕ} {v : Fin 4} {t : ℕ} {b : Id} (hb : b ∈ tHeld N v t) :
    b ∈ tIds N ∧ bt b.1 ≤ t := by
  obtain ⟨hi, h⟩ := mem_normal.mp (tHeld_subset hb)
  exact ⟨hi, by omega⟩

/-- Another author's block held is built `δ` before. -/
theorem bt_lt_of_held {N : ℕ} {v : Fin 4} {t : ℕ} {b : Id} (hb : b ∈ tHeld N v t)
    (hv : b.2 ≠ v) : bt b.1 + 1 ≤ t := by
  obtain ⟨-, h⟩ := mem_normal.mp (tHeld_subset hb)
  rcases h with ⟨h, -⟩ | h
  · exact absurd h hv
  · exact h

theorem mem_tHeld_of {N : ℕ} {v : Fin 4} {t : ℕ} {b : Id} (hb : b ∈ tIds N)
    (ht : 3 ≤ t) (h : bt b.1 + 1 ≤ t) : b ∈ tHeld N v t := by
  rw [tHeld_of_ge ht]; exact mem_normal.mpr ⟨hb, Or.inr h⟩

/-! ## What a node holds -/

theorem gap_eq_two {r : ℕ} : gap r = 2 ↔ r % 4 ≠ 3 ∧ (r + 3) % 4 ≠ 3 := by
  unfold gap; split_ifs with h
  · exact ⟨fun _ => h, fun _ => rfl⟩
  · exact ⟨fun h' => absurd h' (by decide), fun h' => absurd h' h⟩

theorem leader_ne {k : ℕ} : tSlots.leader k ≠ 3 ↔ k % 4 ≠ 3 := by
  rw [ne_three_iff, leader_val]

theorem bt_of_quorumIn {N : ℕ} {v : Fin 4} {t r : ℕ}
    (h : QuorumIn (tRec N) (tHeld N v t) r) : bt r + 1 ≤ t := by
  by_contra hlt
  have hsub : creatorsOf (tRec N).block
      ((tHeld N v t).filter fun b => ((tRec N).block b).round = r) ⊆ {v} := by
    intro w hw
    obtain ⟨b, hb, rfl⟩ := mem_creatorsOf.mp hw
    obtain ⟨hbH, hbr⟩ := Finset.mem_filter.mp hb
    have hbr' : b.1 = r := hbr
    rw [Finset.mem_singleton]
    by_contra hne
    exact hlt (hbr' ▸ bt_lt_of_held hbH hne)
  have := Finset.card_le_card hsub
  unfold QuorumIn at h
  rw [quorum_four, Finset.card_singleton] at *
  omega

theorem card_three : ({0, 1, 2} : Finset (Fin 4)).card = 3 := by decide

theorem quorumIn_of {N : ℕ} {v : Fin 4} {t r : ℕ} (hr : r ≤ N) (ht : 3 ≤ t)
    (h : bt r + 1 ≤ t) : QuorumIn (tRec N) (tHeld N v t) r := by
  unfold QuorumIn; rw [quorum_four, ← card_three]
  refine Finset.card_le_card fun w hw => mem_creatorsOf.mpr ⟨(r, w), Finset.mem_filter.mpr
    ⟨mem_tHeld_of (mem_tIds.mpr ⟨hr, mem_three.mp hw⟩) ht h, rfl⟩, rfl⟩

theorem certIn_of {N : ℕ} {v : Fin 4} {t r : ℕ} {L : Id} (hr : r ≤ N) (ht : 3 ≤ t)
    (h : bt r + 1 ≤ t) (hL : L.1 + 1 = r) (hL3 : L.2 ≠ 3) :
    CertIn (tRec N) (tHeld N v t) r L := by
  unfold CertIn; rw [quorum_four, ← card_three]
  refine Finset.card_le_card fun w hw => mem_creatorsOf.mpr ⟨(r, w), Finset.mem_filter.mpr
    ⟨mem_tHeld_of (mem_tIds.mpr ⟨hr, mem_three.mp hw⟩) ht h, rfl,
      mem_tRefs.mpr ⟨by simp; omega, hL, hL3⟩⟩, rfl⟩

theorem leader_of {N k : ℕ} {L : Id} (h : IsLeaderBlock (tRec N) k L) : k % 4 ≠ 3 := by
  obtain ⟨hL, -, hc⟩ := h
  have hc' : L.2 = tSlots.leader k := hc
  exact leader_ne.mp (hc' ▸ (mem_tIds.mp hL).2)

theorem of_waitsFor {N : ℕ} {v : Fin 4} {t r : ℕ} (hr : 1 ≤ r)
    (h : WaitsFor (tRec N) (tHeld N v t) r) : bt r + 1 ≤ t ∧ gap r = 2 := by
  obtain ⟨hq, hl, hc⟩ := h
  obtain ⟨L, -, hL⟩ := hl r rfl
  obtain ⟨L', hL', -⟩ := hc (r - 1) (by rw [slotRound_eq]; omega)
  have h1 := leader_of hL
  have h2 := leader_of hL'
  exact ⟨bt_of_quorumIn hq, gap_eq_two.mpr ⟨h1, by omega⟩⟩

theorem waitsFor_of {N : ℕ} {v : Fin 4} {t r : ℕ} (hr : 1 ≤ r) (hrN : r ≤ N) (ht : 3 ≤ t)
    (h : bt r + 1 ≤ t) (hg : gap r = 2) : WaitsFor (tRec N) (tHeld N v t) r := by
  obtain ⟨h1, h2⟩ := gap_eq_two.mp hg
  refine ⟨quorumIn_of hrN ht h, fun k hk => ?_, fun k hk => ?_⟩
  · rw [slotRound_eq] at hk; subst hk
    have hL : (k, tSlots.leader k) ∈ tIds N := mem_tIds.mpr ⟨hrN, leader_ne.mpr h1⟩
    exact ⟨_, mem_tHeld_of hL ht h, hL, rfl, rfl⟩
  · rw [slotRound_eq] at hk
    have hL : (k, tSlots.leader k) ∈ tIds N :=
      mem_tIds.mpr ⟨by omega, leader_ne.mpr (by omega)⟩
    exact ⟨_, ⟨hL, rfl, rfl⟩, certIn_of hrN ht h hk (leader_ne.mpr (by omega))⟩

theorem not_allIn {N : ℕ} {v : Fin 4} {t r : ℕ} : ¬ AllIn (tRec N) (tHeld N v t) r := by
  intro h
  obtain ⟨x, hx, -, hxc⟩ := h 3
  exact (mem_tIds.mp (bt_le_of_held hx).1).2 hxc

theorem of_behindIn {N : ℕ} {v : Fin 4} {t r : ℕ}
    (h : BehindIn (tRec N) (tHeld N v t) v r) : bt (r + 1) + 1 ≤ t ∧ r + 1 ≤ N := by
  obtain ⟨w, hw⟩ := Finset.card_pos.mp (lt_of_lt_of_le (Nat.succ_pos _) h)
  obtain ⟨hwv, hw⟩ := Finset.mem_erase.mp hw
  obtain ⟨b, hb, rfl⟩ := mem_creatorsOf.mp hw
  obtain ⟨hbH, hbr⟩ := Finset.mem_filter.mp hb
  have hbr' : b.1 = r + 1 := hbr
  exact ⟨hbr' ▸ bt_lt_of_held hbH hwv, hbr' ▸ (mem_tIds.mp (bt_le_of_held hbH).1).1⟩

/-! ## The run -/

theorem built_eq {N : ℕ} (b : Id) : (tl N).built b = bt b.1 := rfl

theorem normal_mono {N : ℕ} {v : Fin 4} {t t' : ℕ} (ht : t ≤ t') :
    normal N v t ⊆ normal N v t' := fun b hb => by
  obtain ⟨hi, h⟩ := mem_normal.mp hb
  refine mem_normal.mpr ⟨hi, ?_⟩
  rcases h with ⟨h1, h2⟩ | h
  · exact Or.inl ⟨h1, by omega⟩
  · exact Or.inr (by omega)

/-- **The timeline is a reactive run** from round `2` to round `N`, at
`G = 3`, `δ = 1`, `τ = 4`, `γ = 2` and `μ = 1`, with every correct
validator up from `G` on. -/
theorem t_run {N : ℕ} (hN : 2 ≤ N) : ReactiveRun (tRec N) (tl N) Correct 3 1 4 2 1 2 N where
  stable := Finset.Subset.refl _
  large := card_correct
  held_ids _ _ _ hb := (bt_le_of_held hb).1
  mono v _ t t' hG htt' b hb := by
    change b ∈ tHeld N v t at hb; change b ∈ tHeld N v t'
    rw [tHeld_of_ge hG] at hb; rw [tHeld_of_ge (by omega)]
    exact normal_mono htt' hb
  delivers _ _ t hG b hb _ w _ :=
    mem_tHeld_of (bt_le_of_held hb).1 (by omega) (by have := (bt_le_of_held hb).2; omega)
  closed v _ t b hb _ j hj := by
    obtain ⟨h0, hjb, hj3⟩ := mem_tRefs.mp hj
    obtain ⟨hbi, hbt⟩ := bt_le_of_held hb
    have hji : j ∈ tIds N := mem_tIds.mpr ⟨by have := (mem_tIds.mp hbi).1; omega, hj3⟩
    change j ∈ tHeld N v t
    change b ∈ tHeld N v t at hb
    unfold tHeld at hb ⊢
    split_ifs at hb ⊢ with hc
    · obtain ⟨-, h⟩ := mem_tDisk.mp hb
      have := bt_succ b.1
      exact mem_tDisk.mpr ⟨hji, Or.inr (by rw [hjb]; rcases h with ⟨-, h⟩ | h <;> omega)⟩
    · have := bt_succ j.1
      rw [hjb] at this
      exact mem_normal.mpr ⟨hji, Or.inr (by omega)⟩
  causal _ _ _ _ hb _ := (bt_le_of_held hb).2
  prior _ _ _ _ hb _ hne := bt_lt_of_held hb hne
  disk_held v _ t := by
    change tDisk N v t ⊆ tHeld N v t
    unfold tHeld; split_ifs
    · exact subset_rfl
    · exact tDisk_subset
  stores b hb _ t ht := mem_tDisk.mpr ⟨hb, Or.inl ⟨rfl, ht⟩⟩
  waits b hb _ r hbr hr := by
    have hbr' : b.1 = r + 1 := hbr
    have hbN := (mem_tIds.mp hb).1
    have hstep : (tl N).built b = bt r + 1 + gap r := by rw [built_eq, hbr']; exact bt_step hr
    have h7 := bt_ge hr
    have := gap_le r
    by_cases hg : gap r = 2
    · exact Or.inl ⟨by omega, waitsFor_of (by omega) (by omega) (by omega) (by omega) hg,
        waitsFor_of (by omega) (by omega) (by omega) (by omega) hg⟩
    · exact Or.inr (Or.inr (Or.inl ⟨by omega, quorumIn_of (by omega) (by omega) (by omega)⟩))
  prompt v hv r t hr hrN hw := by
    refine ⟨(r + 1, v), mem_tIds.mpr ⟨by omega, mem_correct_four.mp hv⟩, rfl, le_rfl, ?_⟩
    rw [built_eq]
    change bt (r + 1) ≤ t
    rw [bt_step hr]
    have := gap_le r
    rcases hw with ⟨-, -, ⟨hγ, hW⟩ | ⟨-, hA⟩ | ⟨hτ, hQ⟩⟩ | ⟨-, hB⟩
    · obtain ⟨h1, h2⟩ := of_waitsFor (by omega) hW; omega
    · exact absurd hA not_allIn
    · have := bt_of_quorumIn hQ; omega
    · have := (of_behindIn hB).1; rw [bt_step hr] at this; omega
  covers b _ _ x hx hxr :=
    ⟨x, mem_tRefs.mpr ⟨by change x.1 + 1 = b.1 at hxr; omega, hxr,
      (mem_tIds.mp (bt_le_of_held hx).1).2⟩, rfl⟩
  certifies b _ _ k hk := by
    rintro ⟨L, hL, -⟩
    obtain ⟨hLi, hLr, hLc⟩ := hL
    have hk' : k + 2 = b.1 := hk
    have hLr' : L.1 = k := hLr
    refine ⟨L, ⟨hLi, hLr, hLc⟩, ?_⟩
    unfold CarriesVotes; rw [quorum_four, ← card_three]
    exact Finset.card_le_card fun w hw => mem_creatorsOf.mpr ⟨(k + 1, w),
      mem_carriedVotes.mpr ⟨mem_tRefs.mpr ⟨by omega, by simp; omega, mem_three.mp hw⟩,
        mem_tRefs.mpr ⟨by simp, by simp; omega, (mem_tIds.mp hLi).2⟩⟩, rfl⟩
  start := ⟨7, fun v hv => ⟨(2, v), mem_tIds.mpr ⟨hN, mem_correct_four.mp hv⟩, rfl, le_rfl,
    le_rfl⟩⟩
  late b _ _ hr := bt_ge hr

/-- Correct validators keep on disk the histories of their blocks'
references, to any depth. -/
theorem t_keepsHistory (N K : ℕ) : KeepsHistory (tRec N) (tl N) K := by
  intro b hb _ t ht y hy z hz
  obtain ⟨h0, hyb, -⟩ := mem_tRefs.mp hy
  have hyi := (tRec N).complete b hb y hy
  have hzr := (round_of_mem_historyUpto K hyi hz).1
  have hzr' : z.1 ≤ y.1 := hzr
  have := bt_strictMono.monotone (show z.1 + 1 ≤ b.1 by omega)
  exact mem_tDisk.mpr ⟨historyUpto_subset_ids K hyi hz, Or.inr (by rw [built_eq] at ht; omega)⟩

/-- Correct validators hold the available sub-DAG of a leader block `δ`
after they hold the block. -/
theorem t_fetches (N K : ℕ) : Fetches (tRec N) (tl N) Correct K 3 1 := by
  intro v _ t hG j A hA _ hAv z hz
  have hAi := (bt_le_of_held hAv).1
  obtain ⟨y, hy, hzy⟩ := hz
  have h1 := hy.round_le hAi
  have h2 := (round_of_mem_historyUpto K (hy.mem hAi) hzy).1
  have h1' : y.1 ≤ A.1 := h1
  have h2' : z.1 ≤ y.1 := h2
  have := bt_strictMono.monotone (h2'.trans h1')
  have := (bt_le_of_held hAv).2
  exact mem_tHeld_of (avail_subset_ids hAi ⟨y, hy, hzy⟩) (by omega) (by omega)

/-- Correct validators build above the blocks of their own on their disk,
through the restart of validator `2`. -/
theorem t_buildsAboveDisk (N : ℕ) : BuildsAboveDisk (tRec N).ids (tRec N).block (tl N) where
  stores b hb _ t ht := ⟨b, mem_tDisk.mpr ⟨hb, Or.inl ⟨rfl, ht⟩⟩, rfl, le_rfl⟩
  above b _ _ h0 b' hb' hc := by
    rw [built_eq] at h0 hb'
    obtain ⟨-, h⟩ := mem_tDisk.mp hb'
    change b'.1 < b.1
    rcases h with ⟨-, h⟩ | h
    · exact bt_strictMono.lt_iff_lt.mp (by omega)
    · have := bt_strictMono.lt_iff_lt.mp (show bt (b'.1 + 1) < bt b.1 by omega); omega
  single b _ c _ _ hc ht := Prod.ext (bt_strictMono.injective ht) hc

/-! ## What Theorem 7 gives -/

theorem bt_five : bt 5 = 20 := by decide

/-- **Building above the disk persists the last round built**, through the
restart, by `Reactive.OnDisk`. -/
theorem t_persists (N : ℕ) : ∃ next, Persists (tRec N).ids (tRec N).block (tl N).built next :=
  Reactive.onDisk (Fin 4) Id Unit _ _ _ (t_buildsAboveDisk N)

/-- **Slot `5` commits by time `27`**: its leader and the leaders next to it
are correct, the blocks of round `5` are built at time `20`, and by
`Reactive.Commits` every correct node commits the slot directly on what it
holds at `20 + 3δ + 2 max γ μ = 27`. -/
theorem t_commits {N : ℕ} (hN : 7 ≤ N) (K : ℕ) {v : Fin 4}
    (hv : v ∈ (Correct : Finset (Fin 4))) :
    ∃ L, IsLeaderBlock (tRec N) 5 L ∧ NodeDecided (tRec N) K (tHeld N v 27) 5 (some L) :=
  Reactive.commits (Fin 4) Id Unit (tRec N) (tl N) Correct 3 1 4 2 1 2 K N (t_run (by omega))
    (by norm_num) (by norm_num) (by norm_num) 5 20 (by rw [slotRound_eq]; omega)
    (by rw [slotRound_eq]; omega)
    (fun j h1 h2 => mem_correct_four.mpr
      (leader_ne.mpr (by simp only [slotRound_eq] at h1 h2; omega)))
    (fun w hw => ⟨(5, w), mem_tIds.mpr ⟨by omega, mem_correct_four.mp hw⟩, rfl, rfl,
      by rw [built_eq, bt_five]⟩) v hv

/-- **The run is synchronous** from round `3`, by `Reactive.Synchronised`. -/
theorem t_synchronised {N : ℕ} (hN : 2 ≤ N) :
    SyncFrom (tRec N) (Correct : Finset (Fin 4)) 3 N :=
  Reactive.synchronised (Fin 4) Id Unit (tRec N) (tl N) Correct 3 1 4 2 1 2 N (t_run hN)
    (by norm_num) (by norm_num) (by norm_num)

/-- Every fourth slot from `0` starts three slots led by correct validators. -/
theorem t_fair : FairRunOn (Correct : Finset (Fin 4)) 3 := fun k =>
  ⟨4 * (k / 4) + 4, by omega, fun i hi =>
    mem_correct_four.mpr (leader_ne.mpr (by omega))⟩

/-- **The ledger grows**, by `Reactive.Ledger`: past any slot there is a run
of three slots led by correct validators below which every correct node,
at one time, decides every slot and has fetched below the leaders it
commits. -/
theorem t_ledger {N : ℕ} (hN : 2 ≤ N) (K D k : ℕ) : ∃ b, k ≤ b ∧
    (b + 3 - 1 + 2 ≤ N → ∃ t, ∀ v ∈ (Correct : Finset (Fin 4)),
      ∃ g : ℕ → Option Id, ∀ i, i < b + 3 →
        NodeDecided (tRec N) K (tHeld N v t) i (g i) ∧
        ∀ L, g i = some L → FetchedIn (tRec N) K (tHeld N v t) L (L.1 - D)) :=
  Reactive.ledger (Fin 4) Id Unit (tRec N) (tl N) Correct 3 1 4 2 1 2 N K D 1 3 (t_run hN)
    (by norm_num) (by norm_num) (by norm_num) (t_fetches N K) (by norm_num)
    (fun b i hi => by unfold EligibleAt; rw [slotRound_eq, slotRound_eq]; omega) t_fair k

/-- **The channel closes**, by `Close.Closes`, when every block declares it
closed: every two rounds hold a slot led by a correct validator. -/
theorem t_closes {N : ℕ} (hN : 2 ≤ N) : ∃ b, b + 3 - 1 + 2 ≤ N → ∃ t,
    ∀ v ∈ (Correct : Finset (Fin 4)), ∃ (g : ℕ → Option Id) (n : ℕ),
      DecidesBelow (tRec N) 3 (tHeld N v t) 2 g n ∧
      ClosesAfter (tRec N) 3 (tHeld N v t) 2 (fun _ => True) g n :=
  Close.closes (Fin 4) Id Unit (tRec N) (tl N) Correct 3 1 4 2 1 2 N 3 2 1 3 0 (fun _ => True)
    (t_run hN) (by norm_num) (by norm_num) (by norm_num) le_rfl (t_fetches N 3) (by norm_num)
    (fun b i hi => by unfold EligibleAt; rw [slotRound_eq, slotRound_eq]; omega) t_fair
    (fun r => by
      by_cases hr : (r + 1) % 4 = 3
      · exact ⟨r + 2, by rw [slotRound_eq]; omega, (slotRound_eq _).le,
          mem_correct_four.mpr (leader_ne.mpr (by omega))⟩
      · exact ⟨r + 1, by rw [slotRound_eq]; omega, by rw [slotRound_eq]; omega,
          mem_correct_four.mpr (leader_ne.mpr hr)⟩)
    fun _ _ _ _ => trivial

end Timed

end KPartialDag

end LeanDagTest
