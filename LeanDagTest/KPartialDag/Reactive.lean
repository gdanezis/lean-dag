import LeanDag.KPartialDag.Reactive.Proof
/-!
# Reactive nodes in time — a witness

`ReactiveRun` is satisfiable: one correct validator builds one block a
round up to round `N`, each referencing the one below, all at time `1`, and
holds every block, and keeps it on disk, from time `1` on. With
`G = δ = μ = 0` and `τ = γ = 1`, `Reactive.Commits` then decides every slot
from `2` to `N − 2`. The witness shows the fields of `ReactiveRun` are
consistent; with `δ = 0` it exercises none of the timing, and no restart.
-/

namespace LeanDagTest

namespace KPartialDag

open LeanDag LeanDag.KPartialDag

instance unitFaults : Faults Unit where
  f := 0
  byzantine := ∅
  card_validators := by simp
  card_byzantine := by simp

instance unitSlots : Slots Unit := Slots.identity fun _ => ()

theorem quorum_unit : quorumCard Unit = 1 := rfl

/-- Block `i` is at round `i` and references block `i − 1`. -/
def chainBlock (i : ℕ) : Block Unit ℕ Unit :=
  ⟨i, (), if i = 0 then ∅ else {i - 1}, ()⟩

theorem mem_chainRefs {i j : ℕ} : j ∈ (chainBlock i).refs ↔ 0 < i ∧ j = i - 1 := by
  unfold chainBlock
  split_ifs with h <;> simp [h]; omega

/-- The chain of blocks `0, …, N`. -/
def chain (N : ℕ) : KRecord Unit ℕ Unit where
  ids := Finset.range (N + 1)
  block := chainBlock
  complete i hi j hj := by
    rw [mem_chainRefs] at hj
    simp only [Finset.mem_range] at hi ⊢
    omega
  valid i _ := by
    refine ⟨fun j hj => ?_, fun h0 => ?_, fun j hj k hk _ => ?_⟩
    · rw [mem_chainRefs] at hj
      simp only [chainBlock]; omega
    · simp only [chainBlock] at h0
      rw [quorum_unit]
      simp [creators, creatorsOf, chainBlock, Nat.pos_iff_ne_zero.mp h0]
    · rw [mem_chainRefs] at hj hk
      omega
  no_equivocation i _ j _ _ _ h := h

/-- Every block is held from time `1` on. -/
def chainHeld (N t : ℕ) : Finset ℕ := if 1 ≤ t then Finset.range (N + 1) else ∅

theorem mem_chainHeld {N t b : ℕ} : b ∈ chainHeld N t ↔ 1 ≤ t ∧ b ≤ N := by
  unfold chainHeld
  split_ifs with h <;> simp [h, Nat.lt_succ_iff]

/-- Every block is held, and kept on disk, from time `1` on, and built at
time `1`. -/
def chainTimeline (N : ℕ) : Timeline Unit ℕ :=
  ⟨fun _ => chainHeld N, fun _ => chainHeld N, fun _ => 1⟩

theorem correct_unit : (Correct : Finset Unit) = {()} := by
  ext v
  simp only [Correct, Finset.mem_compl, Finset.mem_singleton]
  exact ⟨fun _ => trivial, fun _ => Finset.notMem_empty v⟩

theorem slotRound_unit (k : ℕ) : Slots.slotRound Unit k = k := rfl

theorem mem_correct_unit (v : Unit) : v ∈ (Correct : Finset Unit) := by
  rw [correct_unit]; exact Finset.mem_singleton_self _

theorem quorumIn_chain {N r : ℕ} (hr : r ≤ N) :
    QuorumIn (chain N) (Finset.range (N + 1)) r := by
  rw [QuorumIn, quorum_unit]
  exact Finset.card_pos.mpr ⟨(), mem_creatorsOf.mpr
    ⟨r, Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), rfl⟩, rfl⟩⟩

theorem waitsFor_chain {N r : ℕ} (hr : r < N) :
    WaitsFor (chain N) (Finset.range (N + 1)) r := by
  refine ⟨quorumIn_chain (by omega), fun k hk => ⟨r, Finset.mem_range.mpr (by omega),
    Finset.mem_range.mpr (by omega), hk.symm, rfl⟩, fun k hk => ⟨k,
    ⟨Finset.mem_range.mpr (by rw [slotRound_unit] at hk; omega), rfl, rfl⟩, ?_⟩⟩
  rw [slotRound_unit] at hk
  rw [CertIn, quorum_unit]
  refine Finset.card_pos.mpr ⟨(), mem_creatorsOf.mpr
    ⟨r, Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), rfl, ?_⟩, rfl⟩⟩
  exact mem_chainRefs.mpr ⟨by omega, by omega⟩

theorem not_quorumIn_empty {N r : ℕ} : ¬ QuorumIn (chain N) ∅ r := by
  rw [QuorumIn, quorum_unit]
  simp [creatorsOf]

theorem not_behindIn {N r : ℕ} {H : Finset ℕ} {v : Unit} : ¬ BehindIn (chain N) H v r := by
  intro h
  have : ((creatorsOf (chain N).block
      (H.filter fun b => ((chain N).block b).round = r + 1)).erase v).card = 0 :=
    Finset.card_eq_zero.mpr
      (Finset.eq_empty_of_forall_notMem fun w hw => (Finset.mem_erase.mp hw).1 rfl)
  unfold BehindIn at h
  rw [this] at h
  exact Nat.not_succ_le_zero _ h

/-- **The chain is a reactive run** from round `0` to round `N`. -/
theorem chain_run (N : ℕ) :
    ReactiveRun (chain N) (chainTimeline N) (Correct : Finset Unit) 0 0 1 1 0 0 N where
  stable := Finset.Subset.refl _
  large := card_correct
  held_ids _ _ b hb := Finset.mem_range.mpr (by have := mem_chainHeld.mp hb; omega)
  mono _ _ _ _ _ htt' b hb := by
    obtain ⟨h1, h2⟩ := mem_chainHeld.mp hb
    exact mem_chainHeld.mpr ⟨by omega, h2⟩
  delivers _ _ _ _ b hb _ _ _ := by simpa using hb
  closed _ _ _ b hb _ j hj := by
    obtain ⟨h1, h2⟩ := mem_chainHeld.mp hb
    have := mem_chainRefs.mp hj
    exact mem_chainHeld.mpr ⟨h1, by omega⟩
  causal _ _ _ _ hb _ := (mem_chainHeld.mp hb).1
  prior _ _ _ _ _ _ hne := absurd rfl hne
  disk_held _ _ _ := Finset.Subset.refl _
  stores b hb _ t ht := mem_chainHeld.mpr ⟨ht, by simp [chain] at hb; omega⟩
  late _ _ _ _ := le_rfl
  start := ⟨1, fun _ _ => ⟨0, Finset.mem_range.mpr (by omega), rfl, le_rfl, le_rfl⟩⟩
  waits b hb _ r hbr _ := by
    have hr : r < N := by
      have : (chain N).block b = chainBlock b := rfl
      simp only [Finset.mem_range, chain] at hb
      simp only [this, chainBlock] at hbr
      omega
    have hH : (chainTimeline N).held ((chain N).block b).creator ((chainTimeline N).built b) =
        Finset.range (N + 1) := by simp [chainTimeline, chainHeld]
    rw [hH]
    exact Or.inr (Or.inl ⟨waitsFor_chain hr,
      fun _ => ⟨r, Finset.mem_range.mpr (by omega), rfl, rfl⟩⟩)
  prompt v _ r t _ hr hw := by
    refine ⟨r + 1, Finset.mem_range.mpr (by omega), rfl, le_rfl, ?_⟩
    change 1 ≤ t
    rcases hw with ⟨-, hQ, -⟩ | ⟨-, hB⟩
    · by_contra h0
      have : (chainTimeline N).held v (t - 0) = ∅ := by
        simp [chainTimeline, chainHeld]; omega
      exact not_quorumIn_empty (this ▸ hQ)
    · exact absurd hB not_behindIn
  covers b hb _ x hx hxb := by
    have hb' : (chain N).block b = chainBlock b := rfl
    have hx' : (chain N).block x = chainBlock x := rfl
    simp only [hb', hx', chainBlock] at hxb
    exact ⟨x, mem_chainRefs.mpr ⟨by omega, by omega⟩, rfl⟩
  certifies b hb _ k hk _ := by
    rw [slotRound_unit] at hk
    have hbk : b = k + 2 := hk.symm
    subst hbk
    refine ⟨k, ⟨Finset.mem_range.mpr (by simp [chain] at hb; omega), rfl, rfl⟩, ?_⟩
    rw [CarriesVotes, quorum_unit]
    exact Finset.card_pos.mpr ⟨(), mem_creatorsOf.mpr ⟨k + 1, mem_carriedVotes.mpr
      ⟨mem_chainRefs.mpr ⟨by omega, by omega⟩, mem_chainRefs.mpr ⟨by omega, by omega⟩⟩, rfl⟩⟩

/-- **The chain decides**: by `Reactive.Commits`, the node decides slot `k`
directly on what it holds at time `3`, for every slot `k` from `2` to
`N − 2`. -/
theorem chain_decides (N K k : ℕ) (h2 : 2 ≤ k) (hk : k + 2 ≤ N) :
    ∃ L, IsLeaderBlock (chain N) k L ∧
      NodeDecided (chain N) K ((chainTimeline N).held () 3) k (some L) := by
  have := Reactive.commits Unit ℕ Unit (chain N) (chainTimeline N) Correct 0 0 1 1 0 0 K N
    (chain_run N)
    (by norm_num) (by norm_num) le_rfl k 1 (by rw [slotRound_unit]; omega)
    (by rw [slotRound_unit]; omega) (fun _ _ _ => mem_correct_unit _)
    (fun v _ => ⟨k, Finset.mem_range.mpr (by omega), rfl, rfl, le_rfl⟩) () (mem_correct_unit _)
  simpa using this

/-- **The chain is synchronous** from round `1`, by `Reactive.Synchronised`. -/
theorem chain_synchronised (N : ℕ) : SyncFrom (chain N) (Correct : Finset Unit) 1 N :=
  Reactive.synchronised Unit ℕ Unit (chain N) (chainTimeline N) Correct 0 0 1 1 0 0 N
    (chain_run N)
    (by norm_num) (by norm_num) le_rfl

end KPartialDag

end LeanDagTest
