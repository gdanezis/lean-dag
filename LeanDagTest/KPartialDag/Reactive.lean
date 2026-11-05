import LeanDag.KPartialDag.Reactive.Proof
/-!
# Reactive nodes in time — a witness

`ReactiveRun` is satisfiable: one correct validator builds one block a
round up to round `N`, each referencing the one below, and holds every block
at every time. With `G = δ = τ = 0`, `Reactive.Commits` then decides every
slot from `2` to `N − 2`. The witness shows the fields of `ReactiveRun` are
consistent; with `δ = 0` it exercises none of the timing.
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

/-- Every block is held at every time, and built at time `0`. -/
def chainTimeline (N : ℕ) : Timeline Unit ℕ := ⟨fun _ _ => Finset.range (N + 1), fun _ => 0⟩

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

/-- **The chain is a reactive run** from round `0` to round `N`. -/
theorem chain_run (N : ℕ) : ReactiveRun (chain N) (chainTimeline N) 0 0 0 0 N where
  held_ids _ _ := Finset.Subset.refl _
  mono _ _ _ _ _ := Finset.Subset.refl _
  gossip _ _ _ _ _ _ := Finset.Subset.refl _
  closed _ _ _ b hb j hj := (chain N).complete b hb j hj
  own _ hb _ := hb
  causal _ _ _ _ _ _ := Nat.zero_le _
  late _ _ _ _ := le_rfl
  start := ⟨0, fun _ _ => ⟨0, Finset.mem_range.mpr (by omega), rfl, rfl, le_rfl⟩⟩
  waits b hb _ r hbr _ := Or.inl (waitsFor_chain (by
    have : (chain N).block b = chainBlock b := rfl
    simp only [Finset.mem_range, chain] at hb
    simp only [this, chainBlock] at hbr
    omega))
  prompt _ _ r _ _ hr _ := ⟨r + 1, Finset.mem_range.mpr (by omega), rfl, rfl, Nat.zero_le _⟩
  votes b hb _ k hk _ := by
    rw [slotRound_unit] at hk
    have hbk : b = k + 1 := hk.symm
    subst hbk
    refine ⟨k, mem_chainRefs.mpr ⟨by omega, by omega⟩,
      Finset.mem_range.mpr (by simp [chain] at hb; omega), rfl, rfl⟩
  certifies b hb _ k hk _ := by
    rw [slotRound_unit] at hk
    have hbk : b = k + 2 := hk.symm
    subst hbk
    refine ⟨k, ⟨Finset.mem_range.mpr (by simp [chain] at hb; omega), rfl, rfl⟩, ?_⟩
    rw [CarriesVotes, quorum_unit]
    exact Finset.card_pos.mpr ⟨(), mem_creatorsOf.mpr ⟨k + 1, mem_carriedVotes.mpr
      ⟨mem_chainRefs.mpr ⟨by omega, by omega⟩, mem_chainRefs.mpr ⟨by omega, by omega⟩⟩, rfl⟩⟩

/-- **The chain decides**: by `Reactive.Commits`, the node decides slot `k`
directly on what it holds, for every slot `k` from `2` to `N − 2`. -/
theorem chain_decides (N K k : ℕ) (h2 : 2 ≤ k) (hk : k + 2 ≤ N) :
    ∃ L, IsLeaderBlock (chain N) k L ∧
      NodeDecided (chain N) K ((chainTimeline N).held () 0) k (some L) := by
  have := Reactive.commits Unit ℕ Unit (chain N) (chainTimeline N) 0 0 0 0 K N (chain_run N)
    le_rfl k 0 (by rw [slotRound_unit]; omega) (by rw [slotRound_unit]; omega)
    (fun _ _ _ => mem_correct_unit _)
    (fun v _ => ⟨k, Finset.mem_range.mpr (by omega), rfl, rfl, le_rfl⟩) () (mem_correct_unit _)
  simpa using this

end KPartialDag

end LeanDagTest
