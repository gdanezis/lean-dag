import LeanDag.KPartialSparse.Model.Order
import LeanDag.KPartialSparse.Helpers.Live
/-!
# Sparse K-partial DAG — the order, helpers

`docs/kpartial-sparse.md` §8. What a node reads of a leader's output
(`outIn_eq`), the agreement and growth of ledgers (`ledgerIn_grows`), the
ledger order, settled blocks, and, after synchrony with leaders of `T`
covering `T`, the output and inclusion of the blocks of `T`
(`mem_out_of_covers`, `mem_ledgerIn_of_gap`).
-/

namespace LeanDag

namespace KPartialSparse

open KPartialDag (Crashes LiveRow)
open scoped KPartialDag
open Scheme

variable {Validator : Type*} [Fintype Validator] [DecidableEq Validator] [F : Faults Validator]
variable [Cr : Crashes Validator] [Ld : Leaders Validator]
variable {BlockId : Type*} [LinearOrder BlockId] {Payload : Type*} [ClaimFormat BlockId Payload]
variable {U : SRecord Validator BlockId Payload} {K D : ℕ} {H : Finset BlockId}
variable {T : Finset Validator} {R : ℕ} {p : Params}

omit [ClaimFormat BlockId Payload] in
/-- What a node reads of a leader's output lies in the output. -/
theorem outIn_subset {L : BlockId} : OutIn U K H D L ⊆ Out U K D L :=
  fun _ hb => ⟨availIn_subset hb.1, hb.2⟩

omit [ClaimFormat BlockId Payload] in
/-- **Fetched down to `D` rounds below the leader, a node reads all its
output.** -/
theorem outIn_eq (hH : H ⊆ U.ids) {L : BlockId}
    (hf : FetchedIn U K H L ((U.block L).round - D)) : OutIn U K H D L = Out U K D L :=
  Set.Subset.antisymm outIn_subset fun _ hb =>
    ⟨avail_subset_availIn hH hf hb.1 (by have := hb.2; omega), hb.2⟩

omit [ClaimFormat BlockId Payload] in
/-- The ledger grows with the slots settled. -/
theorem ledgerIn_mono {g : ℕ → Option BlockId} {n n' : ℕ} (h : n ≤ n') :
    LedgerIn U K H D g n ⊆ LedgerIn U K H D g n' := by
  rintro b ⟨k, hk, hrest⟩
  exact ⟨k, by omega, hrest⟩

omit [ClaimFormat BlockId Payload] in
/-- **A block enters a ledger at one slot.** -/
theorem entersIn_unique {g : ℕ → Option BlockId} {b : BlockId} {k₁ k₂ : ℕ}
    (h₁ : EntersIn U K H D g b k₁) (h₂ : EntersIn U K H D g b k₂) : k₁ = k₂ := by
  rcases lt_trichotomy k₁ k₂ with h | h | h
  · obtain ⟨L, hL, hb⟩ := h₁.1
    exact absurd hb (h₂.2 k₁ h L hL)
  · exact h
  · obtain ⟨L, hL, hb⟩ := h₂.1
    exact absurd hb (h₁.2 k₂ h L hL)

omit [ClaimFormat BlockId Payload] in
/-- A block of a ledger enters it at some slot. -/
theorem exists_entersIn {g : ℕ → Option BlockId} {n : ℕ} {b : BlockId}
    (h : b ∈ LedgerIn U K H D g n) : ∃ k, k < n ∧ EntersIn U K H D g b k := by
  classical
  have hex : ∃ k, ∃ L, g k = some L ∧ b ∈ OutIn U K H D L := by
    obtain ⟨k, -, hrest⟩ := h
    exact ⟨k, hrest⟩
  obtain ⟨k, hk, hrest⟩ := h
  exact ⟨Nat.find hex, lt_of_le_of_lt (Nat.find_min' hex hrest) hk, Nat.find_spec hex,
    fun j hj L hL hb => Nat.find_min hex hj ⟨L, hL, hb⟩⟩

omit [ClaimFormat BlockId Payload] in
/-- Verdicts that agree, with outputs that agree, give one ledger. -/
theorem ledgerIn_subset_of {H₁ H₂ : Finset BlockId} {g₁ g₂ : ℕ → Option BlockId} {n : ℕ}
    (hg : ∀ k, k < n → g₁ k = g₂ k)
    (hout : ∀ k L, k < n → g₁ k = some L → OutIn U K H₁ D L = OutIn U K H₂ D L) :
    LedgerIn U K H₁ D g₁ n ⊆ LedgerIn U K H₂ D g₂ n := by
  rintro b ⟨k, hk, L, hL, hb⟩
  exact ⟨k, hk, L, by rw [← hg k hk]; exact hL, by rw [← hout k L hk hL]; exact hb⟩

omit [ClaimFormat BlockId Payload] in
/-- Verdicts that agree, with outputs that agree, give one entry slot. -/
theorem entersIn_of {H₁ H₂ : Finset BlockId} {g₁ g₂ : ℕ → Option BlockId} {n : ℕ}
    (hg : ∀ k, k < n → g₁ k = g₂ k)
    (hout : ∀ k L, k < n → g₁ k = some L → OutIn U K H₁ D L = OutIn U K H₂ D L)
    {b : BlockId} {k : ℕ} (hk : k < n) (h : EntersIn U K H₁ D g₁ b k) :
    EntersIn U K H₂ D g₂ b k := by
  obtain ⟨⟨L, hL, hb⟩, hmin⟩ := h
  refine ⟨⟨L, by rw [← hg k hk]; exact hL, by rw [← hout k L hk hL]; exact hb⟩, ?_⟩
  intro j hj L' hL' hb'
  have hL₁ : g₁ j = some L' := by rw [hg j (by omega)]; exact hL'
  exact hmin j hj L' hL₁ (by rw [hout j L' (by omega) hL₁]; exact hb')

variable [S : Slots Validator]

/-- **Two nodes have one ledger, and one entry slot per block**, at a row and
the depth the sub-DAG needs, on a disciplined schedule and record, once each
has fetched down to `D` rounds below the leaders it committed. -/
theorem ledgerIn_agree (hrow : Row Validator p) (hdeep : Deep Validator K)
    (hI : Disciplined K p.certThreshold S U) {H₁ H₂ : Finset BlockId} (hH₁ : H₁ ⊆ U.ids)
    (hH₂ : H₂ ⊆ U.ids) {g₁ g₂ : ℕ → Option BlockId} {n : ℕ}
    (h₁ : ∀ k, k < n → NodeDecided p U K H₁ k (g₁ k))
    (h₂ : ∀ k, k < n → NodeDecided p U K H₂ k (g₂ k))
    (hf₁ : ∀ k L, k < n → g₁ k = some L → FetchedIn U K H₁ L ((U.block L).round - D))
    (hf₂ : ∀ k L, k < n → g₂ k = some L → FetchedIn U K H₂ L ((U.block L).round - D)) :
    LedgerIn U K H₁ D g₁ n = LedgerIn U K H₂ D g₂ n ∧
      ∀ b k, k < n → (EntersIn U K H₁ D g₁ b k ↔ EntersIn U K H₂ D g₂ b k) := by
  have hg : ∀ k, k < n → g₁ k = g₂ k :=
    fun k hk => (h₁ k hk).agree hrow hdeep hI hH₁ hH₂ (h₂ k hk)
  have hg' : ∀ k, k < n → g₂ k = g₁ k := fun k hk => (hg k hk).symm
  have hout : ∀ k L, k < n → g₁ k = some L → OutIn U K H₁ D L = OutIn U K H₂ D L :=
    fun k L hk hL => (outIn_eq hH₁ (hf₁ k L hk hL)).trans
      (outIn_eq hH₂ (hf₂ k L hk (by rw [← hg k hk]; exact hL))).symm
  have hout' : ∀ k L, k < n → g₂ k = some L → OutIn U K H₂ D L = OutIn U K H₁ D L :=
    fun k L hk hL => (hout k L hk (by rw [hg k hk]; exact hL)).symm
  exact ⟨Set.Subset.antisymm (ledgerIn_subset_of hg hout) (ledgerIn_subset_of hg' hout'),
    fun b k hk => ⟨entersIn_of hg hout hk, entersIn_of hg' hout' hk⟩⟩

/-- **No retraction**: what a node outputs after slots `0, …, n-1`, it, or any
other node, outputs at the same slot after `n'` slots, for `n ≤ n'`. -/
theorem ledgerIn_grows (hrow : Row Validator p) (hdeep : Deep Validator K)
    (hI : Disciplined K p.certThreshold S U) {H₁ H₂ : Finset BlockId} (hH₁ : H₁ ⊆ U.ids)
    (hH₂ : H₂ ⊆ U.ids) {g₁ g₂ : ℕ → Option BlockId} {n n' : ℕ}
    (hn : n ≤ n') (h₁ : ∀ k, k < n → NodeDecided p U K H₁ k (g₁ k))
    (h₂ : ∀ k, k < n' → NodeDecided p U K H₂ k (g₂ k))
    (hf₁ : ∀ k L, k < n → g₁ k = some L → FetchedIn U K H₁ L ((U.block L).round - D))
    (hf₂ : ∀ k L, k < n' → g₂ k = some L → FetchedIn U K H₂ L ((U.block L).round - D)) :
    LedgerIn U K H₁ D g₁ n ⊆ LedgerIn U K H₂ D g₂ n' ∧
      ∀ b k, k < n → EntersIn U K H₁ D g₁ b k → EntersIn U K H₂ D g₂ b k := by
  obtain ⟨hl, he⟩ := ledgerIn_agree hrow hdeep hI hH₁ hH₂ h₁ (fun k hk => h₂ k (by omega)) hf₁
    (fun k L hk => hf₂ k L (by omega))
  exact ⟨hl ▸ ledgerIn_mono hn, fun b k hk h => (he b k hk).mp h⟩

section Slot

variable [LinearOrder Validator]

omit [ClaimFormat BlockId Payload] S in
/-- The order within a slot is total: two distinct blocks are ordered. -/
theorem keyLt_total {b b' : BlockId} (h : b ≠ b') : KeyLt U b b' ∨ KeyLt U b' b := by
  rcases lt_trichotomy (slotKey U b) (slotKey U b') with h1 | h1 | h1
  · exact Or.inl h1
  · exfalso
    apply h
    have := congrArg (fun p => (ofLex (ofLex p).2).2) h1
    simpa [slotKey] using this
  · exact Or.inr h1

omit [ClaimFormat BlockId Payload] S in
/-- **Within a slot, a reference comes first.** -/
theorem keyLt_of_ref {b b' : BlockId} (hb : b ∈ U.ids) (h : b' ∈ (U.block b).refs) :
    KeyLt U b' b := by
  have := (U.valid b hb).below b' h
  exact Prod.Lex.toLex_lt_toLex.mpr (Or.inl this)

omit [ClaimFormat BlockId Payload] S in
/-- **The ledger order is irreflexive.** -/
theorem precedesIn_irrefl {g : ℕ → Option BlockId} {n : ℕ} (b : BlockId) :
    ¬ PrecedesIn U K H D g n b b := by
  rintro ⟨k, k', -, -, h, h', hlt⟩
  have := entersIn_unique h h'
  rcases hlt with hlt | ⟨-, hlt⟩
  · omega
  · exact lt_irrefl _ hlt

omit [ClaimFormat BlockId Payload] S in
/-- **The ledger order is transitive.** -/
theorem precedesIn_trans {g : ℕ → Option BlockId} {n : ℕ} {b b' b'' : BlockId}
    (h₁ : PrecedesIn U K H D g n b b') (h₂ : PrecedesIn U K H D g n b' b'') :
    PrecedesIn U K H D g n b b'' := by
  obtain ⟨k₁, k₂, hk₁, -, he₁, he₂, hlt₁⟩ := h₁
  obtain ⟨k₂', k₃, -, hk₃, he₂', he₃, hlt₂⟩ := h₂
  have := entersIn_unique he₂ he₂'
  refine ⟨k₁, k₃, hk₁, hk₃, he₁, he₃, ?_⟩
  rcases hlt₁ with h | ⟨h, hkey⟩ <;> rcases hlt₂ with h' | ⟨h', hkey'⟩
  all_goals first | exact Or.inl (by omega) | exact Or.inr ⟨by omega, lt_trans hkey hkey'⟩

omit [ClaimFormat BlockId Payload] S in
/-- **The ledger order is total** on the ledger. -/
theorem precedesIn_total {g : ℕ → Option BlockId} {n : ℕ} {b b' : BlockId}
    (hb : b ∈ LedgerIn U K H D g n) (hb' : b' ∈ LedgerIn U K H D g n) (hne : b ≠ b') :
    PrecedesIn U K H D g n b b' ∨ PrecedesIn U K H D g n b' b := by
  obtain ⟨k, hk, he⟩ := exists_entersIn hb
  obtain ⟨k', hk', he'⟩ := exists_entersIn hb'
  rcases lt_trichotomy k k' with h | h | h
  · exact Or.inl ⟨k, k', hk, hk', he, he', Or.inl h⟩
  · rcases keyLt_total (U := U) hne with hkey | hkey
    · exact Or.inl ⟨k, k', hk, hk', he, he', Or.inr ⟨h, hkey⟩⟩
    · exact Or.inr ⟨k', k, hk', hk, he', he, Or.inr ⟨h.symm, hkey⟩⟩
  · exact Or.inr ⟨k', k, hk', hk, he', he, Or.inl h⟩

omit [ClaimFormat BlockId Payload] S in
/-- **Within a slot, the ledger order is causal**: a reference of a block that
enters at the same slot precedes it. -/
theorem precedesIn_of_ref {g : ℕ → Option BlockId} {n k : ℕ} {b b' : BlockId}
    (hb : b ∈ U.ids) (h : b' ∈ (U.block b).refs) (hk : k < n) (he : EntersIn U K H D g b k)
    (he' : EntersIn U K H D g b' k) : PrecedesIn U K H D g n b' b :=
  ⟨k, k, hk, hk, he', he, Or.inr ⟨rfl, keyLt_of_ref hb h⟩⟩

/-- **The ledger order is kept**: as a node settles more slots, and across
nodes. -/
theorem precedesIn_grows (hrow : Row Validator p) (hdeep : Deep Validator K)
    (hI : Disciplined K p.certThreshold S U) {H₁ H₂ : Finset BlockId} (hH₁ : H₁ ⊆ U.ids)
    (hH₂ : H₂ ⊆ U.ids) {g₁ g₂ : ℕ → Option BlockId} {n n' : ℕ}
    (hn : n ≤ n') (h₁ : ∀ k, k < n → NodeDecided p U K H₁ k (g₁ k))
    (h₂ : ∀ k, k < n' → NodeDecided p U K H₂ k (g₂ k))
    (hf₁ : ∀ k L, k < n → g₁ k = some L → FetchedIn U K H₁ L ((U.block L).round - D))
    (hf₂ : ∀ k L, k < n' → g₂ k = some L → FetchedIn U K H₂ L ((U.block L).round - D))
    {b b' : BlockId} (h : PrecedesIn U K H₁ D g₁ n b b') : PrecedesIn U K H₂ D g₂ n' b b' := by
  obtain ⟨k, k', hk, hk', he, he', hlt⟩ := h
  have hgrow := (ledgerIn_grows hrow hdeep hI hH₁ hH₂ hn h₁ h₂ hf₁ hf₂).2
  exact ⟨k, k', by omega, by omega, hgrow b k hk he, hgrow b' k' hk' he', hlt⟩

end Slot

/-- **A block's fate is settled** once every slot at most `D` rounds above it is
decided: if it is not in the ledger then, it never enters. -/
theorem mem_ledgerIn_settled {g : ℕ → Option BlockId} {n n' : ℕ}
    (hdec : ∀ k, k < n' → NodeDecided p U K H k (g k)) {b : BlockId}
    (hn : ∀ k, S.slotRound k ≤ (U.block b).round + D → k < n)
    (hb : b ∈ LedgerIn U K H D g n') : b ∈ LedgerIn U K H D g n := by
  obtain ⟨k, hk, L, hL, hbL⟩ := hb
  have hLk := (hL ▸ hdec k hk : NodeDecided p U K H k (some L)).isLeaderBlock
  exact ⟨k, hn k (by have := hbL.2; rw [hLk.2.1] at this; omega), L, hL, hbL⟩

/-- **Settled out everywhere**: a block missing from a node's ledger once the
node has decided every slot at most `D` rounds above it is in no node's
ledger, once each has fetched below the leaders it committed. -/
theorem notMem_ledgerIn_of_settled (hrow : Row Validator p) (hdeep : Deep Validator K)
    (hI : Disciplined K p.certThreshold S U) {H₁ H₂ : Finset BlockId} (hH₁ : H₁ ⊆ U.ids)
    (hH₂ : H₂ ⊆ U.ids) {g₁ g₂ : ℕ → Option BlockId} {n n' : ℕ}
    (h₁ : ∀ k, k < n → NodeDecided p U K H₁ k (g₁ k))
    (h₂ : ∀ k, k < n' → NodeDecided p U K H₂ k (g₂ k))
    (hf₁ : ∀ k L, k < n → g₁ k = some L → FetchedIn U K H₁ L ((U.block L).round - D))
    (hf₂ : ∀ k L, k < n' → g₂ k = some L → FetchedIn U K H₂ L ((U.block L).round - D))
    {b : BlockId} (hn : ∀ k, S.slotRound k ≤ (U.block b).round + D → k < n)
    (hb : b ∉ LedgerIn U K H₁ D g₁ n) : b ∉ LedgerIn U K H₂ D g₂ n' := by
  intro hb₂
  have hm : b ∈ LedgerIn U K H₂ D g₂ (min n n') := by
    rcases le_total n n' with h | h
    · rw [min_eq_left h]; exact mem_ledgerIn_settled h₂ hn hb₂
    · rw [min_eq_right h]; exact hb₂
  have hle := min_le_right n n'
  exact hb ((ledgerIn_grows hrow hdeep hI hH₂ hH₁ (min_le_left n n')
    (fun k hk => h₂ k (by omega)) h₁ (fun k L hk => hf₂ k L (by omega)) hf₁).1 hm)

omit [ClaimFormat BlockId Payload] in
/-- **A leader of `T` covering `T` outputs every block of `T` at most `D ≤ K`
rounds below it**: it references its author's block one round below, and that
author's chain leads down to the block. -/
theorem mem_out_of_covers (hT : T ⊆ (Correct : Finset Validator)) (hch : Chains U)
    (hDK : D ≤ K) {k : ℕ} {L : BlockId} (hL : IsLeaderBlock U k L) (hlead : S.leader k ∈ T)
    (hcov : CoversFrom U T R (S.slotRound k))
    (hpop : ∀ r, R ≤ r → r < S.slotRound k → PopulatedOn U T r) {x : BlockId}
    (hx : x ∈ U.ids) (hxc : (U.block x).creator ∈ T) (hRx : R ≤ (U.block x).round)
    (hxL : (U.block x).round < S.slotRound k)
    (hD : S.slotRound k ≤ (U.block x).round + D) : x ∈ Out U K D L := by
  rw [Out, Set.mem_setOf_eq, hL.2.1]
  refine ⟨?_, hD⟩
  obtain ⟨y, hy, hyc, hyr⟩ := hpop (S.slotRound k - 1) (by omega) (by omega) _ hxc
  have hyL : y ∈ (U.block L).refs :=
    hcov k (by omega) le_rfl hlead L hL y hy (hyc ▸ hxc) (by omega)
  have hxy : x ∈ window U ((U.block y).round - (U.block x).round) y :=
    mem_window_of_chain hch _ hy hx (hyc ▸ hT hxc) hyc.symm (by omega) le_rfl
  have hxL' := window_trans (ref_mem_window (k := 0) hyL (by rw [hL.2.1]; omega)) hxy
  exact ⟨L, K, Anchored.anchor, window_mono (by omega) _ hxL'⟩

/-- **After synchrony with leaders of `T` covering `T`, a block of `T` enters
the ledger** of a node that has decided every slot at most `D ≤ K` rounds
above it, when every `D` rounds hold a slot led by `T`: the node holds the
blocks of `T` that certify such a slot, commits it directly, and its leader
outputs the block. -/
theorem mem_ledgerIn_of_gap (hrow : Row Validator p) (hdeep : Deep Validator K)
    (hI : Disciplined K p.certThreshold S U) (hlive : LiveRow Validator p)
    (hT : T ⊆ (Correct : Finset Validator)) (hDK : D ≤ K) (hH : H ⊆ U.ids)
    (hgap : ∀ r, ∃ k, r < S.slotRound k ∧ S.slotRound k ≤ r + D ∧ S.leader k ∈ T)
    {g : ℕ → Option BlockId} {n : ℕ} (hdec : ∀ k, k < n → NodeDecided p U K H k (g k))
    (hf : ∀ k L, k < n → g k = some L → FetchedIn U K H L ((U.block L).round - D))
    {x : BlockId} (hx : x ∈ U.ids) (hxc : (U.block x).creator ∈ T)
    (hRx : R ≤ (U.block x).round) (hn : ∀ k, S.slotRound k ≤ (U.block x).round + D → k < n)
    (hsync : SyncFrom U T R ((U.block x).round + D + 2))
    (hcov : CoversFrom U T R ((U.block x).round + D))
    (hW : HeldBy U T ((U.block x).round + 2) ((U.block x).round + D + 2) ⊆ ↑H) :
    x ∈ LedgerIn U K H D g n := by
  obtain ⟨k, hxk, hkD, hlead⟩ := hgap (U.block x).round
  have hkn := hn k hkD
  have hcb := certRound_bounds (p := p) (S.slotRound k)
  obtain ⟨L, hL, hdecL⟩ := nodeDecided_of_responds (K := K) hlive hsync.1
    ((respondsFrom_of_syncFrom (p := p) hsync).2 k (by omega) (by omega) hlead)
    (fun z hz => hW ⟨hz.1, hz.2.1, by have := hz.2.2.1; omega, by have := hz.2.2.2; omega⟩)
  have hg : g k = some L := (hdec k hkn).agree hrow hdeep hI hH hH hdecL
  refine ⟨k, hkn, L, hg, ?_⟩
  rw [outIn_eq hH (hf k L hkn hg)]
  exact mem_out_of_covers hT hI.2.1 hDK hL hlead
    (fun j h1 h2 h3 L' hL' y hy hyc hyr => hcov j h1 (by omega) h3 L' hL' y hy hyc hyr)
    (fun r h1 h2 => hsync.2.1 r h1 (by omega)) hx hxc hRx hxk hkD

end KPartialSparse

end LeanDag
