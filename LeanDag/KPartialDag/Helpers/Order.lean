import LeanDag.KPartialDag.Model.Order
import LeanDag.KPartialDag.Helpers.Live
/-!
# The order — helpers

`docs/kpartial.md` §7. What a node reads of a leader's output lies in the
leader's output, and is all of it once the sub-DAG is fetched down to `D`
rounds below the leader (`outIn_eq`). So two nodes that agree on their
verdicts, and have fetched below the leaders they committed, have one ledger
and one entry slot per block (`ledgerIn_agree`). After synchrony, the blocks
of `T` at least two rounds below a leader of `T` are anchored, round by round
downward (`anchoredBelow_of_synchronisedOn`), and the round just below lies
in the leader's history to depth `K`; so the leader outputs every block of
`T` at most `D` rounds below it (`mem_out_of_synchronisedOn`), and a node
deciding a slot led by `T` outputs them (`mem_ledgerIn_of_leader_mem`).
-/

namespace LeanDag

namespace KPartialDag

variable {Validator : Type*} [Fintype Validator] [DecidableEq Validator] [F : Faults Validator]
variable {BlockId : Type*} [DecidableEq BlockId] {Payload : Type*}
variable {U : KRecord Validator BlockId Payload} {K D : ℕ} {H : Finset BlockId}
variable {T : Finset Validator} {R : ℕ}

/-- What a node reads of a leader's output lies in the output. -/
theorem outIn_subset {L : BlockId} : OutIn U K H D L ⊆ Out U K D L :=
  fun _ hb => ⟨availIn_subset hb.1, hb.2⟩

/-- **Fetched down to `D` rounds below the leader, a node reads all its
output.** -/
theorem outIn_eq (hH : H ⊆ U.ids) {L : BlockId}
    (hf : FetchedIn U K H L ((U.block L).round - D)) : OutIn U K H D L = Out U K D L :=
  Set.Subset.antisymm outIn_subset fun _ hb =>
    ⟨avail_subset_availIn hH hf hb.1 (by have := hb.2; omega), hb.2⟩

/-- Verdicts that agree, with outputs that agree, give one ledger. -/
theorem ledgerIn_subset_of {H₁ H₂ : Finset BlockId} {g₁ g₂ : ℕ → Option BlockId} {n : ℕ}
    (hg : ∀ k, k < n → g₁ k = g₂ k)
    (hout : ∀ k L, k < n → g₁ k = some L → OutIn U K H₁ D L = OutIn U K H₂ D L) :
    LedgerIn U K H₁ D g₁ n ⊆ LedgerIn U K H₂ D g₂ n := by
  rintro b ⟨k, hk, L, hL, hb⟩
  exact ⟨k, hk, L, by rw [← hg k hk]; exact hL, by rw [← hout k L hk hL]; exact hb⟩

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

/-- **Two nodes have one ledger, and one entry slot per block**, at `K ≥ 3`,
once each has fetched down to `D` rounds below the leaders it committed. -/
theorem ledgerIn_agree (hK : 3 ≤ K) {H₁ H₂ : Finset BlockId} (hH₁ : H₁ ⊆ U.ids)
    (hH₂ : H₂ ⊆ U.ids) [S : Slots Validator] {g₁ g₂ : ℕ → Option BlockId} {n : ℕ}
    (h₁ : ∀ k, k < n → NodeDecided U K H₁ k (g₁ k))
    (h₂ : ∀ k, k < n → NodeDecided U K H₂ k (g₂ k))
    (hf₁ : ∀ k L, k < n → g₁ k = some L → FetchedIn U K H₁ L ((U.block L).round - D))
    (hf₂ : ∀ k L, k < n → g₂ k = some L → FetchedIn U K H₂ L ((U.block L).round - D)) :
    LedgerIn U K H₁ D g₁ n = LedgerIn U K H₂ D g₂ n ∧
      ∀ b k, k < n → (EntersIn U K H₁ D g₁ b k ↔ EntersIn U K H₂ D g₂ b k) := by
  have hg : ∀ k, k < n → g₁ k = g₂ k := fun k hk => (h₁ k hk).agree hK hH₁ hH₂ (h₂ k hk)
  have hg' : ∀ k, k < n → g₂ k = g₁ k := fun k hk => (hg k hk).symm
  have hout : ∀ k L, k < n → g₁ k = some L → OutIn U K H₁ D L = OutIn U K H₂ D L :=
    fun k L hk hL => (outIn_eq hH₁ (hf₁ k L hk hL)).trans
      (outIn_eq hH₂ (hf₂ k L hk (by rw [← hg k hk]; exact hL))).symm
  have hout' : ∀ k L, k < n → g₂ k = some L → OutIn U K H₂ D L = OutIn U K H₁ D L :=
    fun k L hk hL => (hout k L hk (by rw [hg k hk]; exact hL)).symm
  exact ⟨Set.Subset.antisymm (ledgerIn_subset_of hg hout) (ledgerIn_subset_of hg' hout'),
    fun b k hk => ⟨entersIn_of hg hout hk, entersIn_of hg' hout' hk⟩⟩

/-- **After synchrony, a block of `T` is anchored** when the blocks of `T` of
the round above, which reference it, lie in the windows of anchored
blocks. -/
theorem anchoredBelow_of_synchronisedOn (hcard : quorumCard Validator ≤ T.card)
    (hs : SynchronisedOn U T R) {A : BlockId} {m : ℕ} (hRm : R ≤ m)
    (hpop : PopulatedOn U T (m + 1)) {x : BlockId} (hx : x ∈ U.ids)
    (hxr : (U.block x).round = m) (hxc : (U.block x).creator ∈ T) (y : BlockId → BlockId)
    (hy : ∀ z ∈ U.ids, (U.block z).round = m + 1 → (U.block z).creator ∈ T →
      AnchoredBelow U K A (y z) ∧ z ∈ historyUpto U K (y z)) :
    AnchoredBelow U K A x := by
  classical
  let S := (blocksAt U (m + 1)).filter fun z => (U.block z).creator ∈ T
  have hS : ∀ z ∈ S, z ∈ U.ids ∧ (U.block z).round = m + 1 ∧ (U.block z).creator ∈ T :=
    fun z hz => by
      obtain ⟨hzb, hzc⟩ := Finset.mem_filter.mp hz
      obtain ⟨hzi, hzr⟩ := mem_blocksAt.mp hzb
      exact ⟨hzi, hzr, hzc⟩
  refine AnchoredBelow.referenced S y (fun z hz => (hy z (hS z hz).1 (hS z hz).2.1 (hS z hz).2.2).1)
    (fun z hz => (hy z (hS z hz).1 (hS z hz).2.1 (hS z hz).2.2).2)
    (fun z hz => hs m hRm z (hS z hz).1 (hS z hz).2.1 (hS z hz).2.2 x hx hxr hxc) ?_
  have hT : T ⊆ creatorsOf U.block S := fun v hv => by
    obtain ⟨z, hz, hzc, hzr⟩ := hpop v hv
    exact mem_creatorsOf.mpr
      ⟨z, Finset.mem_filter.mpr ⟨mem_blocksAt.mpr ⟨hz, hzr⟩, by rw [hzc]; exact hv⟩, hzc⟩
  have := Finset.card_le_card hT
  have := F.card_validators
  omega

/-- **After synchrony, a leader of `T` outputs every block of `T` at most `D`
rounds below it**, from round `R` on, at `K ≥ 1`. -/
theorem mem_out_of_synchronisedOn (hK : 1 ≤ K) (hcard : quorumCard Validator ≤ T.card)
    (hs : SynchronisedOn U T R) {L : BlockId}
    (hpop : ∀ r, R ≤ r → r < (U.block L).round → PopulatedOn U T r) (hL : L ∈ U.ids)
    (hLc : (U.block L).creator ∈ T) {x : BlockId} (hx : x ∈ U.ids)
    (hxc : (U.block x).creator ∈ T) (hRx : R ≤ (U.block x).round)
    (hxL : (U.block x).round < (U.block L).round)
    (hD : (U.block L).round ≤ (U.block x).round + D) : x ∈ Out U K D L := by
  refine ⟨?_, hD⟩
  -- the blocks of `T` at least two rounds below `L`, from `R` on, are anchored
  have key : ∀ d x, x ∈ U.ids → (U.block x).creator ∈ T → R ≤ (U.block x).round →
      (U.block x).round + 2 + d = (U.block L).round → AnchoredBelow U K L x := by
    intro d
    induction d with
    | zero =>
      intro x hx hxc hRx hxr
      exact anchoredBelow_of_synchronisedOn hcard hs hRx (hpop _ (by omega) (by omega)) hx rfl
        hxc (fun _ => L) fun z hz hzr hzc => ⟨AnchoredBelow.anchor,
          ref_mem_historyUpto hK (hs _ (by omega) L hL (by omega) hLc z hz hzr hzc)⟩
    | succ d ih =>
      intro x hx hxc hRx hxr
      exact anchoredBelow_of_synchronisedOn hcard hs hRx (hpop _ (by omega) (by omega)) hx rfl
        hxc id fun z hz hzr hzc => ⟨ih z hz hzc (by omega) (by omega), mem_historyUpto_self⟩
  by_cases h : (U.block x).round + 1 = (U.block L).round
  · exact ⟨L, AnchoredBelow.anchor,
      ref_mem_historyUpto hK (hs _ hRx L hL h.symm hLc x hx rfl hxc)⟩
  · exact ⟨x, key ((U.block L).round - (U.block x).round - 2) x hx hxc hRx (by omega),
      mem_historyUpto_self⟩

variable [S : Slots Validator]

/-- **After synchrony, a node deciding a slot led by `T` outputs every block of
`T` at most `D` rounds below the slot**, from round `R` on, at `K ≥ 3`, once
it holds the blocks of `T` two rounds above the slot with their references
and has fetched below the slot's leader. -/
theorem mem_ledgerIn_of_leader_mem (hK : 3 ≤ K) (hcard : quorumCard Validator ≤ T.card)
    (hs : SynchronisedOn U T R) (hH : H ⊆ U.ids) {g : ℕ → Option BlockId} {k : ℕ}
    (hlead : S.leader k ∈ T) (hpop : ∀ r, R ≤ r → r ≤ S.slotRound k + 2 → PopulatedOn U T r)
    (hW : WithRefs U T (S.slotRound k + 2) (S.slotRound k + 2) ⊆ ↑H)
    (hk : NodeDecided U K H k (g k))
    (hf : ∀ L, g k = some L → FetchedIn U K H L ((U.block L).round - D))
    {x : BlockId} (hx : x ∈ U.ids) (hxc : (U.block x).creator ∈ T)
    (hRx : R ≤ (U.block x).round) (hxk : (U.block x).round < S.slotRound k)
    (hD : S.slotRound k ≤ (U.block x).round + D) : x ∈ LedgerIn U K H D g (k + 1) := by
  obtain ⟨L, hL, hdec⟩ := nodeDecided_of_leader_mem (K := K) hcard hs (by omega) hlead
    (fun r h1 h2 => hpop r (by omega) h2) hW
  have hg : g k = some L := hk.agree hK hH hH hdec
  have hLc : (U.block L).creator ∈ T := by rw [hL.2.2]; exact hlead
  have hLr := hL.2.1
  refine ⟨k, by omega, L, hg, ?_⟩
  rw [outIn_eq hH (hf L hg)]
  exact mem_out_of_synchronisedOn (by omega) hcard hs (fun r h1 h2 => hpop r h1 (by omega))
    hL.1 hLc hx hxc hRx (by omega) (by omega)

end KPartialDag

end LeanDag
