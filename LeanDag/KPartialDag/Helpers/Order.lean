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
deciding a slot led by `T` outputs them (`mem_ledgerIn_of_leader_mem`); when
every `D` rounds hold a slot led by `T`, every block of `T` enters
(`mem_ledgerIn_of_gap`).

A block enters a ledger at one slot (`entersIn_unique`), and two nodes, or
one node at two times, agree on the slots settled by both
(`ledgerIn_grows`). A block output by a leader lies at most `D` rounds below
it, so its fate is settled once the slots up to `D` rounds above it are
decided (`mem_ledgerIn_settled`). Ordered within a slot by round, author and
id, the ledger is a strict total order (`precedesIn_irrefl`,
`precedesIn_trans`, `precedesIn_total`), causal within a slot
(`precedesIn_of_ref`) and kept as slots settle (`precedesIn_grows`).
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

/-- The ledger grows with the slots settled. -/
theorem ledgerIn_mono {g : ℕ → Option BlockId} {n n' : ℕ} (h : n ≤ n') :
    LedgerIn U K H D g n ⊆ LedgerIn U K H D g n' := by
  rintro b ⟨k, hk, hrest⟩
  exact ⟨k, by omega, hrest⟩

/-- **A block enters a ledger at one slot.** -/
theorem entersIn_unique {g : ℕ → Option BlockId} {b : BlockId} {k₁ k₂ : ℕ}
    (h₁ : EntersIn U K H D g b k₁) (h₂ : EntersIn U K H D g b k₂) : k₁ = k₂ := by
  rcases lt_trichotomy k₁ k₂ with h | h | h
  · obtain ⟨L, hL, hb⟩ := h₁.1
    exact absurd hb (h₂.2 k₁ h L hL)
  · exact h
  · obtain ⟨L, hL, hb⟩ := h₂.1
    exact absurd hb (h₁.2 k₂ h L hL)

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

/-- **No retraction**: what a node outputs after slots `0, …, n-1`, it, or any
other node, outputs at the same slot after `n'` slots, for `n ≤ n'`, at
`K ≥ 3`, once each has fetched below the leaders it committed. -/
theorem ledgerIn_grows (hK : 3 ≤ K) {H₁ H₂ : Finset BlockId} (hH₁ : H₁ ⊆ U.ids)
    (hH₂ : H₂ ⊆ U.ids) [S : Slots Validator] {g₁ g₂ : ℕ → Option BlockId} {n n' : ℕ}
    (hn : n ≤ n') (h₁ : ∀ k, k < n → NodeDecided U K H₁ k (g₁ k))
    (h₂ : ∀ k, k < n' → NodeDecided U K H₂ k (g₂ k))
    (hf₁ : ∀ k L, k < n → g₁ k = some L → FetchedIn U K H₁ L ((U.block L).round - D))
    (hf₂ : ∀ k L, k < n' → g₂ k = some L → FetchedIn U K H₂ L ((U.block L).round - D)) :
    LedgerIn U K H₁ D g₁ n ⊆ LedgerIn U K H₂ D g₂ n' ∧
      ∀ b k, k < n → EntersIn U K H₁ D g₁ b k → EntersIn U K H₂ D g₂ b k := by
  obtain ⟨hl, he⟩ := ledgerIn_agree hK hH₁ hH₂ h₁ (fun k hk => h₂ k (by omega)) hf₁
    (fun k L hk => hf₂ k L (by omega))
  exact ⟨hl ▸ ledgerIn_mono hn, fun b k hk h => (he b k hk).mp h⟩

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

section Slot

variable [LinearOrder Validator] [LinearOrder BlockId]

omit [DecidableEq BlockId] in
/-- The order within a slot is total: two distinct blocks are ordered. -/
theorem keyLt_total {b b' : BlockId} (h : b ≠ b') : KeyLt U b b' ∨ KeyLt U b' b := by
  rcases lt_trichotomy (slotKey U b) (slotKey U b') with h1 | h1 | h1
  · exact Or.inl h1
  · exfalso
    apply h
    have := congrArg (fun p => (ofLex (ofLex p).2).2) h1
    simpa [slotKey] using this
  · exact Or.inr h1

omit [DecidableEq BlockId] in
/-- **Within a slot, a reference comes first.** -/
theorem keyLt_of_ref {b b' : BlockId} (hb : b ∈ U.ids) (h : b' ∈ (U.block b).refs) :
    KeyLt U b' b := by
  have := (U.valid b hb).predecessor b' h
  exact Prod.Lex.toLex_lt_toLex.mpr (Or.inl (by omega))

/-- **The ledger order is irreflexive.** -/
theorem precedesIn_irrefl {g : ℕ → Option BlockId} {n : ℕ} (b : BlockId) :
    ¬ PrecedesIn U K H D g n b b := by
  rintro ⟨k, k', -, -, h, h', hlt⟩
  have := entersIn_unique h h'
  rcases hlt with hlt | ⟨-, hlt⟩
  · omega
  · exact lt_irrefl _ hlt

/-- **The ledger order is transitive.** -/
theorem precedesIn_trans {g : ℕ → Option BlockId} {n : ℕ} {b b' b'' : BlockId}
    (h₁ : PrecedesIn U K H D g n b b') (h₂ : PrecedesIn U K H D g n b' b'') :
    PrecedesIn U K H D g n b b'' := by
  obtain ⟨k₁, k₂, hk₁, -, he₁, he₂, hlt₁⟩ := h₁
  obtain ⟨k₂', k₃, -, hk₃, he₂', he₃, hlt₂⟩ := h₂
  have := entersIn_unique he₂ he₂'
  refine ⟨k₁, k₃, hk₁, hk₃, he₁, he₃, ?_⟩
  rcases hlt₁ with h | ⟨h, hkey⟩ <;> rcases hlt₂ with h' | ⟨h', hkey'⟩
  · exact Or.inl (by omega)
  · exact Or.inl (by omega)
  · exact Or.inl (by omega)
  · exact Or.inr ⟨by omega, lt_trans hkey hkey'⟩

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

/-- **Within a slot, the ledger order is causal**: a reference of a block
that enters at the same slot precedes it. -/
theorem precedesIn_of_ref {g : ℕ → Option BlockId} {n k : ℕ} {b b' : BlockId}
    (hb : b ∈ U.ids) (h : b' ∈ (U.block b).refs) (hk : k < n) (he : EntersIn U K H D g b k)
    (he' : EntersIn U K H D g b' k) : PrecedesIn U K H D g n b' b :=
  ⟨k, k, hk, hk, he', he, Or.inr ⟨rfl, keyLt_of_ref hb h⟩⟩

/-- **The ledger order is kept**: as a node settles more slots, and across
nodes, at `K ≥ 3`, once each has fetched below the leaders it committed. -/
theorem precedesIn_grows (hK : 3 ≤ K) {H₁ H₂ : Finset BlockId} (hH₁ : H₁ ⊆ U.ids)
    (hH₂ : H₂ ⊆ U.ids) [S : Slots Validator] {g₁ g₂ : ℕ → Option BlockId} {n n' : ℕ}
    (hn : n ≤ n') (h₁ : ∀ k, k < n → NodeDecided U K H₁ k (g₁ k))
    (h₂ : ∀ k, k < n' → NodeDecided U K H₂ k (g₂ k))
    (hf₁ : ∀ k L, k < n → g₁ k = some L → FetchedIn U K H₁ L ((U.block L).round - D))
    (hf₂ : ∀ k L, k < n' → g₂ k = some L → FetchedIn U K H₂ L ((U.block L).round - D))
    {b b' : BlockId} (h : PrecedesIn U K H₁ D g₁ n b b') : PrecedesIn U K H₂ D g₂ n' b b' := by
  obtain ⟨k, k', hk, hk', he, he', hlt⟩ := h
  have hgrow := (ledgerIn_grows hK hH₁ hH₂ hn h₁ h₂ hf₁ hf₂).2
  exact ⟨k, k', by omega, by omega, hgrow b k hk he, hgrow b' k' hk' he', hlt⟩

end Slot

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
  obtain ⟨L, hL, hdec⟩ := nodeDecided_of_responds (K := K) hcard
    (responds_of_synchronisedOn hcard hs (by omega) hlead fun r h1 h2 => hpop r (by omega) h2) hW
  have hg : g k = some L := hk.agree hK hH hH hdec
  have hLc : (U.block L).creator ∈ T := by rw [hL.2.2]; exact hlead
  have hLr := hL.2.1
  refine ⟨k, by omega, L, hg, ?_⟩
  rw [outIn_eq hH (hf L hg)]
  exact mem_out_of_synchronisedOn (by omega) hcard hs (fun r h1 h2 => hpop r h1 (by omega))
    hL.1 hLc hx hxc hRx (by omega) (by omega)

/-- **A block's fate is settled** once every slot at most `D` rounds above it
is decided: if it is not in the ledger then, it never enters. -/
theorem mem_ledgerIn_settled (hH : H ⊆ U.ids) {g : ℕ → Option BlockId} {n n' : ℕ}
    (hdec : ∀ k, k < n' → NodeDecided U K H k (g k)) {b : BlockId}
    (hn : ∀ k, S.slotRound k ≤ (U.block b).round + D → k < n)
    (hb : b ∈ LedgerIn U K H D g n') : b ∈ LedgerIn U K H D g n := by
  obtain ⟨k, hk, L, hL, hbL⟩ := hb
  have hLk := ((hL ▸ hdec k hk : NodeDecided U K H k (some L)).certified hH).1
  exact ⟨k, hn k (by have := hbL.2; rw [hLk.2.1] at this; omega), L, hL, hbL⟩

/-- **After synchrony, a block of `T` enters the ledger** of a node that has
decided every slot at most `D` rounds above it, when every `D` rounds hold a
slot led by `T`. -/
theorem mem_ledgerIn_of_gap (hK : 3 ≤ K) (hcard : quorumCard Validator ≤ T.card)
    (hs : SynchronisedOn U T R) (hH : H ⊆ U.ids)
    (hgap : ∀ r, ∃ k, r < S.slotRound k ∧ S.slotRound k ≤ r + D ∧ S.leader k ∈ T)
    {g : ℕ → Option BlockId} {n : ℕ} (hdec : ∀ k, k < n → NodeDecided U K H k (g k))
    (hf : ∀ k L, k < n → g k = some L → FetchedIn U K H L ((U.block L).round - D))
    {x : BlockId} (hx : x ∈ U.ids) (hxc : (U.block x).creator ∈ T)
    (hRx : R ≤ (U.block x).round) (hn : ∀ k, S.slotRound k ≤ (U.block x).round + D → k < n)
    (hpop : ∀ r, R ≤ r → r ≤ (U.block x).round + D + 2 → PopulatedOn U T r)
    (hW : WithRefs U T ((U.block x).round + 3) ((U.block x).round + D + 2) ⊆ ↑H) :
    x ∈ LedgerIn U K H D g n := by
  obtain ⟨k, hxk, hkD, hlead⟩ := hgap (U.block x).round
  have hkn := hn k hkD
  exact ledgerIn_mono (by omega) (mem_ledgerIn_of_leader_mem hK hcard hs hH hlead
    (fun r h1 h2 => hpop r h1 (by omega))
    (fun z hz => hW (withRefs_mono (by omega) (by omega) hz)) (hdec k hkn)
    (fun L hL => hf k L hkn hL) hx hxc hRx hxk hkD)


end KPartialDag

end LeanDag
