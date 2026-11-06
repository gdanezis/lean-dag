import LeanDag.KPartialDag.Model.Close
import LeanDag.KPartialDag.Helpers.Reactive
import LeanDag.KPartialDag.Helpers.Bounds
/-!
# Closing the channel — helpers

`docs/kpartial.md` §12. A node's decisions hold on more blocks
(`NodeDecided.mono`), and with them its last commit (`closesAfter_mono`); two
nodes reach one last commit with one ledger (`closesAfter_agree`); on
a reactive run where `T` declares the channel closed, every node of `T`
reaches the last commit (`exists_closesAfter`).
-/

namespace LeanDag

namespace KPartialDag

variable {Validator : Type*} [Fintype Validator] [DecidableEq Validator] [F : Faults Validator]
variable {BlockId : Type*} [DecidableEq BlockId] {Payload : Type*}
variable {U : KRecord Validator BlockId Payload} {K D : ℕ} {H H' : Finset BlockId} {A : BlockId}

/-- A link read on `H` holds on more. -/
theorem LinkedIn.mono (hH : H ⊆ H') {L : BlockId} {r : ℕ} (h : LinkedIn U K H A L r) :
    LinkedIn U K H' A L r := by
  obtain ⟨C, hC, hCr, hrefs, hv⟩ := h
  exact ⟨C, availIn_mono hH hC, hCr, fun j hj => availIn_mono hH (hrefs j hj), hv⟩

/-- **A sub-DAG fetched into `H` is fetched into more**, of the record: above
the round fetched to, the sub-DAG read on more is the record's, and so the
one read on `H`. -/
theorem FetchedIn.mono (hH : H ⊆ H') (hH' : H' ⊆ U.ids) {ρ : ℕ} (hf : FetchedIn U K H A ρ) :
    FetchedIn U K H' A ρ := by
  refine ⟨hf.1.trans hH, fun S x hS href hcard => (hf.2 S x (fun z hz => ?_) href hcard).trans hH⟩
  exact ⟨avail_subset_availIn (hH.trans hH') hf (availIn_subset (hS z hz).1) (hS z hz).2.le,
    (hS z hz).2⟩

/-- The blocks held with their references grow with what is held. -/
theorem heldWithRefs_mono (hH : H ⊆ H') (s : Finset BlockId) :
    heldWithRefs U H s ⊆ heldWithRefs U H' s := fun b hb => by
  obtain ⟨hbs, hbH, hr⟩ := Finset.mem_filter.mp hb
  exact Finset.mem_filter.mpr ⟨hbs, hH hbH, fun j hj => hH (hr j hj)⟩

variable [S : Slots Validator]

/-- **A node's decision holds on more blocks** of the record: the direct
tests and the links only gain, and an indirect skip reads a sub-DAG fetched
below the slot, which is the record's. -/
theorem NodeDecided.mono (hH : H ⊆ H') (hH' : H' ⊆ U.ids) {k : ℕ} {v : Option BlockId}
    (h : NodeDecided U K H k v) : NodeDecided U K H' k v := by
  induction h with
  | directCommit hL hc =>
    exact .directCommit hL (hc.trans (Finset.card_le_card
      (Finset.image_subset_image (heldWithRefs_mono hH _))))
  | directSkip hs =>
    exact .directSkip (hs.trans (Finset.card_le_card
      (Finset.image_subset_image (heldWithRefs_mono hH _))))
  | indirectCommit hkj helig _ _ hL hlink ihj ihm =>
    exact .indirectCommit hkj helig ihj ihm hL (hlink.mono hH)
  | indirectSkip hkj helig _ _ hf hnone ihj ihm =>
    exact .indirectSkip hkj helig ihj ihm (hf.mono hH hH') fun L hL hlink =>
      hnone L hL (avail_linkedIn (hH.trans hH') hf (linkedIn_avail hH' hlink))

/-- Decisions below `n` hold on more blocks. -/
theorem DecidesBelow.mono (hH : H ⊆ H') (hH' : H' ⊆ U.ids) {g : ℕ → Option BlockId} {n : ℕ}
    (h : DecidesBelow U K H D g n) : DecidesBelow U K H' D g n := fun i hi =>
  ⟨(h i hi).1.mono hH hH', fun L hL => ((h i hi).2 L hL).mono hH hH'⟩

/-- **Closure is read alike on more blocks**, up to the slots decided. -/
theorem closedIn_iff_of_mono (hH : H ⊆ H') (hH' : H' ⊆ U.ids) {closes : Payload → Prop}
    {g : ℕ → Option BlockId} {n m : ℕ} (h : DecidesBelow U K H D g n) (hm : m ≤ n) :
    ClosedIn U K H D closes g m ↔ ClosedIn U K H' D closes g m := by
  have hout : ∀ k L, k < m → g k = some L → OutIn U K H D L = OutIn U K H' D L :=
    fun k L hk hL => (outIn_eq (hH.trans hH') ((h k (by omega)).2 L hL)).trans
      (outIn_eq hH' (((h k (by omega)).2 L hL).mono hH hH')).symm
  have heq : LedgerIn U K H D g m = LedgerIn U K H' D g m :=
    Set.Subset.antisymm (ledgerIn_subset_of (fun _ _ => rfl) hout)
      (ledgerIn_subset_of (fun _ _ => rfl) fun k L hk hL => (hout k L hk hL).symm)
  unfold ClosedIn
  rw [heq]

/-- **The last commit holds on more blocks**: a node holding what a node that
reached the last commit holds reaches it alike. -/
theorem closesAfter_mono (hH : H ⊆ H') (hH' : H' ⊆ U.ids) {closes : Payload → Prop}
    {g : ℕ → Option BlockId} {n : ℕ} (h : DecidesBelow U K H D g n)
    (hc : ClosesAfter U K H D closes g n) : ClosesAfter U K H' D closes g n :=
  ⟨(closedIn_iff_of_mono hH hH' h le_rfl).mp hc.1, fun m hm hm' =>
    hc.2 m hm ((closedIn_iff_of_mono hH hH' h hm.le).mpr hm')⟩

/-- Two nodes read closure alike after slots they have both decided, at
`K ≥ 3`. -/
theorem closedIn_iff_of_agree (hK : 3 ≤ K) {H₁ H₂ : Finset BlockId} (hH₁ : H₁ ⊆ U.ids)
    (hH₂ : H₂ ⊆ U.ids) {closes : Payload → Prop} {g₁ g₂ : ℕ → Option BlockId} {n₁ n₂ m : ℕ}
    (h₁ : DecidesBelow U K H₁ D g₁ n₁) (h₂ : DecidesBelow U K H₂ D g₂ n₂) (hm₁ : m ≤ n₁)
    (hm₂ : m ≤ n₂) : ClosedIn U K H₁ D closes g₁ m ↔ ClosedIn U K H₂ D closes g₂ m := by
  have heq := (ledgerIn_agree (D := D) hK hH₁ hH₂ (n := m) (fun k hk => (h₁ k (by omega)).1)
    (fun k hk => (h₂ k (by omega)).1) (fun k L hk => (h₁ k (by omega)).2 L)
    (fun k L hk => (h₂ k (by omega)).2 L)).1
  unfold ClosedIn
  rw [heq]

/-- **Two nodes reach one last commit with one ledger**, at `K ≥ 3`. -/
theorem closesAfter_agree (hK : 3 ≤ K) {H₁ H₂ : Finset BlockId} (hH₁ : H₁ ⊆ U.ids)
    (hH₂ : H₂ ⊆ U.ids) {closes : Payload → Prop} {g₁ g₂ : ℕ → Option BlockId} {n₁ n₂ : ℕ}
    (h₁ : DecidesBelow U K H₁ D g₁ n₁) (hc₁ : ClosesAfter U K H₁ D closes g₁ n₁)
    (h₂ : DecidesBelow U K H₂ D g₂ n₂) (hc₂ : ClosesAfter U K H₂ D closes g₂ n₂) :
    n₁ = n₂ ∧ LedgerIn U K H₁ D g₁ n₁ = LedgerIn U K H₂ D g₂ n₂ := by
  have hn : n₁ = n₂ := by
    rcases lt_trichotomy n₁ n₂ with hlt | heq | hlt
    · exact absurd ((closedIn_iff_of_agree hK hH₁ hH₂ h₁ h₂ le_rfl hlt.le).mp hc₁.1)
        (hc₂.2 n₁ hlt)
    · exact heq
    · exact absurd ((closedIn_iff_of_agree hK hH₁ hH₂ h₁ h₂ hlt.le le_rfl).mpr hc₂.1)
        (hc₁.2 n₂ hlt)
  subst hn
  exact ⟨rfl, (ledgerIn_agree hK hH₁ hH₂ (fun k hk => (h₁ k hk).1) (fun k hk => (h₂ k hk).1)
    (fun k L hk => (h₁ k hk).2 L) (fun k L hk => (h₂ k hk).2 L)).1⟩

variable {tl : Timeline Validator BlockId} {T : Finset Validator} {G δ τ γ μ R N : ℕ}

namespace ReactiveRun

variable (h : ReactiveRun U tl T G δ τ γ μ R N)
include h

/-- **The channel closes**, at `2δ ≤ γ ≤ τ` and `δ < γ`, `K ≥ 3`, when nodes of
`T` fetch, the schedule offers runs of `c` leaders of `T` spanning
eligibility and a slot led by `T` every `D` rounds, and `T` declares the
channel closed from round `r₀` on: there is a slot `b` such that, if the run
reaches round `σ(b + c − 1) + 2`, every node of `T` at one time has decided
every slot up to its last commit. -/
theorem exists_closesAfter (hγ : 2 * δ ≤ γ) (hδ : δ < γ) (hγτ : γ ≤ τ) {Δ : ℕ} (hK : 3 ≤ K)
    (hF : Fetches U tl T K G Δ) {c : ℕ} (hc : 0 < c)
    (hspan : ∀ b i, i < b → EligibleAt (S := S) 2 i (b + c - 1)) (fair : FairRunOn T c)
    (hgap : ∀ r, ∃ k, r < S.slotRound k ∧ S.slotRound k ≤ r + D ∧ S.leader k ∈ T)
    {closes : Payload → Prop} {r₀ : ℕ} (hcl : DeclaresFrom U T closes r₀) :
    ∃ b, S.slotRound (b + c - 1) + 2 ≤ N → ∃ t, ∀ v ∈ T, ∃ g n,
      DecidesBelow U K (tl.held v t) D g n ∧ ClosesAfter U K (tl.held v t) D closes g n := by
  classical
  set s := max r₀ (R + 1)
  obtain ⟨k₀, hk₀⟩ := S.unbounded (s + D + 1)
  obtain ⟨b, hkb, hb⟩ := h.exists_ledger_from (by omega) hδ hγτ D hF hc hspan fair k₀
  refine ⟨b, fun hN => ⟨max G (U.ids.sup tl.built) + δ + Δ, fun v hv => ?_⟩⟩
  obtain ⟨g, hg⟩ := hb hN _ le_rfl v hv
  have hbN : s + D + 1 ≤ S.slotRound (b + c - 1) := hk₀.trans (S.mono (by omega))
  have hsync := h.syncFrom hγ hδ hγτ
  -- the blocks of `T` at round `s` enter the ledger, and declare the channel closed
  set X := U.ids.filter fun x => (U.block x).creator ∈ T ∧ (U.block x).round = s
  have hclosed : ClosedIn U K (tl.held v (max G (U.ids.sup tl.built) + δ + Δ)) D closes g
      (b + c) := by
    refine ⟨X, fun x hx => ?_, fun x hx => ?_, h.large.trans (Finset.card_le_card fun w hw => ?_)⟩
    · obtain ⟨hxi, hxT, hxr⟩ := Finset.mem_filter.mp hx
      exact mem_ledgerIn_of_gap (R := R + 1) hK h.large
        (fun m h1 h2 => hsync.2.1 m h1 (by omega)) (h.held_ids v _) hgap
        (fun i hi => (hg i hi).1) (fun i L hi hL => (hg i hi).2 L hL) hxi hxT (by omega)
        (fun k hk => by
          by_contra hkn
          have := S.mono (show k₀ ≤ k by omega)
          omega)
        (fun r h1 h2 => hsync.2.2 r h1 (by omega))
        (h.withRefs_subset_held (by omega) hv (by omega))
    · obtain ⟨hxi, hxT, hxr⟩ := Finset.mem_filter.mp hx
      exact hcl x hxi hxT (by omega)
    · obtain ⟨x, hx, hxw, hxr⟩ := h.populatedOn hδ hγτ (s := s) (by omega) (by omega) w hw
      exact Finset.mem_image.mpr ⟨x, Finset.mem_filter.mpr ⟨hx, hxw ▸ hw, hxr⟩, hxw⟩
  have hex : ∃ n, ClosedIn U K (tl.held v (max G (U.ids.sup tl.built) + δ + Δ)) D closes g n :=
    ⟨_, hclosed⟩
  have hle := Nat.find_min' hex hclosed
  exact ⟨g, Nat.find hex, fun i hi => hg i (by omega), Nat.find_spec hex,
    fun m hm => Nat.find_min hex hm⟩

end ReactiveRun

end KPartialDag

end LeanDag
