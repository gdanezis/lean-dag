import LeanDag.KPartialSparse.Model.Close
import LeanDag.KPartialSparse.Helpers.Reactive
import LeanDag.KPartialSparse.Helpers.Order
/-!
# Sparse K-partial DAG — closing the channel, helpers

`docs/kpartial-sparse.md` §9. A node's decisions hold on more blocks
(`NodeDecided.mono`), and with them its last commit (`closesAfter_mono`); two
nodes reach one last commit with one ledger (`closesAfter_agree`); on a timed
run where `T` declares the channel closed, every node of `T` reaches the last
commit (`TimedRun.exists_closesAfter`).
-/

namespace LeanDag

namespace KPartialSparse

open KPartialDag (Crashes Timeline LiveRow)
open scoped KPartialDag
open Scheme

variable {Validator : Type*} [Fintype Validator] [DecidableEq Validator] [F : Faults Validator]
variable [Cr : Crashes Validator] [Ld : Leaders Validator]
variable {BlockId : Type*} [LinearOrder BlockId] {Payload : Type*}
variable {U : SRecord Validator BlockId Payload} {K D : ℕ} {H H' : Finset BlockId} {A : BlockId}

/-! ## More blocks -/

/-- An anchor point read on `H` is read on more. -/
theorem AnchoredIn.mono (hH : H ⊆ H') {x : BlockId} {d : ℕ} (h : AnchoredIn U K H A x d) :
    AnchoredIn U K H' A x d := by
  induction h with
  | anchor h => exact .anchor (h.trans hH)
  | reached i S m y d y' d' _ hz _ hmz hi hm hcard hx ih ih' =>
    exact .reached i S m y d y' d' ih hz ih' hmz hi hm hcard (hx.trans hH)

/-- The sub-DAG read on `H` is read on more. -/
theorem availIn_mono (hH : H ⊆ H') {z : BlockId} (hz : z ∈ AvailIn U K H A) :
    z ∈ AvailIn U K H' A := by
  obtain ⟨y, d, hy, hzy⟩ := hz
  exact ⟨y, d, hy.mono hH, hzy⟩

/-- **A sub-DAG fetched into `H` is fetched into more**, of the record: above the
round fetched to, what is read on more is the record's, and so read on `H`. -/
theorem FetchedIn.mono (hH : H ⊆ H') (hH' : H' ⊆ U.ids) {ρ : ℕ} (hf : FetchedIn U K H A ρ) :
    FetchedIn U K H' A ρ := by
  have hHi := hH.trans hH'
  refine ⟨hf.1.trans hH, fun i S m x hi hS hcard =>
    (hf.2 i S m x hi (fun z hzS => ?_) hcard).trans hH⟩
  obtain ⟨h₁, h₂, h₃, h₄, h₅, h₆⟩ := hS z hzS
  refine ⟨avail_subset_availIn hHi hf (availIn_subset h₁) h₂.le, h₂, fun hpos => ?_, h₄, h₅, h₆⟩
  obtain ⟨y, d, hy, hmy⟩ := h₃ hpos
  have hA : A ∈ U.ids := hH' (hf.1.trans hH self_mem_window)
  have hyr := round_le_of_mem_historyUpto _ (hy.toAnchored.mem hA)
    (window_subset_historyUpto (hmy mem_windowFrom_self))
  exact ⟨y, d, hy.toAnchored.anchoredIn hHi hf (by omega), hmy⟩

variable [ClaimFormat BlockId Payload] {p : Params}

/-- A link read on `H` holds on more. -/
theorem LinkedIn.mono (hH : H ⊆ H') {L : BlockId} {r : ℕ} (h : LinkedIn p U K H A L r) :
    LinkedIn p U K H' A L r := by
  obtain ⟨X, hX, hXn⟩ := h
  exact ⟨X, fun C hC => ⟨availIn_mono hH (hX C hC).1, (hX C hC).2⟩, hXn⟩

variable [S : Slots Validator]

/-- **A node's decision holds on more blocks** of the record: the direct tests
and the links only gain, and an indirect decision reads a sub-DAG fetched below
the slot's certificates, which is the record's. -/
theorem NodeDecided.mono (hH : H ⊆ H') (hH' : H' ⊆ U.ids) {k : ℕ} {v : Option BlockId}
    (h : NodeDecided p U K H k v) : NodeDecided p U K H' k v := by
  have hcr : ∀ (X : Finset BlockId), (creatorsOf U.block (X.filter (· ∈ H))).card ≤
      (creatorsOf U.block (X.filter (· ∈ H'))).card := fun X =>
    Finset.card_le_card (Finset.image_subset_image (Finset.monotone_filter_right _
      fun _ _ hb => hH hb))
  induction h with
  | directCommit hL hc => exact .directCommit hL (hc.trans (hcr _))
  | directSkip hs => exact .directSkip (hs.trans (hcr _))
  | indirectCommit hkj helig _ _ hf hL hlink hleast ihj ihm =>
    exact .indirectCommit hkj helig ihj ihm (hf.mono hH hH') hL (hlink.mono hH)
      fun L' hL' hlt hl' => hleast L' hL' hlt
        (certLinked_linkedIn (hH.trans hH') hf (linkedIn_certLinked hH' hl'))
  | indirectSkip hkj helig _ _ hf hnone ihj ihm =>
    exact .indirectSkip hkj helig ihj ihm (hf.mono hH hH') fun L hL hl =>
      hnone L hL (certLinked_linkedIn (hH.trans hH') hf (linkedIn_certLinked hH' hl))

/-- Decisions below `n` hold on more blocks. -/
theorem DecidesBelow.mono (hH : H ⊆ H') (hH' : H' ⊆ U.ids) {g : ℕ → Option BlockId} {n : ℕ}
    (h : DecidesBelow p U K H D g n) : DecidesBelow p U K H' D g n := fun i hi =>
  ⟨(h i hi).1.mono hH hH', fun L hL => ((h i hi).2 L hL).mono hH hH'⟩

/-- **Closure is read alike on more blocks**, up to the slots decided. -/
theorem closedIn_iff_of_mono (hH : H ⊆ H') (hH' : H' ⊆ U.ids) {closes : Payload → Prop}
    {g : ℕ → Option BlockId} {n m : ℕ} (h : DecidesBelow p U K H D g n) (hm : m ≤ n) :
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
    {g : ℕ → Option BlockId} {n : ℕ} (h : DecidesBelow p U K H D g n)
    (hc : ClosesAfter U K H D closes g n) : ClosesAfter U K H' D closes g n :=
  ⟨(closedIn_iff_of_mono hH hH' h le_rfl).mp hc.1, fun m hm hm' =>
    hc.2 m hm ((closedIn_iff_of_mono hH hH' h hm.le).mpr hm')⟩

/-! ## Two nodes -/

/-- Two nodes read closure alike after slots they have both decided. -/
theorem closedIn_iff_of_agree (hrow : Row Validator p) (hdeep : Deep Validator K)
    (hI : Disciplined K p.certThreshold S U) {H₁ H₂ : Finset BlockId} (hH₁ : H₁ ⊆ U.ids)
    (hH₂ : H₂ ⊆ U.ids) {closes : Payload → Prop} {g₁ g₂ : ℕ → Option BlockId} {n₁ n₂ m : ℕ}
    (h₁ : DecidesBelow p U K H₁ D g₁ n₁) (h₂ : DecidesBelow p U K H₂ D g₂ n₂) (hm₁ : m ≤ n₁)
    (hm₂ : m ≤ n₂) : ClosedIn U K H₁ D closes g₁ m ↔ ClosedIn U K H₂ D closes g₂ m := by
  have heq := (ledgerIn_agree (D := D) hrow hdeep hI hH₁ hH₂ (n := m)
    (fun k hk => (h₁ k (by omega)).1) (fun k hk => (h₂ k (by omega)).1)
    (fun k L hk => (h₁ k (by omega)).2 L) (fun k L hk => (h₂ k (by omega)).2 L)).1
  unfold ClosedIn
  rw [heq]

/-- **Two nodes reach one last commit with one ledger.** -/
theorem closesAfter_agree (hrow : Row Validator p) (hdeep : Deep Validator K)
    (hI : Disciplined K p.certThreshold S U) {H₁ H₂ : Finset BlockId} (hH₁ : H₁ ⊆ U.ids)
    (hH₂ : H₂ ⊆ U.ids) {closes : Payload → Prop} {g₁ g₂ : ℕ → Option BlockId} {n₁ n₂ : ℕ}
    (h₁ : DecidesBelow p U K H₁ D g₁ n₁) (hc₁ : ClosesAfter U K H₁ D closes g₁ n₁)
    (h₂ : DecidesBelow p U K H₂ D g₂ n₂) (hc₂ : ClosesAfter U K H₂ D closes g₂ n₂) :
    n₁ = n₂ ∧ LedgerIn U K H₁ D g₁ n₁ = LedgerIn U K H₂ D g₂ n₂ := by
  have hn : n₁ = n₂ := by
    rcases lt_trichotomy n₁ n₂ with hlt | heq | hlt
    · exact absurd ((closedIn_iff_of_agree hrow hdeep hI hH₁ hH₂ h₁ h₂ le_rfl hlt.le).mp hc₁.1)
        (hc₂.2 n₁ hlt)
    · exact heq
    · exact absurd ((closedIn_iff_of_agree hrow hdeep hI hH₁ hH₂ h₁ h₂ hlt.le le_rfl).mpr
        hc₂.1) (hc₁.2 n₂ hlt)
  subst hn
  exact ⟨rfl, (ledgerIn_agree hrow hdeep hI hH₁ hH₂ (fun k hk => (h₁ k hk).1)
    (fun k hk => (h₂ k hk).1) (fun k L hk => (h₁ k hk).2 L) (fun k L hk => (h₂ k hk).2 L)).1⟩

/-! ## A timed run -/

omit [LinearOrder BlockId] in
/-- Synchrony up to `N` holds up to less. -/
theorem SyncFrom.mono {T : Finset Validator} {R N N' : ℕ} (h : SyncFrom U T R N) (hN : N' ≤ N) :
    SyncFrom U T R N' :=
  ⟨h.1, fun r h1 h2 => h.2.1 r h1 (by omega),
    fun k h1 h2 => h.2.2.1 k h1 (by omega), fun k h1 h2 => h.2.2.2 k h1 (by omega)⟩

omit [ClaimFormat BlockId Payload] [LinearOrder BlockId] in
/-- Coverage up to `N` holds up to less. -/
theorem CoversFrom.mono {T : Finset Validator} {R N N' : ℕ} (h : CoversFrom U T R N)
    (hN : N' ≤ N) : CoversFrom U T R N' :=
  fun k h1 h2 => h k h1 (by omega)

variable {tl : Timeline Validator BlockId} {T : Finset Validator} {G δ τ γ R N : ℕ}

namespace TimedRun

variable (h : TimedRun U tl T G δ τ γ R N)
include h

/-- **The channel closes**, at a live row, `2δ ≤ γ ≤ τ` and `δ < γ`, the depth
the sub-DAG needs and `D ≤ K`, on a disciplined record, when nodes of `T`
fetch, a two-round row links by `f + c + 1` votes or more, each slot's leader
leads its round on the substrate, the schedule offers runs of `c` leaders of
`T` spanning eligibility and a slot led by `T` every `D` rounds, and `T`
declares the channel closed from round `r₀` on: there is a slot `b` such that,
if the run reaches the round of its last certificates, every node of `T` at
one time has decided every slot up to its last commit. -/
theorem exists_closesAfter (hrow : Row Validator p)
    (hlink : p.voteIsCert = true → F.f + Cr.c + 1 ≤ p.linkSize) (hdeep : Deep Validator K)
    (hI : Disciplined K p.certThreshold S U) (hlive : LiveRow Validator p) (hDK : D ≤ K)
    (hγ : 2 * δ ≤ γ) (hδ : δ < γ) (hγτ : γ ≤ τ) {Δ : ℕ} (hF : Fetches U tl T K G Δ)
    (hsl : ∀ k, S.leader k ∈ Ld.leaders (S.slotRound k)) {c : ℕ} (hc : 0 < c)
    (hspan : ∀ b i, i < b → EligibleAt (S := S) (p.waveLength - 1) i (b + c - 1))
    (fair : FairRunOn T c)
    (hgap : ∀ r, ∃ k, r < S.slotRound k ∧ S.slotRound k ≤ r + D ∧ S.leader k ∈ T)
    {closes : Payload → Prop} {r₀ : ℕ} (hcl : DeclaresFrom U T closes r₀) :
    ∃ b, certRound p (S.slotRound (b + c - 1)) ≤ N → ∃ t, ∀ v ∈ T, ∃ g n,
      DecidesBelow p U K (tl.held v t) D g n ∧ ClosesAfter U K (tl.held v t) D closes g n := by
  classical
  set s := max r₀ (R + 1)
  obtain ⟨k₀, hk₀⟩ := S.unbounded (s + D + 2)
  obtain ⟨b, hkb, hb⟩ := h.exists_ledger_at hrow hlink hI hlive (by omega) hδ hγτ D hF hc
    hspan fair k₀
  refine ⟨b, fun hN => ?_⟩
  set T₀ := max G (U.ids.sup tl.built)
  have hT₀ : ∀ x ∈ U.ids, tl.built x ≤ T₀ := fun x hx =>
    (Finset.le_sup (f := tl.built) hx).trans (le_max_right _ _)
  set t' := T₀ + δ + Δ
  refine ⟨t', fun v hv => ?_⟩
  obtain ⟨g, hg⟩ := hb hN v hv
  have hHi := h.held_ids v t'
  have hdec : DecidesBelow p U K (tl.held v t') D g (b + c) := fun i hi => hg i hi
  have hcb := certRound_bounds (p := p) (S.slotRound (b + c - 1))
  have hbN : s + D + 2 ≤ S.slotRound (b + c - 1) := hk₀.trans (S.mono (by omega))
  have hsync := h.syncFrom (by omega) hδ hγτ
  have hcov := h.coversFrom hγ hδ hγτ hsl
  set X := U.ids.filter fun x => (U.block x).creator ∈ T ∧ (U.block x).round = s
  have hclosed : ClosedIn U K (tl.held v t') D closes g (b + c) := by
    refine ⟨X, fun x hx => ?_, fun x hx => ?_, h.large.trans (Finset.card_le_card fun w hw => ?_)⟩
    · obtain ⟨hxi, hxT, hxr⟩ := Finset.mem_filter.mp hx
      exact mem_ledgerIn_of_gap (R := R + 1) hrow hdeep hI hlive h.stable hDK hHi hgap
        (fun i hi => (hdec i hi).1) (fun i L hi hL => (hdec i hi).2 L hL) hxi hxT (by omega)
        (fun k hk => by
          by_contra hkn
          have := S.mono (show k₀ ≤ k by omega)
          omega)
        (hsync.mono (by omega)) (hcov.mono (by omega))
        (fun z hz => h.mem_held_of_round hz.1 hz.2.1 (by have := hz.2.2.1; omega) hv
          (hT₀ z hz.1) (by omega))
    · obtain ⟨hxi, hxT, hxr⟩ := Finset.mem_filter.mp hx
      exact hcl x hxi hxT (by omega)
    · obtain ⟨x, hx, hxw, hxr⟩ := h.populatedOn hδ hγτ (s := s) (by omega) (by omega) w hw
      exact Finset.mem_image.mpr ⟨x, Finset.mem_filter.mpr ⟨hx, hxw ▸ hw, hxr⟩, hxw⟩
  have hex : ∃ n, ClosedIn U K (tl.held v t') D closes g n := ⟨_, hclosed⟩
  have hle := Nat.find_min' hex hclosed
  exact ⟨g, Nat.find hex, fun i hi => hdec i (by omega), Nat.find_spec hex,
    fun m hm => Nat.find_min hex hm⟩

end TimedRun

end KPartialSparse

end LeanDag
