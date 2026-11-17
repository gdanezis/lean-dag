import LeanDagTest.KPartialSparse.Witness
import LeanDag.KPartialSparse.Reactive.Proof
/-!
# Sparse K-partial DAG — a timed witness

The record of `Witness.lean` in time, at `G = 0`, `δ = 1`, `γ = 2`, `τ = 4`:
every block of round `r` is built at time `4 + 3r`, its author holds it from
then on, and every other validator one step later. Each round is built `γ`
after the round below is delivered. The timeline is a timed run from round
`0` to round `6`; by Theorem 5 it is synchronous among the correct
validators, and each of them commits slot `2` by time `17`. Read with a later
`G = 10`, the timeline meets the rules for nodes, and a run resumes above
round `0`. The timed nodes check claims at `K = 6`, so the record meets the
claim disciplines.
-/

namespace LeanDagTest

namespace KPartialSparse

open LeanDag LeanDag.KPartialSparse
open LeanDag.KPartialDag (Timeline)
open scoped LeanDag.KPartialDag

/-- Block `4r + v` is built at time `4 + 3r`. -/
def tBuilt (b : ℕ) : ℕ := 4 + 3 * (b / 4)

/-- A validator holds its own blocks once built and others' one step later. -/
def tHeld (v : Fin 4) (t : ℕ) : Finset ℕ :=
  wIds.filter fun b : ℕ => tBuilt b + (if (wBlock b).creator = v then 0 else 1) ≤ t

/-- A validator keeps its own blocks on disk once built. -/
def tDisk (v : Fin 4) (t : ℕ) : Finset ℕ :=
  wIds.filter fun b : ℕ => (wBlock b).creator = v ∧ tBuilt b ≤ t

/-- The timeline. -/
def tTl : Timeline (Fin 4) ℕ := ⟨tHeld, tDisk, tBuilt⟩

theorem mem_tHeld {v : Fin 4} {t : ℕ} {b : ℕ} :
    b ∈ tHeld v t ↔ b ∈ wIds ∧ tBuilt b + (if (wBlock b).creator = v then 0 else 1) ≤ t := by
  simp [tHeld]

/-- The blocks at rounds `0` to `r`. -/
def upto (r : ℕ) : Finset ℕ := wIds.filter fun b : ℕ => b / 4 ≤ r

theorem upto_subset {r : ℕ} {v : Fin 4} {t : ℕ} (ht : 4 + 3 * r + 1 ≤ t) : upto r ⊆ tHeld v t := by
  intro b hb
  simp only [upto, Finset.mem_filter] at hb
  obtain ⟨hb, hbr⟩ := hb
  refine mem_tHeld.mpr ⟨hb, ?_⟩
  unfold tBuilt
  split_ifs <;> omega

theorem round_wBlock (b : ℕ) : (wBlock b).round = b / 4 := rfl

theorem creator_val (b : ℕ) : ((wBlock b).creator).val = b % 4 := rfl

theorem bid_mem (k : ℕ) (hk : k ≤ 6) : bid k (lead k) ∈ wIds := by
  have : ∀ k ≤ 6, bid k (lead k) ∈ wIds := by decide
  exact this k hk

/-- The leader block of round `k`. -/
theorem isLeader_bid (k : ℕ) (hk : k ≤ 6) : IsLeaderBlock (S := wSlots) wU k (bid k (lead k)) := by
  have hround : (wBlock (bid k (lead k))).round = k := by
    rw [round_wBlock]; unfold bid; have := (lead k).isLt; omega
  have hcreator : (wBlock (bid k (lead k))).creator = lead k := by
    ext; rw [creator_val]; unfold bid; have := (lead k).isLt; omega
  exact ⟨bid_mem k hk, hround, hcreator⟩

/-- What each round needs, at rounds `0` to `5`, held by the blocks up to it. -/
theorem waitsFor_upto : ∀ r ≤ 5, WaitsFor wU (upto r) r := by
  intro r hr
  have hq : ∀ r ≤ 5, QuorumIn wU (upto r) r := by unfold QuorumIn; decide
  have hl : ∀ r ≤ 5, bid r (lead r) ∈ upto r := by decide
  have hv : ∀ r ≤ 5, 1 ≤ r → CertIn wU (upto r) r (bid (r - 1) (lead (r - 1))) := by
    unfold CertIn; decide
  have hlead : ∀ k ≤ 5, IsLeaderBlock (S := wSlots) wU k (bid k (lead k)) :=
    fun k hk => isLeader_bid k (by omega)
  refine ⟨hq r hr, fun k hk => ?_, fun k hk => ?_⟩
  · have hk' : k = r := hk
    subst hk'
    exact ⟨bid k (lead k), hl k hr, hlead k hr⟩
  · have hk' : k + 1 = r := hk
    refine ⟨bid k (lead k), hlead k (by omega), ?_⟩
    have := hv r hr (by omega)
    rwa [show r - 1 = k by omega] at this

/-! ## Holding in time -/

theorem built_eq (b : ℕ) : tTl.built b = 4 + 3 * (b / 4) := rfl

theorem held_eq (v : Fin 4) (t : ℕ) : tTl.held v t = tHeld v t := rfl

/-- A quorum at round `r` is held only once others' round-`r` blocks have
arrived. -/
theorem quorum_time {v : Fin 4} {t r : ℕ} (h : QuorumIn wU (tHeld v t) r) : 4 + 3 * r + 1 ≤ t := by
  have hq : kQuorum (Fin 4) = 3 := rfl
  unfold QuorumIn at h
  rw [hq] at h
  obtain ⟨w, hw, hwv⟩ := Finset.exists_mem_ne (show 1 < (creatorsOf wU.block
    ((tHeld v t).filter fun b => (wU.block b).round = r)).card by omega) v
  obtain ⟨x, hx, rfl⟩ := mem_creatorsOf.mp hw
  obtain ⟨hxH, hxr⟩ := Finset.mem_filter.mp hx
  obtain ⟨-, hxt⟩ := mem_tHeld.mp hxH
  have hwv' : (wBlock x).creator ≠ v := hwv
  rw [if_neg hwv'] at hxt
  change (wBlock x).round = r at hxr
  rw [round_wBlock] at hxr
  unfold tBuilt at hxt
  omega

/-- Being behind round `r + 1` comes only once others' round-`(r + 1)` blocks
have arrived. -/
theorem behind_time {v : Fin 4} {t r : ℕ} (h : BehindIn wU (tHeld v t) v r) :
    4 + 3 * (r + 1) + 1 ≤ t := by
  unfold BehindIn at h
  obtain ⟨w, hw⟩ := Finset.card_pos.mp (by have : (1 : ℕ) + 0 + 1 = 2 := rfl; omega :
    0 < ((creatorsOf wU.block ((tHeld v t).filter fun b => (wU.block b).round = r + 1)).erase
      v).card)
  obtain ⟨hwv, hw⟩ := Finset.mem_erase.mp hw
  obtain ⟨x, hx, rfl⟩ := mem_creatorsOf.mp hw
  obtain ⟨hxH, hxr⟩ := Finset.mem_filter.mp hx
  obtain ⟨-, hxt⟩ := mem_tHeld.mp hxH
  have hwv' : (wBlock x).creator ≠ v := hwv
  rw [if_neg hwv'] at hxt
  change (wBlock x).round = r + 1 at hxr
  rw [round_wBlock] at hxr
  unfold tBuilt at hxt
  omega

theorem held_built {v : Fin 4} {t : ℕ} {b : ℕ} (hb : b ∈ tHeld v t) : 4 + 3 * (b / 4) ≤ t := by
  obtain ⟨-, hbt⟩ := mem_tHeld.mp hb
  unfold tBuilt at hbt
  split_ifs at hbt <;> omega

theorem round_le_six {b : ℕ} (hb : b ∈ wIds) : b / 4 ≤ 6 := by
  have : ∀ b ∈ wIds, b / 4 ≤ 6 := by decide
  exact this b hb

theorem bid_val (r : ℕ) (v : Fin 4) : (bid r v : ℕ) = 4 * r + v.val := rfl

theorem bid_div (r : ℕ) (v : Fin 4) : (bid r v : ℕ) / 4 = r := by
  show (4 * r + v.val) / 4 = r
  have := v.isLt; omega

/-! ## The timed run -/

theorem wT_correct : wT ⊆ (Correct : Finset (Fin 4)) := by decide

theorem all_correct {b : ℕ} (hb : b ∈ wIds) : (wBlock b).creator ∈ (Correct : Finset (Fin 4)) := by
  have : ∀ b ∈ wIds, (wBlock b).creator ∈ (Correct : Finset (Fin 4)) := by decide
  exact this b hb

theorem refs_lead : ∀ b : ℕ, b ∈ wIds → 1 ≤ b / 4 →
    bid (b / 4 - 1) (lead (b / 4 - 1)) ∈ (wBlock b).refs := by decide

theorem claims_lead : ∀ b : ℕ, b ∈ wIds → 2 ≤ b / 4 →
    claimsOf wU b = {bid (b / 4 - 2) (lead (b / 4 - 2))} := by decide

theorem claims_low : ∀ b : ℕ, b ∈ wIds → b / 4 < 2 → claimsOf wU b = ∅ := by
  decide

theorem lead_mem (k : ℕ) : lead k ∈ wT := by
  have : (lead k).val < 3 := Nat.mod_lt _ (by omega)
  revert this; generalize lead k = w; revert w; decide

/-- **Backed**, on the timeline. -/
theorem backed_rule (v : Fin 4) (t : ℕ) (b : ℕ) (hb : b ∈ tHeld v t) (L : ℕ)
    (hL : L ∈ claimsOf wU b) : CertIn wU (tHeld v t) ((wU.block L).round + 1) L := by
  have hbi : b ∈ wIds := (mem_tHeld.mp hb).1
  have ht := held_built hb
  have h6 := round_le_six hbi
  by_cases h2 : 2 ≤ b / 4
  · rw [claims_lead b hbi h2, Finset.mem_singleton] at hL
    subst hL
    obtain ⟨m, hm⟩ : ∃ m, b / 4 = m + 2 := ⟨b / 4 - 2, by omega⟩
    rw [hm, show m + 2 - 2 = m by omega]
    have hr : (wU.block (bid m (lead m))).round = m := (isLeader_bid m (by omega)).2.1
    rw [hr]
    obtain ⟨-, -, hc⟩ := waitsFor_upto (m + 1) (by omega)
    obtain ⟨L', hL', hc'⟩ := hc m rfl
    have := isLeaderBlock_unique_of_honest (S := wSlots) (U := wU) (lead_mem _ |> wT_correct)
      hL' (isLeader_bid m (by omega))
    rw [this] at hc'
    exact certIn_mono (upto_subset (by omega)) hc'
  · rw [claims_low b hbi (by omega)] at hL
    simp at hL

theorem refs_all : ∀ b : ℕ, b ∈ wIds → (wBlock b).creator = lead (b / 4) →
    ∀ x : ℕ, x ∈ wIds → x / 4 + 1 = b / 4 → x ∈ (wBlock b).refs := by decide

theorem refs_self : ∀ b : ℕ, b ∈ wIds → 1 ≤ b / 4 →
    bid (b / 4 - 1) (wBlock b).creator ∈ (wBlock b).refs := by decide

/-- **The timeline is a timed run** from round `0` to round `6`. -/
theorem wTimed : TimedRun (S := wSlots) wU tTl wT 0 1 4 2 0 6 where
  stable := wT_correct
  large := by decide
  held_ids := fun _ _ => Finset.filter_subset _ _
  mono := fun v _ t t' _ htt' b hb => by
    obtain ⟨hb, hbt⟩ := mem_tHeld.mp hb
    exact mem_tHeld.mpr ⟨hb, by omega⟩
  delivers := fun v _ t _ b hb _ w _ => by
    obtain ⟨hb, hbt⟩ := mem_tHeld.mp hb
    refine mem_tHeld.mpr ⟨hb, ?_⟩
    split_ifs at hbt ⊢ <;> omega
  closed := fun v _ t b hb _ j hj => by
    have hbi : b ∈ wIds := (mem_tHeld.mp hb).1
    have hji : j ∈ wIds := wU.complete b hbi j hj
    have hlt := (wU.valid b hbi).below j hj
    change (wBlock j).round < (wBlock b).round at hlt
    rw [round_wBlock, round_wBlock] at hlt
    have := held_built hb
    refine mem_tHeld.mpr ⟨hji, ?_⟩
    unfold tBuilt; split_ifs <;> omega
  grounded := fun v _ t b hb _ hR => by
    have hbi : b ∈ wIds := (mem_tHeld.mp hb).1
    have := held_built hb
    have h6 := round_le_six hbi
    change 0 < (wBlock b).round at hR
    change QuorumIn wU (tHeld v t) ((wBlock b).round - 1)
    rw [round_wBlock] at hR ⊢
    exact quorumIn_mono (upto_subset (by omega)) (waitsFor_upto _ (by omega)).1
  backed := fun v _ t b hb _ L hL => backed_rule v t b hb L hL
  causal := fun v _ t b hb _ => by
    have := held_built hb
    rw [built_eq]; omega
  prior := fun v _ t b hb _ hbv => by
    obtain ⟨-, hbt⟩ := mem_tHeld.mp hb
    have hbv' : (wBlock b).creator ≠ v := hbv
    rw [if_neg hbv'] at hbt
    rw [built_eq]; unfold tBuilt at hbt; omega
  disk_held := fun v _ t b hb => by
    obtain ⟨hb, hbv, hbt⟩ := Finset.mem_filter.mp hb
    refine mem_tHeld.mpr ⟨hb, ?_⟩
    rw [if_pos hbv]; omega
  stores := fun b hb _ t hbt =>
    Finset.mem_filter.mpr ⟨hb, rfl, by rw [built_eq] at hbt; unfold tBuilt; omega⟩
  waits := fun b hb _ r hbr _ => by
    change (wBlock b).round = r + 1 at hbr
    rw [round_wBlock] at hbr
    have h6 := round_le_six hb
    have hW := waitsFor_upto r (by omega)
    refine Or.inl ⟨by rw [built_eq]; omega, waitsFor_mono (upto_subset ?_) hW,
      waitsFor_mono (upto_subset ?_) hW⟩ <;> rw [built_eq] <;> omega
  prompt := fun v hv r t _ hr hw => by
    refine ⟨bid (r + 1) v, ?_, ?_, ?_, ?_⟩
    · have : ∀ v ∈ wT, ∀ r < 6, bid (r + 1) v ∈ wIds := by decide
      exact this v hv r hr
    · change (wBlock (bid (r + 1) v)).creator = v
      ext; rw [creator_val]; unfold bid; have := v.isLt; omega
    · change r + 1 ≤ (wBlock (bid (r + 1) v)).round
      rw [round_wBlock]; unfold bid; have := v.isLt; omega
    · rw [built_eq]
      rw [bid_div]
      rcases hw with ⟨h1, hW⟩ | ⟨h1, hQ⟩ | ⟨-, hB⟩
      · have := quorum_time hW.1; omega
      · have := quorum_time hQ; omega
      · have := behind_time hB; omega
  votes := fun b hb _ k _ hk _ => by
    change wSlots.slotRound k + 1 = (wBlock b).round at hk
    rw [round_wBlock] at hk
    have hsr : wSlots.slotRound k = k := rfl
    rw [hsr] at hk
    have h6 := round_le_six hb
    have hk6 : k ≤ 6 := by omega
    have hb1 : 1 ≤ b / 4 := by rw [← hk]; omega
    refine ⟨bid k (lead k), ?_, isLeader_bid k hk6⟩
    have := refs_lead b hb hb1
    rwa [show b / 4 - 1 = k by rw [← hk]; omega] at this
  covers := fun b hb _ hbl x hx _ hxr => by
    have hxi := (mem_tHeld.mp hx).1
    change (wBlock b).creator ∈ ({lead (wBlock b).round} : Finset (Fin 4)) at hbl
    rw [Finset.mem_singleton, round_wBlock] at hbl
    change (wBlock x).round + 1 = (wBlock b).round at hxr
    rw [round_wBlock, round_wBlock] at hxr
    exact refs_all b hb hbl x hxi hxr
  self_ref := fun b hb _ x hx hxb hlt => by
    rw [built_eq, built_eq] at hlt
    refine ⟨bid (b / 4 - 1) (wBlock b).creator, refs_self b hb (by omega), ?_, ?_⟩
    · change (wBlock (bid (b / 4 - 1) (wBlock b).creator)).creator = (wBlock b).creator
      ext; rw [creator_val]; unfold bid; have := (wBlock b).creator.isLt; omega
    · change (wBlock x).round ≤ (wBlock (bid (b / 4 - 1) (wBlock b).creator)).round
      rw [round_wBlock, round_wBlock, bid_div]; omega
  claims := fun b hb _ k hk L hL _ => by
    change wSlots.slotRound k + 2 = (wBlock b).round at hk
    rw [round_wBlock] at hk
    have hsr : wSlots.slotRound k = k := rfl
    rw [hsr] at hk
    have h6 := round_le_six hb
    have hk6 : k ≤ 6 := by omega
    have hb2 : 2 ≤ b / 4 := by rw [← hk]; omega
    have hbk : b / 4 - 2 = k := by rw [← hk]; omega
    have hLe : L = bid k (lead k) := isLeaderBlock_unique_of_honest (S := wSlots) (U := wU)
      (lead_mem _ |> wT_correct) hL (isLeader_bid k hk6)
    rw [hLe, claims_lead b hb hb2, hbk]
    exact Finset.mem_singleton_self _
  start := ⟨4, fun v hv => ⟨bid 0 v, by
    have : ∀ v ∈ wT, bid 0 v ∈ wIds := by decide
    exact this v hv, by
      change (wBlock (bid 0 v)).creator = v
      ext; rw [creator_val]; unfold bid; have := v.isLt; omega,
    Nat.zero_le _, by rw [built_eq]; unfold bid; have := v.isLt; omega⟩⟩
  late := fun b _ _ _ => by rw [built_eq]; omega

/-- **Theorem 5 at work**: the timed run is synchronous among the correct
validators from round `1` to round `6`. -/
theorem wTimedSync : SyncFrom (S := wSlots) wU wT 1 6 :=
  Reactive.synchronised (Fin 4) ℕ (Finset ℕ) wU tTl wT 0 1 4 2 0 6 wTimed (by omega)
    (by omega) (by omega)

/-- **Theorem 5 at work**: every correct validator has built round `2` by time
`10`, and commits slot `2` on what it holds at time `17`. -/
theorem wTimedCommits (v : Fin 4) (hv : v ∈ wT) :
    ∃ L, IsLeaderBlock (S := wSlots) wU 2 L ∧
      NodeDecided (S := wSlots) (Scheme.Params.mysticeti 4 1) wU 6 (tHeld v 17) 2 (some L) :=
  Reactive.commits (Fin 4) ℕ (Finset ℕ) (Scheme.Params.mysticeti 4 1) wU tTl wT 0 1 4 2 0 6 6
    wLive wTimed (by omega) (by omega) (by omega) 2 10 (by decide) (by decide)
    (fun j _ _ => lead_mem j)
    (fun w hw => ⟨bid 2 w, by
      have : ∀ v ∈ wT, bid 2 v ∈ wIds := by decide
      exact this w hw, by
      change (wBlock (bid 2 w)).creator = w
      ext; rw [creator_val]; unfold bid; have := w.isLt; omega, by
      change (wBlock (bid 2 w)).round = 2
      rw [round_wBlock]; unfold bid; have := w.isLt; omega, by
      rw [built_eq]; unfold bid; have := w.isLt; omega⟩) v hv

/-- The timeline meets the rules for nodes for any later `G`. -/
theorem wRules (G : ℕ) : TimedRules (S := wSlots) wU tTl wT G 1 4 2 0 6 :=
  { wTimed.toTimedRules with
    mono := fun v hv t t' _ h => wTimed.mono v hv t t' (Nat.zero_le _) h
    delivers := fun v hv t _ b hb hbc w hw => wTimed.delivers v hv t (Nat.zero_le _) b hb hbc w hw
    prompt := fun v hv r t hr hrN hw => wTimed.prompt v hv r t hr hrN (by
      rcases hw with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩
      · exact Or.inl ⟨by omega, h2⟩
      · exact Or.inr (Or.inl ⟨by omega, h2⟩)
      · exact Or.inr (Or.inr ⟨by omega, h2⟩)) }

/-- **Theorem 5, resuming**: with `G = 10`, validator `0` has built round `2` by
`G`, so a timed run starts above round `0`, which every correct validator
reaches by `G + 3δ + 3τ = 25`. -/
theorem wResumes : ∃ R', 0 < R' ∧ (R' ≤ 6 → TimedRun (S := wSlots) wU tTl wT 10 1 4 2 R' 6 ∧
    ReachedBy wU tTl wT R' 25) :=
  Reactive.resumes (Fin 4) ℕ (Finset ℕ) wU tTl wT 10 1 4 2 0 6 (wRules 10) (bid 2 0)
    (by decide) (by decide) (by rw [built_eq, bid_div]) (by
      change 0 < (wBlock (bid 2 0)).round
      rw [round_wBlock, bid_div]; omega)

/-! ## Checked claims -/

theorem backs_mono {H H' : Finset ℕ} (hH : H ⊆ H') {L : ℕ} (h : Backs wU 3 H L) :
    Backs wU 3 H' L :=
  ⟨hH h.1, le_trans h.2 (Finset.card_le_card (Finset.image_subset_image
    (Finset.filter_subset_filter _ hH)))⟩

/-- A claim of a block at round `r + 1` or below is backed by the blocks up to
round `r`. -/
theorem backs_upto {X : ℕ} (hX : X ∈ wIds) {r : ℕ} (hr : X / 4 ≤ r + 1) {L : ℕ}
    (hL : L ∈ claimsOf wU X) : Backs wU 3 (upto r) L := by
  have h6 := round_le_six hX
  by_cases h2 : 2 ≤ X / 4
  · rw [claims_lead X hX h2, Finset.mem_singleton] at hL
    subst hL
    obtain ⟨m, hm⟩ : ∃ m, X / 4 = m + 2 := ⟨X / 4 - 2, by omega⟩
    rw [hm, show m + 2 - 2 = m by omega]
    have hr' : (wU.block (bid m (lead m))).round = m := (isLeader_bid m (by omega)).2.1
    obtain ⟨-, -, hc⟩ := waitsFor_upto (m + 1) (by omega)
    obtain ⟨L', hL', hc'⟩ := hc m rfl
    have := isLeaderBlock_unique_of_honest (S := wSlots) (U := wU) (lead_mem _ |> wT_correct)
      hL' (isLeader_bid m (by omega))
    rw [this] at hc'
    have hsub : upto (m + 1) ⊆ upto r := by
      intro b hb
      simp only [upto, Finset.mem_filter] at hb ⊢
      exact ⟨hb.1, by omega⟩
    have hmem : bid m (lead m) ∈ upto (m + 1) := by
      refine Finset.mem_filter.mpr ⟨bid_mem m (by omega), ?_⟩
      show bid m (lead m) / 4 ≤ m + 1
      rw [bid_div]; omega
    exact backs_mono hsub (backs_of_certIn (by decide) hmem (by rw [hr']; exact hc'))
  · rw [claims_low X hX (by omega)] at hL
    simp at hL

/-- A block at round `r` or below is referenceable on the blocks up to round
`r`. -/
theorem referenceable_upto {m : ℕ} (hm : m ∈ wIds) {r : ℕ} (hr : m / 4 ≤ r) :
    Referenceable wU 6 3 (upto r) m := by
  have hsub : window wU 6 m ⊆ upto r := by
    intro z hz
    have hzi := KPartialSparse.window_subset_ids (U := wU) 6 hm hz
    have hzr := round_le_of_mem_historyUpto (U := wU) 6 hm (window_subset_historyUpto hz)
    change (wBlock z).round ≤ (wBlock m).round at hzr
    rw [round_wBlock, round_wBlock] at hzr
    exact Finset.mem_filter.mpr ⟨hzi, by omega⟩
  refine ⟨hsub, fun X hX L hL => backs_upto ?_ ?_ hL⟩
  · exact (Finset.mem_filter.mp (hsub hX)).1
  · have := (Finset.mem_filter.mp (hsub hX)).2; omega

theorem upto_held {r t : ℕ} {v : Fin 4} (ht : 4 + 3 * r + 1 ≤ t) {m : ℕ} (hm : m ∈ wIds)
    (hr : m / 4 ≤ r) : Referenceable wU 6 3 (tHeld v t) m := by
  obtain ⟨h1, h2⟩ := referenceable_upto hm hr
  exact ⟨h1.trans (upto_subset ht), fun X hX L hL => backs_mono (upto_subset ht) (h2 X hX L hL)⟩

/-- **The timed nodes check claims**, at `K = 6` and threshold `3`. -/
theorem wChecked : TimedChecks wU tTl 6 3 where
  refs_checked := fun b hb _ m hm => by
    have hmi := wU.complete b hb m hm
    have hlt := (wU.valid b hb).below m hm
    change (wBlock m).round < (wBlock b).round at hlt
    rw [round_wBlock, round_wBlock] at hlt
    exact upto_held (r := b / 4 - 1) (by rw [built_eq]; omega) hmi (by omega)
  claims_backed := fun b hb _ L hL => by
    have h6 := round_le_six hb
    by_cases h1 : 1 ≤ b / 4
    · exact backs_mono (upto_subset (r := b / 4 - 1) (by rw [built_eq]; omega))
        (backs_upto hb (by omega) hL)
    · rw [claims_low b hb (by omega)] at hL; simp at hL
  carries := fun v _ s b hb _ m hm => by
    have hbi := (mem_tHeld.mp hb).1
    have hbt := held_built hb
    have hmi := wU.complete b hbi m hm
    have hlt := (wU.valid b hbi).below m hm
    change (wBlock m).round < (wBlock b).round at hlt
    rw [round_wBlock, round_wBlock] at hlt
    exact upto_held (r := b / 4 - 1) (by omega) hmi (by omega)
  carries_claims := fun v _ s b hb _ L hL => by
    have hbi := (mem_tHeld.mp hb).1
    have hbt := held_built hb
    have h6 := round_le_six hbi
    by_cases h1 : 1 ≤ b / 4
    · exact backs_mono (upto_subset (r := b / 4 - 1) (by omega)) (backs_upto hbi (by omega) hL)
    · rw [claims_low b hbi (by omega)] at hL; simp at hL

/-- **Theorem 5, checked**: the timed nodes meet the record's claim
disciplines. -/
theorem wTimedDisciplines : Checks wU 6 3 ∧ Truthful wU 3 :=
  Reactive.checked (Fin 4) ℕ (Finset ℕ) wU tTl 6 3 (fun _ _ => Finset.filter_subset _ _) wChecked

/-- The witness's nodes build above their disks. -/
theorem wAboveDisk : KPartialDag.BuildsAboveDisk wU.ids wU.block tTl where
  stores := fun b hb _ t ht => by
    refine ⟨b, Finset.mem_filter.mpr ⟨hb, rfl, ?_⟩, rfl, le_rfl⟩
    rw [built_eq] at ht; unfold tBuilt; omega
  above := fun b hb _ h0 b' hb' hb'c => by
    obtain ⟨-, -, hb't⟩ := Finset.mem_filter.mp hb'
    rw [built_eq] at h0
    change tBuilt b' ≤ tBuilt b - 1 at hb't
    change (wBlock b').round < (wBlock b).round
    rw [round_wBlock, round_wBlock]; unfold tBuilt at hb't; omega
  single := fun b hb c hc hbc hcb ht => by
    rw [built_eq, built_eq] at ht
    exact wU.no_equivocation b hb c hc hbc hcb (by
      change (wBlock b).round = (wBlock c).round; rw [round_wBlock, round_wBlock]; omega)

/-- **Theorem 5, chains**: the timed nodes keep chains. -/
theorem wTimedChains : Chains wU :=
  Reactive.chained (Fin 4) ℕ (Finset ℕ) wU tTl wT 0 1 4 2 0 6 wTimed.toTimedRules wAboveDisk

/-- **Theorem 5, covering**: on the timed run, leaders of the correct validators
cover them from round `1`. -/
theorem wTimedCovers : CoversFrom (S := wSlots) wU wT 1 6 :=
  Reactive.covered (Fin 4) ℕ (Finset ℕ) wU tTl wT 0 1 4 2 0 6 wTimed (by omega) (by omega)
    (by omega) (fun _ => Finset.mem_singleton.mpr rfl)

/-- The witness's nodes hold a held leader block's available sub-DAG one step
later: it lies at or below the leader, so was built no later. -/
theorem wFetches : Fetches (S := wSlots) wU tTl wT 6 0 1 := by
  intro v _ t _ j A hA hAH z hz
  have hAi := hA.1
  have hzi := KPartialSparse.avail_subset_ids hAi hz
  have hzr := round_le_of_avail (U := wU) hAi hz
  change (wBlock z).round ≤ (wBlock A).round at hzr
  rw [round_wBlock, round_wBlock] at hzr
  have hAt := held_built hAH
  refine mem_tHeld.mpr ⟨hzi, ?_⟩
  unfold tBuilt; split_ifs <;> omega

/-- **Theorem 5, the ledger**: every slot below the end of a run of slots led by
the correct validators is decided by every one of them at one time, once the
run fits in the record. -/
theorem wTimedLedger : ∃ b, 0 ≤ b ∧ (certRound (Scheme.Params.mysticeti 4 1)
    (wSlots.slotRound (b + 3 - 1)) ≤ 6 → ∃ t, ∀ v ∈ wT, ∃ g : ℕ → Option ℕ, ∀ i, i < b + 3 →
      NodeDecided (S := wSlots) (Scheme.Params.mysticeti 4 1) wU 6 (tTl.held v t) i (g i) ∧
        ∀ L, g i = some L → FetchedIn wU 6 (tTl.held v t) L ((wU.block L).round - 1)) :=
  Reactive.ledger (Fin 4) ℕ (Finset ℕ) (Scheme.Params.mysticeti 4 1) wU tTl wT 0 1 4 2 0 6 6 1 1 3
    wRow.1 (fun h => absurd h (by decide)) wDisciplined wLive wTimed (by omega) (by omega)
    (by omega) wFetches (by omega) (fun b i hi => by
      show i + (3 - 1) < b + 3 - 1; omega)
    (fun k => ⟨k, le_rfl, fun _ _ => lead_mem _⟩) 0

end KPartialSparse

end LeanDagTest
