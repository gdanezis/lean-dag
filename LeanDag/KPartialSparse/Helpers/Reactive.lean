import LeanDag.KPartialSparse.Model.Reactive
import LeanDag.KPartialSparse.Helpers.Live
import LeanDag.KPartialDag.Helpers.Reactive
import LeanDag.KPartialSparse.Model.Order
/-!
# Sparse K-partial DAG — nodes in time, helpers

`docs/kpartial-sparse.md` §7. Holding a correct block grounds a quorum below
it (`quorumIn_of_held`); a quorum brings every node of `T` to its round
(`reachedBy_of_quorumIn`); no node of `T` skips a round of a run
(`builtBy_below`); leaders of `T` reach their voters and the votes of `T`
reach their claimers before the timeout (`leader_mem_held`, `certIn_held`);
so the run is synchronous (`syncFrom`), each round takes at most `δ + τ`, and
`δ + γ` when led by `T` (`builtBy_succ_slow`, `builtBy_succ_fast`), and a slot
led by `T` commits within `3δ + 2γ` (`nodeDecided_fast`).
-/

namespace LeanDag

namespace KPartialSparse

open KPartialDag (Crashes Timeline LiveRow)
open scoped KPartialDag
open Scheme

variable {Validator : Type*} [Fintype Validator] [DecidableEq Validator] [F : Faults Validator]
variable [Cr : Crashes Validator] [Ld : Leaders Validator]
variable {BlockId : Type*} [LinearOrder BlockId] {Payload : Type*} [ClaimFormat BlockId Payload]
variable [S : Slots Validator]
variable {U : SRecord Validator BlockId Payload} {tl : Timeline Validator BlockId}
variable {T : Finset Validator} {G δ τ γ R N : ℕ}

/-! ## Counting -/

omit [LinearOrder BlockId] [ClaimFormat BlockId Payload] S in
theorem creatorsOf_filter_mono {H H' : Finset BlockId} (hH : H ⊆ H') (p : BlockId → Prop)
    [DecidablePred p] : creatorsOf U.block (H.filter p) ⊆ creatorsOf U.block (H'.filter p) :=
  Finset.image_subset_image (Finset.filter_subset_filter _ hH)

omit [LinearOrder BlockId] [ClaimFormat BlockId Payload] S in
theorem quorumIn_mono {H H' : Finset BlockId} (hH : H ⊆ H') {r : ℕ} (h : QuorumIn U H r) :
    QuorumIn U H' r :=
  le_trans h (Finset.card_le_card (creatorsOf_filter_mono hH _))

omit [ClaimFormat BlockId Payload] S in
theorem certIn_mono {H H' : Finset BlockId} (hH : H ⊆ H') {r : ℕ} {L : BlockId}
    (h : CertIn U H r L) : CertIn U H' r L :=
  le_trans h (Finset.card_le_card (creatorsOf_filter_mono hH _))

omit [ClaimFormat BlockId Payload] in
/-- **What a node waits for grows with what it holds.** -/
theorem waitsFor_mono {H H' : Finset BlockId} (hH : H ⊆ H') {r : ℕ} (h : WaitsFor U H r) :
    WaitsFor U H' r := by
  obtain ⟨hq, hl, hc⟩ := h
  refine ⟨quorumIn_mono hH hq, fun k hk => ?_, fun k hk => ?_⟩
  · obtain ⟨L, hL, hlead⟩ := hl k hk
    exact ⟨L, hH hL, hlead⟩
  · obtain ⟨L, hlead, hcert⟩ := hc k hk
    exact ⟨L, hlead, certIn_mono hH hcert⟩

omit [LinearOrder BlockId] [ClaimFormat BlockId Payload] S in
/-- A set of blocks with a block by every validator of a quorum `T` reaches a
quorum. -/
theorem quorum_le_of_mem (hT : kQuorum Validator ≤ T.card) {X : Finset BlockId}
    (h : ∀ w ∈ T, ∃ y ∈ X, (U.block y).creator = w) :
    kQuorum Validator ≤ (creatorsOf U.block X).card :=
  le_trans hT (Finset.card_le_card fun w hw => by
    obtain ⟨y, hy, hyw⟩ := h w hw
    exact mem_creatorsOf.mpr ⟨y, hy, hyw⟩)

omit [LinearOrder BlockId] [ClaimFormat BlockId Payload] S in
/-- A set of blocks whose authors reach a quorum holds a block by a validator
of a quorum `T`. -/
theorem exists_mem_of_quorum (hT : kQuorum Validator ≤ T.card) {X : Finset BlockId}
    (h : kQuorum Validator ≤ (creatorsOf U.block X).card) :
    ∃ x ∈ X, (U.block x).creator ∈ T := by
  by_contra hno
  push Not at hno
  have hsub : creatorsOf U.block X ⊆ Finset.univ \ T := fun v hv => by
    obtain ⟨x, hx, rfl⟩ := mem_creatorsOf.mp hv
    exact Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, hno x hx⟩
  have := Finset.card_le_card hsub
  rw [Finset.card_univ_sdiff] at this
  have := Cr.card_validators
  omega

omit Ld [LinearOrder BlockId] [ClaimFormat BlockId Payload] S in
/-- `f + c + 1` validators include one of a quorum `T`. -/
theorem exists_mem_of_card (hT : kQuorum Validator ≤ T.card) {A : Finset Validator}
    (hA : F.f + Cr.c + 1 ≤ A.card) : ∃ v ∈ A, v ∈ T := by
  by_contra hno
  push Not at hno
  have := Finset.card_le_card fun v hv =>
    Finset.mem_sdiff.mpr ⟨Finset.mem_univ v, hno v hv⟩
  rw [Finset.card_univ_sdiff] at this
  have := F.card_validators
  omega

omit [LinearOrder BlockId] [ClaimFormat BlockId Payload] S in
/-- Blocks behind for `v` include a block of round `r + 1` by another author
of a quorum `T`. -/
theorem exists_mem_of_behindIn (hT : kQuorum Validator ≤ T.card) {H : Finset BlockId}
    {v : Validator} {r : ℕ} (h : BehindIn U H v r) :
    ∃ y ∈ H, (U.block y).round = r + 1 ∧ (U.block y).creator ∈ T ∧
      (U.block y).creator ≠ v := by
  obtain ⟨w, hw, hwT⟩ := exists_mem_of_card hT h
  obtain ⟨hwv, hw⟩ := Finset.mem_erase.mp hw
  obtain ⟨y, hy, hyw⟩ := mem_creatorsOf.mp hw
  obtain ⟨hyH, hyr⟩ := Finset.mem_filter.mp hy
  exact ⟨y, hyH, hyr, hyw ▸ hwT, hyw ▸ hwv⟩

omit [LinearOrder BlockId] [ClaimFormat BlockId Payload] S in
theorem reachedBy_mono {s t t' : ℕ} (hb : ReachedBy U tl T s t) (ht : t ≤ t') :
    ReachedBy U tl T s t' := fun v hv => by
  obtain ⟨b, hb, hbv, hbr, hbt⟩ := hb v hv
  exact ⟨b, hb, hbv, hbr, hbt.trans ht⟩

omit [LinearOrder BlockId] [ClaimFormat BlockId Payload] S in
theorem BuiltBy.reachedBy {s t : ℕ} (hb : BuiltBy U tl T s t) : ReachedBy U tl T s t :=
  fun v hv => by
    obtain ⟨b, hb, hbv, hbr, hbt⟩ := hb v hv
    exact ⟨b, hb, hbv, hbr.ge, hbt⟩

/-! ## The rules for nodes -/

namespace TimedRules

variable (h : TimedRules U tl T G δ τ γ R N)
include h

/-- A correct node holds each block it has built, from its disk. -/
theorem own (b : BlockId) (hb : b ∈ U.ids)
    (hbc : (U.block b).creator ∈ (Correct : Finset Validator)) (t : ℕ) (ht : tl.built b ≤ t) :
    b ∈ tl.held (U.block b).creator t :=
  h.disk_held _ hbc t (h.stores b hb hbc t ht)

/-- The rules for nodes hold from any later round. -/
theorem above {R' : ℕ} (hR : R ≤ R') : TimedRules U tl T G δ τ γ R' N :=
  { h with
    grounded := fun v hv t b hb hbc hb' => h.grounded v hv t b hb hbc (by omega)
    waits := fun b hb hbc r hbr hr => h.waits b hb hbc r hbr (hR.trans hr)
    prompt := fun v hv r t hr hrN hw => h.prompt v hv r t (hR.trans hr) hrN hw }

/-- From `G` on, a correct block that a node of `T` holds at `t₀` is held by
every node of `T` from `t₀ + δ` on. -/
theorem mem_held_of_held {u : Validator} (hu : u ∈ T) {t₀ t : ℕ}
    (hG : G ≤ t₀) {b : BlockId} (hb : b ∈ tl.held u t₀)
    (hbc : (U.block b).creator ∈ (Correct : Finset Validator))
    {v : Validator} (hv : v ∈ T) (ht : t₀ + δ ≤ t) : b ∈ tl.held v t :=
  h.mono v hv _ _ (by omega) ht (h.delivers u hu t₀ hG b hb hbc v hv)

/-- **Holding a correct block grounds a quorum below it**: a correct node that
holds a correct block above round `k ≥ R` holds a quorum at round `k`. -/
theorem quorumIn_of_held {v : Validator} (hv : v ∈ (Correct : Finset Validator)) {t k : ℕ}
    (hk : R ≤ k) {y : BlockId} (hy : y ∈ tl.held v t)
    (hyc : (U.block y).creator ∈ (Correct : Finset Validator))
    (hky : k < (U.block y).round) : QuorumIn U (tl.held v t) k := by
  obtain ⟨m, hm⟩ : ∃ m, (U.block y).round = k + 1 + m := ⟨(U.block y).round - (k + 1), by omega⟩
  induction m generalizing y with
  | zero =>
    have := h.grounded v hv t y hy hyc (by omega)
    rwa [show (U.block y).round - 1 = k by omega] at this
  | succ m ih =>
    have hq := h.grounded v hv t y hy hyc (by omega)
    rw [show (U.block y).round - 1 = k + 1 + m by omega] at hq
    obtain ⟨z, hz, hzT⟩ := exists_mem_of_quorum h.large hq
    obtain ⟨hz, hzr⟩ := Finset.mem_filter.mp hz
    exact ih hz (h.stable hzT) (by omega) hzr

/-- A block of `T` at round `s + 1 > R` or above is built no earlier than a
block of `T` of round `s + 1`. -/
theorem exists_succ_built {e : BlockId} (he : e ∈ U.ids) (heT : (U.block e).creator ∈ T)
    {s : ℕ} (hs : R ≤ s) (hes : s + 1 ≤ (U.block e).round) : ∃ y ∈ U.ids,
      (U.block y).creator ∈ T ∧ (U.block y).round = s + 1 ∧ tl.built y ≤ tl.built e := by
  rcases Nat.eq_or_lt_of_le hes with heq | hlt
  · exact ⟨e, he, heT, heq.symm, le_rfl⟩
  have hec := h.stable heT
  obtain ⟨y, hy, hyT⟩ := exists_mem_of_quorum h.large
    (h.quorumIn_of_held hec (by omega) (h.own e he hec _ le_rfl) hec hlt)
  obtain ⟨hyH, hyr⟩ := Finset.mem_filter.mp hy
  exact ⟨y, h.held_ids _ _ hyH, hyT, hyr, h.causal _ hec _ y hyH (h.stable hyT)⟩

/-- Once every validator of `T` has reached round `s ≥ R` by a time `t ≥ G`,
every node of `T` holds a quorum at round `s` by `t + δ`. -/
theorem quorumIn_of_reachedBy {s t : ℕ} (hs : R ≤ s) (hG : G ≤ t)
    (hb : ReachedBy U tl T s t) {v : Validator} (hv : v ∈ T) :
    QuorumIn U (tl.held v (t + δ)) s := by
  by_cases habove : ∃ y ∈ tl.held v (t + δ),
      (U.block y).creator ∈ (Correct : Finset Validator) ∧ s < (U.block y).round
  · obtain ⟨y, hy, hyc, hys⟩ := habove
    exact h.quorumIn_of_held (h.stable hv) hs hy hyc hys
  push Not at habove
  exact quorum_le_of_mem h.large fun w hw => by
    have hwc := h.stable hw
    obtain ⟨y, hy, hyw, hys, hyt⟩ := hb w hw
    have hyv := h.mem_held_of_held hw hG (h.own y hy (hyw ▸ hwc) _ hyt |> (hyw ▸ ·))
      (hyw ▸ hwc) hv le_rfl
    exact ⟨y, Finset.mem_filter.mpr ⟨hyv, le_antisymm (habove y hyv (hyw ▸ hwc)) hys⟩, hyw⟩

/-- A node of `T` that holds a quorum of round `r`, from `R` to below `N`, at a
time `t ≥ G` has built above round `r` by `t + τ`. -/
theorem built_of_quorumIn {v : Validator} (hv : v ∈ T) {r t : ℕ} (hr : R ≤ r) (hrN : r < N)
    (hG : G ≤ t) (hQ : QuorumIn U (tl.held v t) r) :
    ∃ b ∈ U.ids, (U.block b).creator = v ∧ r + 1 ≤ (U.block b).round ∧ tl.built b ≤ t + τ :=
  h.prompt v hv r _ hr hrN (Or.inr (Or.inl ⟨by omega, by rw [Nat.add_sub_cancel]; exact hQ⟩))

/-- A node of `T` that holds what it waits for above round `r`, from `R` to
below `N`, at a time `t ≥ G` has built above round `r` by `t + γ`. -/
theorem built_of_waitsFor {v : Validator} (hv : v ∈ T) {r t : ℕ} (hr : R ≤ r) (hrN : r < N)
    (hG : G ≤ t) (hW : WaitsFor U (tl.held v t) r) :
    ∃ b ∈ U.ids, (U.block b).creator = v ∧ r + 1 ≤ (U.block b).round ∧ tl.built b ≤ t + γ :=
  h.prompt v hv r _ hr hrN (Or.inl ⟨by omega, by rw [Nat.add_sub_cancel]; exact hW⟩)

/-- **Induction behind**: a property of the blocks of round `s + 1`, `s ≥ R`,
by authors of `T`, that holds for those built on the wait or the timer, and
passes to a block from a block of the round by an author of `T` that its
author holds, holds for every block of round `s + 1` by an author of `T`. -/
theorem induction_behind {s : ℕ} (hR : R ≤ s) (P : BlockId → Prop)
    (hwait : ∀ b ∈ U.ids, (U.block b).creator ∈ T → (U.block b).round = s + 1 →
      (γ ≤ tl.built b ∧ WaitsFor U (tl.held (U.block b).creator (tl.built b - γ)) s ∧
          WaitsFor U (tl.held (U.block b).creator (tl.built b)) s) ∨
        (τ ≤ tl.built b ∧ QuorumIn U (tl.held (U.block b).creator (tl.built b - τ)) s) → P b)
    (hstep : ∀ b ∈ U.ids, (U.block b).creator ∈ T → (U.block b).round = s + 1 →
      ∀ y ∈ tl.held (U.block b).creator (tl.built b), (U.block y).creator ∈ T →
      (U.block y).round = s + 1 → P y → P b)
    {b : BlockId} (hb : b ∈ U.ids) (hbT : (U.block b).creator ∈ T)
    (hbr : (U.block b).round = s + 1) : P b := by
  suffices ∀ n, ∀ b ∈ U.ids, (U.block b).creator ∈ T →
      (U.block b).round = s + 1 → tl.built b = n → P b from this _ b hb hbT hbr rfl
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro b hb hbT hbr hn
    rcases h.waits b hb (h.stable hbT) s hbr hR with hW | hW | hB
    · exact hwait b hb hbT hbr (Or.inl hW)
    · exact hwait b hb hbT hbr (Or.inr hW)
    · obtain ⟨y, hyH, hyr, hyT, hyv⟩ := exists_mem_of_behindIn h.large hB
      exact hstep b hb hbT hbr y hyH hyT hyr (ih _ (hn ▸ h.prior _ (h.stable hbT) _ y hyH
        (h.stable hyT) hyv) y (h.held_ids _ _ hyH) hyT hyr rfl)

/-- **Catching up**: once nodes of `T` hold, at a time `t ≥ G`, blocks of
round `s + 1`, from `R + 1` to `N`, by `f + c + 1` correct authors, every
validator of `T` has reached round `s + 1` by `t + δ`. -/
theorem reachedBy_of_behind {s t : ℕ} (hR : R ≤ s) (hN : s < N) (hG : G ≤ t)
    {A : Finset Validator} (hA : A ⊆ (Correct : Finset Validator))
    (hcard : F.f + Cr.c + 1 ≤ A.card)
    (hb : ∀ v ∈ A, ∃ u ∈ T, ∃ b ∈ tl.held u t,
      (U.block b).creator = v ∧ (U.block b).round = s + 1) :
    ReachedBy U tl T (s + 1) (t + δ) := by
  intro w hw
  by_cases hwA : w ∈ A
  · obtain ⟨u, hu, b, hb, hbw, hbr⟩ := hb w hwA
    exact ⟨b, h.held_ids _ _ hb, hbw, hbr.ge,
      (h.causal u (h.stable hu) t b hb (hbw ▸ hA hwA)).trans (by omega)⟩
  refine h.prompt w hw s _ hR hN (Or.inr (Or.inr ⟨by omega, le_trans hcard
    (Finset.card_le_card fun v hv => ?_)⟩))
  obtain ⟨u, hu, b, hb', hbv, hbr⟩ := hb v hv
  refine Finset.mem_erase.mpr ⟨fun hvw => hwA (hvw ▸ hv), mem_creatorsOf.mpr ⟨b,
    Finset.mem_filter.mpr ⟨h.mem_held_of_held hu hG hb' (hbv ▸ hA hv) hw le_rfl,
      hbr⟩, hbv⟩⟩

/-- **A quorum brings every node of `T` to its round**: once a node of `T`
holds, at a time `t ≥ G`, blocks of a quorum at round `s`, from `R + 1` to
`N`, every validator of `T` has reached round `s` by `t + δ`. -/
theorem reachedBy_of_quorumIn {s t : ℕ} (hR : R < s) (hN : s ≤ N) (hG : G ≤ t) {u : Validator}
    (hu : u ∈ T) (hQ : QuorumIn U (tl.held u t) s) : ReachedBy U tl T s (t + δ) := by
  obtain ⟨s, rfl⟩ : ∃ s', s = s' + 1 := ⟨s - 1, by omega⟩
  have hsplit := card_le_card_inter_correct_add_byzantine
    (creatorsOf U.block ((tl.held u t).filter fun b => (U.block b).round = s + 1))
  have := F.card_byzantine
  have := Cr.card_validators
  refine h.reachedBy_of_behind (by omega) (by omega) hG
    (A := creatorsOf U.block ((tl.held u t).filter fun b => (U.block b).round = s + 1) ∩
      (Correct : Finset Validator)) Finset.inter_subset_right
    (by unfold QuorumIn at hQ; omega) fun v hv => ?_
  obtain ⟨hvc, -⟩ := Finset.mem_inter.mp hv
  obtain ⟨x, hx, hxv⟩ := mem_creatorsOf.mp hvc
  obtain ⟨hxH, hxr⟩ := Finset.mem_filter.mp hx
  exact ⟨u, hu, x, hxH, hxv, hxr⟩

/-- **Every round up to `N` is reached, each within `δ + τ`** of a time from `G`
on. -/
theorem reachedBy_succ {s t : ℕ} (hs : R ≤ s) (hsN : s < N) (hG : G ≤ t)
    (hb : ReachedBy U tl T s t) : ReachedBy U tl T (s + 1) (t + δ + τ) := fun _ hv =>
  h.built_of_quorumIn hv hs hsN (by omega) (h.quorumIn_of_reachedBy hs hG hb hv)

/-- **Recovery**: once a validator of `T` has built at a round `r`, from
`R + 1` to `N`, by a time `t₀ ≥ G`, every validator of `T` reaches round `r`
by `t₀ + δ + τ`. Its author keeps its block of round `r` on disk. -/
theorem reachedBy_of_built {b : BlockId} (hb : b ∈ U.ids)
    (hbT : (U.block b).creator ∈ T) {t₀ : ℕ} (hG : G ≤ t₀) (hbt : tl.built b ≤ t₀)
    (hRb : R < (U.block b).round) (hbN : (U.block b).round ≤ N) :
    ReachedBy U tl T (U.block b).round (t₀ + δ + τ) := by
  intro w hw
  have hbc := h.stable hbT
  have hbw := h.mem_held_of_held hbT hG (h.own b hb hbc t₀ hbt) hbc hw le_rfl
  obtain ⟨b', hb', hb'w, hb'r, hb't⟩ := h.built_of_quorumIn hw (r := (U.block b).round - 1)
    (t := t₀ + δ) (by omega) (by omega) (by omega)
    (h.quorumIn_of_held (h.stable hw) (by omega) hbw hbc (by omega))
  exact ⟨b', hb', hb'w, by omega, hb't⟩

end TimedRules

/-! ## Starting a run -/

namespace TimedStarted

variable (h : TimedStarted U tl T G δ τ γ R N)
include h

/-- **A timed run starts after `G + τ`**: the round `R'` after the last round
from `R` on that a node of `T` reached before `G + τ`, or `R` if there is
none, starts a timed run, and every validator of `T` reaches it within
`2δ + 2τ` of `G + τ` and of the time all reached round `R`. -/
theorem exists_run : ∃ R', R ≤ R' ∧ (R' = R ∨ ∃ x ∈ U.ids,
    (U.block x).creator ∈ T ∧ (U.block x).round + 1 = R' ∧
      tl.built x < G + τ) ∧ (R' ≤ N → TimedRun U tl T G δ τ γ R' N ∧
    ∀ t₀, ReachedBy U tl T R t₀ → ReachedBy U tl T R' (max t₀ (G + τ) + 2 * δ + 2 * τ)) := by
  classical
  set X := U.ids.filter fun x => (U.block x).creator ∈ T ∧
    R ≤ (U.block x).round ∧ tl.built x < G + τ
  by_cases hX : X.Nonempty
  · obtain ⟨x, hxX, hmax⟩ := X.exists_max_image (fun x => (U.block x).round) hX
    obtain ⟨hx, hxc, hxR, hxt⟩ := Finset.mem_filter.mp hxX
    refine ⟨(U.block x).round + 1, by omega, Or.inr ⟨x, hx, hxc, rfl, hxt⟩, fun hN => ?_⟩
    have hbuilt : ∀ t₀, ReachedBy U tl T R t₀ →
        ReachedBy U tl T ((U.block x).round + 1) (max t₀ (G + τ) + 2 * δ + 2 * τ) := by
      intro t₀ ht₀
      have hm : ReachedBy U tl T (U.block x).round (max t₀ (G + τ) + δ + τ) := by
        rcases Nat.eq_or_lt_of_le hxR with heq | hlt
        · exact reachedBy_mono (heq ▸ ht₀) (by omega)
        exact reachedBy_mono (h.reachedBy_of_built hx hxc (t₀ := G + τ) (by omega) hxt.le hlt
          (by omega)) (by omega)
      exact reachedBy_mono (h.reachedBy_succ hxR (by omega) (by omega) hm) (by omega)
    obtain ⟨t₀, ht₀⟩ := h.start
    refine ⟨⟨⟨h.above (by omega), _, hbuilt t₀ ht₀⟩, fun b hb hbc hbr => ?_⟩, hbuilt⟩
    by_contra hlt
    have := hmax b (Finset.mem_filter.mpr ⟨hb, hbc, by omega, by omega⟩)
    omega
  · refine ⟨R, le_rfl, Or.inl rfl, fun _ => ⟨⟨h, fun b hb hbc hbr => ?_⟩,
      fun t₀ ht₀ => reachedBy_mono ht₀ (by omega)⟩⟩
    by_contra hlt
    exact hX ⟨b, Finset.mem_filter.mpr ⟨hb, hbc, hbr, by omega⟩⟩

end TimedStarted

namespace TimedRules

variable (h : TimedRules U tl T G δ τ γ R N)
include h

/-- **Operations resume**: once a validator of `T` has built above round `R` by
`G`, a timed run starts above `R`, and every validator of `T` reaches it
within `3δ + 3τ` of `G`. -/
theorem exists_resumed {b : BlockId} (hb : b ∈ U.ids)
    (hbc : (U.block b).creator ∈ T) (hbG : tl.built b ≤ G)
    (hRb : R < (U.block b).round) :
    ∃ R', R < R' ∧ (R' ≤ N → TimedRun U tl T G δ τ γ R' N ∧
      ReachedBy U tl T R' (G + 3 * δ + 3 * τ)) := by
  by_cases hbN : (U.block b).round ≤ N
  · have hr := h.reachedBy_of_built hb hbc le_rfl hbG hRb hbN
    have hstart : TimedStarted U tl T G δ τ γ (U.block b).round N := ⟨h.above hRb.le, _, hr⟩
    obtain ⟨R', hR', -, hrun⟩ := hstart.exists_run
    refine ⟨R', by omega, fun hR'N => ⟨(hrun hR'N).1, reachedBy_mono ((hrun hR'N).2 _ hr) ?_⟩⟩
    omega
  · exact ⟨_, hRb, fun h' => absurd h' hbN⟩

end TimedRules

omit [ClaimFormat BlockId Payload] S in
/-- **Nothing the sub-DAG holds is lost**: when correct nodes keep windows on
disk, every block of the available sub-DAG below a block with votes from
`f + c + 1` distinct authors is on the disk of a node of a quorum `T` of
correct nodes from some time on, through any crash. Its voters, or the
`f + c + 1` authors reaching an anchor point, include a node of `T`. -/
theorem exists_disk_of_avail (hT : T ⊆ (Correct : Finset Validator))
    (hTq : kQuorum Validator ≤ T.card) {K : ℕ} (hK : KeepsHistory U tl K)
    {A z : BlockId} (hA : A ∈ U.ids)
    (hV : F.f + Cr.c + 1 ≤ (supporters U A ((U.block A).round + 1)).card)
    (hz : z ∈ Avail U K A) : ∃ w ∈ T, ∃ t₀, ∀ t, t₀ ≤ t → z ∈ tl.disk w t := by
  obtain ⟨y, d, hy, hzy⟩ := hz
  cases hy with
  | anchor =>
    obtain ⟨c, hc, hcT⟩ := exists_mem_of_card hTq hV
    obtain ⟨b, hbi, -, hbA, rfl⟩ := mem_supporters.mp hc
    exact ⟨_, hcT, _, fun t ht => hK b hbi (hT hcT) t ht A hbA hzy⟩
  | reached i S m yf df yf' df' hyf hzf hyf' hmz hi hm hcard =>
    obtain ⟨c, hc, hcT⟩ := exists_mem_of_card hTq hcard
    obtain ⟨w, hw, rfl⟩ := mem_creatorsOf.mp hc
    have hwi : w ∈ U.ids := window_subset_ids _ ((hyf w hw).mem hA) (hzf w hw)
    have hzm := window_trans (hm w hw).2.1 hzy
    rw [show i + (K - i) = K by omega] at hzm
    exact ⟨_, hcT, _, fun t ht => hK w hwi (hT hcT) t ht (m w) (hm w hw).1 hzm⟩

/-! ## Block shape and chains -/

omit [ClaimFormat BlockId Payload] S [LinearOrder BlockId] in
/-- **Building above the disk keeps chains**: a correct block referencing a block
of its own at or above each block its author built before it, by an author
that builds above its disk, references one at or above each earlier-round
block of its author. -/
theorem chains_of_selfRef (hids : ∀ b ∈ U.ids, (U.block b).creator ∈ (Correct : Finset Validator) →
      ∀ x ∈ U.ids, (U.block x).creator = (U.block b).creator → tl.built x < tl.built b →
      ∃ s ∈ (U.block b).refs, (U.block s).creator = (U.block b).creator ∧
        (U.block x).round ≤ (U.block s).round)
    (hd : KPartialDag.BuildsAboveDisk U.ids U.block tl) : Chains U := by
  intro y hy hyc x hx hxy hlt
  refine hids y hy hyc x hx hxy ?_
  by_contra hge
  push Not at hge
  rcases Nat.eq_or_lt_of_le hge with heq | hlt'
  · have := hd.single y hy x hx hyc hxy.symm heq
    subst this; omega
  · have := hd.round_lt hy hx hyc hxy hlt'
    omega

omit [ClaimFormat BlockId Payload] S [LinearOrder BlockId] in
/-- **A dense block can be built** from the correct blocks one round below that a
node holds, when they come from a quorum of distinct authors. -/
theorem exists_dense_block {H : Finset BlockId} (hH : H ⊆ U.ids) {r : ℕ}
    (hq : kQuorum Validator ≤ (creatorsOf U.block (H.filter fun x =>
      (U.block x).creator ∈ (Correct : Finset Validator) ∧ (U.block x).round = r)).card)
    (v : Validator) (pay : Payload) :
    ∃ b : Block Validator BlockId Payload, b.creator = v ∧ b.round = r + 1 ∧ b.refs ⊆ H ∧
      SValid Validator BlockId Payload U.block b := by
  classical
  set X := H.filter fun x =>
    (U.block x).creator ∈ (Correct : Finset Validator) ∧ (U.block x).round = r
  have hX : ∀ x ∈ X, x ∈ U.ids ∧ (U.block x).creator ∈ (Correct : Finset Validator) ∧
      (U.block x).round = r := fun x hx => by
    obtain ⟨hxH, hxc, hxr⟩ := Finset.mem_filter.mp hx
    exact ⟨hH hxH, hxc, hxr⟩
  have hdense : Dense (kQuorum Validator) U.block ⟨r + 1, v, X, pay⟩ := by
    unfold Dense below1
    have : X.filter (fun i => (U.block i).round + 1 = r + 1) = X :=
      Finset.filter_true_of_mem fun x hx => by rw [(hX x hx).2.2]
    simp only at this ⊢
    rw [this]; exact hq
  refine ⟨⟨r + 1, v, X, pay⟩, rfl, rfl, Finset.filter_subset _ _, ?_, ?_, ?_, ?_, ?_⟩
  · intro i hi; have := (hX i hi).2.2; simp only; omega
  · intro i hi _; have := (hX i hi).2.2; simp only; omega
  · intro i hi j hj hij
    exact U.no_equivocation i (hX i hi).1 j (hX j hj).1 (hX i hi).2.1 hij
      ((hX i hi).2.2.trans (hX j hj).2.2.symm)
  · exact fun _ => Or.inl hdense
  · exact fun _ _ => hdense

omit [ClaimFormat BlockId Payload] S in
/-- **A sparse block can be built** by a correct node that is not a leader of the
round above, holding its own block one round below and a leader block there
of a correct leader: it references its own block and the correct leaders'
blocks it holds. -/
theorem exists_sparse_block {H : Finset BlockId} (hH : H ⊆ U.ids) {r : ℕ} {v : Validator}
    (hv : v ∈ (Correct : Finset Validator)) (hvl : v ∉ Ld.leaders (r + 1)) {o : BlockId}
    (ho : o ∈ H) (hoc : (U.block o).creator = v) (hor : (U.block o).round = r) {L₀ : BlockId}
    (hL₀ : L₀ ∈ H) (hL₀c : (U.block L₀).creator ∈ (Correct : Finset Validator))
    (hL₀l : (U.block L₀).creator ∈ Ld.leaders r) (hL₀r : (U.block L₀).round = r)
    (pay : Payload) :
    ∃ b : Block Validator BlockId Payload, b.creator = v ∧ b.round = r + 1 ∧ b.refs ⊆ H ∧
      SValid Validator BlockId Payload U.block b := by
  classical
  set X := insert o (H.filter fun x => (U.block x).creator ∈ (Correct : Finset Validator) ∧
    (U.block x).round = r ∧ (U.block x).creator ∈ Ld.leaders r)
  have hX : ∀ x ∈ X, x ∈ U.ids ∧ (U.block x).creator ∈ (Correct : Finset Validator) ∧
      (U.block x).round = r ∧ ((U.block x).creator = v ∨ (U.block x).creator ∈ Ld.leaders r) :=
    fun x hx => by
      rcases Finset.mem_insert.mp hx with rfl | hx
      · exact ⟨hH ho, hoc ▸ hv, hor, Or.inl hoc⟩
      · obtain ⟨hxH, hxc, hxr, hxl⟩ := Finset.mem_filter.mp hx
        exact ⟨hH hxH, hxc, hxr, Or.inr hxl⟩
  have hsub : X ⊆ H := Finset.insert_subset ho (Finset.filter_subset _ _)
  refine ⟨⟨r + 1, v, X, pay⟩, rfl, rfl, hsub, ?_, ?_, ?_, ?_, ?_⟩
  · intro i hi; have := (hX i hi).2.2.1; simp only; omega
  · intro i hi _; have := (hX i hi).2.2.1; simp only; omega
  · intro i hi j hj hij
    exact U.no_equivocation i (hX i hi).1 j (hX j hj).1 (hX i hi).2.1 hij
      ((hX i hi).2.2.1.trans (hX j hj).2.2.1.symm)
  · intro _
    right
    refine ⟨⟨o, Finset.mem_insert_self _ _, hoc, by simp only; omega⟩, fun i hi hic => ?_,
      ⟨L₀, Finset.mem_insert_of_mem (Finset.mem_filter.mpr ⟨hL₀, hL₀c, hL₀r, hL₀l⟩),
        by simp only; omega, by simp only; rw [show r + 1 - 1 = r by omega]; exact hL₀l⟩⟩
    obtain ⟨-, -, hir, hil⟩ := hX i hi
    refine ⟨by simp only; omega, ?_⟩
    simp only [show r + 1 - 1 = r by omega]
    exact hil.resolve_left hic
  · intro _ hl; exact absurd hl hvl

/-! ## Committed leaders are certified -/

/-- **A leader a node commits is certified**, at a row, on a disciplined record,
when a two-round row links by `f + c + 1` votes or more: at the certificate
threshold in a three-round row, and by `f + c + 1` voters in every row. -/
theorem NodeDecided.certified {p : Params} (hrow : Row Validator p)
    (hlink : p.voteIsCert = true → F.f + Cr.c + 1 ≤ p.linkSize) {K : ℕ}
    (hI : Disciplined K p.certThreshold S U) {H : Finset BlockId} (hH : H ⊆ U.ids) {j : ℕ}
    {A : BlockId} (h : NodeDecided p U K H j (some A)) :
    (p.voteIsCert = false → Certified U p.certThreshold A) ∧
      F.f + Cr.c + 1 ≤ (supporters U A ((U.block A).round + 1)).card := by
  have ha := row_arith hrow
  have hn := Cr.card_validators
  suffices key : ∀ j v, NodeDecided p U K H j v → ∀ A, v = some A →
      (p.voteIsCert = false → Certified U p.certThreshold A) ∧
        F.f + Cr.c + 1 ≤ (supporters U A ((U.block A).round + 1)).card from key j _ h A rfl
  intro j v h
  induction h with
  | @directCommit k L hL hc =>
    intro A hA
    cases hA
    have hc' : p.commitThreshold ≤ (creatorsOf U.block (certsFor p U L (S.slotRound k))).card :=
      hc.trans (Finset.card_le_card (Finset.image_subset_image (Finset.filter_subset _ _)))
    have hcert := certified_of_commit hrow hI.2.2.2 hL.2.1 hc'
    unfold Certified at hcert
    refine ⟨fun hv => by unfold Certified; simpa [commitStrength, hv] using hcert, ?_⟩
    have : F.f + Cr.c + 1 ≤ commitStrength p := by omega
    omega
  | directSkip _ => intro A hA; cases hA
  | @indirectCommit k j' A₀ L hkj helig hj hmid hf hL hlink' hleast ihj ihm =>
    intro A hA
    cases hA
    have hanc : p.voteIsCert = true ∨ Certified U p.certThreshold A₀ := by
      cases hv : p.voteIsCert
      · exact Or.inr ((ihj A₀ rfl).1 hv)
      · exact Or.inl rfl
    have hcert := certified_of_link hrow hI.2.2.1 hanc hL.2.1 (linkedIn_certLinked hH hlink')
    unfold Certified at hcert
    refine ⟨fun hv => by unfold Certified; simpa [linkStrength, hv] using hcert, ?_⟩
    have : F.f + Cr.c + 1 ≤ linkStrength p := by
      cases hv : p.voteIsCert
      · have := ha.1; simp only [commitStrength, linkStrength, hv, Bool.false_eq_true,
          if_false] at this ⊢; omega
      · simp only [linkStrength, hv, if_true]; exact hlink hv
    omega
  | indirectSkip _ _ _ _ _ _ => intro A hA; cases hA

/-! ## Checked claims -/

omit S in
/-- **Timed nodes meet the claim disciplines**: correct nodes that reference only
referenceable blocks and claim only what they back, on what they hold, check
and claim truthfully on the record. -/
theorem buildsChecked_of_timed {K t : ℕ} (hids : ∀ v s, tl.held v s ⊆ U.ids)
    (h : TimedChecks U tl K t) : BuildsChecked U K t :=
  fun z hz hzc => ⟨_, hids _ _, h.claims_backed z hz hzc, fun m hm => h.refs_checked z hz hzc m hm⟩

omit S in
/-- **The wait never blocks a correct block**: a correct node holding a correct
block holds it referenceable, since it holds the evidence its author held for
each reference, and backs its own claims. -/
theorem referenceable_of_held {K t : ℕ} (hids : ∀ v s, tl.held v s ⊆ U.ids)
    (h : TimedChecks U tl K t) {v : Validator}
    (hv : v ∈ (Correct : Finset Validator)) {s : ℕ} {b : BlockId} (hb : b ∈ tl.held v s)
    (hbc : (U.block b).creator ∈ (Correct : Finset Validator)) :
    Referenceable U K t (tl.held v s) b := by
  rcases Nat.eq_zero_or_pos K with rfl | hK
  · refine ⟨fun w hw => ?_, fun X hX L hL => ?_⟩
    · rw [mem_window_zero hw]; exact hb
    · obtain rfl := mem_window_zero hX
      exact h.carries_claims v hv s X hb hbc L hL
  obtain ⟨k, rfl⟩ : ∃ k, K = k + 1 := ⟨K - 1, by omega⟩
  have hbi : b ∈ U.ids := hids v s hb
  have hin : ∀ m ∈ (U.block b).refs, ∀ {w : BlockId},
      w ∈ windowFrom U.block k ((U.block b).round - (k + 1)) m → w ∈ window U (k + 1) m :=
    fun m hm w hw => by
      have := (U.valid b hbi).below m hm
      exact windowFrom_mono (by omega) (by omega) m hw
  refine ⟨fun w hw => ?_, fun X hX L hL => ?_⟩
  · rcases mem_windowFrom_succ.mp hw with rfl | ⟨m, hm, -, hwm⟩
    · exact hb
    · exact (h.carries v hv s b hb hbc m hm).1 (hin m hm hwm)
  · rcases mem_windowFrom_succ.mp hX with rfl | ⟨m, hm, -, hXm⟩
    · exact h.carries_claims v hv s X hb hbc L hL
    · exact (h.carries v hv s b hb hbc m hm).2 X (hin m hm hXm) L hL

omit [ClaimFormat BlockId Payload] S in
/-- **Votes from a quorum back a claim**: holding a block and votes for it from a
quorum one round above backs a claim for it at any threshold within the
quorum. -/
theorem backs_of_certIn {H : Finset BlockId} {L : BlockId} {t : ℕ}
    (ht : t ≤ kQuorum Validator) (hL : L ∈ H) (h : CertIn U H ((U.block L).round + 1) L) :
    Backs U t H L :=
  ⟨hL, ht.trans h⟩

/-! ## A timed run -/

namespace TimedRun

variable (h : TimedRun U tl T G δ τ γ R N)
include h

/-- Every round from `R` to `N` is reached by some time. -/
theorem exists_reachedBy {s : ℕ} (hs : R ≤ s) (hsN : s ≤ N) : ∃ t, ReachedBy U tl T s t := by
  induction s, hs using Nat.le_induction with
  | base => exact h.start
  | succ s hs ih =>
    obtain ⟨t, ht⟩ := ih (by omega)
    exact ⟨_, h.reachedBy_succ hs (by omega) (le_max_right t G)
      (reachedBy_mono ht (le_max_left t G))⟩

/-- Every validator of `T` has reached a round from `R` on only at `G + τ` or
later. -/
theorem le_of_reachedBy {s t : ℕ} (hs : R ≤ s) (hb : ReachedBy U tl T s t) : G + τ ≤ t := by
  obtain ⟨v, hv⟩ := Finset.card_pos.mp
    (by have := h.large; have := Cr.card_validators; omega : 0 < T.card)
  obtain ⟨b, hb, hbv, hbr, hbt⟩ := hb v hv
  have := h.late b hb (hbv ▸ hv) (by omega)
  omega

/-- A block of `T` from round `R` on, built by `t₀`, is held by every node of
`T` from `t₀ + δ` on. -/
theorem mem_held_of_round {b : BlockId} (hb : b ∈ U.ids)
    (hbc : (U.block b).creator ∈ T) (hbR : R ≤ (U.block b).round)
    {v : Validator} (hv : v ∈ T) {t₀ t : ℕ}
    (h0 : tl.built b ≤ t₀) (ht : t₀ + δ ≤ t) : b ∈ tl.held v t :=
  h.mem_held_of_held hbc (by have := h.late b hb hbc hbR; omega)
    (h.own b hb (h.stable hbc) _ le_rfl) (h.stable hbc) hv (by omega)

/-- **No node of `T` skips a round of the run**, at `δ < γ ≤ τ`: by the time a
block of `T` of round `s + 1`, `s` from `R + 1` to `N`, is built, every
validator of `T` has built at round `s`. -/
theorem builtBy_below (hδ : δ < γ) (hγτ : γ ≤ τ) {s : ℕ} (hs : R + 1 ≤ s) (hsN : s ≤ N)
    {c : BlockId} (hc : c ∈ U.ids) (hcT : (U.block c).creator ∈ T)
    (hcr : (U.block c).round = s + 1) : BuiltBy U tl T s (tl.built c) := by
  suffices ∀ n, ∀ c ∈ U.ids, (U.block c).creator ∈ T →
      (U.block c).round = s + 1 → tl.built c = n → BuiltBy U tl T s n from
    this _ c hc hcT hcr rfl
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro c hc hcT hcr hn x hx
    have hcc := h.stable hcT
    have hxc := h.stable hx
    have hup : ∀ e ∈ U.ids, (U.block e).creator = x → s ≤ (U.block e).round →
        tl.built e < n →
        ∃ z ∈ U.ids, (U.block z).creator = x ∧ (U.block z).round = s ∧ tl.built z ≤ n := by
      intro e he hex hes hen
      rcases Nat.eq_or_lt_of_le hes with heq | hlt
      · exact ⟨e, he, hex, heq.symm, hen.le⟩
      obtain ⟨y, hy, hyT, hyr, hyt⟩ := h.exists_succ_built he (hex ▸ hx) (by omega) hlt
      obtain ⟨z, hz, hzx, hzr, hzt⟩ := ih _ (by omega) y hy hyT hyr rfl _ hx
      exact ⟨z, hz, hzx, hzr, by omega⟩
    have hquorum : ∀ t₁, G ≤ t₁ → t₁ + δ < n →
        QuorumIn U (tl.held (U.block c).creator t₁) s →
        ∃ z ∈ U.ids, (U.block z).creator = x ∧ (U.block z).round = s ∧ tl.built z ≤ n := by
      intro t₁ hG ht₁ hQ
      obtain ⟨e, he, hex, hes, het⟩ := h.reachedBy_of_quorumIn (by omega) hsN hG hcT hQ x hx
      exact hup e he hex hes (by omega)
    have hlc := h.late c hc hcT (by omega)
    rcases h.waits c hc hcc s hcr (by omega) with ⟨-, hW, -⟩ | ⟨-, hQ⟩ | hB
    · exact hquorum _ (by omega) (by omega) hW.1
    · exact hquorum _ (by omega) (by omega) hQ
    · obtain ⟨y, hyH, hyr, hyT, hyv⟩ := exists_mem_of_behindIn h.large hB
      have hyt := h.prior _ hcc _ y hyH (h.stable hyT) hyv
      obtain ⟨z, hz, hzx, hzr, hzt⟩ := ih _ (by omega) y (h.held_ids _ _ hyH) hyT hyr rfl x hx
      exact ⟨z, hz, hzx, hzr, by omega⟩

/-- **Exact rounds in the run**, at `δ < γ ≤ τ`: once every validator of `T`
has reached round `s`, from `R + 1` to `N`, by `t`, every validator of `T` has
built at round `s` by `t`. -/
theorem builtBy_of_reachedBy (hδ : δ < γ) (hγτ : γ ≤ τ) {s t : ℕ} (hs : R + 1 ≤ s)
    (hsN : s ≤ N) (hb : ReachedBy U tl T s t) : BuiltBy U tl T s t := by
  intro x hx
  obtain ⟨e, he, hex, hes, het⟩ := hb x hx
  rcases Nat.eq_or_lt_of_le hes with heq | hlt
  · exact ⟨e, he, hex, heq.symm, het⟩
  obtain ⟨y, hy, hyT, hyr, hyt⟩ := h.exists_succ_built he (hex ▸ hx) (by omega) hlt
  obtain ⟨z, hz, hzx, hzr, hzt⟩ := h.builtBy_below hδ hγτ hs hsN hy hyT hyr _ hx
  exact ⟨z, hz, hzx, hzr, by omega⟩

/-- **Each round within `δ + τ`**, at `δ < γ ≤ τ`: once every validator of `T`
has reached round `s`, from `R` to below `N`, by `t`, every validator of `T`
has built at round `s + 1` by `t + δ + τ`. -/
theorem builtBy_succ_slow (hδ : δ < γ) (hγτ : γ ≤ τ) {s t : ℕ} (hs : R ≤ s) (hsN : s < N)
    (hb : ReachedBy U tl T s t) : BuiltBy U tl T (s + 1) (t + δ + τ) :=
  h.builtBy_of_reachedBy hδ hγτ (by omega) (by omega)
    (h.reachedBy_succ hs hsN (h.le_of_reachedBy hs hb |>.trans' (by omega)) hb)

/-- **A leader of `T` reaches every voter of `T` before its timeout**, at
`τ ≥ 2δ` and `δ < γ ≤ τ`: a block of `T` one round above a slot led by a
validator of `T`, from round `R + 1` on, is built once its author holds a
leader block of the slot. -/
theorem leader_mem_held (hτ : 2 * δ ≤ τ) (hδ : δ < γ) (hγτ : γ ≤ τ) {k : ℕ}
    (hk : R + 1 ≤ S.slotRound k) (hN : S.slotRound k + 1 ≤ N) (hlead : S.leader k ∈ T)
    {b : BlockId} (hb : b ∈ U.ids) (hbT : (U.block b).creator ∈ T)
    (hbr : (U.block b).round = S.slotRound k + 1) :
    ∃ L ∈ tl.held (U.block b).creator (tl.built b), IsLeaderBlock U k L := by
  refine h.induction_behind (by omega)
    (fun b => ∃ L ∈ tl.held (U.block b).creator (tl.built b), IsLeaderBlock U k L)
    (fun b hb hbT hbr hW => ?_) (fun b hb hbT hbr y hyH hyT hyr hy => ?_) hb hbT hbr
  · rcases hW with ⟨-, -, hW⟩ | ⟨hτb, hQ⟩
    · exact hW.2.1 k rfl
    have hlb := h.late b hb hbT (by omega)
    obtain ⟨L, hL, hLc, hLr, hLt⟩ := h.builtBy_of_reachedBy hδ hγτ hk (by omega)
      (h.reachedBy_of_quorumIn (t := tl.built b - τ) (by omega) (by omega) (by omega) hbT hQ)
      _ hlead
    exact ⟨L, h.mem_held_of_round hL (hLc ▸ hlead) (by omega) hbT hLt (by omega), hL, by omega,
      hLc⟩
  · obtain ⟨L, hL, hlead'⟩ :=
      h.votes y (h.held_ids _ _ hyH) (h.stable hyT) k (h.stable hlead) (by omega) hy
    exact ⟨L, h.closed _ (h.stable hbT) _ y hyH (h.stable hyT) hL, hlead'⟩

/-- **Every voter of `T` votes for a leader of `T`**: a block of `T` one round
above a slot led by a validator of `T`, from round `R + 1` on, references the
slot's leader block. -/
theorem mem_refs_of_leader (hτ : 2 * δ ≤ τ) (hδ : δ < γ) (hγτ : γ ≤ τ) {k : ℕ}
    (hk : R + 1 ≤ S.slotRound k) (hN : S.slotRound k + 1 ≤ N) (hlead : S.leader k ∈ T)
    {b : BlockId} (hb : b ∈ U.ids) (hbT : (U.block b).creator ∈ T)
    (hbr : (U.block b).round = S.slotRound k + 1) {L : BlockId} (hL : IsLeaderBlock U k L) :
    L ∈ (U.block b).refs := by
  obtain ⟨L', hL', hlead'⟩ := h.votes b hb (h.stable hbT) k (h.stable hlead) hbr.symm
    (h.leader_mem_held hτ hδ hγτ hk hN hlead hb hbT hbr)
  exact isLeaderBlock_unique_of_honest (h.stable hlead) hL hlead' ▸ hL'

/-- **The votes of `T` certify a leader of `T`**, at `τ ≥ 2δ` and `δ < γ ≤ τ`:
once every validator of `T` has built one round above a slot led by a
validator of `T`, from round `R + 1` on, by `t`, every node of `T` holds votes
from a quorum for the slot's leader block from `t + δ` on. -/
theorem certIn_of_builtBy (hτ : 2 * δ ≤ τ) (hδ : δ < γ) (hγτ : γ ≤ τ) {k t t' : ℕ}
    (hk : R + 1 ≤ S.slotRound k) (hN : S.slotRound k + 1 ≤ N) (hlead : S.leader k ∈ T)
    (hB : BuiltBy U tl T (S.slotRound k + 1) t) {v : Validator} (hv : v ∈ T)
    (ht : t + δ ≤ t') :
    ∃ L, IsLeaderBlock U k L ∧ CertIn U (tl.held v t') (S.slotRound k + 1) L := by
  obtain ⟨x, hx, hxl, hxr, -⟩ := hB _ hlead
  obtain ⟨L, -, hL⟩ := h.leader_mem_held hτ hδ hγτ hk hN hlead hx (hxl ▸ hlead) hxr
  refine ⟨L, hL, quorum_le_of_mem h.large fun w hw => ?_⟩
  obtain ⟨y, hy, hyw, hyr, hyt⟩ := hB w hw
  have hyT : (U.block y).creator ∈ T := hyw ▸ hw
  exact ⟨y, Finset.mem_filter.mpr ⟨h.mem_held_of_round hy hyT (by omega) hv hyt ht, hyr,
    h.mem_refs_of_leader hτ hδ hγτ hk hN hlead hy hyT hyr hL⟩, hyw⟩

/-- **The votes of `T` reach every claimer of `T` before its timeout**, at
`τ ≥ 2δ` and `δ < γ ≤ τ`: a block of `T` two rounds above a slot led by a
validator of `T`, from round `R + 1` on, is built once its author holds votes
from a quorum for the slot's leader block. -/
theorem certIn_held (hτ : 2 * δ ≤ τ) (hδ : δ < γ) (hγτ : γ ≤ τ) {k : ℕ}
    (hk : R + 1 ≤ S.slotRound k) (hN : S.slotRound k + 2 ≤ N) (hlead : S.leader k ∈ T)
    {c : BlockId} (hc : c ∈ U.ids) (hcT : (U.block c).creator ∈ T)
    (hcr : (U.block c).round = S.slotRound k + 2) :
    ∃ L, IsLeaderBlock U k L ∧
      CertIn U (tl.held (U.block c).creator (tl.built c)) (S.slotRound k + 1) L := by
  refine h.induction_behind (s := S.slotRound k + 1) (by omega)
    (fun c => ∃ L, IsLeaderBlock U k L ∧
      CertIn U (tl.held (U.block c).creator (tl.built c)) (S.slotRound k + 1) L)
    (fun c hc hcT hcr hW => ?_) (fun c hc hcT hcr y hyH hyT hyr hy => ?_) hc hcT
    (by omega)
  · rcases hW with ⟨-, -, hW⟩ | ⟨hτc, hQ⟩
    · exact hW.2.2 k rfl
    have hlc := h.late c hc hcT (by omega)
    exact h.certIn_of_builtBy hτ hδ hγτ hk (by omega) hlead (h.builtBy_of_reachedBy hδ hγτ
      (by omega) (by omega) (h.reachedBy_of_quorumIn (t := tl.built c - τ) (by omega)
        (by omega) (by omega) hcT hQ)) hcT (by omega)
  · obtain ⟨L, hL, hcert⟩ := hy
    have hyc : L ∈ claimsOf U y :=
      h.claims y (h.held_ids _ _ hyH) (h.stable hyT) k (by omega) L hL hcert
    have := h.backed _ (h.stable hcT) _ y hyH (h.stable hyT) L hyc
    rw [hL.2.1] at this
    exact ⟨L, hL, this⟩

/-- **Every claimer of `T` claims a leader of `T`**: a block of `T` two rounds
above a slot led by a validator of `T`, from round `R + 1` on, claims the
slot's leader block. -/
theorem mem_claims_of_leader (hτ : 2 * δ ≤ τ) (hδ : δ < γ) (hγτ : γ ≤ τ) {k : ℕ}
    (hk : R + 1 ≤ S.slotRound k) (hN : S.slotRound k + 2 ≤ N) (hlead : S.leader k ∈ T)
    {c : BlockId} (hc : c ∈ U.ids) (hcT : (U.block c).creator ∈ T)
    (hcr : (U.block c).round = S.slotRound k + 2) {L : BlockId} (hL : IsLeaderBlock U k L) :
    L ∈ claimsOf U c := by
  obtain ⟨L', hL', hcert⟩ := h.certIn_held hτ hδ hγτ hk hN hlead hc hcT hcr
  obtain rfl := isLeaderBlock_unique_of_honest (h.stable hlead) hL hL'
  exact h.claims c hc (h.stable hcT) k hcr.symm L hL hcert

/-- **Every claimer of `T` backs its claim for a leader of `T`**, at `τ ≥ 2δ`,
`δ < γ ≤ τ` and a threshold within the quorum: when it builds two rounds above
a slot led by a validator of `T`, from round `R + 1` on, its author holds the
slot's leader block and votes for it from a quorum. -/
theorem backs_of_leader (hτ : 2 * δ ≤ τ) (hδ : δ < γ) (hγτ : γ ≤ τ) {k t : ℕ}
    (ht : t ≤ kQuorum Validator) (hk : R + 1 ≤ S.slotRound k) (hN : S.slotRound k + 2 ≤ N)
    (hlead : S.leader k ∈ T) {c : BlockId} (hc : c ∈ U.ids) (hcT : (U.block c).creator ∈ T)
    (hcr : (U.block c).round = S.slotRound k + 2) {L : BlockId} (hL : IsLeaderBlock U k L) :
    Backs U t (tl.held (U.block c).creator (tl.built c)) L := by
  obtain ⟨L', hL', hcert⟩ := h.certIn_held hτ hδ hγτ hk hN hlead hc hcT hcr
  obtain rfl := isLeaderBlock_unique_of_honest (h.stable hlead) hL hL'
  obtain ⟨y, hy, hyT⟩ := exists_mem_of_quorum h.large hcert
  obtain ⟨hyH, -, hLy⟩ := Finset.mem_filter.mp hy
  refine backs_of_certIn ht (h.closed _ (h.stable hcT) _ y hyH (h.stable hyT) hLy) ?_
  rw [hL.2.1]; exact hcert

/-- **A round led by `T` is built within `δ + γ`**, at `τ ≥ 2δ` and
`δ < γ ≤ τ`: when the slots at round `s ≥ R + 2` and one round below have
leaders in `T`, every node of `T` holds what it waits for above `s` once it
holds the blocks of `T` of round `s`. -/
theorem builtBy_succ_fast (hτ : 2 * δ ≤ τ) (hδ : δ < γ) (hγτ : γ ≤ τ) {s t : ℕ}
    (hs : R + 2 ≤ s) (hsN : s < N) (hb : BuiltBy U tl T s t)
    (hlead : ∀ k, S.slotRound k = s ∨ S.slotRound k + 1 = s → S.leader k ∈ T) :
    BuiltBy U tl T (s + 1) (t + δ + γ) := by
  have hG := h.le_of_reachedBy (by omega) hb.reachedBy
  refine h.builtBy_of_reachedBy hδ hγτ (by omega) (by omega) fun v hv => ?_
  refine h.built_of_waitsFor hv (by omega) hsN (by omega)
    ⟨h.quorumIn_of_reachedBy (by omega) (by omega) hb.reachedBy hv, fun k hk => ?_,
      fun k hk => ?_⟩
  · obtain ⟨L, hL, hLc, hLr, hLt⟩ := hb _ (hlead k (Or.inl hk))
    exact ⟨L, h.mem_held_of_round hL (hLc ▸ hlead k (Or.inl hk)) (by omega) hv hLt le_rfl, hL,
      hLr.trans hk.symm, hLc⟩
  · rw [← hk] at hb ⊢
    exact h.certIn_of_builtBy hτ hδ hγτ (by omega) (by omega) (hlead k (Or.inr hk)) hb hv le_rfl

/-- Every validator of `T` builds at every round from `R + 1` to `N`, at
`δ < γ ≤ τ`. -/
theorem populatedOn (hδ : δ < γ) (hγτ : γ ≤ τ) {s : ℕ} (hs : R + 1 ≤ s) (hsN : s ≤ N) :
    PopulatedOn U T s := by
  intro v hv
  obtain ⟨t, ht⟩ := h.exists_reachedBy (show R ≤ s by omega) hsN
  obtain ⟨b, hb, hbv, hbr, -⟩ := h.builtBy_of_reachedBy hδ hγτ hs hsN ht v hv
  exact ⟨b, hb, hbv, hbr⟩

/-- **The run is synchronous among `T`** from round `R + 1` to `N`, at
`τ ≥ 2δ` and `δ < γ ≤ τ`. -/
theorem syncFrom (hτ : 2 * δ ≤ τ) (hδ : δ < γ) (hγτ : γ ≤ τ) : SyncFrom U T (R + 1) N :=
  ⟨h.large, fun _ hr hrN => h.populatedOn hδ hγτ hr hrN,
    fun _ hk hN hlead _ hL _ hC hCT hCr =>
      h.mem_refs_of_leader hτ hδ hγτ hk hN hlead hC hCT hCr hL,
    fun _ hk hN hlead _ hL _ hD hDT hDr =>
      h.mem_claims_of_leader hτ hδ hγτ hk hN hlead hD hDT hDr hL⟩

/-- **A slot led by `T` commits within `3δ + 2γ`**, at a live row, `τ ≥ 2δ` and
`δ < γ ≤ τ`: when every slot from one round below a slot at round `r`, from
`R + 2` to `N − 2`, to one round above it has a leader in `T`, and every
validator of `T` has built at round `r` by `t`, every node of `T` commits the
slot directly on what it holds at `t + 3δ + 2γ`. -/
theorem nodeDecided_fast {p : Params} (hlive : LiveRow Validator p) (hτ : 2 * δ ≤ τ)
    (hδ : δ < γ) (hγτ : γ ≤ τ) (K : ℕ) {k t : ℕ}
    (hk : R + 2 ≤ S.slotRound k) (hN : S.slotRound k + 2 ≤ N)
    (hlead : ∀ j, S.slotRound k ≤ S.slotRound j + 1 → S.slotRound j ≤ S.slotRound k + 1 →
      S.leader j ∈ T)
    (hb : BuiltBy U tl T (S.slotRound k) t) {v : Validator} (hv : v ∈ T) :
    ∃ L, IsLeaderBlock U k L ∧ NodeDecided p U K (tl.held v (t + 3 * δ + 2 * γ)) k (some L) := by
  have h1 := h.builtBy_succ_fast hτ hδ hγτ hk (by omega) hb fun j hj =>
    hlead j (by omega) (by omega)
  have h2 := h.builtBy_succ_fast hτ hδ hγτ (by omega) (by omega) h1 fun j hj =>
    hlead j (by omega) (by omega)
  have hlk := hlead k (by omega) (by omega)
  have hcb := certRound_bounds (p := p) (S.slotRound k)
  refine nodeDecided_of_responds hlive h.large
    ((respondsFrom_of_syncFrom (p := p) (h.syncFrom hτ hδ hγτ)).2 k (by omega) (by omega) hlk) ?_
  rintro c ⟨hc, hcT, hlo, hhi⟩
  have hcr : (U.block c).round = certRound p (S.slotRound k) := le_antisymm hhi hlo
  have hct : tl.built c ≤ t + 2 * δ + 2 * γ := by
    by_cases h1r : certRound p (S.slotRound k) = S.slotRound k + 1
    · obtain ⟨c', hc', hcc', hcr', hct'⟩ := h1 _ hcT
      obtain rfl : c = c' := U.eq_of_creator_eq hc hc' (h.stable hcT) rfl hcc' (by omega)
      omega
    · obtain ⟨c', hc', hcc', hcr', hct'⟩ := h2 _ hcT
      obtain rfl : c = c' := U.eq_of_creator_eq hc hc' (h.stable hcT) rfl hcc' (by omega)
      omega
  exact h.mem_held_of_round hc hcT (by omega) hv hct (by omega)

/-- **A node of `T` holds the blocks of `T` of the round below when it builds**,
at `2δ ≤ γ ≤ τ` and `δ < γ`: a block of `T` of round `r + 1`, `r` from `R + 1`
to `N`, is built `δ` or more after every block of `T` of round `r`. -/
theorem mem_held_below (hγ : 2 * δ ≤ γ) (hδ : δ < γ) (hγτ : γ ≤ τ) {r : ℕ} (hr : R + 1 ≤ r)
    (hrN : r ≤ N) {x : BlockId} (hx : x ∈ U.ids) (hxT : (U.block x).creator ∈ T)
    (hxr : (U.block x).round = r) {b : BlockId} (hb : b ∈ U.ids)
    (hbT : (U.block b).creator ∈ T) (hbr : (U.block b).round = r + 1) :
    x ∈ tl.held (U.block b).creator (tl.built b) := by
  have hquorum : ∀ b, (U.block b).creator ∈ T → ∀ t, G ≤ t → t + 2 * δ ≤ tl.built b →
      QuorumIn U (tl.held (U.block b).creator t) r → tl.built x + δ ≤ tl.built b := by
    intro b hbT t hG ht hQ
    obtain ⟨y, hy, hyc, hyr, hyt⟩ := h.builtBy_of_reachedBy hδ hγτ hr hrN
      (h.reachedBy_of_quorumIn (by omega) hrN hG hbT hQ) _ hxT
    obtain rfl : y = x := U.eq_of_creator_eq hy hx (h.stable hxT) hyc rfl (by omega)
    omega
  have key : tl.built x + δ ≤ tl.built b := by
    refine h.induction_behind (s := r) (by omega) (fun b => tl.built x + δ ≤ tl.built b)
      (fun b hb hbT hbr hW => ?_) (fun b hb hbT hbr y hyH hyT hyr hy => ?_) hb hbT hbr
    · have hlb := h.late b hb hbT (by omega)
      rcases hW with ⟨hγb, hW, -⟩ | ⟨hτb, hQ⟩
      · exact hquorum b hbT _ (by omega) (by omega) hW.1
      · exact hquorum b hbT _ (by omega) (by omega) hQ
    · by_cases hyb : (U.block y).creator = (U.block b).creator
      · obtain rfl : y = b := U.eq_of_creator_eq (h.held_ids _ _ hyH) hb (h.stable hbT) hyb rfl
          (hyr.trans hbr.symm)
        exact hy
      · have := h.prior _ (h.stable hbT) _ y hyH (h.stable hyT) hyb
        omega
  exact h.mem_held_of_round hx hxT (by omega) hbT le_rfl key

/-- **Leaders of `T` cover `T`**, at `2δ ≤ γ ≤ τ` and `δ < γ`, from round `R + 1`
on, when each slot's leader leads its round on the substrate: a leader block
of a slot led by `T` references every block of `T` one round below, which its
author holds when it builds. -/
theorem coversFrom (hγ : 2 * δ ≤ γ) (hδ : δ < γ) (hγτ : γ ≤ τ)
    (hsl : ∀ k, S.leader k ∈ Ld.leaders (S.slotRound k)) : CoversFrom U T (R + 1) N := by
  intro k hk hN hlead L hL y hy hyT hyr
  have hLc : (U.block L).creator ∈ T := by rw [hL.2.2]; exact hlead
  refine h.covers L hL.1 (h.stable hLc) (by rw [hL.2.2, hL.2.1]; exact hsl k) y
    (h.mem_held_below hγ hδ hγτ (r := S.slotRound k - 1) (by omega) (by omega) hy hyT (by omega)
      hL.1 hLc (by rw [hL.2.1]; omega)) (h.stable hyT) (by rw [hL.2.1]; exact hyr)

/-- **A node of `T` can always build a valid block**, at `2δ ≤ γ ≤ τ` and
`δ < γ`: when it builds at round `r + 1`, `r` from `R + 1` to `N`, it holds the
blocks of `T` of round `r`, from which a dense block is valid. -/
theorem exists_valid_block (hγ : 2 * δ ≤ γ) (hδ : δ < γ) (hγτ : γ ≤ τ) {r : ℕ}
    (hr : R + 1 ≤ r) (hrN : r ≤ N) {b : BlockId} (hb : b ∈ U.ids) (hbT : (U.block b).creator ∈ T)
    (hbr : (U.block b).round = r + 1) (pay : Payload) :
    ∃ b' : Block Validator BlockId Payload, b'.creator = (U.block b).creator ∧ b'.round = r + 1 ∧
      b'.refs ⊆ tl.held (U.block b).creator (tl.built b) ∧
      SValid Validator BlockId Payload U.block b' := by
  classical
  refine exists_dense_block (h.held_ids _ _) ?_ _ pay
  refine h.large.trans (Finset.card_le_card fun w hw => ?_)
  obtain ⟨x, hx, hxw, hxr⟩ := h.populatedOn hδ hγτ hr hrN w hw
  have hxT : (U.block x).creator ∈ T := hxw ▸ hw
  exact mem_creatorsOf.mpr ⟨x, Finset.mem_filter.mpr ⟨h.mem_held_below hγ hδ hγτ hr hrN hx hxT hxr
    hb hbT hbr, h.stable hxT, hxr⟩, hxw⟩

/-- **The ledger grows**, at a live row, `τ ≥ 2δ` and `δ < γ ≤ τ`, on a
disciplined record, when nodes of `T` fetch the available sub-DAG of the leader
blocks they hold within `Δ`, a two-round row links by `f + c + 1` votes or more,
and the schedule offers runs of `c` leaders of `T` spanning eligibility: past
any slot `k` there is a slot `b` such that, if the run reaches the round of
its last certificates, every node of `T`, at one time, decides every slot
below `b + c` and has fetched each leader it commits down to `D` rounds below
it. Every leader it commits has a voter in `T`, whose block brings it. -/
theorem exists_ledger_at {p : Params} (hrow : Row Validator p)
    (hlink : p.voteIsCert = true → F.f + Cr.c + 1 ≤ p.linkSize) {K : ℕ}
    (hI : Disciplined K p.certThreshold S U) (hlive : LiveRow Validator p)
    (hτ : 2 * δ ≤ τ) (hδ : δ < γ) (hγτ : γ ≤ τ) {Δ : ℕ} (D : ℕ)
    (hF : Fetches U tl T K G Δ) {c : ℕ} (hc : 0 < c)
    (hspan : ∀ b i, i < b → EligibleAt (S := S) (p.waveLength - 1) i (b + c - 1))
    (fair : FairRunOn T c) (k : ℕ) :
    ∃ b, k ≤ b ∧ (certRound p (S.slotRound (b + c - 1)) ≤ N →
      ∀ v ∈ T, ∃ g : ℕ → Option BlockId, ∀ i, i < b + c →
        NodeDecided p U K (tl.held v (max G (U.ids.sup tl.built) + δ + Δ)) i (g i) ∧
        ∀ L, g i = some L → FetchedIn U K (tl.held v (max G (U.ids.sup tl.built) + δ + Δ)) L
          ((U.block L).round - D)) := by
  classical
  obtain ⟨b, hkb, hRb, hrun⟩ := Slots.exists_run_past fair k (R + 1)
  set T₀ := max G (U.ids.sup tl.built)
  have hT₀ : ∀ x ∈ U.ids, tl.built x ≤ T₀ := fun x hx =>
    (Finset.le_sup (f := tl.built) hx).trans (le_max_right _ _)
  refine ⟨b, hkb, fun hN v hv => ?_⟩
  have hresp' : RespondsFrom p U T (R + 1) N := respondsFrom_of_syncFrom (h.syncFrom hτ hδ hγτ)
  have hresp := responds_of_run hc hRb hrun
    ⟨hresp'.1, fun j h1 h2 h3 => hresp'.2 j h1 (h2.trans hN) h3⟩
  have hheld : HeldBy U T (S.slotRound b) (certRound p (S.slotRound (b + c - 1))) ⊆
      ↑(tl.held v (T₀ + δ + Δ)) := fun z hz =>
    h.mem_held_of_round hz.1 hz.2.1 (by have := hz.2.2.1; omega) hv (hT₀ z hz.1) (by omega)
  have hav : ∀ j A, NodeDecided p U K (tl.held v (T₀ + δ + Δ)) j (some A) →
      Avail U K A ⊆ ↑(tl.held v (T₀ + δ + Δ)) := by
    intro j A hA z hz
    obtain ⟨-, hvote⟩ := hA.certified hrow hlink hI (h.held_ids v _)
    obtain ⟨u, hu, huT⟩ := exists_mem_of_card h.large hvote
    obtain ⟨y, hy, -, hAy, rfl⟩ := mem_supporters.mp hu
    have hyc := h.stable huT
    have hyv := h.mem_held_of_held huT (le_max_left _ _) (h.own y hy hyc _ (hT₀ y hy)) hyc hv
      le_rfl
    have hAv := h.closed v (h.stable hv) _ y hyv hyc hAy
    exact h.mono v hv _ _ (by omega) le_rfl (hF v hv _ (by omega) j A hA.isLeaderBlock hAv z hz)
  have hdec := nodeDecided_of_run hlive h.large hc hspan hresp hheld
    (fun j A _ hA => hav j A hA)
  refine ⟨fun i => if hi : i < b + c then (hdec i hi).choose else none, fun i hi => ?_⟩
  simp only [dif_pos hi]
  refine ⟨(hdec i hi).choose_spec, fun L hL => ?_⟩
  exact fetchedIn_of_subset fun y d hy z hz =>
    hav i L (hL ▸ (hdec i hi).choose_spec) ⟨y, d, hy, hz⟩

/-- **The ledger grows**, as `exists_ledger_at`, at some time. -/
theorem exists_ledger {p : Params} (hrow : Row Validator p)
    (hlink : p.voteIsCert = true → F.f + Cr.c + 1 ≤ p.linkSize) {K : ℕ}
    (hI : Disciplined K p.certThreshold S U) (hlive : LiveRow Validator p)
    (hτ : 2 * δ ≤ τ) (hδ : δ < γ) (hγτ : γ ≤ τ) {Δ : ℕ} (D : ℕ)
    (hF : Fetches U tl T K G Δ) {c : ℕ} (hc : 0 < c)
    (hspan : ∀ b i, i < b → EligibleAt (S := S) (p.waveLength - 1) i (b + c - 1))
    (fair : FairRunOn T c) (k : ℕ) :
    ∃ b, k ≤ b ∧ (certRound p (S.slotRound (b + c - 1)) ≤ N → ∃ t, ∀ v ∈ T,
      ∃ g : ℕ → Option BlockId, ∀ i, i < b + c → NodeDecided p U K (tl.held v t) i (g i) ∧
        ∀ L, g i = some L → FetchedIn U K (tl.held v t) L ((U.block L).round - D)) := by
  obtain ⟨b, hkb, hb⟩ := h.exists_ledger_at hrow hlink hI hlive hτ hδ hγτ D hF hc hspan fair k
  exact ⟨b, hkb, fun hN => ⟨_, hb hN⟩⟩

end TimedRun

end KPartialSparse

end LeanDag
