import LeanDag.KPartialDag.Model.Reactive
import LeanDag.KPartialDag.Helpers.Live
/-!
# Reactive nodes in time — helpers

`docs/kpartial.md` §11. What a node waits for grows with what it holds
(`waitsFor_mono`). A correct block built at time `t` shows that its author
held what it waits for at `t`, or a quorum at `t − τ`, or a correct block of
its round built before `t` (`induction_behind`). Blocks of `f + 1` correct
authors at a round bring every correct node to the round within `δ`
(`builtBy_of_behind`), and so does a quorum that a correct node holds
(`builtBy_of_quorumIn`). A correct node's timer starts at a quorum, so with
`τ ≥ 2δ` a correct leader's block reaches every correct voter before its
timeout (`leader_mem_held`), and the votes of all correct validators reach
every correct node before its timeout two rounds above (`certIn_held`).
After `δ` every correct node holds the correct blocks of a round, so it
builds above once its timeout runs out (`builtBy_succ`), and at once when
the leaders it waits for are correct (`builtBy_succ_fast`). The round after
the last one a correct node reached before `G + τ` starts a reactive run
(`exists_run`).
-/

namespace LeanDag

namespace KPartialDag

variable {Validator : Type*} [Fintype Validator] [DecidableEq Validator] [F : Faults Validator]
variable {BlockId : Type*} [DecidableEq BlockId] {Payload : Type*}
variable [S : Slots Validator]
variable {U : KRecord Validator BlockId Payload} {tl : Timeline Validator BlockId}
variable {G δ τ γ μ R N : ℕ}

omit [DecidableEq BlockId] S in
theorem creatorsOf_filter_mono {H H' : Finset BlockId} (hH : H ⊆ H') (p : BlockId → Prop)
    [DecidablePred p] : creatorsOf U.block (H.filter p) ⊆ creatorsOf U.block (H'.filter p) :=
  Finset.image_subset_image (Finset.filter_subset_filter _ hH)

omit [DecidableEq BlockId] S in
theorem quorumIn_mono {H H' : Finset BlockId} (hH : H ⊆ H') {r : ℕ} (h : QuorumIn U H r) :
    QuorumIn U H' r :=
  le_trans h (Finset.card_le_card (creatorsOf_filter_mono hH _))

omit S in
theorem certIn_mono {H H' : Finset BlockId} (hH : H ⊆ H') {r : ℕ} {L : BlockId}
    (h : CertIn U H r L) : CertIn U H' r L :=
  le_trans h (Finset.card_le_card (creatorsOf_filter_mono hH _))

/-- **What a node waits for grows with what it holds.** -/
theorem waitsFor_mono {H H' : Finset BlockId} (hH : H ⊆ H') {r : ℕ} (h : WaitsFor U H r) :
    WaitsFor U H' r := by
  obtain ⟨hq, hl, hc⟩ := h
  refine ⟨quorumIn_mono hH hq, fun k hk => ?_, fun k hk => ?_⟩
  · obtain ⟨L, hL, hlead⟩ := hl k hk
    exact ⟨L, hH hL, hlead⟩
  · obtain ⟨L, hlead, hcert⟩ := hc k hk
    exact ⟨L, hlead, certIn_mono hH hcert⟩

omit [DecidableEq BlockId] S in
/-- A quorum at round `r` in `H` holds a correct block of round `r`. -/
theorem exists_correct_of_quorumIn {H : Finset BlockId} {r : ℕ} (h : QuorumIn U H r) :
    ∃ x ∈ H, (U.block x).round = r ∧ (U.block x).creator ∈ (Correct : Finset Validator) := by
  obtain ⟨v, hv⟩ := Finset.card_pos.mp
    (lt_of_lt_of_le (Nat.succ_pos _) (card_inter_correct_of_quorum h))
  obtain ⟨hvc, hvC⟩ := Finset.mem_inter.mp hv
  obtain ⟨x, hx, hxv⟩ := mem_creatorsOf.mp hvc
  obtain ⟨hxH, hxr⟩ := Finset.mem_filter.mp hx
  exact ⟨x, hxH, hxr, hxv ▸ hvC⟩

omit [DecidableEq BlockId] S in
/-- A set of blocks of round `r` with a block by every correct validator
reaches a quorum. -/
theorem quorum_le_of_correct {X : Finset BlockId}
    (h : ∀ w ∈ (Correct : Finset Validator), ∃ y ∈ X, (U.block y).creator = w) :
    quorumCard Validator ≤ (creatorsOf U.block X).card :=
  le_trans card_correct (Finset.card_le_card fun w hw => by
    obtain ⟨y, hy, hyw⟩ := h w hw
    exact mem_creatorsOf.mpr ⟨y, hy, hyw⟩)

omit [DecidableEq BlockId] S in
/-- Blocks behind for `v` include a correct block of round `r + 1` by another
author. -/
theorem exists_correct_of_behindIn {H : Finset BlockId} {v : Validator} {r : ℕ}
    (h : BehindIn U H v r) :
    ∃ y ∈ H, (U.block y).round = r + 1 ∧ (U.block y).creator ∈ (Correct : Finset Validator) ∧
      (U.block y).creator ≠ v := by
  obtain ⟨w, hw, hwc⟩ := exists_correct_of_card h
  obtain ⟨hwv, hw⟩ := Finset.mem_erase.mp hw
  obtain ⟨y, hy, hyw⟩ := mem_creatorsOf.mp hw
  obtain ⟨hyH, hyr⟩ := Finset.mem_filter.mp hy
  exact ⟨y, hyH, hyr, hyw ▸ hwc, hyw ▸ hwv⟩

omit [DecidableEq BlockId] S in
theorem builtBy_mono {s t t' : ℕ} (hb : BuiltBy U tl s t) (ht : t ≤ t') :
    BuiltBy U tl s t' := fun v hv => by
  obtain ⟨b, hb, hbv, hbr, hbt⟩ := hb v hv
  exact ⟨b, hb, hbv, hbr, hbt.trans ht⟩

omit [DecidableEq BlockId] S in
/-- A block of round `s + 1` references blocks of a quorum at round `s`. -/
theorem quorumIn_refs {x : BlockId} (hx : x ∈ U.ids) {s : ℕ} (hxr : (U.block x).round = s + 1) :
    QuorumIn U (U.block x).refs s :=
  le_trans ((U.valid x hx).quorum (by omega)) (Finset.card_le_card
    (Finset.image_subset_image fun z hz =>
      Finset.mem_filter.mpr ⟨hz, by have := (U.valid x hx).predecessor z hz; omega⟩))

omit [DecidableEq BlockId] in
/-- A correct leader has one leader block. -/
theorem leaderBlock_eq {k : ℕ} {L L' : BlockId} (hL : IsLeaderBlock U k L)
    (hL' : IsLeaderBlock U k L') (hc : S.leader k ∈ (Correct : Finset Validator)) : L = L' :=
  U.eq_of_creator_eq hL.1 hL'.1 hc hL.2.2 hL'.2.2 (hL.2.1.trans hL'.2.1.symm)

namespace ReactiveRules

variable (h : ReactiveRules U tl G δ τ γ μ R N)
include h

/-- The reactive rules hold from any later round that every correct
validator builds. -/
theorem above {R' : ℕ} (hR : R ≤ R') (hs : ∃ t, BuiltBy U tl R' t) :
    ReactiveRules U tl G δ τ γ μ R' N :=
  { h with
    start := hs
    waits := fun b hb hbc r hbr hr => h.waits b hb hbc r hbr (hR.trans hr)
    prompt := fun v hv r t hr hrN hw => h.prompt v hv r t (hR.trans hr) hrN hw }

/-- A correct block built by a time `t₀ ≥ G` is held by every correct node
`δ` later. -/
theorem mem_held {b : BlockId} (hb : b ∈ U.ids)
    (hbc : (U.block b).creator ∈ (Correct : Finset Validator))
    {v : Validator} (hv : v ∈ (Correct : Finset Validator)) {t₀ t : ℕ} (hG : G ≤ t₀)
    (h0 : tl.built b ≤ t₀) (ht : t₀ + δ ≤ t) : b ∈ tl.held v t :=
  h.mono v hv _ _ ht (h.delivers b hb hbc v hv t₀ hG h0)

/-- **A correct node votes for the leader blocks it holds**: a correct block
references a leader block of each slot one round below whose leader block
its author holds. -/
theorem votes {b : BlockId} (hb : b ∈ U.ids)
    (hbc : (U.block b).creator ∈ (Correct : Finset Validator)) {k : ℕ}
    (hk : S.slotRound k + 1 = (U.block b).round)
    (hL : ∃ L ∈ tl.held (U.block b).creator (tl.built b), IsLeaderBlock U k L) :
    ∃ L ∈ (U.block b).refs, IsLeaderBlock U k L := by
  obtain ⟨L, hLH, hL, hLr, hLc⟩ := hL
  obtain ⟨y, hy, hyc⟩ := h.covers b hb hbc L hLH (by omega)
  have := (U.valid b hb).predecessor y hy
  exact ⟨y, hy, U.complete b hb y hy, by omega, hyc.trans hLc⟩

/-- A correct node that holds a quorum of round `r`, from `R` to below `N`,
at `t` has built at round `r + 1` by `t + max τ μ`. -/
theorem built_of_quorumIn {v : Validator} (hv : v ∈ (Correct : Finset Validator)) {r t : ℕ}
    (hr : R ≤ r) (hrN : r < N) (hQ : QuorumIn U (tl.held v t) r) :
    ∃ b ∈ U.ids, (U.block b).creator = v ∧ (U.block b).round = r + 1 ∧
      tl.built b ≤ t + max τ μ := by
  have := le_max_left τ μ
  have := le_max_right τ μ
  exact h.prompt v hv r _ hr hrN (Or.inl ⟨by omega,
    quorumIn_mono (h.mono v hv t _ (by omega)) hQ,
    Or.inr (Or.inr ⟨by omega, quorumIn_mono (h.mono v hv t _ (by omega)) hQ⟩)⟩)

/-- A correct node that holds what it waits for above round `r`, from `R` to
below `N`, at `t` has built at round `r + 1` by `t + max γ μ`. -/
theorem built_of_waitsFor {v : Validator} (hv : v ∈ (Correct : Finset Validator)) {r t : ℕ}
    (hr : R ≤ r) (hrN : r < N) (hW : WaitsFor U (tl.held v t) r) :
    ∃ b ∈ U.ids, (U.block b).creator = v ∧ (U.block b).round = r + 1 ∧
      tl.built b ≤ t + max γ μ := by
  have := le_max_left γ μ
  have := le_max_right γ μ
  exact h.prompt v hv r _ hr hrN (Or.inl ⟨by omega,
    quorumIn_mono (h.mono v hv t _ (by omega)) hW.1,
    Or.inl ⟨by omega, waitsFor_mono (h.mono v hv t _ (by omega)) hW⟩⟩)

/-- **Induction behind**: a property of the correct blocks of round `s + 1`,
`s ≥ R`, that holds for those built on the wait or the timer, and passes to a
block from a correct block of the round its author holds, holds for every
correct block of round `s + 1`. -/
theorem induction_behind {s : ℕ} (hR : R ≤ s) (P : BlockId → Prop)
    (hwait : ∀ b ∈ U.ids, (U.block b).creator ∈ (Correct : Finset Validator) →
      (U.block b).round = s + 1 →
      (γ ≤ tl.built b ∧ WaitsFor U (tl.held (U.block b).creator (tl.built b - γ)) s) ∨
        (WaitsFor U (tl.held (U.block b).creator (tl.built b)) s ∧
          AllIn U (tl.held (U.block b).creator (tl.built b)) s) ∨
        (τ ≤ tl.built b ∧ QuorumIn U (tl.held (U.block b).creator (tl.built b - τ)) s) → P b)
    (hstep : ∀ b ∈ U.ids, (U.block b).creator ∈ (Correct : Finset Validator) →
      (U.block b).round = s + 1 → ∀ y ∈ tl.held (U.block b).creator (tl.built b),
      (U.block y).creator ∈ (Correct : Finset Validator) → (U.block y).round = s + 1 →
      P y → P b)
    {b : BlockId} (hb : b ∈ U.ids) (hbc : (U.block b).creator ∈ (Correct : Finset Validator))
    (hbr : (U.block b).round = s + 1) : P b := by
  suffices ∀ n, ∀ b ∈ U.ids, (U.block b).creator ∈ (Correct : Finset Validator) →
      (U.block b).round = s + 1 → tl.built b = n → P b from this _ b hb hbc hbr rfl
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro b hb hbc hbr hn
    rcases h.waits b hb hbc s hbr hR with hW | hW | hW | hB
    · exact hwait b hb hbc hbr (Or.inl hW)
    · exact hwait b hb hbc hbr (Or.inr (Or.inl hW))
    · exact hwait b hb hbc hbr (Or.inr (Or.inr hW))
    · obtain ⟨y, hyH, hyr, hyc, hyv⟩ := exists_correct_of_behindIn hB
      exact hstep b hb hbc hbr y hyH hyc hyr (ih _ (hn ▸ h.prior _ hbc _ y hyH hyc hyv) y
        (h.held_ids _ _ hyH) hyc hyr rfl)

/-- **Catching up**: once `f + 1` correct validators have built at round
`s + 1`, from `R + 1` to `N`, by a time `t ≥ G`, every correct validator has
built at round `s + 1` by `t + δ`. -/
theorem builtBy_of_behind {s t : ℕ} (hR : R ≤ s) (hN : s < N) (hG : G ≤ t)
    {A : Finset Validator} (hA : A ⊆ (Correct : Finset Validator)) (hcard : F.f + 1 ≤ A.card)
    (hb : ∀ v ∈ A, ∃ b ∈ U.ids, (U.block b).creator = v ∧ (U.block b).round = s + 1 ∧
      tl.built b ≤ t) :
    BuiltBy U tl (s + 1) (t + δ) := by
  intro w hw
  by_cases hwA : w ∈ A
  · obtain ⟨b, hb, hbw, hbr, hbt⟩ := hb w hwA
    exact ⟨b, hb, hbw, hbr, by omega⟩
  refine h.prompt w hw s _ hR hN (Or.inr (le_trans hcard
    (Finset.card_le_card fun v hv => ?_)))
  obtain ⟨b, hb', hbv, hbr, hbt⟩ := hb v hv
  refine Finset.mem_erase.mpr ⟨fun hvw => hwA (hvw ▸ hv), mem_creatorsOf.mpr ⟨b,
    Finset.mem_filter.mpr ⟨h.mem_held hb' (hbv ▸ hA hv) hw hG hbt le_rfl, hbr⟩, hbv⟩⟩

/-- **A quorum brings every correct node to its round**: once a correct node
holds, at a time `t ≥ G`, blocks of a quorum at round `s + 1`, from `R + 1`
to `N`, every correct validator has built at round `s + 1` by `t + δ`. -/
theorem builtBy_of_quorumIn {s t : ℕ} (hR : R ≤ s) (hN : s < N) (hG : G ≤ t) {u : Validator}
    (hu : u ∈ (Correct : Finset Validator)) (hQ : QuorumIn U (tl.held u t) (s + 1)) :
    BuiltBy U tl (s + 1) (t + δ) := by
  refine h.builtBy_of_behind hR hN hG Finset.inter_subset_right
    (card_inter_correct_of_quorum hQ) fun v hv => ?_
  obtain ⟨hvc, hvC⟩ := Finset.mem_inter.mp hv
  obtain ⟨x, hx, hxv⟩ := mem_creatorsOf.mp hvc
  obtain ⟨hxH, hxr⟩ := Finset.mem_filter.mp hx
  exact ⟨x, h.held_ids _ _ hxH, hxv, hxr, h.causal _ hu _ x hxH (hxv ▸ hvC)⟩

/-- After `δ`, a correct node holds the correct blocks of a round all of
whose correct blocks are built by a time from `G` on, and so a quorum
there. -/
theorem quorumIn_of_builtBy {s t : ℕ} (hG : G ≤ t) (hb : BuiltBy U tl s t) {v : Validator}
    (hv : v ∈ (Correct : Finset Validator)) : QuorumIn U (tl.held v (t + δ)) s :=
  quorum_le_of_correct fun w hw => by
    obtain ⟨y, hy, hyw, hyr, hyt⟩ := hb w hw
    exact ⟨y, Finset.mem_filter.mpr ⟨h.mem_held hy (hyw ▸ hw) hv hG hyt le_rfl, hyr⟩, hyw⟩

/-- **Every round up to `N` is built, each within `δ + max τ μ`** of a time
from `G` on. -/
theorem builtBy_succ {s t : ℕ} (hs : R ≤ s) (hsN : s < N) (hG : G ≤ t)
    (hb : BuiltBy U tl s t) : BuiltBy U tl (s + 1) (t + δ + max τ μ) := fun _ hv =>
  h.built_of_quorumIn hv hs hsN (h.quorumIn_of_builtBy hG hb hv)

/-- Every round from `R` to `N` is built by some time. -/
theorem exists_builtBy {s : ℕ} (hs : R ≤ s) (hsN : s ≤ N) : ∃ t, BuiltBy U tl s t := by
  induction s, hs using Nat.le_induction with
  | base => exact h.start
  | succ s hs ih =>
    obtain ⟨t, ht⟩ := ih (by omega)
    exact ⟨_, h.builtBy_succ hs (by omega) (le_max_right t G)
      (builtBy_mono ht (le_max_left t G))⟩

/-- **A reactive run starts after `G + τ`**: the round `R'` after the last
round from `R` on that a correct node reached before `G + τ`, or `R` if there
is none, starts a reactive run, and every correct validator builds it within
`2δ + 2 max τ μ` of `G + τ` and of the time all built round `R`. -/
theorem exists_run : ∃ R', R ≤ R' ∧ (R' = R ∨ ∃ x ∈ U.ids,
    (U.block x).creator ∈ (Correct : Finset Validator) ∧ (U.block x).round + 1 = R' ∧
      tl.built x < G + τ) ∧ (R' ≤ N → ReactiveRun U tl G δ τ γ μ R' N ∧
    ∀ t₀, BuiltBy U tl R t₀ → BuiltBy U tl R' (max t₀ (G + τ) + 2 * δ + 2 * max τ μ)) := by
  classical
  set X := U.ids.filter fun x => (U.block x).creator ∈ (Correct : Finset Validator) ∧
    R ≤ (U.block x).round ∧ tl.built x < G + τ
  by_cases hX : X.Nonempty
  · obtain ⟨x, hxX, hmax⟩ := X.exists_max_image (fun x => (U.block x).round) hX
    obtain ⟨hx, hxc, hxR, hxt⟩ := Finset.mem_filter.mp hxX
    refine ⟨(U.block x).round + 1, by omega, Or.inr ⟨x, hx, hxc, rfl, hxt⟩, fun hN => ?_⟩
    have hbuilt : ∀ t₀, BuiltBy U tl R t₀ →
        BuiltBy U tl ((U.block x).round + 1) (max t₀ (G + τ) + 2 * δ + 2 * max τ μ) := by
      intro t₀ ht₀
      have hm : BuiltBy U tl (U.block x).round (max t₀ (G + τ) + δ + max τ μ) := by
        rcases Nat.eq_or_lt_of_le hxR with heq | hlt
        · exact builtBy_mono (heq ▸ ht₀) (by omega)
        intro w hw
        have hxw := h.mem_held hx hxc hw (t₀ := G + τ) (by omega) hxt.le le_rfl
        have hQ : QuorumIn U (tl.held w (G + τ + δ)) ((U.block x).round - 1) :=
          quorumIn_mono (h.closed w hw _ x hxw) (quorumIn_refs hx (by omega))
        obtain ⟨b, hb, hbw, hbr, hbt⟩ := h.built_of_quorumIn hw (by omega) (by omega) hQ
        exact ⟨b, hb, hbw, by omega, by omega⟩
      exact builtBy_mono (h.builtBy_succ hxR (by omega) (by omega) hm) (by omega)
    obtain ⟨t₀, ht₀⟩ := h.start
    refine ⟨⟨h.above (by omega) ⟨_, hbuilt t₀ ht₀⟩, fun b hb hbc hbr => ?_⟩, hbuilt⟩
    by_contra hlt
    have := hmax b (Finset.mem_filter.mpr ⟨hb, hbc, by omega, by omega⟩)
    omega
  · refine ⟨R, le_rfl, Or.inl rfl, fun _ => ⟨⟨h, fun b hb hbc hbr => ?_⟩,
      fun t₀ ht₀ => builtBy_mono ht₀ (by omega)⟩⟩
    by_contra hlt
    exact hX ⟨b, Finset.mem_filter.mpr ⟨hb, hbc, hbr, by omega⟩⟩

end ReactiveRules

namespace ReactiveRun

variable (h : ReactiveRun U tl G δ τ γ μ R N)
include h

/-- Every correct validator has built at a round from `R` on only at
`G + τ` or later. -/
theorem le_of_builtBy {s t : ℕ} (hs : R ≤ s) (hb : BuiltBy U tl s t) : G + τ ≤ t := by
  obtain ⟨v, -, hv⟩ := exists_correct_of_card (S := (Correct : Finset Validator))
    (by have := two_f_add_one_le_card_correct (Validator := Validator); omega)
  obtain ⟨b, hb, hbv, hbr, hbt⟩ := hb v hv
  have := h.late b hb (hbv ▸ hv) (by omega)
  omega

/-- **A correct leader's block reaches every correct voter before its
timeout**, at `τ ≥ 2δ`: a correct block one round above a slot led by a
correct validator, from round `R + 1` on, is built once its author holds a
leader block of the slot. -/
theorem leader_mem_held (hτ : 2 * δ ≤ τ) {k : ℕ} (hk : R + 1 ≤ S.slotRound k)
    (hN : S.slotRound k + 2 ≤ N) (hlead : S.leader k ∈ (Correct : Finset Validator))
    {b : BlockId} (hb : b ∈ U.ids)
    (hbc : (U.block b).creator ∈ (Correct : Finset Validator))
    (hbr : (U.block b).round = S.slotRound k + 1) :
    ∃ L ∈ tl.held (U.block b).creator (tl.built b), IsLeaderBlock U k L := by
  refine h.induction_behind (by omega)
    (fun b => ∃ L ∈ tl.held (U.block b).creator (tl.built b), IsLeaderBlock U k L)
    (fun b hb hbc hbr hW => ?_) (fun b hb hbc hbr y hyH hyc hyr hy => ?_) hb hbc hbr
  · rcases hW with ⟨-, hW⟩ | ⟨hW, -⟩ | ⟨hτb, hQ⟩
    · obtain ⟨L, hL, hl⟩ := hW.2.1 k rfl
      exact ⟨L, h.mono _ hbc _ _ (Nat.sub_le _ _) hL, hl⟩
    · exact hW.2.1 k rfl
    have hlb := h.late b hb hbc (by omega)
    obtain ⟨L, hL, hLc, hLr, hLt⟩ := h.builtBy_of_quorumIn (s := S.slotRound k - 1)
      (t := tl.built b - τ) (by omega) (by omega) (by omega) hbc
      (by rwa [show S.slotRound k - 1 + 1 = S.slotRound k by omega])
      _ hlead
    exact ⟨L, h.mem_held hL (hLc ▸ hlead) hbc (by omega) hLt (by omega), hL, by omega, hLc⟩
  · obtain ⟨L, hL, hlead'⟩ := h.votes (h.held_ids _ _ hyH) hyc (by omega) hy
    exact ⟨L, h.closed _ hbc _ y hyH hL, hlead'⟩

/-- **Every correct voter votes for a correct leader**: a correct block one
round above a slot led by a correct validator, from round `R + 1` on,
references the slot's leader block. -/
theorem mem_refs_of_leader (hτ : 2 * δ ≤ τ) {k : ℕ} (hk : R + 1 ≤ S.slotRound k)
    (hN : S.slotRound k + 2 ≤ N) (hlead : S.leader k ∈ (Correct : Finset Validator))
    {b : BlockId} (hb : b ∈ U.ids)
    (hbc : (U.block b).creator ∈ (Correct : Finset Validator))
    (hbr : (U.block b).round = S.slotRound k + 1) {L : BlockId} (hL : IsLeaderBlock U k L) :
    L ∈ (U.block b).refs := by
  obtain ⟨L', hL', hlead'⟩ :=
    h.votes hb hbc hbr.symm (h.leader_mem_held hτ hk hN hlead hb hbc hbr)
  exact (leaderBlock_eq hL hlead' hlead) ▸ hL'

/-- **The votes of all correct validators reach every correct node before its
timeout two rounds above**, at `τ ≥ 2δ`: a correct block two rounds above a
slot led by a correct validator, from round `R + 1` on, is built once its
author holds a certificate for the slot's leader block. -/
theorem certIn_held (hτ : 2 * δ ≤ τ) {k : ℕ} (hk : R + 1 ≤ S.slotRound k)
    (hN : S.slotRound k + 2 ≤ N) (hlead : S.leader k ∈ (Correct : Finset Validator))
    {c : BlockId} (hc : c ∈ U.ids)
    (hcc : (U.block c).creator ∈ (Correct : Finset Validator))
    (hcr : (U.block c).round = S.slotRound k + 2) :
    ∃ L, IsLeaderBlock U k L ∧
      CertIn U (tl.held (U.block c).creator (tl.built c)) (S.slotRound k + 1) L := by
  refine h.induction_behind (s := S.slotRound k + 1) (by omega)
    (fun c => ∃ L, IsLeaderBlock U k L ∧
      CertIn U (tl.held (U.block c).creator (tl.built c)) (S.slotRound k + 1) L)
    (fun c hc hcc hcr hW => ?_) (fun c hc hcc hcr y hyH hyc hyr hy => ?_) hc hcc
    (by omega)
  · rcases hW with ⟨-, hW⟩ | ⟨hW, -⟩ | ⟨hτc, hQ⟩
    · obtain ⟨L, hl, hL⟩ := hW.2.2 k rfl
      exact ⟨L, hl, certIn_mono (h.mono _ hcc _ _ (Nat.sub_le _ _)) hL⟩
    · exact hW.2.2 k rfl
    have hlc := h.late c hc hcc (by omega)
    have hB := h.builtBy_of_quorumIn (t := tl.built c - τ) (by omega) (by omega) (by omega) hcc hQ
    obtain ⟨x, hx, hxl, hxr, -⟩ := hB _ hlead
    obtain ⟨L, -, hL⟩ := h.leader_mem_held hτ hk hN hlead hx (hxl ▸ hlead) hxr
    refine ⟨L, hL, quorum_le_of_correct fun w hw => ?_⟩
    obtain ⟨y, hy, hyw, hyr, hyt⟩ := hB w hw
    have hyc : (U.block y).creator ∈ (Correct : Finset Validator) := hyw ▸ hw
    exact ⟨y, Finset.mem_filter.mpr ⟨h.mem_held hy hyc hcc (by omega) hyt (by omega), hyr,
      h.mem_refs_of_leader hτ hk hN hlead hy hyc hyr hL⟩, hyw⟩
  · have hy' := h.held_ids _ _ hyH
    obtain ⟨L, hL, hv⟩ := h.certifies y hy' hyc k (by omega) hy
    refine ⟨L, hL, le_trans hv (Finset.card_le_card (Finset.image_subset_image fun z hz => ?_))⟩
    obtain ⟨-, hzr, hzL⟩ := mem_carriedVotes_spec hy' hyr hz
    exact Finset.mem_filter.mpr
      ⟨h.closed _ hcc _ y hyH (mem_carriedVotes.mp hz).1, hzr, hzL⟩

/-- **Every correct certifier certifies a correct leader**: a correct block
two rounds above a slot led by a correct validator, from round `R + 1` on,
carries votes from a quorum for the slot's leader block. -/
theorem carriesVotes_of_leader (hτ : 2 * δ ≤ τ) {k : ℕ} (hk : R + 1 ≤ S.slotRound k)
    (hN : S.slotRound k + 2 ≤ N) (hlead : S.leader k ∈ (Correct : Finset Validator))
    {c : BlockId} (hc : c ∈ U.ids)
    (hcc : (U.block c).creator ∈ (Correct : Finset Validator))
    (hcr : (U.block c).round = S.slotRound k + 2) {L : BlockId} (hL : IsLeaderBlock U k L) :
    CarriesVotes U (IsVote U) (quorumCard Validator) c L := by
  obtain ⟨L', hL', hv⟩ :=
    h.certifies c hc hcc k hcr.symm (h.certIn_held hτ hk hN hlead hc hcc hcr)
  exact (leaderBlock_eq hL hL' hlead) ▸ hv

/-- **A round led by correct validators is built within `δ + max γ μ`**, at
`τ ≥ 2δ`: when the slots at round `s ≥ R + 2` and one round below have
correct leaders, every correct node holds what it waits for above `s` once
it holds the correct blocks of round `s`. -/
theorem builtBy_succ_fast (hτ : 2 * δ ≤ τ) {s t : ℕ} (hs : R + 2 ≤ s) (hsN : s < N)
    (hb : BuiltBy U tl s t)
    (hlead : ∀ k, S.slotRound k = s ∨ S.slotRound k + 1 = s →
      S.leader k ∈ (Correct : Finset Validator)) :
    BuiltBy U tl (s + 1) (t + δ + max γ μ) := by
  have hG := h.le_of_builtBy (by omega) hb
  intro v hv
  refine h.built_of_waitsFor hv (by omega) hsN ⟨h.quorumIn_of_builtBy (by omega) hb hv,
    fun k hk => ?_, fun k hk => ?_⟩
  · obtain ⟨L, hL, hLc, hLr, hLt⟩ := hb _ (hlead k (Or.inl hk))
    exact ⟨L, h.mem_held hL (hLc ▸ hlead k (Or.inl hk)) hv (by omega) hLt le_rfl, hL,
      hLr.trans hk.symm, hLc⟩
  · have hc := hlead k (Or.inr hk)
    obtain ⟨x, hx, hxv, hxr, -⟩ := hb v hv
    obtain ⟨L, -, hL⟩ :=
      h.leader_mem_held hτ (by omega) (by omega) hc hx (hxv ▸ hv) (hxr.trans hk.symm)
    refine ⟨L, hL, quorum_le_of_correct fun w hw => ?_⟩
    obtain ⟨y, hy, hyw, hyr, hyt⟩ := hb w hw
    have hyc : (U.block y).creator ∈ (Correct : Finset Validator) := hyw ▸ hw
    exact ⟨y, Finset.mem_filter.mpr ⟨h.mem_held hy hyc hv (by omega) hyt le_rfl, hyr,
      h.mem_refs_of_leader hτ (by omega) (by omega) hc hy hyc (hyr.trans hk.symm) hL⟩, hyw⟩

/-- **Responsiveness among the correct validators** from round `R + 1` to
`N`, at `τ ≥ 2δ`. -/
theorem respondsFrom (hτ : 2 * δ ≤ τ) :
    RespondsFrom U (Correct : Finset Validator) (R + 1) N := by
  refine ⟨card_correct, fun k hk hN hlead => ?_⟩
  obtain ⟨t, ht⟩ := h.exists_builtBy (show R ≤ S.slotRound k by omega) (by omega)
  obtain ⟨L, hL, hLc, hLr, -⟩ := ht _ hlead
  obtain ⟨t', ht'⟩ := h.exists_builtBy (show R ≤ S.slotRound k + 2 by omega) hN
  refine ⟨fun v hv => ?_, L, ⟨hL, hLr, hLc⟩, fun C hC hCc hCr =>
    h.carriesVotes_of_leader hτ hk hN hlead hC hCc hCr ⟨hL, hLr, hLc⟩⟩
  obtain ⟨b, hb, hbv, hbr, -⟩ := ht' v hv
  exact ⟨b, hb, hbv, hbr⟩

/-- **A slot led by correct validators commits within `3δ + 2 max γ μ`**, at
`τ ≥ 2δ`: when every slot from one round below a slot at round `r`, from
`R + 2` to `N − 2`, to one round above it has a correct leader, and every
correct validator has built at round `r` by `t`, every correct node commits
the slot directly by `t + 3δ + 2 max γ μ`. -/
theorem nodeDecided_fast (hτ : 2 * δ ≤ τ) (K : ℕ) {k t : ℕ} (hk : R + 2 ≤ S.slotRound k)
    (hN : S.slotRound k + 2 ≤ N)
    (hlead : ∀ j, S.slotRound k ≤ S.slotRound j + 1 → S.slotRound j ≤ S.slotRound k + 1 →
      S.leader j ∈ (Correct : Finset Validator))
    (hb : BuiltBy U tl (S.slotRound k) t) {v : Validator}
    (hv : v ∈ (Correct : Finset Validator)) :
    ∃ L, IsLeaderBlock U k L ∧
      NodeDecided U K (tl.held v (t + 3 * δ + 2 * max γ μ)) k (some L) := by
  have hG := h.le_of_builtBy (by omega) hb
  have h1 := h.builtBy_succ_fast hτ hk (by omega) hb fun j hj => hlead j (by omega) (by omega)
  have h2 := h.builtBy_succ_fast hτ (by omega) (by omega) h1 fun j hj =>
    hlead j (by omega) (by omega)
  have hlk := hlead k (by omega) (by omega)
  refine nodeDecided_of_responds card_correct ((h.respondsFrom hτ).2 k (by omega) hN hlk) ?_
  rintro z ⟨c, hc, hcc, hlo, hhi, hz⟩
  obtain ⟨c', hc', hcc', hcr', hct'⟩ := h2 _ hcc
  have hcc'' : c = c' := U.eq_of_creator_eq hc hc' hcc rfl hcc' (by omega)
  subst hcc''
  have hheld : c ∈ tl.held v (t + 3 * δ + 2 * max γ μ) :=
    h.mem_held hc hcc hv (by omega) hct' (by omega)
  rcases hz with rfl | hz
  · exact hheld
  · exact h.closed v hv _ c hheld hz

/-- **A correct node holds the correct blocks of the round below when it
builds**, at `2δ ≤ γ ≤ τ`: a correct block of round `r + 1`, `r` from
`R + 1` to `N`, is built once its author holds every correct block of round
`r`. -/
theorem mem_held_below (hγ : 2 * δ ≤ γ) (hγτ : γ ≤ τ) {r : ℕ} (hr : R + 1 ≤ r) (hrN : r ≤ N)
    {x : BlockId} (hx : x ∈ U.ids) (hxc : (U.block x).creator ∈ (Correct : Finset Validator))
    (hxr : (U.block x).round = r) {b : BlockId} (hb : b ∈ U.ids)
    (hbc : (U.block b).creator ∈ (Correct : Finset Validator))
    (hbr : (U.block b).round = r + 1) : x ∈ tl.held (U.block b).creator (tl.built b) := by
  -- a correct node holding a quorum of round `r` at `t` holds `x` by `t + 2δ`
  have hquorum : ∀ b, (U.block b).creator ∈ (Correct : Finset Validator) → ∀ t, G ≤ t →
      t + 2 * δ ≤ tl.built b → QuorumIn U (tl.held (U.block b).creator t) r →
      x ∈ tl.held (U.block b).creator (tl.built b) := by
    intro b hbc t hG ht hQ
    obtain ⟨y, hy, hyc, hyr, hyt⟩ := h.builtBy_of_quorumIn (s := r - 1) (by omega) (by omega)
      hG hbc (by rwa [show r - 1 + 1 = r by omega]) _ hxc
    obtain rfl : y = x := U.eq_of_creator_eq hy hx hxc hyc rfl (by omega)
    exact h.mem_held hy hxc hbc (t₀ := t + δ) (by omega) hyt (by omega)
  refine h.induction_behind (s := r) (by omega)
    (fun b => x ∈ tl.held (U.block b).creator (tl.built b))
    (fun b hb hbc hbr hW => ?_) (fun b hb hbc hbr y hyH hyc hyr hy => ?_) hb hbc hbr
  · have hlb := h.late b hb hbc (by omega)
    rcases hW with ⟨hγb, hW⟩ | ⟨-, hA⟩ | ⟨hτb, hQ⟩
    · exact hquorum b hbc _ (by omega) (by omega) hW.1
    · obtain ⟨x', hx'H, hx'r, hx'c⟩ := hA (U.block x).creator
      obtain rfl : x' = x :=
        U.eq_of_creator_eq (h.held_ids _ _ hx'H) hx hxc hx'c rfl (by omega)
      exact hx'H
    · exact hquorum b hbc _ (by omega) (by omega) hQ
  · obtain ⟨z, hz, hzc⟩ := h.covers y (h.held_ids _ _ hyH) hyc x hy (by omega)
    have hzr := (U.valid y (h.held_ids _ _ hyH)).predecessor z hz
    obtain rfl : z = x :=
      U.eq_of_creator_eq (U.complete y (h.held_ids _ _ hyH) z hz) hx hxc hzc rfl (by omega)
    exact h.closed _ hbc _ y hyH hz

/-- **The run is synchronous among the correct validators** from round
`R + 1` to `N`, at `2δ ≤ γ ≤ τ`: every correct block references every
correct block of the round below. -/
theorem syncFrom (hγ : 2 * δ ≤ γ) (hγτ : γ ≤ τ) :
    SyncFrom U (Correct : Finset Validator) (R + 1) N := by
  refine ⟨card_correct, fun n hn hnN b hb hbr hbc a ha har hac => ?_, fun r hr hrN v hv => ?_⟩
  · obtain ⟨z, hz, hzc⟩ := h.covers b hb hbc a
      (h.mem_held_below hγ hγτ hn hnN.le ha hac har hb hbc hbr) (by omega)
    have hzr := (U.valid b hb).predecessor z hz
    obtain rfl : z = a := U.eq_of_creator_eq (U.complete b hb z hz) ha hac hzc rfl (by omega)
    exact hz
  · obtain ⟨t, ht⟩ := h.exists_builtBy (show R ≤ r by omega) hrN
    obtain ⟨b, hb, hbv, hbr, -⟩ := ht v hv
    exact ⟨b, hb, hbv, hbr⟩

end ReactiveRun

end KPartialDag

end LeanDag
