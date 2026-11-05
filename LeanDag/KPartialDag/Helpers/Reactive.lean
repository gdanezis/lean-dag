import LeanDag.KPartialDag.Model.Reactive
import LeanDag.KPartialDag.Helpers.Live
/-!
# Reactive nodes in time — helpers

`docs/kpartial.md` §11. What a node waits for grows with what it holds
(`waitsFor_mono`). A block of `T` built at time `t` shows that its author held
what it waits for at `t`, or a quorum at `t − τ`, or a block of `T` of its
round built before `t` (`induction_behind`). Blocks of `f + 1` authors of `T`
at a round bring every node of `T` to the round within `δ`
(`reachedBy_of_behind`), and so does a quorum that a node of `T` holds
(`reachedBy_of_quorumIn`); a node of `T` then builds above once its timeout
runs out (`reachedBy_succ`). A node's timer starts at a quorum, so with
`τ ≥ 2δ` a leader's block of `T` reaches every voter of `T` before its timeout
(`leader_mem_held`), and the votes of `T` reach every node of `T` before its
timeout two rounds above (`certIn_held`); a node of `T` builds at once when
the leaders it waits for are in `T` (`builtBy_succ_fast`). The round after
the last one a node of `T` reached before `G + τ` starts a reactive run
(`exists_run`).

A correct node that holds a correct block above round `k` holds a quorum at
`k` (`quorumIn_of_held`), and a correct node holds a block of its own as high
as any it built, from its disk (`exists_held_of_built`); so after crashes
before `G` every node of `T` reaches the highest round built in `T` by `G`
(`reachedBy_of_built`), and operations resume (`exists_resumed`). In a run,
at `δ < γ ≤ τ`, no node of `T` skips a round (`builtBy_below`).

The available sub-DAG of a certified block stays on the disk of a node of
`T` (`exists_disk_of_avail`). Every certified leader is referenced by a vote
of `T` that its author keeps on disk, so every node of `T` holds it and
fetches its available sub-DAG; with the run responsive, every node of `T`
decides every slot up to a run of leaders of `T` (`exists_ledger`).
-/

namespace LeanDag

namespace KPartialDag

variable {Validator : Type*} [Fintype Validator] [DecidableEq Validator] [F : Faults Validator]
variable {BlockId : Type*} [DecidableEq BlockId] {Payload : Type*}
variable [S : Slots Validator]
variable {U : KRecord Validator BlockId Payload} {tl : Timeline Validator BlockId}
variable {T : Finset Validator}
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
/-- A set of blocks with a block by every validator of a quorum `T` reaches a
quorum. -/
theorem quorum_le_of_mem (hT : quorumCard Validator ≤ T.card) {X : Finset BlockId}
    (h : ∀ w ∈ T, ∃ y ∈ X, (U.block y).creator = w) :
    quorumCard Validator ≤ (creatorsOf U.block X).card :=
  le_trans hT (Finset.card_le_card fun w hw => by
    obtain ⟨y, hy, hyw⟩ := h w hw
    exact mem_creatorsOf.mpr ⟨y, hy, hyw⟩)

omit [DecidableEq BlockId] S in
/-- A set of blocks whose authors reach a quorum holds a block by a validator
of a quorum `T`. -/
theorem exists_mem_of_quorum (hT : quorumCard Validator ≤ T.card) {X : Finset BlockId}
    (h : quorumCard Validator ≤ (creatorsOf U.block X).card) :
    ∃ x ∈ X, (U.block x).creator ∈ T := by
  obtain ⟨v, hv⟩ := Finset.card_pos.mp
    (lt_of_lt_of_le (Nat.succ_pos _) (card_inter_ge_of_quorum h hT))
  obtain ⟨hvX, hvT⟩ := Finset.mem_inter.mp hv
  obtain ⟨x, hx, rfl⟩ := mem_creatorsOf.mp hvX
  exact ⟨x, hx, hvT⟩

omit S in
/-- `f + 1` validators include one of a quorum `T`. -/
theorem exists_mem_of_card (hT : quorumCard Validator ≤ T.card) {A : Finset Validator}
    (hA : F.f + 1 ≤ A.card) : ∃ v ∈ A, v ∈ T := by
  by_contra hno
  push Not at hno
  have := Finset.card_le_card fun v hv =>
    Finset.mem_sdiff.mpr ⟨Finset.mem_univ v, hno v hv⟩
  rw [Finset.card_univ_sdiff] at this
  have := F.card_validators
  omega

omit [DecidableEq BlockId] S in
/-- Blocks behind for `v` include a block of round `r + 1` by another author
of a quorum `T`. -/
theorem exists_mem_of_behindIn (hT : quorumCard Validator ≤ T.card) {H : Finset BlockId}
    {v : Validator} {r : ℕ} (h : BehindIn U H v r) :
    ∃ y ∈ H, (U.block y).round = r + 1 ∧ (U.block y).creator ∈ T ∧
      (U.block y).creator ≠ v := by
  obtain ⟨w, hw, hwT⟩ := exists_mem_of_card hT h
  obtain ⟨hwv, hw⟩ := Finset.mem_erase.mp hw
  obtain ⟨y, hy, hyw⟩ := mem_creatorsOf.mp hw
  obtain ⟨hyH, hyr⟩ := Finset.mem_filter.mp hy
  exact ⟨y, hyH, hyr, hyw ▸ hwT, hyw ▸ hwv⟩

omit [DecidableEq BlockId] S in
theorem reachedBy_mono {s t t' : ℕ} (hb : ReachedBy U tl T s t) (ht : t ≤ t') :
    ReachedBy U tl T s t' := fun v hv => by
  obtain ⟨b, hb, hbv, hbr, hbt⟩ := hb v hv
  exact ⟨b, hb, hbv, hbr, hbt.trans ht⟩

omit [DecidableEq BlockId] S in
theorem BuiltBy.reachedBy {s t : ℕ} (hb : BuiltBy U tl T s t) : ReachedBy U tl T s t :=
  fun v hv => by
    obtain ⟨b, hb, hbv, hbr, hbt⟩ := hb v hv
    exact ⟨b, hb, hbv, hbr.ge, hbt⟩

omit [DecidableEq BlockId] S in
/-- A block of round `s + 1` references blocks of a quorum at round `s`. -/
theorem quorumIn_refs {x : BlockId} (hx : x ∈ U.ids) {s : ℕ} (hxr : (U.block x).round = s + 1) :
    QuorumIn U (U.block x).refs s :=
  le_trans ((U.valid x hx).quorum (by omega)) (Finset.card_le_card
    (Finset.image_subset_image fun z hz =>
      Finset.mem_filter.mpr ⟨hz, by have := (U.valid x hx).predecessor z hz; omega⟩))

namespace Persists

variable {ids : Finset BlockId} {block : BlockId → Block Validator BlockId Payload}
variable {order : BlockId → ℕ} {next : Validator → ℕ → ℕ}
variable (h : Persists ids block order next)
include h

omit [DecidableEq BlockId] S in
/-- A correct validator's later builds are at higher rounds. -/
theorem round_lt {i j : BlockId} (hi : i ∈ ids) (hj : j ∈ ids)
    (hc : (block i).creator ∈ (Correct : Finset Validator))
    (hij : (block i).creator = (block j).creator) (hlt : order i < order j) :
    (block i).round < (block j).round := by
  have h1 := h.stores i hi hc
  have h2 := h.grows _ hc (order i + 1) (order j) hlt
  have h3 := h.above j hj (hij ▸ hc)
  rw [← hij] at h3
  omega

omit [DecidableEq BlockId] S in
/-- **A correct validator builds at most one block a round.** -/
theorem eq_of_round {i j : BlockId} (hi : i ∈ ids) (hj : j ∈ ids)
    (hc : (block i).creator ∈ (Correct : Finset Validator))
    (hij : (block i).creator = (block j).creator) (hr : (block i).round = (block j).round) :
    i = j := by
  rcases lt_trichotomy (order i) (order j) with hlt | heq | hgt
  · exact absurd hr (h.round_lt hi hj hc hij hlt).ne
  · exact h.single i hi j hj hc hij heq
  · exact absurd hr (h.round_lt hj hi (hij ▸ hc) hij.symm hgt).ne'

end Persists

namespace BuildsAboveDisk

variable {ids : Finset BlockId} {block : BlockId → Block Validator BlockId Payload}
variable (h : BuildsAboveDisk ids block tl)
include h

omit [DecidableEq BlockId] S in
/-- A correct validator's later builds are at higher rounds. -/
theorem round_lt {b c : BlockId} (hb : b ∈ ids) (hc : c ∈ ids)
    (hbc : (block b).creator ∈ (Correct : Finset Validator))
    (hcb : (block c).creator = (block b).creator) (hlt : tl.built b < tl.built c) :
    (block b).round < (block c).round := by
  obtain ⟨b', hb', hb'c, hb'r⟩ := h.stores b hb hbc (tl.built c - 1) (by omega)
  rw [← hcb] at hb'
  have := h.above c hc (hcb ▸ hbc) (by omega) b' hb' (hb'c.trans hcb.symm)
  omega

omit [DecidableEq BlockId] S in
/-- **Building above the disk persists the last round built**, with builds
numbered by time and the lowest round to build at one above the highest
round built before. -/
theorem persists : ∃ next, Persists ids block tl.built next := by
  classical
  refine ⟨fun v i => (ids.filter fun c => (block c).creator = v ∧ tl.built c < i).sup
    fun c => (block c).round + 1, fun v _ i j hij => Finset.sup_mono fun c hc => ?_,
    fun b hb hbc => Finset.sup_le fun c hc => ?_, fun b hb hbc => ?_, h.single⟩
  · obtain ⟨hc, hcv, hct⟩ := Finset.mem_filter.mp hc
    exact Finset.mem_filter.mpr ⟨hc, hcv, by omega⟩
  · obtain ⟨hc, hcb, hct⟩ := Finset.mem_filter.mp hc
    have := h.round_lt hc hb (hcb ▸ hbc) hcb.symm hct
    omega
  · exact Finset.le_sup (f := fun c => (block c).round + 1)
      (Finset.mem_filter.mpr ⟨hb, rfl, by omega⟩)

end BuildsAboveDisk

namespace NodeRules

variable (h : NodeRules U tl T G δ τ γ μ R N)
include h

/-- The rules for nodes hold from any later round. -/
theorem above {R' : ℕ} (hR : R ≤ R') : NodeRules U tl T G δ τ γ μ R' N :=
  { h with
    waits := fun b hb hbc r hbr hr => h.waits b hb hbc r hbr (hR.trans hr)
    prompt := fun v hv r t hr hrN hw => h.prompt v hv r t (hR.trans hr) hrN hw }

/-- From `G` on, a correct block that a node of `T` holds at `t₀` is held by
every node of `T` from `t₀ + δ` on. -/
theorem mem_held_of_held {u : Validator} (hu : u ∈ T) {t₀ t : ℕ}
    (hG : G ≤ t₀) {b : BlockId} (hb : b ∈ tl.held u t₀)
    (hbc : (U.block b).creator ∈ (Correct : Finset Validator))
    {v : Validator} (hv : v ∈ T) (ht : t₀ + δ ≤ t) :
    b ∈ tl.held v t :=
  h.mono v hv _ _ (by omega) ht (h.delivers u hu t₀ hG b hb hbc v hv)

/-- **History below a correct block**: a correct node that holds a correct
block above round `k` holds a quorum at round `k`. -/
theorem quorumIn_of_held {v : Validator} (hv : v ∈ (Correct : Finset Validator)) {t k : ℕ}
    {y : BlockId} (hy : y ∈ tl.held v t) (hyc : (U.block y).creator ∈ (Correct : Finset Validator))
    (hky : k < (U.block y).round) : QuorumIn U (tl.held v t) k := by
  obtain ⟨m, hm⟩ : ∃ m, (U.block y).round = k + 1 + m := ⟨(U.block y).round - (k + 1), by omega⟩
  induction m generalizing y with
  | zero =>
    exact quorumIn_mono (h.closed v hv t y hy hyc)
      (quorumIn_refs (h.held_ids _ _ hy) (by omega))
  | succ m ih =>
    obtain ⟨z, hz, hzT⟩ := exists_mem_of_quorum h.large
      (quorumIn_refs (s := k + 1 + m) (h.held_ids _ _ hy) (by omega))
    obtain ⟨hz, hzr⟩ := Finset.mem_filter.mp hz
    exact ih (h.closed v hv t y hy hyc hz) (h.stable hzT) (by omega) hzr

/-- A block of `T` at round `s + 1` or above is built no earlier than a block
of `T` of round `s + 1`. -/
theorem exists_succ_built {e : BlockId} (he : e ∈ U.ids) (heT : (U.block e).creator ∈ T)
    {s : ℕ} (hes : s + 1 ≤ (U.block e).round) : ∃ y ∈ U.ids, (U.block y).creator ∈ T ∧
      (U.block y).round = s + 1 ∧ tl.built y ≤ tl.built e := by
  rcases Nat.eq_or_lt_of_le hes with heq | hlt
  · exact ⟨e, he, heT, heq.symm, le_rfl⟩
  have hec := h.stable heT
  obtain ⟨y, hy, hyT⟩ := exists_mem_of_quorum h.large
    (h.quorumIn_of_held hec (h.own e he hec) hec hlt)
  obtain ⟨hyH, hyr⟩ := Finset.mem_filter.mp hy
  exact ⟨y, h.held_ids _ _ hyH, hyT, hyr, h.causal _ hec _ y hyH (h.stable hyT)⟩

/-- **The disk**: a correct validator that has built at round `s` or above by
`t` holds at `t` a block of its own at round `s` or above, whatever it lost in
a restart. -/
theorem exists_held_of_built {v : Validator} (hv : v ∈ (Correct : Finset Validator)) {s t : ℕ}
    (hb : ∃ b ∈ U.ids, (U.block b).creator = v ∧ s ≤ (U.block b).round ∧ tl.built b ≤ t) :
    ∃ y ∈ tl.held v t, (U.block y).creator = v ∧ s ≤ (U.block y).round := by
  obtain ⟨b, hb, hbv, hbs, hbt⟩ := hb
  subst hbv
  exact ⟨b, h.disk_held _ hv t (h.stores b hb hv t hbt).1, rfl, hbs⟩

/-- Once every validator of `T` has reached round `s` by a time `t ≥ G`,
every node of `T` holds a quorum at round `s` by `t + δ`. -/
theorem quorumIn_of_reachedBy {s t : ℕ} (hG : G ≤ t) (hb : ReachedBy U tl T s t)
    {v : Validator} (hv : v ∈ T) : QuorumIn U (tl.held v (t + δ)) s := by
  by_cases habove : ∃ y ∈ tl.held v (t + δ),
      (U.block y).creator ∈ (Correct : Finset Validator) ∧ s < (U.block y).round
  · obtain ⟨y, hy, hyc, hys⟩ := habove
    exact h.quorumIn_of_held (h.stable hv) hy hyc hys
  push Not at habove
  exact quorum_le_of_mem h.large fun w hw => by
    have hwc := h.stable hw
    obtain ⟨y, hy, hyw, hys⟩ := h.exists_held_of_built hwc (hb w hw)
    have hyv := h.mem_held_of_held hw hG hy (hyw ▸ hwc) hv le_rfl
    exact ⟨y, Finset.mem_filter.mpr ⟨hyv, le_antisymm (habove y hyv (hyw ▸ hwc)) hys⟩, hyw⟩

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

/-- A correct block references each correct block of the round below that its
author holds when it builds it. -/
theorem mem_refs_of_held {b x : BlockId} (hb : b ∈ U.ids)
    (hbc : (U.block b).creator ∈ (Correct : Finset Validator)) (hx : x ∈ U.ids)
    (hxc : (U.block x).creator ∈ (Correct : Finset Validator))
    (hxr : (U.block x).round + 1 = (U.block b).round)
    (hxH : x ∈ tl.held (U.block b).creator (tl.built b)) : x ∈ (U.block b).refs := by
  obtain ⟨z, hz, hzc⟩ := h.covers b hb hbc x hxH hxr
  have hzr := (U.valid b hb).predecessor z hz
  obtain rfl : z = x := U.eq_of_creator_eq (U.complete b hb z hz) hx hxc hzc rfl (by omega)
  exact hz

/-- A node of `T` that holds a quorum of round `r`, from `R` to below `N`,
at a time `t ≥ G` has built above round `r` by `t + max τ μ`. -/
theorem built_of_quorumIn {v : Validator} (hv : v ∈ T) {r t : ℕ}
    (hr : R ≤ r) (hrN : r < N) (hG : G ≤ t) (hQ : QuorumIn U (tl.held v t) r) :
    ∃ b ∈ U.ids, (U.block b).creator = v ∧ r + 1 ≤ (U.block b).round ∧
      tl.built b ≤ t + max τ μ := by
  have := le_max_left τ μ
  have := le_max_right τ μ
  exact h.prompt v hv r _ hr hrN (Or.inl ⟨by omega,
    quorumIn_mono (h.mono v hv t _ hG (by omega)) hQ,
    Or.inr (Or.inr ⟨by omega, quorumIn_mono (h.mono v hv t _ hG (by omega)) hQ⟩)⟩)

/-- A node of `T` that holds what it waits for above round `r`, from `R` to
below `N`, at a time `t ≥ G` has built above round `r` by `t + max γ μ`. -/
theorem built_of_waitsFor {v : Validator} (hv : v ∈ T) {r t : ℕ}
    (hr : R ≤ r) (hrN : r < N) (hG : G ≤ t) (hW : WaitsFor U (tl.held v t) r) :
    ∃ b ∈ U.ids, (U.block b).creator = v ∧ r + 1 ≤ (U.block b).round ∧
      tl.built b ≤ t + max γ μ := by
  have := le_max_left γ μ
  have := le_max_right γ μ
  exact h.prompt v hv r _ hr hrN (Or.inl ⟨by omega,
    quorumIn_mono (h.mono v hv t _ hG (by omega)) hW.1,
    Or.inl ⟨by omega, waitsFor_mono (h.mono v hv t _ hG (by omega)) hW⟩⟩)

/-- **Induction behind**: a property of the blocks of round `s + 1`, `s ≥ R`,
by authors of `T`, that holds for those built on the wait or the timer, and
passes to a block from a block of the round by an author of `T` that its
author holds, holds for every block of round `s + 1` by an author of `T`. -/
theorem induction_behind {s : ℕ} (hR : R ≤ s) (P : BlockId → Prop)
    (hwait : ∀ b ∈ U.ids, (U.block b).creator ∈ T → (U.block b).round = s + 1 →
      (γ ≤ tl.built b ∧ WaitsFor U (tl.held (U.block b).creator (tl.built b - γ)) s ∧
          WaitsFor U (tl.held (U.block b).creator (tl.built b)) s) ∨
        (WaitsFor U (tl.held (U.block b).creator (tl.built b)) s ∧
          AllIn U (tl.held (U.block b).creator (tl.built b)) s) ∨
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
    rcases h.waits b hb (h.stable hbT) s hbr hR with hW | hW | hW | hB
    · exact hwait b hb hbT hbr (Or.inl hW)
    · exact hwait b hb hbT hbr (Or.inr (Or.inl hW))
    · exact hwait b hb hbT hbr (Or.inr (Or.inr hW))
    · obtain ⟨y, hyH, hyr, hyT, hyv⟩ := exists_mem_of_behindIn h.large hB
      exact hstep b hb hbT hbr y hyH hyT hyr (ih _ (hn ▸ h.prior _ (h.stable hbT) _ y hyH
        (h.stable hyT) hyv) y (h.held_ids _ _ hyH) hyT hyr rfl)

/-- **Catching up**: once nodes of `T` hold, at a time `t ≥ G`, blocks of
round `s + 1`, from `R + 1` to `N`, by `f + 1` correct authors, every
validator of `T` has reached round `s + 1` by `t + δ`. -/
theorem reachedBy_of_behind {s t : ℕ} (hR : R ≤ s) (hN : s < N) (hG : G ≤ t)
    {A : Finset Validator} (hA : A ⊆ T) (hcard : F.f + 1 ≤ A.card)
    (hb : ∀ v ∈ A, ∃ u ∈ T, ∃ b ∈ tl.held u t,
      (U.block b).creator = v ∧ (U.block b).round = s + 1) :
    ReachedBy U tl T (s + 1) (t + δ) := by
  intro w hw
  by_cases hwA : w ∈ A
  · obtain ⟨u, hu, b, hb, hbw, hbr⟩ := hb w hwA
    exact ⟨b, h.held_ids _ _ hb, hbw, hbr.ge,
      (h.causal u (h.stable hu) t b hb (hbw ▸ h.stable (hA hwA))).trans (by omega)⟩
  refine h.prompt w hw s _ hR hN (Or.inr ⟨by omega, le_trans hcard
    (Finset.card_le_card fun v hv => ?_)⟩)
  obtain ⟨u, hu, b, hb', hbv, hbr⟩ := hb v hv
  refine Finset.mem_erase.mpr ⟨fun hvw => hwA (hvw ▸ hv), mem_creatorsOf.mpr ⟨b,
    Finset.mem_filter.mpr ⟨h.mem_held_of_held hu hG hb' (hbv ▸ h.stable (hA hv)) hw le_rfl,
      hbr⟩, hbv⟩⟩

/-- **A quorum brings every node of `T` to its round**: once a node of `T`
holds, at a time `t ≥ G`, blocks of a quorum at round `s`, from `R + 1` to
`N`, every validator of `T` has reached round `s` by `t + δ`. -/
theorem reachedBy_of_quorumIn {s t : ℕ} (hR : R < s) (hN : s ≤ N) (hG : G ≤ t) {u : Validator}
    (hu : u ∈ T) (hQ : QuorumIn U (tl.held u t) s) : ReachedBy U tl T s (t + δ) := by
  obtain ⟨s, rfl⟩ : ∃ s', s = s' + 1 := ⟨s - 1, by omega⟩
  refine h.reachedBy_of_behind (by omega) (by omega) hG Finset.inter_subset_right
    (card_inter_ge_of_quorum hQ h.large) fun v hv => ?_
  obtain ⟨hvc, -⟩ := Finset.mem_inter.mp hv
  obtain ⟨x, hx, hxv⟩ := mem_creatorsOf.mp hvc
  obtain ⟨hxH, hxr⟩ := Finset.mem_filter.mp hx
  exact ⟨u, hu, x, hxH, hxv, hxr⟩

/-- **Every round up to `N` is reached, each within `δ + max τ μ`** of a time
from `G` on. -/
theorem reachedBy_succ {s t : ℕ} (hs : R ≤ s) (hsN : s < N) (hG : G ≤ t)
    (hb : ReachedBy U tl T s t) : ReachedBy U tl T (s + 1) (t + δ + max τ μ) := fun _ hv =>
  h.built_of_quorumIn hv hs hsN (by omega) (h.quorumIn_of_reachedBy hG hb hv)

/-- **Recovery**: once a validator of `T` has built at a round `r`, from
`R + 1` to `N`, by a time `t₀ ≥ G`, every validator of `T` reaches round `r`
by `t₀ + δ + max τ μ`. Its author keeps its block of round `r` on disk. -/
theorem reachedBy_of_built {b : BlockId} (hb : b ∈ U.ids)
    (hbT : (U.block b).creator ∈ T) {t₀ : ℕ} (hG : G ≤ t₀) (hbt : tl.built b ≤ t₀)
    (hRb : R < (U.block b).round) (hbN : (U.block b).round ≤ N) :
    ReachedBy U tl T (U.block b).round (t₀ + δ + max τ μ) := by
  intro w hw
  have hbc := h.stable hbT
  have hbw := h.mem_held_of_held hbT hG (h.disk_held _ hbc t₀ (h.stores b hb hbc t₀ hbt).1)
    hbc hw le_rfl
  obtain ⟨b', hb', hb'w, hb'r, hb't⟩ := h.built_of_quorumIn hw (r := (U.block b).round - 1)
    (t := t₀ + δ) (by omega) (by omega) (by omega)
    (h.quorumIn_of_held (h.stable hw) hbw hbc (by omega))
  exact ⟨b', hb', hb'w, by omega, hb't⟩

end NodeRules

namespace ReactiveRules

variable (h : ReactiveRules U tl T G δ τ γ μ R N)
include h

/-- Every round from `R` to `N` is reached by some time. -/
theorem exists_reachedBy {s : ℕ} (hs : R ≤ s) (hsN : s ≤ N) : ∃ t, ReachedBy U tl T s t := by
  induction s, hs using Nat.le_induction with
  | base => exact h.start
  | succ s hs ih =>
    obtain ⟨t, ht⟩ := ih (by omega)
    exact ⟨_, h.reachedBy_succ hs (by omega) (le_max_right t G)
      (reachedBy_mono ht (le_max_left t G))⟩

/-- **A reactive run starts after `G + τ`**: the round `R'` after the last
round from `R` on that a node of `T` reached before `G + τ`, or `R` if there
is none, starts a reactive run, and every validator of `T` reaches it within
`2δ + 2 max τ μ` of `G + τ` and of the time all reached round `R`. -/
theorem exists_run : ∃ R', R ≤ R' ∧ (R' = R ∨ ∃ x ∈ U.ids,
    (U.block x).creator ∈ T ∧ (U.block x).round + 1 = R' ∧
      tl.built x < G + τ) ∧ (R' ≤ N → ReactiveRun U tl T G δ τ γ μ R' N ∧
    ∀ t₀, ReachedBy U tl T R t₀ → ReachedBy U tl T R' (max t₀ (G + τ) + 2 * δ + 2 * max τ μ)) := by
  classical
  set X := U.ids.filter fun x => (U.block x).creator ∈ T ∧
    R ≤ (U.block x).round ∧ tl.built x < G + τ
  by_cases hX : X.Nonempty
  · obtain ⟨x, hxX, hmax⟩ := X.exists_max_image (fun x => (U.block x).round) hX
    obtain ⟨hx, hxc, hxR, hxt⟩ := Finset.mem_filter.mp hxX
    refine ⟨(U.block x).round + 1, by omega, Or.inr ⟨x, hx, hxc, rfl, hxt⟩, fun hN => ?_⟩
    have hbuilt : ∀ t₀, ReachedBy U tl T R t₀ →
        ReachedBy U tl T ((U.block x).round + 1) (max t₀ (G + τ) + 2 * δ + 2 * max τ μ) := by
      intro t₀ ht₀
      have hm : ReachedBy U tl T (U.block x).round (max t₀ (G + τ) + δ + max τ μ) := by
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

end ReactiveRules

namespace NodeRules

variable (h : NodeRules U tl T G δ τ γ μ R N)
include h

/-- **Operations resume**: once a validator of `T` has built above round `R`
by `G`, a reactive run starts above `R`, and every validator of `T` reaches
it within `3δ + 3 max τ μ` of `G`. -/
theorem exists_resumed {b : BlockId} (hb : b ∈ U.ids)
    (hbc : (U.block b).creator ∈ T) (hbG : tl.built b ≤ G)
    (hRb : R < (U.block b).round) :
    ∃ R', R < R' ∧ (R' ≤ N → ReactiveRun U tl T G δ τ γ μ R' N ∧
      ReachedBy U tl T R' (G + 3 * δ + 3 * max τ μ)) := by
  by_cases hbN : (U.block b).round ≤ N
  · have hr := h.reachedBy_of_built hb hbc le_rfl hbG hRb hbN
    have hrules : ReactiveRules U tl T G δ τ γ μ (U.block b).round N := ⟨h.above hRb.le, _, hr⟩
    obtain ⟨R', hR', -, hrun⟩ := hrules.exists_run
    refine ⟨R', by omega, fun hR'N => ⟨(hrun hR'N).1, reachedBy_mono ((hrun hR'N).2 _ hr) ?_⟩⟩
    have := le_max_left τ μ
    omega
  · exact ⟨_, hRb, fun h' => absurd h' hbN⟩

/-- **Nothing a leader outputs is lost**: when correct nodes keep histories
on disk, every block of the available sub-DAG of a certified block is on the
disk of a node of `T` from some time on, through any crash. A quorum of
voters, or `f + 1` authors, include a node of `T`. -/
theorem exists_disk_of_avail {K : ℕ} (hK : KeepsHistory U tl K) {A z : BlockId} {r : ℕ}
    (hA : A ∈ U.ids) (hC : (certificatesAt U (IsVote U) (quorumCard Validator) A r).Nonempty)
    (hz : z ∈ Avail U K A) :
    ∃ w ∈ T, ∃ t₀, ∀ t, t₀ ≤ t → z ∈ tl.disk w t := by
  obtain ⟨y, hy, hzy⟩ := hz
  cases hy with
  | anchor =>
    obtain ⟨C, hC⟩ := hC
    obtain ⟨hCi, -, hv⟩ := mem_certificatesAt.mp hC
    obtain ⟨b, hb, hbT⟩ := exists_mem_of_quorum h.large hv
    obtain ⟨hbC, hbA⟩ := mem_carriedVotes.mp hb
    exact ⟨_, hbT, _, fun t ht =>
      hK b (U.complete C hCi b hbC) (h.stable hbT) t ht A hbA hzy⟩
  | referenced S yf hyf hzf href hcard =>
    obtain ⟨c, hc, hcT⟩ := exists_mem_of_card h.large hcard
    obtain ⟨w, hw, rfl⟩ := mem_creatorsOf.mp hc
    exact ⟨_, hcT, _, fun t ht => hK w (avail_subset_ids hA ⟨yf w, hyf w hw, hzf w hw⟩)
      (h.stable hcT) t ht y (href w hw) hzy⟩

end NodeRules

namespace ReactiveRun

variable (h : ReactiveRun U tl T G δ τ γ μ R N)
include h

/-- Every validator of `T` has reached a round from `R` on only at `G + τ`
or later. -/
theorem le_of_reachedBy {s t : ℕ} (hs : R ≤ s) (hb : ReachedBy U tl T s t) : G + τ ≤ t := by
  obtain ⟨v, hv⟩ := Finset.card_pos.mp
    (by have := h.large; have := F.card_validators; omega : 0 < T.card)
  obtain ⟨b, hb, hbv, hbr, hbt⟩ := hb v hv
  have := h.late b hb (hbv ▸ hv) (by omega)
  omega

/-- A block of `T` from round `R` on, built by `t₀`, is held by every node of
`T` from `t₀ + δ` on. -/
theorem mem_held_of_round {b : BlockId} (hb : b ∈ U.ids)
    (hbc : (U.block b).creator ∈ T) (hbR : R ≤ (U.block b).round)
    {v : Validator} (hv : v ∈ T) {t₀ t : ℕ}
    (h0 : tl.built b ≤ t₀) (ht : t₀ + δ ≤ t) : b ∈ tl.held v t :=
  h.mem_held_of_held hbc (by have := h.late b hb hbc hbR; omega) (h.own b hb (h.stable hbc))
    (h.stable hbc) hv (by omega)

/-- **No node of `T` skips a round of the run**, at `δ < γ ≤ τ`: by the
time a block of `T` of round `s + 1`, `s` from `R + 1` to `N`, is built,
every validator of `T` has built at round `s`. -/
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
    -- a node of `T` that built above `s` before `n` built at `s`
    have hup : ∀ e ∈ U.ids, (U.block e).creator = x → s ≤ (U.block e).round →
        tl.built e < n →
        ∃ z ∈ U.ids, (U.block z).creator = x ∧ (U.block z).round = s ∧ tl.built z ≤ n := by
      intro e he hex hes hen
      rcases Nat.eq_or_lt_of_le hes with heq | hlt
      · exact ⟨e, he, hex, heq.symm, hen.le⟩
      obtain ⟨y, hy, hyT, hyr, hyt⟩ := h.exists_succ_built he (hex ▸ hx) hlt
      obtain ⟨z, hz, hzx, hzr, hzt⟩ := ih _ (by omega) y hy hyT hyr rfl _ hx
      exact ⟨z, hz, hzx, hzr, by omega⟩
    -- the author of `c` held a quorum of round `s` at `t₁ ≥ G`, with `t₁ + δ < n`
    have hquorum : ∀ t₁, G ≤ t₁ → t₁ + δ < n →
        QuorumIn U (tl.held (U.block c).creator t₁) s →
        ∃ z ∈ U.ids, (U.block z).creator = x ∧ (U.block z).round = s ∧ tl.built z ≤ n := by
      intro t₁ hG ht₁ hQ
      obtain ⟨e, he, hex, hes, het⟩ := h.reachedBy_of_quorumIn (by omega) hsN hG hcT hQ x hx
      exact hup e he hex hes (by omega)
    have hlc := h.late c hc hcT (by omega)
    rcases h.waits c hc hcc s hcr (by omega) with ⟨-, hW, -⟩ | ⟨-, hA⟩ | ⟨-, hQ⟩ | hB
    · exact hquorum _ (by omega) (by omega) hW.1
    · obtain ⟨z, hzH, hzr, hzx⟩ := hA x
      exact ⟨z, h.held_ids _ _ hzH, hzx, hzr,
        (h.causal _ hcc _ z hzH (hzx ▸ hxc)).trans hn.le⟩
    · exact hquorum _ (by omega) (by omega) hQ
    · obtain ⟨y, hyH, hyr, hyT, hyv⟩ := exists_mem_of_behindIn h.large hB
      have hyt := h.prior _ hcc _ y hyH (h.stable hyT) hyv
      obtain ⟨z, hz, hzx, hzr, hzt⟩ := ih _ (by omega) y (h.held_ids _ _ hyH) hyT hyr rfl x hx
      exact ⟨z, hz, hzx, hzr, by omega⟩

/-- **Exact rounds in the run**, at `δ < γ ≤ τ`: once every validator of `T`
has reached round `s`, from `R + 1` to `N`, by `t`, every validator of `T`
has built at round `s` by `t`. -/
theorem builtBy_of_reachedBy (hδ : δ < γ) (hγτ : γ ≤ τ) {s t : ℕ} (hs : R + 1 ≤ s)
    (hsN : s ≤ N) (hb : ReachedBy U tl T s t) : BuiltBy U tl T s t := by
  intro x hx
  obtain ⟨e, he, hex, hes, het⟩ := hb x hx
  rcases Nat.eq_or_lt_of_le hes with heq | hlt
  · exact ⟨e, he, hex, heq.symm, het⟩
  obtain ⟨y, hy, hyT, hyr, hyt⟩ := h.exists_succ_built he (hex ▸ hx) hlt
  obtain ⟨z, hz, hzx, hzr, hzt⟩ := h.builtBy_below hδ hγτ hs hsN hy hyT hyr _ hx
  exact ⟨z, hz, hzx, hzr, by omega⟩

/-- **A leader of `T` reaches every voter of `T` before its timeout**, at
`τ ≥ 2δ` and `δ < γ ≤ τ`: a block of `T` one round above a slot led by a
validator of `T`, from round `R + 1` on, is built once its author holds a
leader block of the slot. -/
theorem leader_mem_held (hτ : 2 * δ ≤ τ) (hδ : δ < γ) (hγτ : γ ≤ τ) {k : ℕ}
    (hk : R + 1 ≤ S.slotRound k) (hN : S.slotRound k + 2 ≤ N) (hlead : S.leader k ∈ T)
    {b : BlockId} (hb : b ∈ U.ids) (hbT : (U.block b).creator ∈ T)
    (hbr : (U.block b).round = S.slotRound k + 1) :
    ∃ L ∈ tl.held (U.block b).creator (tl.built b), IsLeaderBlock U k L := by
  refine h.induction_behind (by omega)
    (fun b => ∃ L ∈ tl.held (U.block b).creator (tl.built b), IsLeaderBlock U k L)
    (fun b hb hbT hbr hW => ?_) (fun b hb hbT hbr y hyH hyT hyr hy => ?_) hb hbT hbr
  · rcases hW with ⟨-, -, hW⟩ | ⟨hW, -⟩ | ⟨hτb, hQ⟩
    · exact hW.2.1 k rfl
    · exact hW.2.1 k rfl
    have hlb := h.late b hb hbT (by omega)
    obtain ⟨L, hL, hLc, hLr, hLt⟩ := h.builtBy_of_reachedBy hδ hγτ hk (by omega)
      (h.reachedBy_of_quorumIn (t := tl.built b - τ) (by omega) (by omega) (by omega) hbT hQ)
      _ hlead
    exact ⟨L, h.mem_held_of_round hL (hLc ▸ hlead) (by omega) hbT hLt (by omega), hL, by omega,
      hLc⟩
  · obtain ⟨L, hL, hlead'⟩ := h.votes (h.held_ids _ _ hyH) (h.stable hyT) (by omega) hy
    exact ⟨L, h.closed _ (h.stable hbT) _ y hyH (h.stable hyT) hL, hlead'⟩

/-- **Every voter of `T` votes for a leader of `T`**: a block of `T` one round
above a slot led by a validator of `T`, from round `R + 1` on, references
the slot's leader block. -/
theorem mem_refs_of_leader (hτ : 2 * δ ≤ τ) (hδ : δ < γ) (hγτ : γ ≤ τ) {k : ℕ}
    (hk : R + 1 ≤ S.slotRound k) (hN : S.slotRound k + 2 ≤ N) (hlead : S.leader k ∈ T)
    {b : BlockId} (hb : b ∈ U.ids) (hbT : (U.block b).creator ∈ T)
    (hbr : (U.block b).round = S.slotRound k + 1) {L : BlockId} (hL : IsLeaderBlock U k L) :
    L ∈ (U.block b).refs := by
  obtain ⟨L', hL', hlead'⟩ :=
    h.votes hb (h.stable hbT) hbr.symm (h.leader_mem_held hτ hδ hγτ hk hN hlead hb hbT hbr)
  exact isLeaderBlock_unique_of_honest (h.stable hlead) hL hlead' ▸ hL'

/-- **The votes of `T` certify a leader of `T`**, at `τ ≥ 2δ` and
`δ < γ ≤ τ`: once every validator of `T` has built one round above a slot led
by a validator of `T`, from round `R + 1` on, by `t`, every node of `T` holds
a certificate for the slot's leader block from `t + δ` on. -/
theorem certIn_of_builtBy (hτ : 2 * δ ≤ τ) (hδ : δ < γ) (hγτ : γ ≤ τ) {k t t' : ℕ}
    (hk : R + 1 ≤ S.slotRound k) (hN : S.slotRound k + 2 ≤ N) (hlead : S.leader k ∈ T)
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

/-- **The votes of `T` reach every node of `T` before its timeout two rounds
above**, at `τ ≥ 2δ` and `δ < γ ≤ τ`: a block of `T` two rounds above a slot
led by a validator of `T`, from round `R + 1` on, is built once its author
holds a certificate for the slot's leader block. -/
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
  · rcases hW with ⟨-, -, hW⟩ | ⟨hW, -⟩ | ⟨hτc, hQ⟩
    · exact hW.2.2 k rfl
    · exact hW.2.2 k rfl
    have hlc := h.late c hc hcT (by omega)
    exact h.certIn_of_builtBy hτ hδ hγτ hk hN hlead (h.builtBy_of_reachedBy hδ hγτ (by omega)
      (by omega) (h.reachedBy_of_quorumIn (t := tl.built c - τ) (by omega) (by omega) (by omega)
        hcT hQ)) hcT (by omega)
  · have hy' := h.held_ids _ _ hyH
    obtain ⟨L, hL, hv⟩ := h.certifies y hy' (h.stable hyT) k (by omega) hy
    refine ⟨L, hL, le_trans hv (Finset.card_le_card (Finset.image_subset_image fun z hz => ?_))⟩
    obtain ⟨-, hzr, hzL⟩ := mem_carriedVotes_spec hy' hyr hz
    exact Finset.mem_filter.mpr ⟨h.closed _ (h.stable hcT) _ y hyH (h.stable hyT)
      (mem_carriedVotes.mp hz).1, hzr, hzL⟩

/-- **Every certifier of `T` certifies a leader of `T`**: a block of `T` two
rounds above a slot led by a validator of `T`, from round `R + 1` on,
carries votes from a quorum for the slot's leader block. -/
theorem carriesVotes_of_leader (hτ : 2 * δ ≤ τ) (hδ : δ < γ) (hγτ : γ ≤ τ) {k : ℕ}
    (hk : R + 1 ≤ S.slotRound k) (hN : S.slotRound k + 2 ≤ N) (hlead : S.leader k ∈ T)
    {c : BlockId} (hc : c ∈ U.ids) (hcT : (U.block c).creator ∈ T)
    (hcr : (U.block c).round = S.slotRound k + 2) {L : BlockId} (hL : IsLeaderBlock U k L) :
    CarriesVotes U (IsVote U) (quorumCard Validator) c L := by
  obtain ⟨L', hL', hv⟩ := h.certifies c hc (h.stable hcT) k hcr.symm
    (h.certIn_held hτ hδ hγτ hk hN hlead hc hcT hcr)
  exact isLeaderBlock_unique_of_honest (h.stable hlead) hL hL' ▸ hv

/-- **A round led by `T` is built within `δ + max γ μ`**, at `τ ≥ 2δ` and
`δ < γ ≤ τ`: when the slots at round `s ≥ R + 2` and one round below have
leaders in `T`, every node of `T` holds what it waits for above `s` once it
holds the blocks of `T` of round `s`. -/
theorem builtBy_succ_fast (hτ : 2 * δ ≤ τ) (hδ : δ < γ) (hγτ : γ ≤ τ) {s t : ℕ}
    (hs : R + 2 ≤ s) (hsN : s < N) (hb : BuiltBy U tl T s t)
    (hlead : ∀ k, S.slotRound k = s ∨ S.slotRound k + 1 = s → S.leader k ∈ T) :
    BuiltBy U tl T (s + 1) (t + δ + max γ μ) := by
  have hG := h.le_of_reachedBy (by omega) hb.reachedBy
  refine h.builtBy_of_reachedBy hδ hγτ (by omega) (by omega) fun v hv => ?_
  refine h.built_of_waitsFor hv (by omega) hsN (by omega)
    ⟨h.quorumIn_of_reachedBy (by omega) hb.reachedBy hv, fun k hk => ?_, fun k hk => ?_⟩
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

/-- **Responsiveness among `T`** from round `R + 1` to `N`, at `τ ≥ 2δ` and
`δ < γ ≤ τ`. -/
theorem respondsFrom (hτ : 2 * δ ≤ τ) (hδ : δ < γ) (hγτ : γ ≤ τ) :
    RespondsFrom U T (R + 1) N := by
  refine ⟨h.large, fun k hk hN hlead => ?_⟩
  obtain ⟨L, hL, hLc, hLr⟩ := h.populatedOn hδ hγτ hk (by omega) _ hlead
  exact ⟨h.populatedOn hδ hγτ (by omega) hN, L, ⟨hL, hLr, hLc⟩, fun C hC hCT hCr =>
    h.carriesVotes_of_leader hτ hδ hγτ hk hN hlead hC hCT hCr ⟨hL, hLr, hLc⟩⟩

/-- **A slot led by `T` commits within `3δ + 2 max γ μ`**, at `τ ≥ 2δ` and
`δ < γ ≤ τ`: when every slot from one round below a slot at round `r`, from
`R + 2` to `N − 2`, to one round above it has a leader in `T`, and every
validator of `T` has built at round `r` by `t`, every node of `T` commits the
slot directly by `t + 3δ + 2 max γ μ`. -/
theorem nodeDecided_fast (hτ : 2 * δ ≤ τ) (hδ : δ < γ) (hγτ : γ ≤ τ) (K : ℕ) {k t : ℕ}
    (hk : R + 2 ≤ S.slotRound k) (hN : S.slotRound k + 2 ≤ N)
    (hlead : ∀ j, S.slotRound k ≤ S.slotRound j + 1 → S.slotRound j ≤ S.slotRound k + 1 →
      S.leader j ∈ T)
    (hb : BuiltBy U tl T (S.slotRound k) t) {v : Validator} (hv : v ∈ T) :
    ∃ L, IsLeaderBlock U k L ∧
      NodeDecided U K (tl.held v (t + 3 * δ + 2 * max γ μ)) k (some L) := by
  have h1 := h.builtBy_succ_fast hτ hδ hγτ hk (by omega) hb fun j hj =>
    hlead j (by omega) (by omega)
  have h2 := h.builtBy_succ_fast hτ hδ hγτ (by omega) (by omega) h1 fun j hj =>
    hlead j (by omega) (by omega)
  have hlk := hlead k (by omega) (by omega)
  refine nodeDecided_of_responds h.large
    ((h.respondsFrom hτ hδ hγτ).2 k (by omega) hN hlk) ?_
  rintro z ⟨c, hc, hcT, hlo, hhi, hz⟩
  obtain ⟨c', hc', hcc', hcr', hct'⟩ := h2 _ hcT
  have hcc'' : c = c' := U.eq_of_creator_eq hc hc' (h.stable hcT) rfl hcc' (by omega)
  subst hcc''
  have hheld : c ∈ tl.held v (t + 3 * δ + 2 * max γ μ) :=
    h.mem_held_of_round hc hcT (by omega) hv hct' (by omega)
  rcases hz with rfl | hz
  · exact hheld
  · exact h.closed v (h.stable hv) _ c hheld (h.stable hcT) hz

/-- **A node of `T` holds the blocks of `T` of the round below when it
builds**, at `2δ ≤ γ ≤ τ` and `δ < γ`: a block of `T` of round `r + 1`, `r`
from `R + 1` to `N`, is built once its author holds every block of `T` of
round `r`. -/
theorem mem_held_below (hγ : 2 * δ ≤ γ) (hδ : δ < γ) (hγτ : γ ≤ τ) {r : ℕ} (hr : R + 1 ≤ r)
    (hrN : r ≤ N) {x : BlockId} (hx : x ∈ U.ids) (hxT : (U.block x).creator ∈ T)
    (hxr : (U.block x).round = r) {b : BlockId} (hb : b ∈ U.ids)
    (hbT : (U.block b).creator ∈ T)
    (hbr : (U.block b).round = r + 1) : x ∈ tl.held (U.block b).creator (tl.built b) := by
  -- a node of `T` holding a quorum of round `r` at `t` holds `x` by `t + 2δ`
  have hquorum : ∀ b, (U.block b).creator ∈ T → ∀ t, G ≤ t →
      t + 2 * δ ≤ tl.built b → QuorumIn U (tl.held (U.block b).creator t) r →
      x ∈ tl.held (U.block b).creator (tl.built b) := by
    intro b hbT t hG ht hQ
    obtain ⟨y, hy, hyc, hyr, hyt⟩ := h.builtBy_of_reachedBy hδ hγτ hr hrN
      (h.reachedBy_of_quorumIn (by omega) hrN hG hbT hQ) _ hxT
    obtain rfl : y = x := U.eq_of_creator_eq hy hx (h.stable hxT) hyc rfl (by omega)
    exact h.mem_held_of_round hy hxT (by omega) hbT (t₀ := t + δ) hyt (by omega)
  refine h.induction_behind (s := r) (by omega)
    (fun b => x ∈ tl.held (U.block b).creator (tl.built b))
    (fun b hb hbT hbr hW => ?_) (fun b hb hbT hbr y hyH hyT hyr hy => ?_) hb hbT hbr
  · have hlb := h.late b hb hbT (by omega)
    rcases hW with ⟨hγb, hW, -⟩ | ⟨-, hA⟩ | ⟨hτb, hQ⟩
    · exact hquorum b hbT _ (by omega) (by omega) hW.1
    · obtain ⟨x', hx'H, hx'r, hx'c⟩ := hA (U.block x).creator
      obtain rfl : x' = x :=
        U.eq_of_creator_eq (h.held_ids _ _ hx'H) hx (h.stable hxT) hx'c rfl (by omega)
      exact hx'H
    · exact hquorum b hbT _ (by omega) (by omega) hQ
  · exact h.closed _ (h.stable hbT) _ y hyH (h.stable hyT) (h.mem_refs_of_held
      (h.held_ids _ _ hyH) (h.stable hyT) hx (h.stable hxT) (by omega) hy)

/-- **The run is synchronous among `T`** from round `R + 1` to `N`, at
`2δ ≤ γ ≤ τ` and `δ < γ`: every block of `T` references every block of `T`
of the round below. -/
theorem syncFrom (hγ : 2 * δ ≤ γ) (hδ : δ < γ) (hγτ : γ ≤ τ) : SyncFrom U T (R + 1) N := by
  refine ⟨h.large, fun n hn hnN b hb hbr hbT a ha har haT => ?_, fun r hr hrN v hv => ?_⟩
  · exact h.mem_refs_of_held hb (h.stable hbT) ha (h.stable haT) (by omega)
      (h.mem_held_below hγ hδ hγτ hn hnN.le ha haT har hb hbT hbr)
  · exact h.populatedOn hδ hγτ hr hrN v hv

/-- **The ledger grows**, at `τ ≥ 2δ` and `δ < γ ≤ τ`, when nodes of `T`
fetch the available sub-DAG of the certified leader blocks they hold within
`Δ`, and the schedule offers runs of `c` leaders of `T` spanning eligibility:
past any slot `k` there is a slot `b` such that, if the run reaches round
`σ(b + c − 1) + 2`, every node of `T`, at one time, decides every slot below
`b + c` and has fetched each leader it commits down to `D` rounds below it. -/
theorem exists_ledger (hτ : 2 * δ ≤ τ) (hδ : δ < γ) (hγτ : γ ≤ τ) {K Δ : ℕ} (D : ℕ)
    (hF : Fetches U tl T K G Δ) {c : ℕ} (hc : 0 < c)
    (hspan : ∀ b i, i < b → EligibleAt (S := S) 2 i (b + c - 1)) (fair : FairRunOn T c)
    (k : ℕ) :
    ∃ b, k ≤ b ∧ (S.slotRound (b + c - 1) + 2 ≤ N → ∃ t, ∀ v ∈ T,
      ∃ g : ℕ → Option BlockId, ∀ i, i < b + c → NodeDecided U K (tl.held v t) i (g i) ∧
        ∀ L, g i = some L → FetchedIn U K (tl.held v t) L ((U.block L).round - D)) := by
  classical
  obtain ⟨b, hkb, hRb, hrun⟩ := Slots.exists_run_past fair k (R + 1)
  refine ⟨b, hkb, fun hN => ⟨max G (U.ids.sup tl.built) + δ + Δ, fun v hv => ?_⟩⟩
  set T₀ := max G (U.ids.sup tl.built)
  have hT₀ : ∀ x ∈ U.ids, tl.built x ≤ T₀ := fun x hx =>
    (Finset.le_sup (f := tl.built) hx).trans (le_max_right _ _)
  have hresp := responds_of_run hc hRb hrun ⟨(h.respondsFrom hτ hδ hγτ).1,
    fun j h1 h2 h3 => (h.respondsFrom hτ hδ hγτ).2 j h1 (h2.trans hN) h3⟩
  have hheld : WithRefs U T (S.slotRound b) (S.slotRound (b + c - 1) + 2) ∪
      AvailBelow U K (b + c - 1) ⊆ ↑(tl.held v (T₀ + δ + Δ)) := by
    rintro z (⟨x, hx, hxT, hxlo, -, hzx⟩ | ⟨j, A, hj, hA, ⟨C, hC⟩, hzA⟩)
    · have hxv := h.mem_held_of_round hx hxT (by omega) hv (hT₀ x hx) (t := T₀ + δ + Δ)
        (by omega)
      rcases hzx with rfl | hzx
      · exact hxv
      · exact h.closed v (h.stable hv) _ x hxv (h.stable hxT) hzx
    · obtain ⟨hCi, -, hvC⟩ := mem_certificatesAt.mp hC
      obtain ⟨y, hyC, hyT⟩ := exists_mem_of_quorum h.large hvC
      obtain ⟨hyref, hyA⟩ := mem_carriedVotes.mp hyC
      have hy := U.complete C hCi y hyref
      have hyc := h.stable hyT
      have hyw := h.disk_held _ hyc T₀ (h.stores y hy hyc T₀ (hT₀ y hy)).1
      have hyv := h.mem_held_of_held hyT (le_max_left _ _) hyw hyc hv le_rfl
      exact hF v hv (T₀ + δ) (by omega) j A hA ⟨C, hC⟩
        (h.closed v (h.stable hv) _ y hyv hyc hyA) z hzA
  have hdec := nodeDecided_of_run h.large (h.held_ids v _) hc hspan hresp hheld
  refine ⟨fun i => if hi : i < b + c then (hdec i hi).choose else none, fun i hi => ?_⟩
  simp only [dif_pos hi]
  refine ⟨(hdec i hi).choose_spec, fun L hL => ?_⟩
  obtain ⟨hlead, hcert⟩ := NodeDecided.certified (h.held_ids v _) (hL ▸ (hdec i hi).choose_spec)
  exact fetchedIn_of_subset hlead.1 (Nat.sub_le _ _) fun z hz _ =>
    hheld (Set.mem_union_right _ ⟨i, L, by omega, hlead, hcert, hz⟩)

end ReactiveRun

end KPartialDag

end LeanDag
