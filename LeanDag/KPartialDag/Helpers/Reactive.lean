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

A node that holds a block above round `k ≥ R` holds a quorum at `k`
(`quorumIn_of_held`), and a correct node holds a block of its own as high
as any it built, from its disk (`exists_held_of_built`); so after crashes
before `G` every correct node reaches the highest round built by `G`
(`reachedBy_of_built`), and operations resume (`exists_resumed`). In a run,
at `δ < γ ≤ τ`, no correct node skips a round (`builtBy_below`).

A committed leader is certified (`certified_of_nodeDecided`), and its
available sub-DAG stays on a correct node's disk (`exists_disk_of_avail`).
Every certified leader is referenced by a correct vote that its author keeps
on disk, so every correct node holds it and fetches its available sub-DAG;
with the run responsive, every correct node decides every slot up to a run
of correct leaders (`exists_ledger`).
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
theorem reachedBy_mono {s t t' : ℕ} (hb : ReachedBy U tl s t) (ht : t ≤ t') :
    ReachedBy U tl s t' := fun v hv => by
  obtain ⟨b, hb, hbv, hbr, hbt⟩ := hb v hv
  exact ⟨b, hb, hbv, hbr, hbt.trans ht⟩

omit [DecidableEq BlockId] S in
theorem BuiltBy.reachedBy {s t : ℕ} (hb : BuiltBy U tl s t) : ReachedBy U tl s t :=
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

omit [DecidableEq BlockId] in
/-- A correct leader has one leader block. -/
theorem leaderBlock_eq {k : ℕ} {L L' : BlockId} (hL : IsLeaderBlock U k L)
    (hL' : IsLeaderBlock U k L') (hc : S.leader k ∈ (Correct : Finset Validator)) : L = L' :=
  U.eq_of_creator_eq hL.1 hL'.1 hc hL.2.2 hL'.2.2 (hL.2.1.trans hL'.2.1.symm)

/-- **A committed leader is certified**: a leader block that a node commits,
on blocks of the record, has a certificate in the record. -/
theorem certified_of_nodeDecided {K : ℕ} {H : Finset BlockId} (hH : H ⊆ U.ids) {k : ℕ}
    {L : BlockId} (h : NodeDecided U K H k (some L)) : IsLeaderBlock U k L ∧
      (certificatesAt U (IsVote U) (quorumCard Validator) L (S.slotRound k + 2)).Nonempty := by
  cases h with
  | directCommit hL hcard =>
    have hn := F.card_validators
    obtain ⟨c, hc⟩ := Finset.card_pos.mp (lt_of_lt_of_le (by omega) hcard)
    obtain ⟨C, hC, -⟩ := mem_creatorsOf.mp hc
    exact ⟨hL, C, (Finset.mem_filter.mp hC).1⟩
  | indirectCommit _ _ _ _ hL hlink =>
    obtain ⟨C, hC, -⟩ := linkedIn_avail hH hlink
    exact ⟨hL, C, hC⟩

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

variable (h : NodeRules U tl G δ τ γ μ R N)
include h

/-- The rules for nodes hold from any later round. -/
theorem above {R' : ℕ} (hR : R ≤ R') : NodeRules U tl G δ τ γ μ R' N :=
  { h with
    waits := fun b hb hbc r hbr hr => h.waits b hb hbc r hbr (hR.trans hr)
    prompt := fun v hv r t hr hrN hw => h.prompt v hv r t (hR.trans hr) hrN hw }

/-- From `G` on, a correct block that a correct node holds at `t₀` is held by
every correct node from `t₀ + δ` on. -/
theorem mem_held_of_held {u : Validator} (hu : u ∈ (Correct : Finset Validator)) {t₀ t : ℕ}
    (hG : G ≤ t₀) {b : BlockId} (hb : b ∈ tl.held u t₀)
    (hbc : (U.block b).creator ∈ (Correct : Finset Validator))
    {v : Validator} (hv : v ∈ (Correct : Finset Validator)) (ht : t₀ + δ ≤ t) :
    b ∈ tl.held v t :=
  h.mono v hv _ _ (by omega) ht (h.delivers u hu t₀ hG b hb hbc v hv)

/-- A correct block built at `G` or later, by `t₀`, is held by every correct
node from `t₀ + δ` on. -/
theorem mem_held {b : BlockId} (hb : b ∈ U.ids)
    (hbc : (U.block b).creator ∈ (Correct : Finset Validator))
    {v : Validator} (hv : v ∈ (Correct : Finset Validator)) {t₀ t : ℕ} (hG : G ≤ tl.built b)
    (h0 : tl.built b ≤ t₀) (ht : t₀ + δ ≤ t) : b ∈ tl.held v t :=
  h.mem_held_of_held hbc hG (h.own b hb hbc) hbc hv (by omega)

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
    obtain ⟨z, hz, hzr, hzc⟩ := exists_correct_of_quorumIn
      (quorumIn_refs (s := k + 1 + m) (h.held_ids _ _ hy) (by omega))
    exact ih (h.closed v hv t y hy hyc hz) hzc (by omega) hzr

/-- A correct node that holds a correct block above round `s` holds a
correct block of round `s + 1`. -/
theorem exists_succ_held {v : Validator} (hv : v ∈ (Correct : Finset Validator)) {t s : ℕ}
    {e : BlockId} (he : e ∈ tl.held v t)
    (hec : (U.block e).creator ∈ (Correct : Finset Validator)) (hes : s + 1 ≤ (U.block e).round) :
    ∃ y ∈ tl.held v t, (U.block y).creator ∈ (Correct : Finset Validator) ∧
      (U.block y).round = s + 1 := by
  rcases Nat.eq_or_lt_of_le hes with heq | hlt
  · exact ⟨e, he, hec, heq.symm⟩
  obtain ⟨y, hy, hyr, hyc⟩ := exists_correct_of_quorumIn (h.quorumIn_of_held hv he hec hlt)
  exact ⟨y, hy, hyc, hyr⟩

/-- **The disk**: a correct validator that has built at round `s` or above by
`t` holds at `t` a block of its own at round `s` or above, whatever it lost in
a restart. -/
theorem exists_held_of_built {v : Validator} (hv : v ∈ (Correct : Finset Validator)) {s t : ℕ}
    (hb : ∃ b ∈ U.ids, (U.block b).creator = v ∧ s ≤ (U.block b).round ∧ tl.built b ≤ t) :
    ∃ y ∈ tl.held v t, (U.block y).creator = v ∧ s ≤ (U.block y).round := by
  obtain ⟨b, hb, hbv, hbs, hbt⟩ := hb
  subst hbv
  exact ⟨b, h.disk_held _ hv t (h.stores b hb hv t hbt).1, rfl, hbs⟩

/-- Once every correct validator has reached round `s` by a time `t ≥ G`,
every correct node holds a quorum at round `s` by `t + δ`. -/
theorem quorumIn_of_reachedBy {s t : ℕ} (hG : G ≤ t) (hb : ReachedBy U tl s t)
    {v : Validator} (hv : v ∈ (Correct : Finset Validator)) :
    QuorumIn U (tl.held v (t + δ)) s := by
  by_cases habove : ∃ y ∈ tl.held v (t + δ),
      (U.block y).creator ∈ (Correct : Finset Validator) ∧ s < (U.block y).round
  · obtain ⟨y, hy, hyc, hys⟩ := habove
    exact h.quorumIn_of_held hv hy hyc hys
  push Not at habove
  exact quorum_le_of_correct fun w hw => by
    obtain ⟨y, hy, hyw, hys⟩ := h.exists_held_of_built hw (hb w hw)
    have hyv := h.mem_held_of_held hw hG hy (hyw ▸ hw) hv le_rfl
    exact ⟨y, Finset.mem_filter.mpr ⟨hyv, le_antisymm (habove y hyv (hyw ▸ hw)) hys⟩, hyw⟩

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
at a time `t ≥ G` has built above round `r` by `t + max τ μ`. -/
theorem built_of_quorumIn {v : Validator} (hv : v ∈ (Correct : Finset Validator)) {r t : ℕ}
    (hr : R ≤ r) (hrN : r < N) (hG : G ≤ t) (hQ : QuorumIn U (tl.held v t) r) :
    ∃ b ∈ U.ids, (U.block b).creator = v ∧ r + 1 ≤ (U.block b).round ∧
      tl.built b ≤ t + max τ μ := by
  have := le_max_left τ μ
  have := le_max_right τ μ
  exact h.prompt v hv r _ hr hrN (Or.inl ⟨by omega,
    quorumIn_mono (h.mono v hv t _ hG (by omega)) hQ,
    Or.inr (Or.inr ⟨by omega, quorumIn_mono (h.mono v hv t _ hG (by omega)) hQ⟩)⟩)

/-- A correct node that holds what it waits for above round `r`, from `R` to
below `N`, at a time `t ≥ G` has built above round `r` by `t + max γ μ`. -/
theorem built_of_waitsFor {v : Validator} (hv : v ∈ (Correct : Finset Validator)) {r t : ℕ}
    (hr : R ≤ r) (hrN : r < N) (hG : G ≤ t) (hW : WaitsFor U (tl.held v t) r) :
    ∃ b ∈ U.ids, (U.block b).creator = v ∧ r + 1 ≤ (U.block b).round ∧
      tl.built b ≤ t + max γ μ := by
  have := le_max_left γ μ
  have := le_max_right γ μ
  exact h.prompt v hv r _ hr hrN (Or.inl ⟨by omega,
    quorumIn_mono (h.mono v hv t _ hG (by omega)) hW.1,
    Or.inl ⟨by omega, waitsFor_mono (h.mono v hv t _ hG (by omega)) hW⟩⟩)

/-- **Induction behind**: a property of the correct blocks of round `s + 1`,
`s ≥ R`, that holds for those built on the wait or the timer, and passes to a
block from a correct block of the round its author holds, holds for every
correct block of round `s + 1`. -/
theorem induction_behind {s : ℕ} (hR : R ≤ s) (P : BlockId → Prop)
    (hwait : ∀ b ∈ U.ids, (U.block b).creator ∈ (Correct : Finset Validator) →
      (U.block b).round = s + 1 →
      (γ ≤ tl.built b ∧ WaitsFor U (tl.held (U.block b).creator (tl.built b - γ)) s ∧
          WaitsFor U (tl.held (U.block b).creator (tl.built b)) s) ∨
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

/-- **Catching up**: once correct nodes hold, at a time `t ≥ G`, blocks of
round `s + 1`, from `R + 1` to `N`, by `f + 1` correct authors, every
correct validator has reached round `s + 1` by `t + δ`. -/
theorem reachedBy_of_behind {s t : ℕ} (hR : R ≤ s) (hN : s < N) (hG : G ≤ t)
    {A : Finset Validator} (hA : A ⊆ (Correct : Finset Validator)) (hcard : F.f + 1 ≤ A.card)
    (hb : ∀ v ∈ A, ∃ u ∈ (Correct : Finset Validator), ∃ b ∈ tl.held u t,
      (U.block b).creator = v ∧ (U.block b).round = s + 1) :
    ReachedBy U tl (s + 1) (t + δ) := by
  intro w hw
  by_cases hwA : w ∈ A
  · obtain ⟨u, hu, b, hb, hbw, hbr⟩ := hb w hwA
    exact ⟨b, h.held_ids _ _ hb, hbw, hbr.ge,
      (h.causal u hu t b hb (hbw ▸ hA hwA)).trans (by omega)⟩
  refine h.prompt w hw s _ hR hN (Or.inr ⟨by omega, le_trans hcard
    (Finset.card_le_card fun v hv => ?_)⟩)
  obtain ⟨u, hu, b, hb', hbv, hbr⟩ := hb v hv
  refine Finset.mem_erase.mpr ⟨fun hvw => hwA (hvw ▸ hv), mem_creatorsOf.mpr ⟨b,
    Finset.mem_filter.mpr ⟨h.mem_held_of_held hu hG hb' (hbv ▸ hA hv) hw le_rfl, hbr⟩, hbv⟩⟩

/-- **A quorum brings every correct node to its round**: once a correct node
holds, at a time `t ≥ G`, blocks of a quorum at round `s + 1`, from `R + 1`
to `N`, every correct validator has reached round `s + 1` by `t + δ`. -/
theorem reachedBy_of_quorumIn {s t : ℕ} (hR : R ≤ s) (hN : s < N) (hG : G ≤ t) {u : Validator}
    (hu : u ∈ (Correct : Finset Validator)) (hQ : QuorumIn U (tl.held u t) (s + 1)) :
    ReachedBy U tl (s + 1) (t + δ) := by
  refine h.reachedBy_of_behind hR hN hG Finset.inter_subset_right
    (card_inter_correct_of_quorum hQ) fun v hv => ?_
  obtain ⟨hvc, -⟩ := Finset.mem_inter.mp hv
  obtain ⟨x, hx, hxv⟩ := mem_creatorsOf.mp hvc
  obtain ⟨hxH, hxr⟩ := Finset.mem_filter.mp hx
  exact ⟨u, hu, x, hxH, hxv, hxr⟩

/-- **Every round up to `N` is reached, each within `δ + max τ μ`** of a time
from `G` on. -/
theorem reachedBy_succ {s t : ℕ} (hs : R ≤ s) (hsN : s < N) (hG : G ≤ t)
    (hb : ReachedBy U tl s t) : ReachedBy U tl (s + 1) (t + δ + max τ μ) := fun _ hv =>
  h.built_of_quorumIn hv hs hsN (by omega) (h.quorumIn_of_reachedBy hG hb hv)

/-- **Recovery**: once a correct validator has built at a round `r`, from
`R + 1` to `N`, by `G`, every correct validator reaches round `r` by
`G + δ + max τ μ`. Its author keeps a block at `r` or above on disk. -/
theorem reachedBy_of_built {b : BlockId} (hb : b ∈ U.ids)
    (hbc : (U.block b).creator ∈ (Correct : Finset Validator)) (hbG : tl.built b ≤ G)
    (hRb : R < (U.block b).round) (hbN : (U.block b).round ≤ N) :
    ReachedBy U tl (U.block b).round (G + δ + max τ μ) := by
  intro w hw
  obtain ⟨y, hy, hyc, hyr⟩ :=
    h.exists_held_of_built hbc (s := (U.block b).round) ⟨b, hb, rfl, le_rfl, hbG⟩
  have hyw := h.mem_held_of_held hbc le_rfl hy (hyc ▸ hbc) hw le_rfl
  obtain ⟨b', hb', hb'w, hb'r, hb't⟩ := h.built_of_quorumIn hw (r := (U.block b).round - 1)
    (t := G + δ) (by omega) (by omega) (by omega)
    (h.quorumIn_of_held hw hyw (hyc ▸ hbc) (by omega))
  exact ⟨b', hb', hb'w, by omega, hb't⟩

end NodeRules

namespace ReactiveRules

variable (h : ReactiveRules U tl G δ τ γ μ R N)
include h

/-- The reactive rules hold from any later round that every correct
validator reaches. -/
theorem above {R' : ℕ} (hR : R ≤ R') (hs : ∃ t, ReachedBy U tl R' t) :
    ReactiveRules U tl G δ τ γ μ R' N :=
  ⟨h.toNodeRules.above hR, hs⟩

/-- Every round from `R` to `N` is reached by some time. -/
theorem exists_reachedBy {s : ℕ} (hs : R ≤ s) (hsN : s ≤ N) : ∃ t, ReachedBy U tl s t := by
  induction s, hs using Nat.le_induction with
  | base => exact h.start
  | succ s hs ih =>
    obtain ⟨t, ht⟩ := ih (by omega)
    exact ⟨_, h.reachedBy_succ hs (by omega) (le_max_right t G)
      (reachedBy_mono ht (le_max_left t G))⟩

/-- **A reactive run starts after `G + τ`**: the round `R'` after the last
round from `R` on that a correct node reached before `G + τ`, or `R` if there
is none, starts a reactive run, and every correct validator reaches it within
`2δ + 2 max τ μ` of `G + τ` and of the time all reached round `R`. -/
theorem exists_run : ∃ R', R ≤ R' ∧ (R' = R ∨ ∃ x ∈ U.ids,
    (U.block x).creator ∈ (Correct : Finset Validator) ∧ (U.block x).round + 1 = R' ∧
      tl.built x < G + τ) ∧ (R' ≤ N → ReactiveRun U tl G δ τ γ μ R' N ∧
    ∀ t₀, ReachedBy U tl R t₀ → ReachedBy U tl R' (max t₀ (G + τ) + 2 * δ + 2 * max τ μ)) := by
  classical
  set X := U.ids.filter fun x => (U.block x).creator ∈ (Correct : Finset Validator) ∧
    R ≤ (U.block x).round ∧ tl.built x < G + τ
  by_cases hX : X.Nonempty
  · obtain ⟨x, hxX, hmax⟩ := X.exists_max_image (fun x => (U.block x).round) hX
    obtain ⟨hx, hxc, hxR, hxt⟩ := Finset.mem_filter.mp hxX
    refine ⟨(U.block x).round + 1, by omega, Or.inr ⟨x, hx, hxc, rfl, hxt⟩, fun hN => ?_⟩
    have hbuilt : ∀ t₀, ReachedBy U tl R t₀ →
        ReachedBy U tl ((U.block x).round + 1) (max t₀ (G + τ) + 2 * δ + 2 * max τ μ) := by
      intro t₀ ht₀
      have hm : ReachedBy U tl (U.block x).round (max t₀ (G + τ) + δ + max τ μ) := by
        rcases Nat.eq_or_lt_of_le hxR with heq | hlt
        · exact reachedBy_mono (heq ▸ ht₀) (by omega)
        intro w hw
        obtain ⟨y, hy, hyc, hyr⟩ := h.exists_held_of_built hxc (s := (U.block x).round)
          ⟨x, hx, rfl, le_rfl, hxt.le⟩
        have hyw := h.mem_held_of_held hxc (by omega) hy (hyc ▸ hxc) hw le_rfl
        obtain ⟨b, hb, hbw, hbr, hbt⟩ := h.built_of_quorumIn hw (r := (U.block x).round - 1)
          (t := G + τ + δ) (by omega) (by omega) (by omega)
          (h.quorumIn_of_held hw hyw (hyc ▸ hxc) (by omega))
        exact ⟨b, hb, hbw, by omega, by omega⟩
      exact reachedBy_mono (h.reachedBy_succ hxR (by omega) (by omega) hm) (by omega)
    obtain ⟨t₀, ht₀⟩ := h.start
    refine ⟨⟨h.above (by omega) ⟨_, hbuilt t₀ ht₀⟩, fun b hb hbc hbr => ?_⟩, hbuilt⟩
    by_contra hlt
    have := hmax b (Finset.mem_filter.mpr ⟨hb, hbc, by omega, by omega⟩)
    omega
  · refine ⟨R, le_rfl, Or.inl rfl, fun _ => ⟨⟨h, fun b hb hbc hbr => ?_⟩,
      fun t₀ ht₀ => reachedBy_mono ht₀ (by omega)⟩⟩
    by_contra hlt
    exact hX ⟨b, Finset.mem_filter.mpr ⟨hb, hbc, hbr, by omega⟩⟩

end ReactiveRules

namespace NodeRules

variable (h : NodeRules U tl G δ τ γ μ R N)
include h

/-- **Operations resume**: once a correct validator has built above round `R`
by `G`, a reactive run starts above `R`, and every correct validator reaches
it within `3δ + 3 max τ μ` of `G`. -/
theorem exists_resumed {b : BlockId} (hb : b ∈ U.ids)
    (hbc : (U.block b).creator ∈ (Correct : Finset Validator)) (hbG : tl.built b ≤ G)
    (hRb : R < (U.block b).round) :
    ∃ R', R < R' ∧ (R' ≤ N → ReactiveRun U tl G δ τ γ μ R' N ∧
      ReachedBy U tl R' (G + 3 * δ + 3 * max τ μ)) := by
  by_cases hbN : (U.block b).round ≤ N
  · have hr := h.reachedBy_of_built hb hbc hbG hRb hbN
    have hrules : ReactiveRules U tl G δ τ γ μ (U.block b).round N := ⟨h.above hRb.le, _, hr⟩
    obtain ⟨R', hR', -, hrun⟩ := hrules.exists_run
    refine ⟨R', by omega, fun hR'N => ⟨(hrun hR'N).1, reachedBy_mono ((hrun hR'N).2 _ hr) ?_⟩⟩
    have := le_max_left τ μ
    omega
  · exact ⟨_, hRb, fun h' => absurd h' hbN⟩

/-- **Nothing a leader outputs is lost**: when correct nodes keep histories
on disk, every block of the available sub-DAG of a certified block is on a
correct node's disk from some time on, through any crash. -/
theorem exists_disk_of_avail {K : ℕ} (hK : KeepsHistory U tl K) {A z : BlockId} {r : ℕ}
    (hA : A ∈ U.ids) (hC : (certificatesAt U (IsVote U) (quorumCard Validator) A r).Nonempty)
    (hz : z ∈ Avail U K A) :
    ∃ w ∈ (Correct : Finset Validator), ∃ t₀, ∀ t, t₀ ≤ t → z ∈ tl.disk w t := by
  obtain ⟨c, hc, hcc, hzc | ⟨y, hy, hzy⟩⟩ := avail_correctHeld hA hC hz
  · subst hzc
    exact ⟨_, hcc, _, fun t ht => (h.stores z hc hcc t ht).1⟩
  · exact ⟨_, hcc, _, fun t ht => hK c hc hcc t ht y hy hzy⟩

end NodeRules

namespace ReactiveRun

variable (h : ReactiveRun U tl G δ τ γ μ R N)
include h

/-- Every correct validator has reached a round from `R` on only at `G + τ`
or later. -/
theorem le_of_reachedBy {s t : ℕ} (hs : R ≤ s) (hb : ReachedBy U tl s t) : G + τ ≤ t := by
  obtain ⟨v, -, hv⟩ := exists_correct_of_card (S := (Correct : Finset Validator))
    (by have := two_f_add_one_le_card_correct (Validator := Validator); omega)
  obtain ⟨b, hb, hbv, hbr, hbt⟩ := hb v hv
  have := h.late b hb (hbv ▸ hv) (by omega)
  omega

/-- A correct block from round `R` on, built by `t₀`, is held by every
correct node from `t₀ + δ` on. -/
theorem mem_held_of_round {b : BlockId} (hb : b ∈ U.ids)
    (hbc : (U.block b).creator ∈ (Correct : Finset Validator)) (hbR : R ≤ (U.block b).round)
    {v : Validator} (hv : v ∈ (Correct : Finset Validator)) {t₀ t : ℕ}
    (h0 : tl.built b ≤ t₀) (ht : t₀ + δ ≤ t) : b ∈ tl.held v t :=
  h.mem_held hb hbc hv (by have := h.late b hb hbc hbR; omega) h0 ht

/-- **No correct node skips a round of the run**, at `δ < γ ≤ τ`: by the time
a correct block of round `s + 1`, `s` from `R + 1` to `N`, is built, every
correct validator has built at round `s`. -/
theorem builtBy_below (hδ : δ < γ) (hγτ : γ ≤ τ) {s : ℕ} (hs : R + 1 ≤ s) (hsN : s ≤ N)
    {c : BlockId} (hc : c ∈ U.ids) (hcc : (U.block c).creator ∈ (Correct : Finset Validator))
    (hcr : (U.block c).round = s + 1) : BuiltBy U tl s (tl.built c) := by
  suffices ∀ n, ∀ c ∈ U.ids, (U.block c).creator ∈ (Correct : Finset Validator) →
      (U.block c).round = s + 1 → tl.built c = n → BuiltBy U tl s n from
    this _ c hc hcc hcr rfl
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro c hc hcc hcr hn x hx
    -- a correct node that built above `s` before `n` built at `s`
    have hup : ∀ e ∈ U.ids, (U.block e).creator = x → s ≤ (U.block e).round →
        tl.built e < n →
        ∃ z ∈ U.ids, (U.block z).creator = x ∧ (U.block z).round = s ∧ tl.built z ≤ n := by
      intro e he hex hes hen
      rcases Nat.eq_or_lt_of_le hes with heq | hlt
      · exact ⟨e, he, hex, heq.symm, hen.le⟩
      subst hex
      obtain ⟨y, hy, hyc, hyr⟩ := h.exists_succ_held hx (h.own e he hx) hx hlt
      have hyt := h.causal _ hx _ y hy hyc
      obtain ⟨z, hz, hzx, hzr, hzt⟩ :=
        ih _ (by omega) y (h.held_ids _ _ hy) hyc hyr rfl _ hx
      exact ⟨z, hz, hzx, hzr, by omega⟩
    -- the author of `c` held a quorum of round `s` at `T ≥ G`, with `T + δ < n`
    have hquorum : ∀ T, G ≤ T → T + δ < n →
        QuorumIn U (tl.held (U.block c).creator T) s →
        ∃ z ∈ U.ids, (U.block z).creator = x ∧ (U.block z).round = s ∧ tl.built z ≤ n := by
      intro T hG hT hQ
      by_cases hxA : x ∈ creatorsOf U.block
          ((tl.held (U.block c).creator T).filter fun b => (U.block b).round = s)
      · obtain ⟨z, hz, hzx⟩ := mem_creatorsOf.mp hxA
        obtain ⟨hzH, hzr⟩ := Finset.mem_filter.mp hz
        exact ⟨z, h.held_ids _ _ hzH, hzx, hzr,
          (h.causal _ hcc T z hzH (hzx ▸ hx)).trans (by omega)⟩
      have hB : BehindIn U (tl.held x (T + δ)) x (s - 1) := by
        refine le_trans (card_inter_correct_of_quorum hQ) (Finset.card_le_card fun v hv => ?_)
        obtain ⟨hvc, hvC⟩ := Finset.mem_inter.mp hv
        obtain ⟨z, hz, hzv⟩ := mem_creatorsOf.mp hvc
        obtain ⟨hzH, hzr⟩ := Finset.mem_filter.mp hz
        refine Finset.mem_erase.mpr ⟨fun hvx => hxA (hvx ▸ hvc), mem_creatorsOf.mpr ⟨z,
          Finset.mem_filter.mpr ⟨h.mem_held_of_held hcc hG hzH (hzv ▸ hvC) hx le_rfl,
            by omega⟩, hzv⟩⟩
      obtain ⟨e, he, hex, hes, het⟩ :=
        h.prompt x hx (s - 1) (T + δ) (by omega) (by omega) (Or.inr ⟨by omega, hB⟩)
      exact hup e he hex (by omega) (by omega)
    have hlc := h.late c hc hcc (by omega)
    rcases h.waits c hc hcc s hcr (by omega) with ⟨-, hW, -⟩ | ⟨-, hA⟩ | ⟨-, hQ⟩ | hB
    · exact hquorum _ (by omega) (by omega) hW.1
    · obtain ⟨z, hzH, hzr, hzx⟩ := hA x
      exact ⟨z, h.held_ids _ _ hzH, hzx, hzr,
        (h.causal _ hcc _ z hzH (hzx ▸ hx)).trans hn.le⟩
    · exact hquorum _ (by omega) (by omega) hQ
    · obtain ⟨y, hyH, hyr, hyc, hyv⟩ := exists_correct_of_behindIn hB
      obtain ⟨z, hz, hzx, hzr, hzt⟩ := ih _ (hn ▸ h.prior _ hcc _ y hyH hyc hyv) y
        (h.held_ids _ _ hyH) hyc hyr rfl x hx
      exact ⟨z, hz, hzx, hzr, by have := h.prior _ hcc _ y hyH hyc hyv; omega⟩

/-- **Exact rounds in the run**, at `δ < γ ≤ τ`: once every correct validator
has reached round `s`, from `R + 1` to `N`, by `t`, every correct validator
has built at round `s` by `t`. -/
theorem builtBy_of_reachedBy (hδ : δ < γ) (hγτ : γ ≤ τ) {s t : ℕ} (hs : R + 1 ≤ s)
    (hsN : s ≤ N) (hb : ReachedBy U tl s t) : BuiltBy U tl s t := by
  intro x hx
  obtain ⟨e, he, hex, hes, het⟩ := hb x hx
  rcases Nat.eq_or_lt_of_le hes with heq | hlt
  · exact ⟨e, he, hex, heq.symm, het⟩
  subst hex
  obtain ⟨y, hy, hyc, hyr⟩ := h.exists_succ_held hx (h.own e he hx) hx hlt
  obtain ⟨z, hz, hzx, hzr, hzt⟩ :=
    h.builtBy_below hδ hγτ hs hsN (h.held_ids _ _ hy) hyc hyr _ hx
  exact ⟨z, hz, hzx, hzr, by have := h.causal _ hx _ y hy hyc; omega⟩

/-- **A correct leader's block reaches every correct voter before its
timeout**, at `τ ≥ 2δ` and `δ < γ ≤ τ`: a correct block one round above a
slot led by a correct validator, from round `R + 1` on, is built once its
author holds a leader block of the slot. -/
theorem leader_mem_held (hτ : 2 * δ ≤ τ) (hδ : δ < γ) (hγτ : γ ≤ τ) {k : ℕ}
    (hk : R + 1 ≤ S.slotRound k) (hN : S.slotRound k + 2 ≤ N)
    (hlead : S.leader k ∈ (Correct : Finset Validator))
    {b : BlockId} (hb : b ∈ U.ids)
    (hbc : (U.block b).creator ∈ (Correct : Finset Validator))
    (hbr : (U.block b).round = S.slotRound k + 1) :
    ∃ L ∈ tl.held (U.block b).creator (tl.built b), IsLeaderBlock U k L := by
  refine h.induction_behind (by omega)
    (fun b => ∃ L ∈ tl.held (U.block b).creator (tl.built b), IsLeaderBlock U k L)
    (fun b hb hbc hbr hW => ?_) (fun b hb hbc hbr y hyH hyc hyr hy => ?_) hb hbc hbr
  · rcases hW with ⟨-, -, hW⟩ | ⟨hW, -⟩ | ⟨hτb, hQ⟩
    · exact hW.2.1 k rfl
    · exact hW.2.1 k rfl
    have hlb := h.late b hb hbc (by omega)
    have hR : ReachedBy U tl (S.slotRound k) (tl.built b - τ + δ) := by
      have := h.reachedBy_of_quorumIn (s := S.slotRound k - 1) (t := tl.built b - τ) (by omega)
        (by omega) (by omega) hbc (by rwa [show S.slotRound k - 1 + 1 = S.slotRound k by omega])
      rwa [show S.slotRound k - 1 + 1 = S.slotRound k by omega] at this
    obtain ⟨L, hL, hLc, hLr, hLt⟩ :=
      h.builtBy_of_reachedBy hδ hγτ hk (by omega) hR _ hlead
    exact ⟨L, h.mem_held_of_round hL (hLc ▸ hlead) (by omega) hbc hLt (by omega), hL, by omega,
      hLc⟩
  · obtain ⟨L, hL, hlead'⟩ := h.votes (h.held_ids _ _ hyH) hyc (by omega) hy
    exact ⟨L, h.closed _ hbc _ y hyH hyc hL, hlead'⟩

/-- **Every correct voter votes for a correct leader**: a correct block one
round above a slot led by a correct validator, from round `R + 1` on,
references the slot's leader block. -/
theorem mem_refs_of_leader (hτ : 2 * δ ≤ τ) (hδ : δ < γ) (hγτ : γ ≤ τ) {k : ℕ}
    (hk : R + 1 ≤ S.slotRound k) (hN : S.slotRound k + 2 ≤ N)
    (hlead : S.leader k ∈ (Correct : Finset Validator))
    {b : BlockId} (hb : b ∈ U.ids)
    (hbc : (U.block b).creator ∈ (Correct : Finset Validator))
    (hbr : (U.block b).round = S.slotRound k + 1) {L : BlockId} (hL : IsLeaderBlock U k L) :
    L ∈ (U.block b).refs := by
  obtain ⟨L', hL', hlead'⟩ :=
    h.votes hb hbc hbr.symm (h.leader_mem_held hτ hδ hγτ hk hN hlead hb hbc hbr)
  exact (leaderBlock_eq hL hlead' hlead) ▸ hL'

/-- **The votes of all correct validators reach every correct node before its
timeout two rounds above**, at `τ ≥ 2δ` and `δ < γ ≤ τ`: a correct block two
rounds above a slot led by a correct validator, from round `R + 1` on, is
built once its author holds a certificate for the slot's leader block. -/
theorem certIn_held (hτ : 2 * δ ≤ τ) (hδ : δ < γ) (hγτ : γ ≤ τ) {k : ℕ}
    (hk : R + 1 ≤ S.slotRound k) (hN : S.slotRound k + 2 ≤ N)
    (hlead : S.leader k ∈ (Correct : Finset Validator))
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
  · rcases hW with ⟨-, -, hW⟩ | ⟨hW, -⟩ | ⟨hτc, hQ⟩
    · exact hW.2.2 k rfl
    · exact hW.2.2 k rfl
    have hlc := h.late c hc hcc (by omega)
    have hB := h.builtBy_of_reachedBy hδ hγτ (by omega) (by omega)
      (h.reachedBy_of_quorumIn (t := tl.built c - τ) (by omega) (by omega) (by omega) hcc hQ)
    obtain ⟨x, hx, hxl, hxr, -⟩ := hB _ hlead
    obtain ⟨L, -, hL⟩ := h.leader_mem_held hτ hδ hγτ hk hN hlead hx (hxl ▸ hlead) hxr
    refine ⟨L, hL, quorum_le_of_correct fun w hw => ?_⟩
    obtain ⟨y, hy, hyw, hyr, hyt⟩ := hB w hw
    have hyc : (U.block y).creator ∈ (Correct : Finset Validator) := hyw ▸ hw
    exact ⟨y, Finset.mem_filter.mpr ⟨h.mem_held_of_round hy hyc (by omega) hcc hyt (by omega),
      hyr, h.mem_refs_of_leader hτ hδ hγτ hk hN hlead hy hyc hyr hL⟩, hyw⟩
  · have hy' := h.held_ids _ _ hyH
    obtain ⟨L, hL, hv⟩ := h.certifies y hy' hyc k (by omega) hy
    refine ⟨L, hL, le_trans hv (Finset.card_le_card (Finset.image_subset_image fun z hz => ?_))⟩
    obtain ⟨-, hzr, hzL⟩ := mem_carriedVotes_spec hy' hyr hz
    exact Finset.mem_filter.mpr
      ⟨h.closed _ hcc _ y hyH hyc (mem_carriedVotes.mp hz).1, hzr, hzL⟩

/-- **Every correct certifier certifies a correct leader**: a correct block
two rounds above a slot led by a correct validator, from round `R + 1` on,
carries votes from a quorum for the slot's leader block. -/
theorem carriesVotes_of_leader (hτ : 2 * δ ≤ τ) (hδ : δ < γ) (hγτ : γ ≤ τ) {k : ℕ}
    (hk : R + 1 ≤ S.slotRound k) (hN : S.slotRound k + 2 ≤ N)
    (hlead : S.leader k ∈ (Correct : Finset Validator))
    {c : BlockId} (hc : c ∈ U.ids)
    (hcc : (U.block c).creator ∈ (Correct : Finset Validator))
    (hcr : (U.block c).round = S.slotRound k + 2) {L : BlockId} (hL : IsLeaderBlock U k L) :
    CarriesVotes U (IsVote U) (quorumCard Validator) c L := by
  obtain ⟨L', hL', hv⟩ :=
    h.certifies c hc hcc k hcr.symm (h.certIn_held hτ hδ hγτ hk hN hlead hc hcc hcr)
  exact (leaderBlock_eq hL hL' hlead) ▸ hv

/-- **A round led by correct validators is built within `δ + max γ μ`**, at
`τ ≥ 2δ` and `δ < γ ≤ τ`: when the slots at round `s ≥ R + 2` and one round
below have correct leaders, every correct node holds what it waits for above
`s` once it holds the correct blocks of round `s`. -/
theorem builtBy_succ_fast (hτ : 2 * δ ≤ τ) (hδ : δ < γ) (hγτ : γ ≤ τ) {s t : ℕ}
    (hs : R + 2 ≤ s) (hsN : s < N) (hb : BuiltBy U tl s t)
    (hlead : ∀ k, S.slotRound k = s ∨ S.slotRound k + 1 = s →
      S.leader k ∈ (Correct : Finset Validator)) :
    BuiltBy U tl (s + 1) (t + δ + max γ μ) := by
  have hG := h.le_of_reachedBy (by omega) hb.reachedBy
  refine h.builtBy_of_reachedBy hδ hγτ (by omega) (by omega) fun v hv => ?_
  refine h.built_of_waitsFor hv (by omega) hsN (by omega)
    ⟨h.quorumIn_of_reachedBy (by omega) hb.reachedBy hv, fun k hk => ?_,
      fun k hk => ?_⟩
  · obtain ⟨L, hL, hLc, hLr, hLt⟩ := hb _ (hlead k (Or.inl hk))
    exact ⟨L, h.mem_held_of_round hL (hLc ▸ hlead k (Or.inl hk)) (by omega) hv hLt le_rfl, hL,
      hLr.trans hk.symm, hLc⟩
  · have hc := hlead k (Or.inr hk)
    obtain ⟨x, hx, hxv, hxr, -⟩ := hb v hv
    obtain ⟨L, -, hL⟩ :=
      h.leader_mem_held hτ hδ hγτ (by omega) (by omega) hc hx (hxv ▸ hv) (hxr.trans hk.symm)
    refine ⟨L, hL, quorum_le_of_correct fun w hw => ?_⟩
    obtain ⟨y, hy, hyw, hyr, hyt⟩ := hb w hw
    have hyc : (U.block y).creator ∈ (Correct : Finset Validator) := hyw ▸ hw
    exact ⟨y, Finset.mem_filter.mpr ⟨h.mem_held_of_round hy hyc (by omega) hv hyt le_rfl, hyr,
      h.mem_refs_of_leader hτ hδ hγτ (by omega) (by omega) hc hy hyc (hyr.trans hk.symm) hL⟩,
      hyw⟩

/-- Every round from `R + 1` to `N` is built by some time, at `δ < γ ≤ τ`. -/
theorem exists_builtBy (hδ : δ < γ) (hγτ : γ ≤ τ) {s : ℕ} (hs : R + 1 ≤ s) (hsN : s ≤ N) :
    ∃ t, BuiltBy U tl s t := by
  obtain ⟨t, ht⟩ := h.exists_reachedBy (show R ≤ s by omega) hsN
  exact ⟨t, h.builtBy_of_reachedBy hδ hγτ hs hsN ht⟩

/-- **Responsiveness among the correct validators** from round `R + 1` to
`N`, at `τ ≥ 2δ` and `δ < γ ≤ τ`. -/
theorem respondsFrom (hτ : 2 * δ ≤ τ) (hδ : δ < γ) (hγτ : γ ≤ τ) :
    RespondsFrom U (Correct : Finset Validator) (R + 1) N := by
  refine ⟨card_correct, fun k hk hN hlead => ?_⟩
  obtain ⟨t, ht⟩ := h.exists_builtBy hδ hγτ hk (by omega)
  obtain ⟨L, hL, hLc, hLr, -⟩ := ht _ hlead
  obtain ⟨t', ht'⟩ := h.exists_builtBy hδ hγτ (show R + 1 ≤ S.slotRound k + 2 by omega) hN
  refine ⟨fun v hv => ?_, L, ⟨hL, hLr, hLc⟩, fun C hC hCc hCr =>
    h.carriesVotes_of_leader hτ hδ hγτ hk hN hlead hC hCc hCr ⟨hL, hLr, hLc⟩⟩
  obtain ⟨b, hb, hbv, hbr, -⟩ := ht' v hv
  exact ⟨b, hb, hbv, hbr⟩

/-- **A slot led by correct validators commits within `3δ + 2 max γ μ`**, at
`τ ≥ 2δ` and `δ < γ ≤ τ`: when every slot from one round below a slot at
round `r`, from `R + 2` to `N − 2`, to one round above it has a correct
leader, and every correct validator has built at round `r` by `t`, every
correct node commits the slot directly by `t + 3δ + 2 max γ μ`. -/
theorem nodeDecided_fast (hτ : 2 * δ ≤ τ) (hδ : δ < γ) (hγτ : γ ≤ τ) (K : ℕ) {k t : ℕ}
    (hk : R + 2 ≤ S.slotRound k) (hN : S.slotRound k + 2 ≤ N)
    (hlead : ∀ j, S.slotRound k ≤ S.slotRound j + 1 → S.slotRound j ≤ S.slotRound k + 1 →
      S.leader j ∈ (Correct : Finset Validator))
    (hb : BuiltBy U tl (S.slotRound k) t) {v : Validator}
    (hv : v ∈ (Correct : Finset Validator)) :
    ∃ L, IsLeaderBlock U k L ∧
      NodeDecided U K (tl.held v (t + 3 * δ + 2 * max γ μ)) k (some L) := by
  have h1 := h.builtBy_succ_fast hτ hδ hγτ hk (by omega) hb fun j hj =>
    hlead j (by omega) (by omega)
  have h2 := h.builtBy_succ_fast hτ hδ hγτ (by omega) (by omega) h1 fun j hj =>
    hlead j (by omega) (by omega)
  have hlk := hlead k (by omega) (by omega)
  refine nodeDecided_of_responds card_correct
    ((h.respondsFrom hτ hδ hγτ).2 k (by omega) hN hlk) ?_
  rintro z ⟨c, hc, hcc, hlo, hhi, hz⟩
  obtain ⟨c', hc', hcc', hcr', hct'⟩ := h2 _ hcc
  have hcc'' : c = c' := U.eq_of_creator_eq hc hc' hcc rfl hcc' (by omega)
  subst hcc''
  have hheld : c ∈ tl.held v (t + 3 * δ + 2 * max γ μ) :=
    h.mem_held_of_round hc hcc (by omega) hv hct' (by omega)
  rcases hz with rfl | hz
  · exact hheld
  · exact h.closed v hv _ c hheld hcc hz

/-- **A correct node holds the correct blocks of the round below when it
builds**, at `2δ ≤ γ ≤ τ` and `δ < γ`: a correct block of round `r + 1`, `r`
from `R + 1` to `N`, is built once its author holds every correct block of
round `r`. -/
theorem mem_held_below (hγ : 2 * δ ≤ γ) (hδ : δ < γ) (hγτ : γ ≤ τ) {r : ℕ} (hr : R + 1 ≤ r)
    (hrN : r ≤ N) {x : BlockId} (hx : x ∈ U.ids)
    (hxc : (U.block x).creator ∈ (Correct : Finset Validator))
    (hxr : (U.block x).round = r) {b : BlockId} (hb : b ∈ U.ids)
    (hbc : (U.block b).creator ∈ (Correct : Finset Validator))
    (hbr : (U.block b).round = r + 1) : x ∈ tl.held (U.block b).creator (tl.built b) := by
  -- a correct node holding a quorum of round `r` at `t` holds `x` by `t + 2δ`
  have hquorum : ∀ b, (U.block b).creator ∈ (Correct : Finset Validator) → ∀ t, G ≤ t →
      t + 2 * δ ≤ tl.built b → QuorumIn U (tl.held (U.block b).creator t) r →
      x ∈ tl.held (U.block b).creator (tl.built b) := by
    intro b hbc t hG ht hQ
    have hR : ReachedBy U tl r (t + δ) := by
      have := h.reachedBy_of_quorumIn (s := r - 1) (by omega) (by omega) hG hbc
        (by rwa [show r - 1 + 1 = r by omega])
      rwa [show r - 1 + 1 = r by omega] at this
    obtain ⟨y, hy, hyc, hyr, hyt⟩ := h.builtBy_of_reachedBy hδ hγτ hr hrN hR _ hxc
    obtain rfl : y = x := U.eq_of_creator_eq hy hx hxc hyc rfl (by omega)
    exact h.mem_held_of_round hy hxc (by omega) hbc (t₀ := t + δ) hyt (by omega)
  refine h.induction_behind (s := r) (by omega)
    (fun b => x ∈ tl.held (U.block b).creator (tl.built b))
    (fun b hb hbc hbr hW => ?_) (fun b hb hbc hbr y hyH hyc hyr hy => ?_) hb hbc hbr
  · have hlb := h.late b hb hbc (by omega)
    rcases hW with ⟨hγb, hW, -⟩ | ⟨-, hA⟩ | ⟨hτb, hQ⟩
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
    exact h.closed _ hbc _ y hyH hyc hz

/-- **The run is synchronous among the correct validators** from round
`R + 1` to `N`, at `2δ ≤ γ ≤ τ` and `δ < γ`: every correct block references
every correct block of the round below. -/
theorem syncFrom (hγ : 2 * δ ≤ γ) (hδ : δ < γ) (hγτ : γ ≤ τ) :
    SyncFrom U (Correct : Finset Validator) (R + 1) N := by
  refine ⟨card_correct, fun n hn hnN b hb hbr hbc a ha har hac => ?_, fun r hr hrN v hv => ?_⟩
  · obtain ⟨z, hz, hzc⟩ := h.covers b hb hbc a
      (h.mem_held_below hγ hδ hγτ hn hnN.le ha hac har hb hbc hbr) (by omega)
    have hzr := (U.valid b hb).predecessor z hz
    obtain rfl : z = a := U.eq_of_creator_eq (U.complete b hb z hz) ha hac hzc rfl (by omega)
    exact hz
  · obtain ⟨t, ht⟩ := h.exists_builtBy hδ hγτ hr hrN
    obtain ⟨b, hb, hbv, hbr, -⟩ := ht v hv
    exact ⟨b, hb, hbv, hbr⟩

/-- **The ledger grows**, at `τ ≥ 2δ` and `δ < γ ≤ τ`, when correct nodes
fetch the available sub-DAG of the certified leader blocks they hold within
`Δ`, and the schedule offers runs of `c` correct leaders spanning
eligibility: past any slot `k` there is a slot `b` such that, if the run
reaches round `σ(b + c − 1) + 2`, every correct node, at one time, decides
every slot below `b + c` and has fetched each leader it commits down to `D`
rounds below it. -/
theorem exists_ledger (hτ : 2 * δ ≤ τ) (hδ : δ < γ) (hγτ : γ ≤ τ) {K Δ : ℕ} (D : ℕ)
    (hF : Fetches U tl K G Δ) {c : ℕ} (hc : 0 < c)
    (hspan : ∀ b i, i < b → EligibleAt (S := S) 2 i (b + c - 1))
    (fair : FairRunOn (Correct : Finset Validator) c) (k : ℕ) :
    ∃ b, k ≤ b ∧ (S.slotRound (b + c - 1) + 2 ≤ N → ∃ t, ∀ v ∈ (Correct : Finset Validator),
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
  have hheld : WithRefs U (Correct : Finset Validator) (S.slotRound b)
      (S.slotRound (b + c - 1) + 2) ∪ AvailBelow U K (b + c - 1) ⊆
      ↑(tl.held v (T₀ + δ + Δ)) := by
    rintro z (⟨x, hx, hxc, hxlo, -, hzx⟩ | ⟨j, A, hj, hA, ⟨C, hC⟩, hzA⟩)
    · have hxv := h.mem_held_of_round hx hxc (by omega) hv (hT₀ x hx) (t := T₀ + δ + Δ)
        (by omega)
      rcases hzx with rfl | hzx
      · exact hxv
      · exact h.closed v hv _ x hxv hxc hzx
    · obtain ⟨hCi, -, hvC⟩ := mem_certificatesAt.mp hC
      obtain ⟨u, hu, huc⟩ := exists_correct_of_card
        (S := creatorsOf U.block (carriedVotes U (IsVote U) C A))
        (by have := F.card_validators; unfold CarriesVotes at hvC; omega)
      obtain ⟨y, hyC, hyu⟩ := mem_creatorsOf.mp hu
      obtain ⟨hyref, hyA⟩ := mem_carriedVotes.mp hyC
      have hy := U.complete C hCi y hyref
      have hyc : (U.block y).creator ∈ (Correct : Finset Validator) := hyu ▸ huc
      have hyw := h.disk_held _ hyc T₀ (h.stores y hy hyc T₀ (hT₀ y hy)).1
      have hyv := h.mem_held_of_held hyc (le_max_left _ _) hyw hyc hv le_rfl
      exact hF v hv (T₀ + δ) (by omega) j A hA ⟨C, hC⟩ (h.closed v hv _ y hyv hyc hyA) z hzA
  have hdec := nodeDecided_of_run card_correct (h.held_ids v _) hc hspan hresp hheld
  refine ⟨fun i => if hi : i < b + c then (hdec i hi).choose else none, fun i hi => ?_⟩
  simp only [dif_pos hi]
  refine ⟨(hdec i hi).choose_spec, fun L hL => ?_⟩
  obtain ⟨hlead, hcert⟩ :=
    certified_of_nodeDecided (h.held_ids v _) (hL ▸ (hdec i hi).choose_spec)
  exact fetchedIn_of_subset hlead.1 (Nat.sub_le _ _) fun z hz _ =>
    hheld (Set.mem_union_right _ ⟨i, L, by omega, hlead, hcert, hz⟩)

end ReactiveRun

end KPartialDag

end LeanDag
