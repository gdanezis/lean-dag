import LeanDag.KPartialDag.Model.Reactive
import LeanDag.KPartialDag.Helpers.Live
/-!
# Reactive nodes in time — helpers

`docs/kpartial.md` §11. What a node waits for grows with what it holds
(`waitsFor_mono`). A correct block built at time `t` shows that its author
held what it waits for at `t`, or a quorum at `t − τ`; every correct node
holds the same `δ` later, so every correct node has built at that round by
`t + δ` (`exists_built_le`). With `τ ≥ 2δ` a correct leader's block therefore
reaches every correct voter before its timeout (`leader_mem_held`), and the
votes of all correct validators reach every correct node before its timeout
two rounds above (`certIn_held`). After `δ` every correct node holds the
correct blocks of a round, so it builds above once its timeout runs out
(`builtBy_succ`), and at once when the leaders it waits for are correct
(`builtBy_succ_fast`).
-/

namespace LeanDag

namespace KPartialDag

variable {Validator : Type*} [Fintype Validator] [DecidableEq Validator] [F : Faults Validator]
variable {BlockId : Type*} [DecidableEq BlockId] {Payload : Type*}
variable [S : Slots Validator]
variable {U : KRecord Validator BlockId Payload} {tl : Timeline Validator BlockId}
variable {G δ τ R N : ℕ}

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

omit [DecidableEq BlockId] in
/-- A correct leader has one leader block. -/
theorem leaderBlock_eq {k : ℕ} {L L' : BlockId} (hL : IsLeaderBlock U k L)
    (hL' : IsLeaderBlock U k L') (hc : S.leader k ∈ (Correct : Finset Validator)) : L = L' :=
  U.eq_of_creator_eq hL.1 hL'.1 hc hL.2.2 hL'.2.2 (hL.2.1.trans hL'.2.1.symm)

namespace ReactiveRun

variable (h : ReactiveRun U tl G δ τ R N)
include h

/-- A correct block from round `R` on is held by every correct node `δ`
after it is built. -/
theorem mem_held {b : BlockId} (hb : b ∈ U.ids)
    (hbc : (U.block b).creator ∈ (Correct : Finset Validator)) (hR : R ≤ (U.block b).round)
    {v : Validator} (hv : v ∈ (Correct : Finset Validator)) {t : ℕ} (ht : tl.built b + δ ≤ t) :
    b ∈ tl.held v t :=
  h.mono v hv _ _ ht (h.gossip _ hbc v hv _ (by have := h.late b hb hbc hR; omega)
    (h.own b hb hbc))

/-- **Every correct node builds within `δ` of a correct one**: once a
correct block of round `s + 1`, from `R + 1` to `N`, is built, every
correct validator has built at round `s + 1` within `δ`. -/
theorem exists_built_le {x : BlockId} (hx : x ∈ U.ids)
    (hxc : (U.block x).creator ∈ (Correct : Finset Validator)) {s : ℕ}
    (hxs : (U.block x).round = s + 1) (hR : R ≤ s) (hN : s < N) {w : Validator}
    (hw : w ∈ (Correct : Finset Validator)) :
    ∃ b ∈ U.ids, (U.block b).creator = w ∧ (U.block b).round = s + 1 ∧
      tl.built b ≤ tl.built x + δ := by
  have hlate := h.late x hx hxc (by omega)
  rcases h.waits x hx hxc s hxs hR with hW | ⟨hτ, hQ⟩
  · exact h.prompt w hw s _ hR hN
      (Or.inl (waitsFor_mono (h.gossip _ hxc w hw _ (by omega)) hW))
  · refine h.prompt w hw s _ hR hN (Or.inr ⟨by omega, ?_⟩)
    have hg := h.gossip _ hxc w hw (tl.built x - τ) (by omega)
    rw [show tl.built x - τ + δ = tl.built x + δ - τ by omega] at hg
    exact quorumIn_mono hg hQ

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
  rcases h.waits b hb hbc _ hbr (by omega) with hW | ⟨hτb, hQ⟩
  · exact hW.2.1 k rfl
  obtain ⟨x, hxH, hxr, hxc⟩ := exists_correct_of_quorumIn hQ
  have hx := h.held_ids _ _ hxH
  have hxt := h.causal _ hbc _ x hxH hxc
  obtain ⟨L, hL, hLc, hLr, hLt⟩ := h.exists_built_le hx hxc
    (show (U.block x).round = (S.slotRound k - 1) + 1 by omega) (by omega) (by omega) hlead
  refine ⟨L, h.mem_held hL (hLc ▸ hlead) (by omega) hbc (by omega), hL, by omega, hLc⟩

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
    h.votes b hb hbc k hbr.symm (h.leader_mem_held hτ hk hN hlead hb hbc hbr)
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
  rcases h.waits c hc hcc (S.slotRound k + 1) hcr (by omega) with hW | ⟨hτc, hQ⟩
  · exact hW.2.2 k rfl
  obtain ⟨x, hxH, hxr, hxc⟩ := exists_correct_of_quorumIn hQ
  have hx := h.held_ids _ _ hxH
  have hxt := h.causal _ hcc _ x hxH hxc
  obtain ⟨L, -, hL⟩ := h.leader_mem_held hτ hk hN hlead hx hxc hxr
  refine ⟨L, hL, quorum_le_of_correct fun w hw => ?_⟩
  obtain ⟨y, hy, hyw, hyr, hyt⟩ := h.exists_built_le hx hxc hxr (by omega) (by omega) hw
  have hyc : (U.block y).creator ∈ (Correct : Finset Validator) := hyw ▸ hw
  exact ⟨y, Finset.mem_filter.mpr ⟨h.mem_held hy hyc (by omega) hcc (by omega), hyr,
    h.mem_refs_of_leader hτ hk hN hlead hy hyc hyr hL⟩, hyw⟩

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

/-- After `δ`, a correct node holds the correct blocks of a round all of
whose correct blocks are built, and so a quorum there. -/
theorem quorumIn_of_builtBy {s t : ℕ} (hs : R ≤ s) (hb : BuiltBy U tl s t) {v : Validator}
    (hv : v ∈ (Correct : Finset Validator)) : QuorumIn U (tl.held v (t + δ)) s :=
  quorum_le_of_correct fun w hw => by
    obtain ⟨y, hy, hyw, hyr, hyt⟩ := hb w hw
    exact ⟨y, Finset.mem_filter.mpr
      ⟨h.mem_held hy (hyw ▸ hw) (by omega) hv (by omega), hyr⟩, hyw⟩

/-- **Every round up to `N` is built, each within `δ + τ`.** -/
theorem builtBy_succ {s t : ℕ} (hs : R ≤ s) (hsN : s < N) (hb : BuiltBy U tl s t) :
    BuiltBy U tl (s + 1) (t + δ + τ) := by
  intro v hv
  refine h.prompt v hv s _ hs hsN (Or.inr ⟨by omega, ?_⟩)
  rw [show t + δ + τ - τ = t + δ by omega]
  exact h.quorumIn_of_builtBy hs hb hv

/-- Every round from `R` to `N` is built by some time. -/
theorem exists_builtBy {s : ℕ} (hs : R ≤ s) (hsN : s ≤ N) : ∃ t, BuiltBy U tl s t := by
  induction s, hs using Nat.le_induction with
  | base => exact h.start
  | succ s hs ih =>
    obtain ⟨t, ht⟩ := ih (by omega)
    exact ⟨_, h.builtBy_succ hs (by omega) ht⟩

/-- **A round led by correct validators is built within `δ`**, at `τ ≥ 2δ`:
when the slots at round `s ≥ R + 2` and one round below have correct
leaders, every correct node builds above `s` once it holds the correct
blocks of round `s`. -/
theorem builtBy_succ_fast (hτ : 2 * δ ≤ τ) {s t : ℕ} (hs : R + 2 ≤ s) (hsN : s < N)
    (hb : BuiltBy U tl s t)
    (hlead : ∀ k, S.slotRound k = s ∨ S.slotRound k + 1 = s →
      S.leader k ∈ (Correct : Finset Validator)) :
    BuiltBy U tl (s + 1) (t + δ) := by
  intro v hv
  refine h.prompt v hv s _ (by omega) hsN (Or.inl ⟨h.quorumIn_of_builtBy (by omega) hb hv,
    fun k hk => ?_, fun k hk => ?_⟩)
  · obtain ⟨L, hL, hLc, hLr, hLt⟩ := hb _ (hlead k (Or.inl hk))
    exact ⟨L, h.mem_held hL (hLc ▸ hlead k (Or.inl hk)) (by omega) hv (by omega), hL,
      hLr.trans hk.symm, hLc⟩
  · have hc := hlead k (Or.inr hk)
    obtain ⟨x, hx, hxv, hxr, -⟩ := hb v hv
    obtain ⟨L, -, hL⟩ :=
      h.leader_mem_held hτ (by omega) (by omega) hc hx (hxv ▸ hv) (hxr.trans hk.symm)
    refine ⟨L, hL, quorum_le_of_correct fun w hw => ?_⟩
    obtain ⟨y, hy, hyw, hyr, hyt⟩ := hb w hw
    have hyc : (U.block y).creator ∈ (Correct : Finset Validator) := hyw ▸ hw
    exact ⟨y, Finset.mem_filter.mpr ⟨h.mem_held hy hyc (by omega) hv (by omega), hyr,
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

/-- **A slot led by correct validators commits within `3δ`**, at `τ ≥ 2δ`:
when every slot from one round below a slot at round `r`, from `R + 2` to
`N − 2`, to one round above it has a correct leader, and every correct
validator has built at
round `r` by `t`, every correct node commits the slot directly by
`t + 3δ`. -/
theorem nodeDecided_fast (hτ : 2 * δ ≤ τ) (K : ℕ) {k t : ℕ} (hk : R + 2 ≤ S.slotRound k)
    (hN : S.slotRound k + 2 ≤ N)
    (hlead : ∀ j, S.slotRound k ≤ S.slotRound j + 1 → S.slotRound j ≤ S.slotRound k + 1 →
      S.leader j ∈ (Correct : Finset Validator))
    (hb : BuiltBy U tl (S.slotRound k) t) {v : Validator}
    (hv : v ∈ (Correct : Finset Validator)) :
    ∃ L, IsLeaderBlock U k L ∧ NodeDecided U K (tl.held v (t + 3 * δ)) k (some L) := by
  have h1 := h.builtBy_succ_fast hτ hk (by omega) hb fun j hj => hlead j (by omega) (by omega)
  have h2 := h.builtBy_succ_fast hτ (by omega) (by omega) h1 fun j hj =>
    hlead j (by omega) (by omega)
  have hlk := hlead k (by omega) (by omega)
  refine nodeDecided_of_responds card_correct ((h.respondsFrom hτ).2 k (by omega) hN hlk) ?_
  rintro z ⟨c, hc, hcc, hlo, hhi, hz⟩
  obtain ⟨c', hc', hcc', hcr', hct'⟩ := h2 _ hcc
  have hcc'' : c = c' := U.eq_of_creator_eq hc hc' hcc rfl hcc' (by omega)
  subst hcc''
  have hheld : c ∈ tl.held v (t + 3 * δ) := h.mem_held hc hcc (by omega) hv (by omega)
  rcases hz with rfl | hz
  · exact hheld
  · exact h.closed v hv _ c hheld hz

end ReactiveRun

end KPartialDag

end LeanDag
