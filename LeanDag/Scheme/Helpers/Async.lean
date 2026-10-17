import LeanDag.Scheme.Model.Async
import LeanDag.Scheme.Helpers.Support
import LeanDag.Common.Anchored.Bounded
import Mathlib.Combinatorics.Enumerative.DoubleCounting
import Mathlib.Algebra.Group.Action.Defs
import Mathlib.Tactic.Linarith
/-!
# The asynchronous rows: the count

On a record whose blocks reference `q` distinct authors one round down and
whose validators outside `honest`, at most `f`, may equivocate:

* **the common core** (`exists_commonCore`): at `2q ≥ n + f + 1`, some
  honest round-`r` block lies in the history of every block from round
  `r + 2` up. The core's double count (`Common/CommonCore.lean`) at a
  general quorum: some honest author collects so many honest supporters
  that every round-`(r+2)` block, naming `q` of the round's authors,
  names one of them;
* **a safe block is certified** (`isCert_of_safe`): an honest block every
  vote-round block reaches is voted by each, and certified by every
  decision-round block;
* the safe set is bounded below: at one buffer round, by the core of the
  proposal round and by a double count over the buffer round; at two, by
  the honest references of the core of the buffer round.
-/

namespace LeanDag

namespace Scheme

variable {Validator : Type} [Fintype Validator] [DecidableEq Validator]
variable {BlockId : Type} [LinearOrder BlockId] {Payload : Type}
variable {P : Validity Validator BlockId Payload} {honest : Finset Validator} [P.Mechanised]
variable {q : ℕ} [P.Quorate q]
variable {U : BlockRecord Validator BlockId Payload P honest}

/-! ## The common core -/

/-- The common core's arithmetic: with `b ≤ f` validators outside the
honest `c = n − b`, `l ≤ c` honest round-`(r+1)` blocks each naming `q`
authors, some author collecting `k` with `l·q ≤ c·k + l·b`, and `p ≤ l + b`
authors at round `r + 1`, `2q ≥ n + f + 1` gives `k + q > p`. -/
theorem core_arith {n f b c l k p : ℕ}
    (hbf : b ≤ f) (hq : n + f + 1 ≤ 2 * q) (hqn : q ≤ n) (hcb : c + b = n) (hlc : l ≤ c)
    (hA : l * q ≤ c * k + l * b) (hE : p ≤ l + b) :
    p + 1 ≤ k + q := by
  by_contra h
  push Not at h
  have h1 : c * k ≤ c * (l + b - q) := Nat.mul_le_mul_left c (by omega)
  obtain ⟨e, he⟩ : ∃ e, l + b = q + e := ⟨l + b - q, by omega⟩
  rw [show l + b - q = e by omega] at h1
  nlinarith [h1, hA, hlc, hcb, he, hq, hbf]

omit [LinearOrder BlockId] [P.Mechanised] [P.Quorate q] in
/-- A set of validators is its honest part and at most the others. -/
theorem card_le_inter_add_compl (s : Finset Validator) :
    s.card ≤ (s ∩ honest).card + honestᶜ.card := by
  have hsplit := Finset.card_inter_add_card_sdiff s honest
  have : (s \ honest).card ≤ honestᶜ.card :=
    Finset.card_le_card fun x hx => Finset.mem_compl.mpr (Finset.mem_sdiff.mp hx).2
  omega

/-- The honest blocks of round `n`. -/
abbrev honestBlocksAt (U : BlockRecord Validator BlockId Payload P honest) (n : ℕ) :
    Finset BlockId :=
  (blocksAt U n).filter (fun b => (U.block b).creator ∈ honest)

omit [Fintype Validator] [LinearOrder BlockId] [P.Mechanised] [P.Quorate q] in
theorem creator_injOn_honestBlocksAt {n : ℕ} :
    Set.InjOn (fun b => (U.block b).creator) (honestBlocksAt U n) := by
  intro b hb b' hb' h
  obtain ⟨hbs, hbh⟩ := Finset.mem_filter.mp hb
  obtain ⟨hbU, hbr⟩ := mem_blocksAt.mp hbs
  obtain ⟨hb's, -⟩ := Finset.mem_filter.mp hb'
  obtain ⟨hb'U, hb'r⟩ := mem_blocksAt.mp hb's
  exact U.eq_of_creator_eq hbU hb'U hbh rfl h.symm (by rw [hbr, hb'r])

omit [Fintype Validator] [LinearOrder BlockId] [P.Mechanised] [P.Quorate q] in
theorem card_creatorsOf_honestBlocksAt {n : ℕ} :
    (creatorsOf U.block (honestBlocksAt U n)).card = (honestBlocksAt U n).card :=
  Finset.card_image_of_injOn creator_injOn_honestBlocksAt

omit [Fintype Validator] [LinearOrder BlockId] [P.Mechanised] [P.Quorate q] in
theorem creatorsOf_honestBlocksAt_subset {n : ℕ} :
    creatorsOf U.block (honestBlocksAt U n) ⊆ honest := by
  intro v hv
  obtain ⟨b, hb, rfl⟩ := mem_creatorsOf.mp hv
  exact (Finset.mem_filter.mp hb).2

omit [P.Mechanised] [P.Quorate q] in
/-- The authors of a round are its honest authors and at most the others. -/
theorem card_authorsAt_le_honest {n : ℕ} :
    (authorsAt U n).card ≤ (honestBlocksAt U n).card + honestᶜ.card := by
  rw [← card_creatorsOf_honestBlocksAt]
  refine le_trans (Finset.card_le_card ?_) (Finset.card_union_le _ _)
  intro v hv
  obtain ⟨i, hi, hir, rfl⟩ := mem_authorsAt.mp hv
  by_cases hc : (U.block i).creator ∈ honest
  · exact Finset.mem_union_left _ (mem_creatorsOf.mpr
      ⟨i, Finset.mem_filter.mpr ⟨mem_blocksAt.mpr ⟨hi, hir⟩, hc⟩, rfl⟩)
  · exact Finset.mem_union_right _ (Finset.mem_compl.mpr hc)

/-- **The common core's count**: at `2q ≥ n + f + 1`, given a round-`(r+1)`
author pool of at least `q`, some honest round-`r` block has so many honest
supporters at round `r + 1` that with `q` they exceed the pool. -/
theorem exists_honest_common_support {f r : ℕ} (hf : honestᶜ.card ≤ f)
    (hq2 : Fintype.card Validator + f + 1 ≤ 2 * q)
    (hp : q ≤ (authorsAt U (r + 1)).card) :
    ∃ bw ∈ U.ids, (U.block bw).round = r ∧ (U.block bw).creator ∈ honest ∧
      (authorsAt U (r + 1)).card + 1 ≤ (supporters U bw (r + 1) ∩ honest).card + q := by
  classical
  have hE := card_authorsAt_le_honest (U := U) (n := r + 1)
  have hlc : (honestBlocksAt U (r + 1)).card ≤ honest.card := by
    rw [← card_creatorsOf_honestBlocksAt]
    exact Finset.card_le_card creatorsOf_honestBlocksAt_subset
  have hcb : honest.card + honestᶜ.card = Fintype.card Validator := Finset.card_add_card_compl _
  have hqn : q ≤ Fintype.card Validator :=
    le_trans hp (card_authorsAt_le_univ (U := U) (n := r + 1))
  set L := honestBlocksAt U (r + 1) with hLdef
  set g : Validator → ℕ :=
    fun w => (L.filter (fun x => w ∈ creatorsOf U.block (U.block x).refs)).card with hgdef
  have hper : ∀ x ∈ L, q ≤ ((creatorsOf U.block (U.block x).refs) ∩ honest).card + honestᶜ.card := by
    intro x hx
    obtain ⟨hxs, -⟩ := Finset.mem_filter.mp hx
    obtain ⟨hxU, hxr⟩ := mem_blocksAt.mp hxs
    exact le_trans (U.creators_quorum hxU (by omega)) (card_le_inter_add_compl _)
  have hC_ne : honest.Nonempty := by rw [← Finset.card_pos]; omega
  obtain ⟨w, hw_mem, hw_max⟩ := honest.exists_max_image g hC_ne
  have hbig : L.card * (q - honestᶜ.card) ≤ honest.card * g w := by
    have := Finset.card_nsmul_le_card_nsmul
      (r := fun (x : BlockId) (v : Validator) => v ∈ creatorsOf U.block (U.block x).refs)
      (s := L) (t := honest) (m := q - honestᶜ.card) (n := g w)
      (fun x hx => by
        have h := hper x hx
        change q - honestᶜ.card ≤ (honest.filter (fun v => v ∈ creatorsOf U.block (U.block x).refs)).card
        rw [Finset.filter_mem_eq_inter, Finset.inter_comm]
        omega)
      (fun v hv => hw_max v hv)
    simpa [smul_eq_mul] using this
  have hA : L.card * q ≤ honest.card * g w + L.card * honestᶜ.card := by
    have hsplit : L.card * q = L.card * (q - honestᶜ.card) + L.card * honestᶜ.card := by
      rw [← Nat.mul_add, Nat.sub_add_cancel (by omega)]
    omega
  have harith := core_arith (q := q) hf hq2 hqn hcb hlc hA hE
  have hgw_pos : 0 < g w := by omega
  obtain ⟨x₀, hx₀⟩ := Finset.card_pos.mp hgw_pos
  obtain ⟨hx₀L, hx₀w⟩ := Finset.mem_filter.mp hx₀
  obtain ⟨hx₀s, -⟩ := Finset.mem_filter.mp hx₀L
  obtain ⟨hx₀U, hx₀r⟩ := mem_blocksAt.mp hx₀s
  obtain ⟨bw, hbw_mem, hbw_creator⟩ := mem_creatorsOf.mp hx₀w
  have hbwU : bw ∈ U.ids := U.complete _ hx₀U _ hbw_mem
  have hbwr : (U.block bw).round = r := by
    have := U.round_of_mem_refs hx₀U hbw_mem; omega
  refine ⟨bw, hbwU, hbwr, hbw_creator ▸ hw_mem, ?_⟩
  have hsub : Finset.image (fun x => (U.block x).creator)
      (L.filter (fun x => w ∈ creatorsOf U.block (U.block x).refs)) ⊆
        supporters U bw (r + 1) ∩ honest := by
    intro v hv
    simp only [Finset.mem_image, Finset.mem_filter] at hv
    obtain ⟨x, ⟨hxL, hxw⟩, rfl⟩ := hv
    obtain ⟨hxs, hxh⟩ := Finset.mem_filter.mp hxL
    obtain ⟨hxU, hxr⟩ := mem_blocksAt.mp hxs
    obtain ⟨i', hi', hi'c⟩ := mem_creatorsOf.mp hxw
    have hi'U : i' ∈ U.ids := U.complete x hxU i' hi'
    have hi'r : (U.block i').round = r := by
      have := U.round_of_mem_refs hxU hi'; omega
    have hib : i' = bw := U.eq_of_creator_eq hi'U hbwU hw_mem hi'c hbw_creator (by rw [hi'r, hbwr])
    exact Finset.mem_inter.mpr ⟨mem_supporters.mpr ⟨x, hxU, hxr, hib ▸ hi', rfl⟩, hxh⟩
  calc (authorsAt U (r + 1)).card + 1
      ≤ g w + q := harith
    _ = (Finset.image (fun x => (U.block x).creator)
          (L.filter (fun x => w ∈ creatorsOf U.block (U.block x).refs))).card + q := by
        rw [Finset.card_image_of_injOn
          (creator_injOn_honestBlocksAt.mono (Finset.coe_subset.mpr (Finset.filter_subset _ _)))]
    _ ≤ _ := Nat.add_le_add_right (Finset.card_le_card hsub) _

/-- **The common core**: at `2q ≥ n + f + 1`, if a block exists at round
`r + 2`, some honest round-`r` block lies in the history of every block from
round `r + 2` up. -/
theorem exists_commonCore {f r : ℕ} (hf : honestᶜ.card ≤ f)
    (hq2 : Fintype.card Validator + f + 1 ≤ 2 * q) {c₀ : BlockId}
    (hc₀ : c₀ ∈ U.ids) (hc₀r : (U.block c₀).round = r + 2) :
    ∃ b ∈ U.ids, (U.block b).round = r ∧ (U.block b).creator ∈ honest ∧
      ∀ c ∈ U.ids, r + 2 ≤ (U.block c).round → Reaches U c b := by
  have hp : q ≤ (authorsAt U (r + 1)).card :=
    le_trans (U.creators_quorum hc₀ (by omega))
      (Finset.card_le_card (creators_refs_subset_authorsAt hc₀ (by omega)))
  obtain ⟨b, hb, hbr, hbh, hsup⟩ := exists_honest_common_support hf hq2 hp
  refine ⟨b, hb, hbr, hbh, fun c hc hcr => ?_⟩
  have hbase : ∀ c ∈ U.ids, (U.block c).round = r + 2 → ∃ b', b' = b ∧ Reaches U c b' :=
    fun c hc hcr => ⟨b, rfl, reaches_of_honest_support (b := b) (r := r)
      (S := supporters U b (r + 1) ∩ honest)
      (fun v hv => mem_supporters.mp (Finset.mem_inter.mp hv).1)
      (fun v hv => (Finset.mem_inter.mp hv).2) hsup hc hcr⟩
  obtain ⟨b', rfl, hreach⟩ := reaches_pred_of_round_le (Q := fun b' => b' = b) hbase hc hcr
  exact hreach

/-! ## A safe block is committed -/

variable {p : Params} (σ : VoteSel Validator BlockId Payload P honest)

omit [Fintype Validator] [P.Quorate q] in
theorem mem_safeAt {r : ℕ} {v : Validator} :
    v ∈ safeAt p U r ↔ v ∈ honest ∧ ∃ L ∈ U.ids, (U.block L).round = r ∧
      (U.block L).creator = v ∧
      ∀ b ∈ U.ids, (U.block b).round = r + p.voteOffset → Reaches U b L := by
  unfold safeAt
  rw [Finset.mem_filter]
  refine and_congr_right fun _ => exists_congr fun L => and_congr_right fun _ =>
    and_congr_right fun _ => and_congr_right fun _ =>
      forall₂_congr fun b hb => imp_congr_right fun _ => mem_history_iff hb

omit [Fintype Validator] [P.Quorate q] in
/-- An honest block every vote-round block reaches is safe. -/
theorem mem_safeAt_of_reaches {r : ℕ} {L : BlockId} (hL : L ∈ U.ids)
    (hLr : (U.block L).round = r) (hLc : (U.block L).creator ∈ honest)
    (hsafe : ∀ b ∈ U.ids, (U.block b).round = r + p.voteOffset → Reaches U b L) :
    (U.block L).creator ∈ safeAt p U r :=
  mem_safeAt.mpr ⟨hLc, L, hL, hLr, rfl, hsafe⟩

omit [Fintype Validator] in
/-- **Every decision-round block certifies a safe block**: every vote-round
block reaches it, so votes for it, and a decision-round block's certificate
is its own vote, or its references' votes from at least `q ≥ cert` authors. -/
theorem isCert_of_safe {r : ℕ} {L : BlockId} (hw : 2 ≤ p.waveLength)
    (hcv : p.voteIsCert = false → 3 ≤ p.waveLength ∧ p.certThreshold ≤ q)
    (hL : L ∈ U.ids) (hLr : (U.block L).round = r) (hLc : (U.block L).creator ∈ honest)
    (hsafe : ∀ b ∈ U.ids, (U.block b).round = r + p.voteOffset → Reaches U b L)
    {C : BlockId} (hC : C ∈ U.ids) (hCr : (U.block C).round = r + (p.waveLength - 1)) :
    IsCert p σ U C L := by
  unfold IsCert
  split
  · rename_i hv
    have hoff : p.voteOffset = p.waveLength - 1 := by simp [Params.voteOffset, hv]
    exact votes_of_reaches_record U.noEquivOn_honest hC hL hLc (by omega)
      (hsafe C hC (by omega))
  · rename_i hv
    obtain ⟨hw3, hcq⟩ := hcv (by simpa using hv)
    have hoff : p.voteOffset = p.waveLength - 2 := by
      simp only [Params.voteOffset, show p.voteIsCert = false by simpa using hv,
        Bool.false_eq_true, if_false]
      omega
    have hall : carriedVotes U (σ.Votes U) C L = (U.block C).refs := by
      refine Finset.filter_true_of_mem fun b hb => ?_
      have hbU := U.complete C hC b hb
      have hbr := U.round_of_mem_refs hC hb
      exact votes_of_reaches_record U.noEquivOn_honest hbU hL hLc (by omega)
        (hsafe b hbU (by omega))
    show p.certThreshold ≤ (creatorsOf U.block (carriedVotes U (σ.Votes U) C L)).card
    rw [hall]
    exact le_trans hcq (U.creators_quorum hC (by omega))

/-! ## The safe set -/

/-- **One buffer round: the safe set is nonempty.** The common core of the
proposal round is reached by every block from two rounds up, the vote round
among them. -/
theorem safeAt_nonempty {f r : ℕ} {T : Finset Validator} (hf : honestᶜ.card ≤ f)
    (hq2 : Fintype.card Validator + f + 1 ≤ 2 * q) (hvo : 2 ≤ p.voteOffset) (hT : T.Nonempty)
    (hpop2 : PopulatedOn U T (r + 2)) :
    (safeAt p U r).Nonempty := by
  obtain ⟨v, hv⟩ := hT
  obtain ⟨c₀, hc₀, -, hc₀r⟩ := hpop2 v hv
  obtain ⟨b, hb, hbr, hbh, hreach⟩ := exists_commonCore hf hq2 hc₀ hc₀r
  exact ⟨_, mem_safeAt_of_reaches hb hbr hbh fun x hx hxr => hreach x hx (by omega)⟩

/-- **Two buffer rounds: the safe set holds `q − f` validators.** The common
core of the round above the proposal is reached by every block from two
rounds above it, the vote round among them, and so is each of its honest
references. -/
theorem le_card_safeAt {f r : ℕ} {T : Finset Validator} (hf : honestᶜ.card ≤ f)
    (hq2 : Fintype.card Validator + f + 1 ≤ 2 * q) (hvo : 3 ≤ p.voteOffset) (hT : T.Nonempty)
    (hpop3 : PopulatedOn U T (r + 3)) :
    q ≤ (safeAt p U r).card + f := by
  obtain ⟨v, hv⟩ := hT
  obtain ⟨c₀, hc₀, -, hc₀r⟩ := hpop3 v hv
  obtain ⟨c, hc, hcr, -, hreach⟩ :=
    exists_commonCore (r := r + 1) hf hq2 hc₀ (by rw [hc₀r])
  have hsub : creatorsOf U.block (U.block c).refs ∩ honest ⊆ safeAt p U r := by
    intro w hw'
    obtain ⟨hwc, hwh⟩ := Finset.mem_inter.mp hw'
    obtain ⟨L, hL, rfl⟩ := mem_creatorsOf.mp hwc
    have hLU := U.complete c hc L hL
    have hLr : (U.block L).round = r := by have := U.round_of_mem_refs hc hL; omega
    exact mem_safeAt_of_reaches hLU hLr hwh
      fun x hx hxr => (hreach x hx (by omega)).trans (Reaches.single hL)
  have hq := U.creators_quorum hc (by omega)
  have := card_le_inter_add_compl (honest := honest) (creatorsOf U.block (U.block c).refs)
  have := Finset.card_le_card hsub
  omega

omit [Fintype Validator] [P.Mechanised] [P.Quorate q] in
theorem safeAt_subset_honest {r : ℕ} : safeAt p U r ⊆ honest := Finset.filter_subset _ _

/-- **One buffer round: the double count.** With an honest population `T`
of the buffer round, each of its blocks names at least `q − f` honest
round-`r` blocks, and an honest block named by more than `n − q` of them is
reached from two rounds up, so safe. Counting the names twice:
`|T|·(q − f) + G·(n − q) ≤ G·|T| + |honest|·(n − q)`, `G` the safe set's
size. -/
theorem card_safeAt_count {f r : ℕ} {T : Finset Validator} (hf : honestᶜ.card ≤ f)
    (hvo : 2 ≤ p.voteOffset) (hTh : T ⊆ honest) (hpop1 : PopulatedOn U T (r + 1))
    (hnq : Fintype.card Validator - q ≤ T.card) :
    T.card * (q - f) + (safeAt p U r).card * (Fintype.card Validator - q) ≤
      (safeAt p U r).card * T.card + honest.card * (Fintype.card Validator - q) := by
  classical
  set n := Fintype.card Validator
  set d := n - q
  set sB := (blocksAt U (r + 1)).filter (fun a => (U.block a).creator ∈ T) with hsB
  set tB := honestBlocksAt U r with htB
  let rel : BlockId → BlockId → Prop := fun a b => b ∈ (U.block a).refs
  -- the population's blocks are as many as the population
  have hsinj : Set.InjOn (fun a => (U.block a).creator) sB := by
    intro a ha a' ha' h
    obtain ⟨has, hat⟩ := Finset.mem_filter.mp ha
    obtain ⟨haU, har⟩ := mem_blocksAt.mp has
    obtain ⟨ha's, -⟩ := Finset.mem_filter.mp ha'
    obtain ⟨ha'U, ha'r⟩ := mem_blocksAt.mp ha's
    exact U.eq_of_creator_eq haU ha'U (hTh hat) rfl h.symm (by rw [har, ha'r])
  have hscard : sB.card = T.card := by
    rw [← Finset.card_image_of_injOn hsinj]
    congr 1
    ext v
    simp only [Finset.mem_image]
    constructor
    · rintro ⟨a, ha, rfl⟩; exact (Finset.mem_filter.mp ha).2
    · intro hv
      obtain ⟨a, ha, hac, har⟩ := hpop1 v hv
      exact ⟨a, Finset.mem_filter.mpr ⟨mem_blocksAt.mpr ⟨ha, har⟩, hac ▸ hv⟩, hac⟩
  -- each population block names at least `q − f` honest round-`r` blocks
  have habove : ∀ a ∈ sB, q - f ≤ (tB.bipartiteAbove rel a).card := by
    intro a ha
    obtain ⟨has, -⟩ := Finset.mem_filter.mp ha
    obtain ⟨haU, har⟩ := mem_blocksAt.mp has
    have hq := U.creators_quorum haU (by omega)
    have hsplit := card_le_inter_add_compl (honest := honest) (creatorsOf U.block (U.block a).refs)
    have hsub : creatorsOf U.block (U.block a).refs ∩ honest ⊆
        creatorsOf U.block (tB.bipartiteAbove rel a) := by
      intro v hv
      obtain ⟨hvc, hvh⟩ := Finset.mem_inter.mp hv
      obtain ⟨b, hb, rfl⟩ := mem_creatorsOf.mp hvc
      have hbU := U.complete a haU b hb
      have hbr : (U.block b).round = r := by have := U.round_of_mem_refs haU hb; omega
      exact mem_creatorsOf.mpr ⟨b, Finset.mem_filter.mpr
        ⟨Finset.mem_filter.mpr ⟨mem_blocksAt.mpr ⟨hbU, hbr⟩, hvh⟩, hb⟩, rfl⟩
    have h1 := Finset.card_le_card hsub
    have h2 : (creatorsOf U.block (tB.bipartiteAbove rel a)).card ≤
        (tB.bipartiteAbove rel a).card := Finset.card_image_le
    omega
  -- a block named by more than `n − q` of them is good
  have hgood : ∀ b ∈ tB, d < (sB.bipartiteBelow rel b).card →
      (U.block b).creator ∈ safeAt p U r := by
    intro b hb hlt
    obtain ⟨hbs, hbh⟩ := Finset.mem_filter.mp hb
    obtain ⟨hbU, hbr⟩ := mem_blocksAt.mp hbs
    have hinj : Set.InjOn (fun a => (U.block a).creator) (sB.bipartiteBelow rel b) :=
      hsinj.mono (Finset.coe_subset.mpr (Finset.filter_subset _ _))
    have hcardS : (creatorsOf U.block (sB.bipartiteBelow rel b)).card =
        (sB.bipartiteBelow rel b).card := Finset.card_image_of_injOn hinj
    have hreach2 : ∀ c ∈ U.ids, (U.block c).round = r + 2 → Reaches U c b := by
      intro c hc hcr
      refine reaches_of_honest_support_of_card (b := b) (r := r)
        (S := creatorsOf U.block (sB.bipartiteBelow rel b)) ?_ ?_ (by omega) hc hcr
      · intro v hv
        obtain ⟨a, ha, rfl⟩ := mem_creatorsOf.mp hv
        obtain ⟨has, hab⟩ := Finset.mem_filter.mp ha
        obtain ⟨has', -⟩ := Finset.mem_filter.mp has
        obtain ⟨haU, har⟩ := mem_blocksAt.mp has'
        exact ⟨a, haU, har, hab, rfl⟩
      · intro v hv
        obtain ⟨a, ha, rfl⟩ := mem_creatorsOf.mp hv
        exact hTh (Finset.mem_filter.mp (Finset.mem_filter.mp ha).1).2
    refine mem_safeAt_of_reaches hbU hbr hbh fun x hx hxr => ?_
    obtain ⟨b', rfl, h⟩ := reaches_pred_of_round_le (Q := fun b' => b' = b) (N := r + 2)
      (fun c hc hcr => ⟨b, rfl, hreach2 c hc hcr⟩) hx (by omega)
    exact h
  -- the double count
  have hsum := Finset.sum_card_bipartiteAbove_eq_sum_card_bipartiteBelow
    (s := sB) (t := tB) (r := rel)
  have hlow : sB.card * (q - f) ≤ ∑ a ∈ sB, (tB.bipartiteAbove rel a).card := by
    have := Finset.card_nsmul_le_sum sB (fun a => (tB.bipartiteAbove rel a).card) (q - f) habove
    simpa [smul_eq_mul] using this
  set G' := (tB.filter (fun b => d < (sB.bipartiteBelow rel b).card)).card
  set R := (tB.filter (fun b => ¬ d < (sB.bipartiteBelow rel b).card)).card
  have hsplit := Finset.sum_filter_add_sum_filter_not tB
    (fun b => d < (sB.bipartiteBelow rel b).card) (fun b => (sB.bipartiteBelow rel b).card)
  have hX : ∑ b ∈ tB.filter (fun b => d < (sB.bipartiteBelow rel b).card),
      (sB.bipartiteBelow rel b).card ≤ G' * sB.card := by
    have := Finset.sum_le_card_nsmul (tB.filter (fun b => d < (sB.bipartiteBelow rel b).card))
      (fun b => (sB.bipartiteBelow rel b).card) sB.card
      (fun b _ => Finset.card_le_card (Finset.filter_subset _ _))
    rwa [smul_eq_mul] at this
  have hY : ∑ b ∈ tB.filter (fun b => ¬ d < (sB.bipartiteBelow rel b).card),
      (sB.bipartiteBelow rel b).card ≤ R * d := by
    have := Finset.sum_le_card_nsmul (tB.filter (fun b => ¬ d < (sB.bipartiteBelow rel b).card))
      (fun b => (sB.bipartiteBelow rel b).card) d
      (fun b hb => by have := (Finset.mem_filter.mp hb).2; omega)
    rwa [smul_eq_mul] at this
  have hGR : G' + R = tB.card := Finset.card_filter_add_card_filter_not _
  have hA : tB.card ≤ honest.card := by
    rw [← card_creatorsOf_honestBlocksAt]
    exact Finset.card_le_card creatorsOf_honestBlocksAt_subset
  have hG' : G' ≤ (safeAt p U r).card := by
    have heq : (Finset.image (fun b => (U.block b).creator)
        (tB.filter (fun b => d < (sB.bipartiteBelow rel b).card))).card = G' :=
      Finset.card_image_of_injOn (creator_injOn_honestBlocksAt.mono
        (Finset.coe_subset.mpr (Finset.filter_subset _ _)))
    rw [← heq]
    refine Finset.card_le_card fun v hv => ?_
    obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp hv
    obtain ⟨hbt, hlt⟩ := Finset.mem_filter.mp hb
    exact hgood b hbt hlt
  rw [hscard] at hlow hX
  have hmain : T.card * (q - f) ≤ G' * T.card + R * d := by omega
  obtain ⟨e, he⟩ : ∃ e, (safeAt p U r).card = G' + e := ⟨_, (Nat.add_sub_cancel' hG').symm⟩
  obtain ⟨h', hh'⟩ : ∃ h', honest.card = G' + R + h' := ⟨honest.card - (G' + R), by omega⟩
  rw [he, hh']
  have hed : e * d ≤ e * T.card := Nat.mul_le_mul_left e hnq
  nlinarith [hmain, hed]

omit [P.Mechanised] [P.Quorate q] in
/-- **Several leaders**: leaders at round `r` more than `n` less the safe set
include a safe one. -/
theorem exists_safe_leader [S : Slots Validator] {r : ℕ} {M : Finset Validator}
    (hM : ∀ v ∈ M, ∃ k, S.slotRound k = r ∧ S.leader k = v)
    (hcard : Fintype.card Validator < M.card + (safeAt p U r).card) :
    ∃ k, S.slotRound k = r ∧ S.leader k ∈ safe p U k := by
  obtain ⟨v, hv⟩ := Finset.inter_nonempty_of_card_lt_card_add_card (Finset.subset_univ M)
    (Finset.subset_univ _) (by simpa using hcard)
  obtain ⟨hvM, hvg⟩ := Finset.mem_inter.mp hv
  obtain ⟨k, hkr, hkv⟩ := hM v hvM
  exact ⟨k, hkr, by
    show S.leader k ∈ safeAt p U (S.slotRound k)
    rw [hkr, hkv]; exact hvg⟩

end Scheme

end LeanDag
