import LeanDag.Scheme.Model.Async
import LeanDag.Scheme.Helpers.Support
import LeanDag.Common.Anchored.Bounded
import LeanDag.Common.CommonCore
import Mathlib.Combinatorics.Enumerative.DoubleCounting
import Mathlib.Algebra.Group.Action.Defs
import Mathlib.Tactic.Linarith
/-!
# The asynchronous rows: the count

On a record whose blocks reference `q` distinct authors one round down and
whose validators outside `honest`, at most `f`, may equivocate:

* **the common core** (`exists_commonCore`, `Common/CommonCore.lean`): at
  `2q ≥ n + f + 1`, some honest round-`r` block lies in the history of
  every block from round `r + 2` up;
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
  have vote : ∀ b ∈ U.ids, (U.block b).round = r + p.voteOffset → σ.Votes U b L :=
    fun b hb hbr => votes_of_reaches_record U.noEquivOn_honest hb hL hLc
      (by have := Params.one_le_voteOffset hw; omega)
      (hsafe b hb hbr)
  refine isCert_of_votes σ p (fun hv => vote C hC (by rw [Params.voteOffset_of_true hv]; omega))
    fun hv => ⟨_, le_trans (hcv hv).2 (U.creators_quorum hC (by omega)), fun u hu => ?_⟩
  obtain ⟨b, hb, rfl⟩ := mem_creatorsOf.mp hu
  have hbU := U.complete C hC b hb
  have hbr := U.round_of_mem_refs hC hb
  exact ⟨b, hb, rfl, vote b hbU (by rw [Params.voteOffset_of_false hv (hcv hv).1]; omega)⟩

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
  have hmain := card_mul_le_of_bipartite_filter sB tB rel (d := d) habove
  set G' := (tB.filter (fun b => d < (sB.bipartiteBelow rel b).card)).card
  set R := (tB.filter (fun b => ¬ d < (sB.bipartiteBelow rel b).card)).card
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
  rw [hscard] at hmain
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
