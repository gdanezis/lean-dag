import LeanDag.Scheme.Model.Reactive
import LeanDag.Scheme.Model.Crash
import LeanDag.Scheme.Helpers.Support
import Mathlib.Data.Prod.Lex
import Mathlib.Data.Fintype.Fin
/-!
# The full run: a responsive run at every row

On `n` validators, every validator builds every round up to `N`, and its
round-`r` block, identified by `(r, v)`, references every block of round
`r − 1`. The record is valid at every quorum `q ≤ n` with distinct authors
and self-reference (`record`). Run in lockstep, round `r` built at time
`r` and every block held by every validator from the time it is built,
with no delay and no processing time, it is a responsive run of the family
(`run`) at every row whose certificate threshold is at most `n`, at every
vote rule and every schedule: every block reaches every block of a lower
round, so both wait clauses hold by their first disjunct.
-/

namespace LeanDag

namespace Scheme

namespace Full

variable (n : ℕ)

/-- Validator `v`'s round-`r` block, identified by `(r, v)`, referencing
the whole round below. -/
def blk (b : Lex (ℕ × Fin n)) : Block (Fin n) (Lex (ℕ × Fin n)) Unit where
  round := (ofLex b).1
  creator := (ofLex b).2
  refs := if (ofLex b).1 = 0 then ∅ else
    (Finset.univ : Finset (Fin n)).image fun w => toLex ((ofLex b).1 - 1, w)
  payload := ()

variable {n}

@[simp] theorem blk_round (b : Lex (ℕ × Fin n)) : (blk n b).round = (ofLex b).1 := rfl
@[simp] theorem blk_creator (b : Lex (ℕ × Fin n)) : (blk n b).creator = (ofLex b).2 := rfl

theorem mem_blk_refs {b j : Lex (ℕ × Fin n)} :
    j ∈ (blk n b).refs ↔ (ofLex j).1 + 1 = (ofLex b).1 := by
  unfold blk
  dsimp only
  split
  · rename_i h
    simp only [Finset.notMem_empty, false_iff]
    omega
  · rename_i h
    simp only [Finset.mem_image, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨w, rfl⟩
      simp only [ofLex_toLex]
      omega
    · intro h1
      refine ⟨(ofLex j).2, ?_⟩
      rw [← toLex_ofLex j]
      congr 1
      ext <;> simp; omega

/-- **The full record** up to round `N`, at quorum `q ≤ n`. -/
def record {q : ℕ} (hq : q ≤ n) (N : ℕ) :
    BlockRecord (Fin n) (Lex (ℕ × Fin n)) Unit (ValidAt q (Clause.distinct.and Clause.selfParent))
      Finset.univ where
  ids := ((Finset.range (N + 1)) ×ˢ Finset.univ).map toLex.toEmbedding
  block := blk n
  complete i hi j hj := by
    simp only [Finset.mem_map, Finset.mem_product, Finset.mem_range, Finset.mem_univ, and_true,
      Equiv.coe_toEmbedding] at hi ⊢
    obtain ⟨x, hx, rfl⟩ := hi
    have h := mem_blk_refs.mp hj
    simp only [ofLex_toLex] at h
    exact ⟨ofLex j, by omega, toLex_ofLex j⟩
  valid i _ := by
    refine ⟨fun j hj => mem_blk_refs.mp hj, fun hr => ?_, fun j hj l hl hjl => ?_,
      fun hr => ?_⟩
    · -- every validator is among the creators
      have hsub : (Finset.univ : Finset (Fin n)) ⊆ creators (blk n) (blk n i) := by
        intro w _
        refine mem_creatorsOf.mpr ⟨toLex ((ofLex i).1 - 1, w), mem_blk_refs.mpr ?_, by simp⟩
        simp only [ofLex_toLex]
        simp only [blk_round] at hr
        omega
      refine le_trans ?_ (Finset.card_le_card hsub)
      simpa using hq
    · simp only [blk_creator] at hjl
      have h1 := mem_blk_refs.mp hj
      have h2 := mem_blk_refs.mp hl
      rw [← toLex_ofLex j, ← toLex_ofLex l]
      congr 1
      exact Prod.ext (by omega) hjl
    · refine ⟨toLex ((ofLex i).1 - 1, (ofLex i).2), mem_blk_refs.mpr ?_, by simp⟩
      simp only [ofLex_toLex]
      simp only [blk_round] at hr
      omega
  no_equivocation i _ j _ _ hc hr := by
    rw [← toLex_ofLex i, ← toLex_ofLex j]
    exact congrArg toLex (Prod.ext hr hc)

variable {q : ℕ} {hq : q ≤ n} {N : ℕ}

@[simp] theorem record_block : (record hq N).block = blk n := rfl

theorem mem_record_ids {b : Lex (ℕ × Fin n)} :
    b ∈ (record hq N).ids ↔ (ofLex b).1 ≤ N := by
  simp only [record, Finset.mem_map, Finset.mem_product, Finset.mem_range, Finset.mem_univ,
    and_true, Equiv.coe_toEmbedding]
  constructor
  · rintro ⟨x, hx, rfl⟩; simp only [ofLex_toLex]; omega
  · intro h; exact ⟨ofLex b, by omega, toLex_ofLex b⟩

/-- **Every block reaches every block of a lower round.** -/
theorem reaches_of_lt : ∀ (d : ℕ) {b j : Lex (ℕ × Fin n)},
    (ofLex b).1 = (ofLex j).1 + d + 1 → Reaches (record hq N) b j
  | 0, b, j, h => Reaches.single (mem_blk_refs.mpr (by omega))
  | d + 1, b, j, h => by
      refine Reaches.of_mem_refs (j := toLex ((ofLex b).1 - 1, (ofLex j).2))
        (mem_blk_refs.mpr (by simp only [ofLex_toLex]; omega)) (reaches_of_lt d ?_)
      simp only [ofLex_toLex]
      omega

/-- What every validator holds at time `t`: the blocks of rounds up to `t`. -/
def holdsAt (hq : q ≤ n) (N : ℕ) (t : ℕ) : Finset (Lex (ℕ × Fin n)) :=
  (record hq N).ids.filter fun b => (ofLex b).1 ≤ t

theorem mem_holdsAt {t : ℕ} {b : Lex (ℕ × Fin n)} :
    b ∈ holdsAt hq N t ↔ (ofLex b).1 ≤ N ∧ (ofLex b).1 ≤ t := by
  simp only [holdsAt, Finset.mem_filter, mem_record_ids]

attribute [local instance] noFaults

variable [NeZero n] [S : Slots (Fin n)]

omit [NeZero n] S in
/-- **Every block two rounds above a leader block certifies it**, at a row
whose votes are certified a round later and whose certificate threshold is
at most `n`: its references are the whole round below, each of which
reaches the leader block and so votes for it. -/
theorem certifies {p : Params} (hcert : p.certThreshold ≤ n)
    (σ : VoteSel (Fin n) (Lex (ℕ × Fin n)) Unit
      (ValidAt q (Clause.distinct.and Clause.selfParent)) Finset.univ)
    (hvc : p.voteIsCert = false) {L c : Lex (ℕ × Fin n)} (hLmem : L ∈ (record hq N).ids)
    (hc : c ∈ (record hq N).ids) (hlt : (ofLex L).1 + 2 ≤ (ofLex c).1) :
    IsCert p σ (record hq N) c L := by
  unfold IsCert
  rw [if_neg (by rw [hvc]; decide)]
  change p.certThreshold ≤ (creatorsOf (blk n) (carriedVotes (record hq N)
    (σ.Votes (record hq N)) c L)).card
  have hsub : (Finset.univ : Finset (Fin n)) ⊆
      creatorsOf (blk n) (carriedVotes (record hq N) (σ.Votes (record hq N)) c L) := by
    intro w _
    have hcN := mem_record_ids.mp hc
    refine mem_creatorsOf.mpr ⟨toLex ((ofLex c).1 - 1, w), ?_, by simp⟩
    refine Finset.mem_filter.mpr ⟨mem_blk_refs.mpr (by simp only [ofLex_toLex]; omega), ?_⟩
    refine votes_of_reaches_record (record hq N).noEquivOn_honest
      (mem_record_ids.mpr (by simp only [ofLex_toLex]; omega)) hLmem (Finset.mem_univ _)
      (by change (ofLex L).1 < (ofLex (toLex ((ofLex c).1 - 1, w))).1
          simp only [ofLex_toLex]; omega)
      (reaches_of_lt ((ofLex c).1 - 2 - (ofLex L).1) ?_)
    simp only [ofLex_toLex]
    omega
  exact le_trans (by simpa using hcert) (Finset.card_le_card hsub)

/-- **The full run is a responsive run** of the family at quorum `qr`, at
every row whose certificate threshold is at most `n`, every vote rule and
every schedule: round `r` built at time `r`, every block held by every
validator from then on, no delay and no processing time, a timeout of
`1`. -/
def run (qr : ℕ) (p : Params) (hcert : p.certThreshold ≤ n)
    (σ : VoteSel (Fin n) (Lex (ℕ × Fin n)) Unit
      (ValidAt q (Clause.distinct.and Clause.selfParent)) Finset.univ) :
    SchemeReactive qr p σ (record hq N) Finset.univ N where
  top := fun _ => N
  built := fun _ r => r
  timeout := fun _ => 1
  proc := 0
  gst := 0
  delay := 0
  rounds_le := fun b hb => mem_record_ids.mp hb
  built_of_le_top := fun v _ r hr =>
    ⟨toLex (r, v), mem_record_ids.mpr (by simpa using hr), by simp, by simp⟩
  le_top_of_built := fun _ _ b hb _ => mem_record_ids.mp hb
  timeout_pos := fun _ => le_refl 1
  latest := fun r => r
  built_le_latest := fun _ _ _ _ => le_refl _
  built_lt := fun _ _ _ _ => Nat.lt_succ_self _
  deadline := fun _ _ _ _ _ => le_refl _
  holds := fun _ t => holdsAt hq N t
  holds_sub := fun _ _ => Finset.filter_subset _ _
  refs_held := fun _ _ r b hb _ hbr j hj => by
    have hj' := mem_blk_refs.mp hj
    have hb' := mem_record_ids.mp hb
    change (ofLex b).1 = r + 1 at hbr
    exact mem_holdsAt.mpr ⟨by omega, by omega⟩
  holds_closed := fun _ _ t b hb j hj => by
    have hj' := mem_blk_refs.mp hj
    have hb' := mem_holdsAt.mp hb
    exact mem_holdsAt.mpr ⟨by omega, by omega⟩
  holds_own := fun _ _ r _ b hb _ hbr => by
    change (ofLex b).1 = r at hbr
    exact mem_holdsAt.mpr ⟨mem_record_ids.mp hb, le_of_eq hbr⟩
  holds_mono := fun _ s t hst b hb => by
    have hb' := mem_holdsAt.mp hb
    exact mem_holdsAt.mpr ⟨hb'.1, le_trans hb'.2 hst⟩
  converges := fun _ _ _ _ t _ b hb => by simpa using hb
  advances := fun _ _ _ hr _ _ => hr
  catchup := fun _ _ r hr b _ _ hbr t _ hheld => by
    have hh := mem_holdsAt.mp hheld
    change (ofLex b).1 = r at hbr
    exact ⟨hr, by omega⟩
  advancesAt := fun _ _ _ hr _ _ => hr
  reach_or_wait := fun _ _ k _ _ _ L hL m _ c _ _ hcr => by
    left
    obtain ⟨_, hLr, -⟩ := hL
    change (ofLex L).1 = S.slotRound k at hLr
    change (ofLex c).1 = S.slotRound k + m + 1 at hcr
    exact reaches_of_lt m (by omega)
  cert_or_wait := fun hvc _ _ k _ _ _ L hL c hc _ hcr => by
    left
    obtain ⟨hLmem, hLr, -⟩ := hL
    change (ofLex L).1 = S.slotRound k at hLr
    change (ofLex c).1 = S.slotRound k + p.voteOffset + 1 at hcr
    have hvo : 1 ≤ p.voteOffset := by
      unfold Params.voteOffset; rw [hvc]; simp
    exact certifies hcert σ hvc hLmem hc (by omega)

@[simp] theorem run_gst (qr : ℕ) (p : Params) (hcert : p.certThreshold ≤ n) (σ) :
    (run (hq := hq) (N := N) qr p hcert σ).gst = 0 := rfl

@[simp] theorem run_delay (qr : ℕ) (p : Params) (hcert : p.certThreshold ≤ n) (σ) :
    (run (hq := hq) (N := N) qr p hcert σ).delay = 0 := rfl

@[simp] theorem run_proc (qr : ℕ) (p : Params) (hcert : p.certThreshold ≤ n) (σ) :
    (run (hq := hq) (N := N) qr p hcert σ).proc = 0 := rfl

@[simp] theorem run_timeout (qr : ℕ) (p : Params) (hcert : p.certThreshold ≤ n) (σ) (r : ℕ) :
    (run (hq := hq) (N := N) qr p hcert σ).timeout r = 1 := rfl

end Full

namespace Full

variable {n q : ℕ} {hq : q ≤ n} {N : ℕ}

/-- When round `r` is built in the run with an outage: round `0` at time
`0`, round `r > 0` at time `r + D`. -/
def at_ (D r : ℕ) : ℕ := if r = 0 then 0 else r + D

theorem at_mono {D r s : ℕ} (h : r ≤ s) : at_ D r ≤ at_ D s := by
  unfold at_; split <;> split <;> omega

theorem at_lt {D r : ℕ} : at_ D r < at_ D (r + 1) := by
  unfold at_; split <;> simp

/-- What every validator holds at time `t` in the run with an outage. -/
def holdsOut (hq : q ≤ n) (N D t : ℕ) : Finset (Lex (ℕ × Fin n)) :=
  (record hq N).ids.filter fun b => at_ D (ofLex b).1 ≤ t

theorem mem_holdsOut {D t : ℕ} {b : Lex (ℕ × Fin n)} :
    b ∈ holdsOut hq N D t ↔ (ofLex b).1 ≤ N ∧ at_ D (ofLex b).1 ≤ t := by
  simp only [holdsOut, Finset.mem_filter, mem_record_ids]

attribute [local instance] noFaults

variable [NeZero n] [S : Slots (Fin n)]

/-- **Every validator crashes at once.** All build round `0` at time `0`,
all are down from `1` to `D`, and each rebuilds every round on restart:
a crash run whose validators all stay up from `D + 1` on. -/
def crashRun (qr : ℕ) (p : Params) (hcert : p.certThreshold ≤ n)
    (σ : VoteSel (Fin n) (Lex (ℕ × Fin n)) Unit
      (ValidAt q (Clause.distinct.and Clause.selfParent)) Finset.univ) (D : ℕ) :
    CrashRun qr p σ (record hq N) Finset.univ N where
  top := fun _ => N
  built := fun _ r => at_ D r
  timeout := fun _ => 1
  gst := 0
  delay := 0
  proc := 0
  latest := fun r => at_ D r
  holds := fun _ t => holdsOut hq N D t
  up := fun _ t => t = 0 ∨ D < t
  tr := D + 1
  up_from := fun _ _ t ht => Or.inr (by omega)
  up_built := fun _ _ r _ => by
    show at_ D r = 0 ∨ D < at_ D r
    unfold at_; split <;> omega
  rounds_le := fun b hb => mem_record_ids.mp hb
  built_of_le_top := fun v _ r hr =>
    ⟨toLex (r, v), mem_record_ids.mpr (by simpa using hr), by simp, by simp⟩
  le_top_of_built := fun _ _ b hb _ => mem_record_ids.mp hb
  timeout_pos := fun _ => le_refl 1
  built_le_latest := fun _ _ _ _ => le_refl _
  holds_sub := fun _ _ => Finset.filter_subset _ _
  holds_closed := fun _ _ t b hb j hj => by
    have hj' := mem_blk_refs.mp hj
    have hb' := mem_holdsOut.mp hb
    exact mem_holdsOut.mpr ⟨by omega, le_trans (at_mono (by omega)) hb'.2⟩
  refs_held := fun _ _ r b hb _ hbr j hj => by
    have hj' := mem_blk_refs.mp hj
    have hb' := mem_record_ids.mp hb
    change (ofLex b).1 = r + 1 at hbr
    exact mem_holdsOut.mpr ⟨by omega, at_mono (by omega)⟩
  holds_own := fun _ _ r _ b hb _ hbr => by
    change (ofLex b).1 = r at hbr
    exact mem_holdsOut.mpr ⟨mem_record_ids.mp hb, by rw [hbr]⟩
  holds_mono := fun _ s t hst b hb => by
    have hb' := mem_holdsOut.mp hb
    exact mem_holdsOut.mpr ⟨hb'.1, le_trans hb'.2 hst⟩
  converges := fun _ _ _ _ t _ _ _ b hb => by simpa using hb
  advances := fun _ _ _ hr _ _ => hr
  catchup := fun _ _ r hr b _ _ hbr t _ _ hheld => by
    have hh := mem_holdsOut.mp hheld
    change (ofLex b).1 = r at hbr
    rw [hbr] at hh
    exact ⟨hr, by omega⟩
  built_lt := fun _ _ _ _ => at_lt
  deadline := fun _ _ r _ _ hup => by
    rcases Nat.eq_zero_or_pos r with rfl | hr
    · -- from round `0`, the validator was down unless there was no outage
      have h1 := hup 1 (Nat.zero_le _) (by unfold at_; simp)
      rcases h1 with h1 | h1
      · omega
      · unfold at_; simp; omega
    · unfold at_; split <;> split <;> omega
  advancesAt := fun _ _ _ hr _ _ => hr
  reach_or_wait := fun _ _ k _ _ _ L hL m _ c _ _ hcr => by
    left
    obtain ⟨_, hLr, -⟩ := hL
    change (ofLex L).1 = S.slotRound k at hLr
    change (ofLex c).1 = S.slotRound k + m + 1 at hcr
    exact reaches_of_lt m (by omega)
  cert_or_wait := fun hvc _ _ k _ _ _ L hL c hc _ hcr => by
    left
    obtain ⟨hLmem, hLr, -⟩ := hL
    change (ofLex L).1 = S.slotRound k at hLr
    change (ofLex c).1 = S.slotRound k + p.voteOffset + 1 at hcr
    have hvo : 1 ≤ p.voteOffset := by
      unfold Params.voteOffset; rw [hvc]; simp
    exact certifies hcert σ hvc hLmem hc (by omega)

end Full

end Scheme

end LeanDag
