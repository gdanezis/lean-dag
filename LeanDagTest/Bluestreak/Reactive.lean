import LeanDag.Bluestreak.Reactive
import Mathlib.Tactic.FinCases

/-!
# The sparse DAG, grown, under the reactive schedule

`Usparse N` is Bluestreak's good case at every horizon: four validators,
`f = 1`, block `b` at round `b / 4` by author `b % 4`, the leader of
round `r` being `r % 4`. A leader block references the whole round
below; every other block references its own previous block and the
previous round's leader block; every non-leader block two rounds above
a leader claims it. `spReactive N` is a `ReactiveB` on it at the core's
reactive constants — builds at spacing `6` inside a timeout of
`9 = 2Δ + proc` — with every wait clause discharged by its reactive
exit, and the two discipline clauses by the layout: every claim in the
cone of a held block is backed by the round below the claimed leader,
which has arrived. `disciplined`, `decided` and the descent below a run
are then instantiated.
-/

namespace LeanDagTest

open LeanDag LeanDag.Bluestreak

instance spFaults : Faults (Fin 4) where
  f := 1
  byzantine := {0}
  card_validators := by decide
  card_byzantine := by decide

instance spSlots : Slots (Fin 4) := Slots.identity fun k => ⟨k % 4, Nat.mod_lt _ (by omega)⟩

theorem spSlots_leader_val (k : ℕ) : (spSlots.leader k).val = k % 4 := rfl

/-- The leader block of round `r`. -/
def leaderId (r : ℕ) : ℕ := 4 * r + r % 4

/-- Block `b`'s references: the whole round below for a leader block,
the author's previous block and the previous leader block otherwise. -/
def spRefs (b : ℕ) : Finset ℕ :=
  if b / 4 = 0 then ∅
  else if b % 4 = (b / 4) % 4 then Finset.Ico (4 * (b / 4) - 4) (4 * (b / 4))
  else {4 * (b / 4) - 4 + b % 4, leaderId (b / 4 - 1)}

def spBlock (b : ℕ) : Block (Fin 4) ℕ Unit where
  round := b / 4
  creator := ⟨b % 4, by omega⟩
  refs := spRefs b
  payload := ()

@[simp] theorem spBlock_round (b : ℕ) : (spBlock b).round = b / 4 := rfl
@[simp] theorem spBlock_creator_val (b : ℕ) : ((spBlock b).creator : ℕ) = b % 4 := rfl
@[simp] theorem spBlock_refs (b : ℕ) : (spBlock b).refs = spRefs b := rfl

/-- Non-leader blocks two rounds above a leader claim it. -/
instance spClaims : ClaimMap ℕ where
  claim b := if 2 ≤ b / 4 ∧ b % 4 ≠ (b / 4) % 4 then some (leaderId (b / 4 - 2)) else none

theorem spClaims_eq (b : ℕ) :
    claim b = if 2 ≤ b / 4 ∧ b % 4 ≠ (b / 4) % 4 then some (leaderId (b / 4 - 2)) else none := rfl

/-! ## The references, arithmetically -/

theorem mem_spRefs {b i : ℕ} :
    i ∈ spRefs b ↔ 0 < b / 4 ∧
      ((b % 4 = (b / 4) % 4 ∧ 4 * (b / 4) - 4 ≤ i ∧ i < 4 * (b / 4)) ∨
        (b % 4 ≠ (b / 4) % 4 ∧ (i = 4 * (b / 4) - 4 + b % 4 ∨ i = leaderId (b / 4 - 1)))) := by
  unfold spRefs
  split_ifs with h0 hl
  · simp only [Finset.notMem_empty, false_iff]; omega
  · simp only [Finset.mem_Ico]
    constructor
    · intro h; exact ⟨by omega, Or.inl ⟨hl, h.1, h.2⟩⟩
    · rintro ⟨-, ⟨-, h1, h2⟩ | ⟨h, -⟩⟩
      · exact ⟨h1, h2⟩
      · exact absurd hl h
  · simp only [Finset.mem_insert, Finset.mem_singleton]
    constructor
    · intro h; exact ⟨by omega, Or.inr ⟨hl, h⟩⟩
    · rintro ⟨-, ⟨h, -⟩ | ⟨-, h⟩⟩
      · exact absurd h hl
      · exact h

/-- Every reference sits in the round below. -/
theorem spRefs_bounds {b i : ℕ} (h : i ∈ spRefs b) : 4 * (b / 4) - 4 ≤ i ∧ i < 4 * (b / 4) := by
  rcases mem_spRefs.mp h with ⟨h0, ⟨_, h1, h2⟩ | ⟨_, rfl | rfl⟩⟩
  · exact ⟨h1, h2⟩
  · omega
  · unfold leaderId; omega

/-- The previous leader block is referenced by every block of the round. -/
theorem leaderId_mem_spRefs {r w : ℕ} (hw : w < 4) : leaderId r ∈ spRefs (4 * (r + 1) + w) := by
  rw [mem_spRefs]
  have h1 : (4 * (r + 1) + w) / 4 = r + 1 := by omega
  have h2 : (4 * (r + 1) + w) % 4 = w := by omega
  rw [h1, h2]
  refine ⟨by omega, ?_⟩
  by_cases hw' : w = (r + 1) % 4
  · left; refine ⟨hw', ?_, ?_⟩ <;> unfold leaderId <;> omega
  · right; exact ⟨hw', Or.inr (by simp)⟩

/-- A leader block's references are the whole round below. -/
theorem spRefs_leader {r : ℕ} (hr : 0 < r) :
    spRefs (leaderId r) = Finset.Ico (4 * r - 4) (4 * r) := by
  unfold spRefs leaderId
  have h1 : (4 * r + r % 4) / 4 = r := by omega
  have h2 : (4 * r + r % 4) % 4 = r % 4 := by omega
  rw [h1, h2]
  simp [Nat.pos_iff_ne_zero.mp hr]

/-- Four references at distinct authors are the full committee. -/
theorem card_creators_Ico {r : ℕ} (hr : 0 < r) :
    (creatorsOf spBlock (Finset.Ico (4 * r - 4) (4 * r))).card = 4 := by
  rw [creatorsOf, Finset.card_image_of_injOn, Nat.card_Ico]
  · omega
  · intro a ha b hb hab
    rw [Finset.mem_coe, Finset.mem_Ico] at ha hb
    have : a % 4 = b % 4 := by
      have := congrArg (fun (v : Fin 4) => (v : ℕ)) hab
      simpa using this
    omega

/-- A candidate of slot `k` is the leader block of round `k`. -/
theorem eq_leaderId_of_isLeaderBlock {k L : ℕ}
    {U : Universe (Fin 4) ℕ Unit} (hblk : U.block = spBlock) (hL : IsLeaderBlock U k L) :
    L = leaderId k := by
  obtain ⟨-, hr, hc⟩ := hL
  rw [hblk] at hr hc
  have hc' : L % 4 = k % 4 := congrArg (fun (v : Fin 4) => (v : ℕ)) hc
  have hr' : L / 4 = k := hr
  unfold leaderId
  omega

/-- A slot not led by `0` is led by `T`. -/
theorem leader_mem_T {k : ℕ} (hk : k % 4 ≠ 0) :
    spSlots.leader k ∈ ({1, 2, 3} : Finset (Fin 4)) := by
  have h4 : k % 4 < 4 := Nat.mod_lt _ (by omega)
  rcases (by omega : k % 4 = 1 ∨ k % 4 = 2 ∨ k % 4 = 3) with h | h | h
  · exact Finset.mem_insert.mpr (Or.inl (Fin.ext (by rw [spSlots_leader_val, h]; rfl)))
  · exact Finset.mem_insert.mpr (Or.inr (Finset.mem_insert.mpr
      (Or.inl (Fin.ext (by rw [spSlots_leader_val, h]; rfl)))))
  · exact Finset.mem_insert.mpr (Or.inr (Finset.mem_insert.mpr
      (Or.inr (Finset.mem_singleton.mpr (Fin.ext (by rw [spSlots_leader_val, h]; rfl))))))

/-! ## The universe -/

def Usparse (N : ℕ) : Universe (Fin 4) ℕ Unit where
  ids := Finset.range (4 * (N + 1))
  block := spBlock
  complete := by
    intro i hi j hj
    rw [Finset.mem_range] at hi ⊢
    have := spRefs_bounds hj
    omega
  valid := by
    intro i _
    refine ⟨fun j hj => ?_, fun _ => Nat.zero_le _, fun j hj l hl hjl => ?_, fun h => ?_⟩
    · have := spRefs_bounds hj
      simp only [spBlock_round]; omega
    · have := spRefs_bounds hj
      have := spRefs_bounds hl
      have : j % 4 = l % 4 := by
        have := congrArg (fun (v : Fin 4) => (v : ℕ)) hjl
        simpa using this
      omega
    · simp only [spBlock_round] at h
      refine ⟨4 * (i / 4) - 4 + i % 4, ?_, ?_⟩
      · show _ ∈ spRefs i
        rw [mem_spRefs]
        refine ⟨h, ?_⟩
        by_cases hl : i % 4 = (i / 4) % 4
        · left; exact ⟨hl, by omega, by omega⟩
        · right; exact ⟨hl, Or.inl rfl⟩
      · apply Fin.ext; simp only [spBlock_creator_val]; omega
  no_equivocation := by
    intro i _ j _ _ hc hr
    have : i % 4 = j % 4 := by
      have := congrArg (fun (v : Fin 4) => (v : ℕ)) hc
      simpa using this
    simp only [spBlock_round] at hr
    omega

@[simp] theorem usparse_ids (N : ℕ) : (Usparse N).ids = Finset.range (4 * (N + 1)) := rfl
@[simp] theorem usparse_block (N : ℕ) : (Usparse N).block = spBlock := rfl

/-! ## Holdings, and what backs a claim -/

/-- What `v` holds at `t`: block `b`, built at `b % 4 + 6 * (b / 4)`, once
`delay = 2` has passed, and its own blocks from the build. -/
def spHolds (N : ℕ) (v : Fin 4) (t : ℕ) : Finset ℕ :=
  (Finset.range (4 * (N + 1))).filter fun b =>
    b % 4 + 6 * (b / 4) + 2 ≤ t ∨ (b % 4 = (v : ℕ) ∧ b % 4 + 6 * (b / 4) ≤ t)

theorem mem_spHolds {N : ℕ} {v : Fin 4} {t b : ℕ} :
    b ∈ spHolds N v t ↔ b < 4 * (N + 1) ∧
      (b % 4 + 6 * (b / 4) + 2 ≤ t ∨ (b % 4 = (v : ℕ) ∧ b % 4 + 6 * (b / 4) ≤ t)) := by
  simp [spHolds]

/-- **The round below a leader backs it**, once it has arrived: all four
of its blocks reference the leader block, and all four have been held
since `6 * (m - 1) + 5`. -/
theorem backedIn_leaderId {N m t : ℕ} (v : Fin 4) (hm : 1 ≤ m) (hmN : m ≤ N)
    (ht : 6 * m + 5 ≤ t) : BackedIn (Usparse N) (spHolds N v t) (leaderId (m - 1)) := by
  unfold BackedIn
  have hq : quorumCard (Fin 4) = 3 := rfl
  rw [hq]
  refine le_trans (by decide : 3 ≤ (Finset.univ : Finset (Fin 4)).card)
    (Finset.card_le_card fun w _ => ?_)
  refine mem_creatorsOf.mpr ⟨4 * m + (w : ℕ), Finset.mem_inter.mpr ⟨?_, ?_⟩, ?_⟩
  · refine mem_votesFor.mpr ⟨?_, ?_, ?_⟩
    · simp only [usparse_ids, Finset.mem_range]; have := w.isLt; omega
    · simp only [usparse_block, spBlock_round]; unfold leaderId; omega
    · simp only [usparse_block, spBlock_refs]
      have := leaderId_mem_spRefs (r := m - 1) w.isLt
      rwa [show m - 1 + 1 = m by omega] at this
  · rw [mem_spHolds]
    have := w.isLt
    refine ⟨by omega, Or.inl ?_⟩
    have h1 : (4 * m + (w : ℕ)) % 4 = w := by omega
    have h2 : (4 * m + (w : ℕ)) / 4 = m := by omega
    omega
  · apply Fin.ext; simp only [usparse_block, spBlock_creator_val]; omega

/-- A claim names the leader two rounds below the claimer, and only from
round two. -/
theorem claim_spec {b L : ℕ} (h : claim b = some L) :
    2 ≤ b / 4 ∧ L = leaderId (b / 4 - 2) := by
  rw [spClaims_eq] at h
  split_ifs at h with hb
  exact ⟨hb.1, (Option.some.inj h).symm⟩

/-! ## The reactive schedule -/

theorem mem_T_bounds' {v : Fin 4} (hv : v ∈ ({1, 2, 3} : Finset (Fin 4))) :
    1 ≤ (v : ℕ) ∧ (v : ℕ) ≤ 3 := by fin_cases hv <;> exact ⟨by decide, by decide⟩

theorem correct_eq : (Correct : Finset (Fin 4)) = {1, 2, 3} := by decide

/-- **A claim reached from a held block is backed** by the time the round
after the claimer's round has arrived. -/
theorem backedIn_of_reaches_sp {N : ℕ} {v : Fin 4} {j Y L t : ℕ} (hj : j < 4 * (N + 1))
    (hjY : Reaches (Usparse N) j Y) (hcl : claim Y = some L) (ht : 6 * (j / 4) ≤ t + 1) :
    BackedIn (Usparse N) (spHolds N v t) L := by
  have hYi : Y ∈ (Usparse N).ids :=
    mem_ids_of_reaches (by simpa [usparse_ids] using hj) hjY
  have hYr : ((Usparse N).block Y).round ≤ ((Usparse N).block j).round :=
    round_le_of_reaches (by simpa [usparse_ids] using hj) hjY
  simp only [usparse_block, spBlock_round] at hYr
  simp only [usparse_ids, Finset.mem_range] at hYi
  obtain ⟨h2, rfl⟩ := claim_spec hcl
  rw [show Y / 4 - 2 = (Y / 4 - 1) - 1 by omega]
  exact backedIn_leaderId v (by omega) (by omega) (by omega)

/-- The reactive witness: `Usparse` at spacing `6` inside a timeout of
`9`. -/
def spReactive (N : ℕ) : ReactiveB (Usparse N) {1, 2, 3} N where
  top _ := N
  built v n := (v : ℕ) + 6 * n
  timeout _ := 9
  proc := 5
  gst := 0
  delay := 2
  rounds_le b hb := by
    simp only [usparse_ids, Finset.mem_range] at hb
    simp only [usparse_block, spBlock_round]; omega
  built_of_le_top v _ n hn := by
    have := v.isLt
    refine ⟨4 * n + (v : ℕ), ?_, ?_, ?_⟩
    · simp only [usparse_ids, Finset.mem_range]; omega
    · apply Fin.ext; simp only [usparse_block, spBlock_creator_val]; omega
    · simp only [usparse_block, spBlock_round]; omega
  le_top_of_built _ _ b hb _ := by
    simp only [usparse_ids, Finset.mem_range] at hb
    simp only [usparse_block, spBlock_round]; omega
  timeout_pos _ := by omega
  latest n := 3 + 6 * n
  built_le_latest v _ _ _ := by have := v.isLt; omega
  holds := spHolds N
  holds_sub _ _ := by
    simp only [spHolds, usparse_ids]; exact Finset.filter_subset _ _
  holds_closed v hv t b hb j hj := by
    obtain ⟨h1, h3⟩ := mem_T_bounds' hv
    rw [mem_spHolds] at hb ⊢
    simp only [usparse_block, spBlock_refs] at hj
    have := spRefs_bounds hj
    refine ⟨by omega, Or.inl ?_⟩
    rcases hb.2 with h | ⟨_, h⟩ <;> omega
  refs_held v hv n b hb hbc hbr := by
    obtain ⟨h1, h3⟩ := mem_T_bounds' hv
    intro j hj
    simp only [usparse_ids, Finset.mem_range] at hb
    simp only [usparse_block, spBlock_round] at hbr
    simp only [usparse_block, spBlock_refs] at hj
    have := spRefs_bounds hj
    rw [mem_spHolds]
    exact ⟨by omega, Or.inl (by omega)⟩
  holds_own v hv n _ b hb hbc hbr := by
    obtain ⟨h1, h3⟩ := mem_T_bounds' hv
    simp only [usparse_ids, Finset.mem_range] at hb
    simp only [usparse_block, spBlock_round] at hbr
    have hb4 : b % 4 = (v : ℕ) := congrArg (fun (x : Fin 4) => (x : ℕ)) hbc
    rw [mem_spHolds]
    exact ⟨hb, Or.inr ⟨hb4, by omega⟩⟩
  holds_mono v s t hst := by
    intro b hb
    rw [mem_spHolds] at hb ⊢
    exact ⟨hb.1, by omega⟩
  converges v _ w _ t _ := by
    intro b hb
    rw [mem_spHolds] at hb ⊢
    refine ⟨hb.1, Or.inl ?_⟩
    rcases hb.2 with h | h <;> omega
  advances _ _ _ hn _ _ := hn
  catchup v hv n hn b hb hbT hbr t _ hheld := by
    have hv4 := v.isLt
    simp only [usparse_ids, Finset.mem_range] at hb
    simp only [usparse_block, spBlock_round] at hbr
    rw [mem_spHolds] at hheld
    refine ⟨hn, ?_⟩
    change (v : ℕ) + 6 * n ≤ t + 5
    rcases hheld.2 with h | ⟨_, h⟩ <;> omega
  built_lt _ _ _ _ := by omega
  deadline _ _ _ _ := by omega
  leader_quorum k L hL h0 := by
    have hL' := eq_leaderId_of_isLeaderBlock (usparse_block N) hL
    subst hL'
    simp only [usparse_block, spBlock_round] at h0
    have hk : 0 < k := by unfold leaderId at h0; omega
    have hq : quorumCard (Fin 4) = 3 := rfl
    rw [hq]
    unfold creators
    simp only [usparse_block, spBlock_refs, spRefs_leader hk]
    rw [card_creators_Ico hk]
    omega
  refs_referenceable v hv n b hb hbc hbr j hj := by
    rw [correct_eq] at hv
    obtain ⟨h1, h3⟩ := mem_T_bounds' hv
    simp only [usparse_ids, Finset.mem_range] at hb
    simp only [usparse_block, spBlock_round] at hbr
    simp only [usparse_block, spBlock_refs] at hj
    have hjb := spRefs_bounds hj
    refine ⟨?_, fun Y hjY L hcl => ?_⟩
    · rw [mem_spHolds]
      exact ⟨by omega, Or.inl (by omega)⟩
    · exact backedIn_of_reaches_sp (by omega) hjY hcl (by omega)
  claim_held v hv n b hb hbc hbr L hcl := by
    rw [correct_eq] at hv
    obtain ⟨h1, h3⟩ := mem_T_bounds' hv
    simp only [usparse_ids, Finset.mem_range] at hb
    simp only [usparse_block, spBlock_round] at hbr
    exact backedIn_of_reaches_sp hb Reaches.refl hcl (by omega)
  vote_or_wait v hv k hN _ L hL c hc hcc hcr := by
    left
    have hL' := eq_leaderId_of_isLeaderBlock (usparse_block N) hL
    subst hL'
    have hcr' : c / 4 = k + 1 := hcr
    simp only [usparse_block, spBlock_refs]
    have := leaderId_mem_spRefs (r := k) (w := c % 4) (by omega)
    rwa [show 4 * (k + 1) + c % 4 = c by omega] at this
  claim_or_wait v hv k hN _ L hL c hc hcc hcr := by
    left
    have hL' := eq_leaderId_of_isLeaderBlock (usparse_block N) hL
    subst hL'
    have hcr' : c / 4 = k + 2 := hcr
    by_cases hlead : c % 4 = (c / 4) % 4
    · -- the leader block: its references carry the whole round below, all votes
      right
      unfold CarriesVotes
      have hq : quorumCard (Fin 4) = 3 := rfl
      rw [hq]
      have hc' : c = leaderId (k + 2) := by unfold leaderId; omega
      subst hc'
      have hcv : carriedVotes (Usparse N) (IsVote (Usparse N)) (leaderId (k + 2)) (leaderId k) =
          Finset.Ico (4 * (k + 2) - 4) (4 * (k + 2)) := by
        ext b
        rw [mem_carriedVotes]
        simp only [usparse_block, spBlock_refs, spRefs_leader (show 0 < k + 2 by omega),
          IsVote, Finset.mem_Ico]
        constructor
        · exact fun h => h.1
        · intro h
          refine ⟨h, ?_⟩
          have := leaderId_mem_spRefs (r := k) (w := b % 4) (by omega)
          rwa [show 4 * (k + 1) + b % 4 = b by omega] at this
      rw [hcv, show (Usparse N).block = spBlock from rfl, card_creators_Ico (by omega)]
      omega
    · left
      rw [spClaims_eq, if_pos ⟨by omega, hlead⟩]
      congr 2
      omega

/-! ## What the witness carries -/

/-- The discipline, and with it every safety law, holds of `Usparse N`. -/
theorem usparse_disciplined (N : ℕ) : Disciplined (Usparse N) := (spReactive N).disciplined

/-- The round-robin schedule places three consecutive `T`-led slots past
every slot: those led by `1`, `2`, `3`. -/
theorem sp_fairRun : FairRunOn (S := spSlots) ({1, 2, 3} : Finset (Fin 4)) 3 := by
  intro k
  exact ⟨4 * (k / 4 + 1) + 1, by omega, fun i hi => leader_mem_T (by omega)⟩

/-- The identity schedule spans at three, at wave two. -/
theorem sp_spans :
    (bluestreakAnchored (Fin 4) ℕ Unit).SpansEligible (S := spSlots) 3 :=
  (bluestreakAnchored (Fin 4) ℕ Unit).spansEligible_of_identity (fun _ => rfl) fun _ => le_rfl

/-- **Reactive liveness, instantiated**: every `T`-led slot within the
horizon is committed, on the full view and on every reliable
validator's own view. -/
theorem sp_decided (N k : ℕ) (hN : k + 2 ≤ N) (hk : k % 4 ≠ 0) :
    ∃ L, IsLeaderBlock (Usparse N) k L ∧
      Decided (Usparse N) (View.full (Usparse N)) k (some L) :=
  (spReactive N).decided (R := 0) (by decide) (by decide) le_rfl
    (fun _ _ => le_rfl) (Nat.zero_le _) hN (leader_mem_T hk)

theorem sp_decided_local (N k : ℕ) (hN : k + 2 ≤ N) (hk : k % 4 ≠ 0) :
    ∃ L, IsLeaderBlock (Usparse N) k L ∧ ∀ v ∈ ({1, 2, 3} : Finset (Fin 4)),
      Decided (Usparse N) ((spReactive N).viewAt v (3 + 6 * (k + 2) + 2)) k (some L) :=
  (spReactive N).decided_local (R := 0) (by decide) (by decide) le_rfl
    (fun _ _ => le_rfl) (Nat.zero_le _) hN (leader_mem_T hk)

/-- **The descent, instantiated**: the run at slots `1, 2, 3` decides slot
`0` — whose leader is the Byzantine `0` — on any horizon from `5`. -/
theorem sp_slot0 (N : ℕ) (hN : 5 ≤ N) :
    ∃ v, Decided (Usparse N) (View.full (Usparse N)) 0 v :=
  (spReactive N).decided_below_of_run (R := 0) (by decide) (by decide) le_rfl
    (fun _ _ => le_rfl) sp_spans (b := 1) (Nat.zero_le _) (by change 1 + 2 + 2 ≤ N; omega)
    (fun i hi => leader_mem_T (by omega)) 0 (by omega)

end LeanDagTest
