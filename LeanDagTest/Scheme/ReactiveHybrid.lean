import LeanDag.Scheme.Reactive.Proof
import LeanDag.Scheme.Model.LeastSel
import LeanDag.Scheme.Helpers.Hydrozoan
import LeanDag.Hydrozoan.Helpers.Carrier
/-!
# The family, run reactively, at a hybrid committee

Three replicas, none Byzantine and replica `0` crashed: `n = 3f + 2c + 1`
at `f = 0, c = 1`, which Hydrozoan's fault model admits and the core's
excludes (`3 · 1 + 1 > 3`). Replicas `1` and `2` build every round, each
block referencing both blocks of the round below, so the quorum is
`q = n − f − c = 2`. They build at spacing `6`, inside a timeout of
`9 = 2Δ + proc`, so no replica waits a timeout, and the pacemaker advances
on `q = 2` round authors. At the Hybrid Mysticeti row, whose thresholds
are all `2`, the execution meets the family's reactive precondition at
Hydrozoan's reliability, and a reliably-led slot commits by the generic
`LeaderCommits`.
-/

namespace LeanDagTest

namespace Scheme

open LeanDag LeanDag.Scheme

instance threeReplicas : LeanDag.Hydrozoan.Faults (Fin 3) where
  f := 0
  c := 1
  k := 0
  byzantine := ∅
  crashed := {0}
  byzantine_disjoint_crashed := by decide
  card_replicas := by decide
  card_byzantine := by decide
  card_crashed := by decide

/-- Block `b`: round `b / 2`, by replica `b % 2 + 1`, referencing both
blocks of the round below. -/
def hyBlock (b : ℕ) : Block (Fin 3) ℕ Unit where
  round := b / 2
  creator := ⟨b % 2 + 1, by omega⟩
  refs := (Finset.range (2 * (b / 2))).filter fun j => j / 2 + 1 = b / 2
  payload := ()

theorem mem_hyBlock_refs {b j : ℕ} :
    j ∈ (hyBlock b).refs ↔ j / 2 + 1 = b / 2 := by
  simp only [hyBlock, Finset.mem_filter, Finset.mem_range]
  omega

theorem hyBlock_creator_val (b : ℕ) : ((hyBlock b).creator : ℕ) = b % 2 + 1 := rfl

/-- A block above round `0` references blocks of both live replicas. -/
theorem le_card_hyCreators {b : ℕ} (hb : 0 < b / 2) :
    2 ≤ (creators hyBlock (hyBlock b)).card := by
  have hsub : ({1, 2} : Finset (Fin 3)) ⊆ creators hyBlock (hyBlock b) := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    refine mem_creatorsOf.mpr ?_
    rcases hx with rfl | rfl
    · exact ⟨2 * (b / 2 - 1), mem_hyBlock_refs.mpr (by omega), Fin.ext (by
        simp only [hyBlock_creator_val]; omega)⟩
    · exact ⟨2 * (b / 2 - 1) + 1, mem_hyBlock_refs.mpr (by omega), Fin.ext (by
        simp only [hyBlock_creator_val]; omega)⟩
  exact le_trans (by decide) (Finset.card_le_card hsub)

/-- The record: rounds `0` to `N`, two blocks a round. -/
def Uhy (N : ℕ) : BlockRecord (Fin 3) ℕ Unit HybridValid Hydrozoan.NonByzantine where
  ids := Finset.range (2 * (N + 1))
  block := hyBlock
  complete i hi j hj := by
    simp only [Finset.mem_range] at hi ⊢
    have := mem_hyBlock_refs.mp hj
    omega
  valid i _ := by
    refine ⟨fun j hj => ?_, fun hr => ?_, ⟨fun j hj l hl hjl => ?_, fun hr => ?_⟩⟩
    · have := mem_hyBlock_refs.mp hj
      show j / 2 + 1 = i / 2
      omega
    · show Fintype.card (Fin 3) - 0 - 1 ≤ _
      exact le_trans (by decide) (le_card_hyCreators hr)
    · have h1 := mem_hyBlock_refs.mp hj
      have h2 := mem_hyBlock_refs.mp hl
      have h3 := congrArg Fin.val hjl
      simp only [hyBlock_creator_val] at h3
      omega
    · have hr' : 0 < i / 2 := hr
      exact ⟨2 * (i / 2 - 1) + i % 2, mem_hyBlock_refs.mpr (by omega), Fin.ext (by
        simp only [hyBlock_creator_val]; omega)⟩
  no_equivocation i _ j _ _ hc hr := by
    have h3 := congrArg Fin.val hc
    simp only [hyBlock_creator_val] at h3
    have : i / 2 = j / 2 := hr
    omega

@[simp] theorem uhy_ids (N : ℕ) : (Uhy N).ids = Finset.range (2 * (N + 1)) := rfl
@[simp] theorem uhy_block (N : ℕ) : (Uhy N).block = hyBlock := rfl

/-- Slots every three rounds, alternating between the live replicas. -/
@[reducible] def hySlots : Slots (Fin 3) :=
  Slots.uniformSingle 3 (by omega) (fun k => ⟨k % 2 + 1, by omega⟩)

attribute [local instance 2000] hySlots

/-- The live replicas. -/
abbrev Thy : Finset (Fin 3) := {1, 2}

theorem mem_Thy {v : Fin 3} (hv : v ∈ Thy) : 1 ≤ (v : ℕ) ∧ (v : ℕ) ≤ 2 := by
  simp only [Thy, Finset.mem_insert, Finset.mem_singleton] at hv
  rcases hv with rfl | rfl <;> decide

/-- What replica `v` holds at `t`: block `b` (built at `b % 2 + 1 + 6 (b / 2)`)
once `Δ = 2` has passed, and its own from the moment it builds. -/
def hyHolds (N : ℕ) (v : Fin 3) (t : ℕ) : Finset ℕ :=
  (Finset.range (2 * (N + 1))).filter fun b =>
    b % 2 + 1 + 6 * (b / 2) + 2 ≤ t ∨ (b % 2 + 1 = (v : ℕ) ∧ b % 2 + 1 + 6 * (b / 2) ≤ t)

/-- The Hybrid Mysticeti row at three replicas, `f = 0`, `c = 1`. -/
abbrev hyP : Params := Params.hybridMysticeti (Fintype.card (Fin 3)) 0 1

/-- The least vote. -/
abbrev σH : VoteSel (Fin 3) ℕ Unit HybridValid Hydrozoan.NonByzantine := leastSel

/-- The row's thresholds are `q = 2`, and the core's fault class excludes
the committee at `f + c`. -/
example : hyP.commitThreshold = 2 ∧ hyP.certThreshold = 2 ∧ hyP.skipThreshold = 2 ∧
    Hydrozoan.q (Fin 3) = 2 ∧ ¬ (3 * (0 + 1) + 1 ≤ Fintype.card (Fin 3)) := by
  decide

/-- **The family run reactively, at `q = 2`.** -/
def hyReactive (N : ℕ) :
    SchemeReactive (S := hySlots) 2 hyP σH (Uhy N) Thy N :=
  letI : Faults (Fin 3) := noFaults
  { top := fun _ => N
    built := fun v n => (v : ℕ) + 6 * n
    timeout := fun _ => 9
    proc := 5
    gst := 0
    delay := 2
    rounds_le := fun b hb => by
      simp only [uhy_ids, Finset.mem_range] at hb
      show b / 2 ≤ N
      omega
    built_of_le_top := fun v hv n hn => by
      obtain ⟨h1, h2⟩ := mem_Thy hv
      refine ⟨2 * n + ((v : ℕ) - 1), by simp only [uhy_ids, Finset.mem_range]; omega,
        Fin.ext ?_, ?_⟩
      · simp only [uhy_block, hyBlock_creator_val]; omega
      · show (2 * n + ((v : ℕ) - 1)) / 2 = n
        omega
    le_top_of_built := fun _ _ b hb _ => by
      simp only [uhy_ids, Finset.mem_range] at hb
      show b / 2 ≤ N
      omega
    timeout_pos := fun _ => by omega
    latest := fun n => 2 + 6 * n
    built_le_latest := fun v hv _ _ => by obtain ⟨_, _⟩ := mem_Thy hv; omega
    built_lt := fun _ _ _ _ => by omega
    deadline := fun _ _ _ _ => by omega
    holds := hyHolds N
    holds_sub := fun _ _ => by
      simp only [hyHolds, uhy_ids]; exact Finset.filter_subset _ _
    refs_held := fun v hv n b hb hbc hbr => by
      obtain ⟨_, _⟩ := mem_Thy hv
      intro j hj
      simp only [uhy_ids, Finset.mem_range] at hb
      have hbr' : b / 2 = n + 1 := hbr
      have hjr := mem_hyBlock_refs.mp hj
      simp only [hyHolds, Finset.mem_filter, Finset.mem_range]
      exact ⟨by omega, Or.inl (by omega)⟩
    holds_closed := fun v hv t b hb j hj => by
      simp only [hyHolds, Finset.mem_filter, Finset.mem_range] at hb ⊢
      have hjr := mem_hyBlock_refs.mp hj
      refine ⟨by omega, Or.inl ?_⟩
      rcases hb.2 with h | ⟨_, h⟩ <;> omega
    holds_own := fun v hv n _ b hb hbc hbr => by
      obtain ⟨_, _⟩ := mem_Thy hv
      simp only [uhy_ids, Finset.mem_range] at hb
      have hbr' : b / 2 = n := hbr
      have hb2 : b % 2 + 1 = (v : ℕ) := by
        have := congrArg Fin.val hbc
        simpa [uhy_block, hyBlock_creator_val] using this
      simp only [hyHolds, Finset.mem_filter, Finset.mem_range]
      exact ⟨hb, Or.inr ⟨hb2, by omega⟩⟩
    holds_mono := fun v s t hst => by
      intro b hb
      simp only [hyHolds, Finset.mem_filter, Finset.mem_range] at hb ⊢
      exact ⟨hb.1, by omega⟩
    converges := fun v _ w _ t _ => by
      intro b hb
      simp only [hyHolds, Finset.mem_filter, Finset.mem_range] at hb ⊢
      refine ⟨hb.1, Or.inl ?_⟩
      rcases hb.2 with h | h <;> omega
    advances := fun _ _ _ hn _ _ => hn
    catchup := fun v hv n hn b hb hbT hbr t _ hheld => by
      obtain ⟨_, _⟩ := mem_Thy hv
      simp only [uhy_ids, Finset.mem_range] at hb
      have hbr' : b / 2 = n := hbr
      simp only [hyHolds, Finset.mem_filter, Finset.mem_range] at hheld
      refine ⟨hn, ?_⟩
      show (v : ℕ) + 6 * n ≤ t + 5
      rcases hheld.2 with h | ⟨_, h⟩ <;> omega
    advancesAt := fun _ _ _ hn _ _ => hn
    reach_or_wait := fun v hv k _ _ L hL m hm c hc hcc hcr => by
      -- the reactive exit: every block references the whole round below
      left
      have hvo : hyP.voteOffset = 1 := by decide
      obtain ⟨hmem, hround, -⟩ := hL
      simp only [uhy_ids, Finset.mem_range] at hmem hc
      have hround' : L / 2 = hySlots.slotRound k := hround
      have hcr' : c / 2 = hySlots.slotRound k + m + 1 := hcr
      exact Reaches.single (by
        show L ∈ (hyBlock c).refs
        exact mem_hyBlock_refs.mpr (by omega))
    cert_or_wait := fun _ v hv k hN hlead L hL c hc hcc hcr => by
      -- the reactive exit: both round-`(r + 1)` blocks vote and are referenced
      left
      have hvo : hyP.voteOffset = 1 := by decide
      rw [hvo] at hcr hN
      obtain ⟨hmem, hround, hLc⟩ := hL
      have hmem' := hmem
      simp only [uhy_ids, Finset.mem_range] at hmem hc
      have hround' : L / 2 = hySlots.slotRound k := hround
      have hcr' : c / 2 = hySlots.slotRound k + 1 + 1 := hcr
      unfold IsCert
      rw [if_neg (by decide)]
      show 2 ≤ (creatorsOf hyBlock (carriedVotes (Uhy N) (σH.Votes (Uhy N)) c L)).card
      have hsub : ({1, 2} : Finset (Fin 3)) ⊆
          creatorsOf hyBlock (carriedVotes (Uhy N) (σH.Votes (Uhy N)) c L) := by
        intro x hx
        have hx' : (x : ℕ) = 1 ∨ (x : ℕ) = 2 := by
          simp only [Finset.mem_insert, Finset.mem_singleton] at hx
          rcases hx with rfl | rfl <;> simp
        refine mem_creatorsOf.mpr ⟨2 * (hySlots.slotRound k + 1) + ((x : ℕ) - 1), ?_,
          Fin.ext (by simp only [hyBlock_creator_val]; omega)⟩
        refine Finset.mem_filter.mpr ⟨mem_hyBlock_refs.mpr (by omega), ?_⟩
        refine votes_of_reaches_record (Uhy N).noEquivOn_honest
          (by simp only [uhy_ids, Finset.mem_range]; omega) hmem'
          (by
            show _ ∈ (∅ : Finset (Fin 3))ᶜ
            simp)
          (by show L / 2 < (2 * (hySlots.slotRound k + 1) + ((x : ℕ) - 1)) / 2; omega)
          (Reaches.single ?_)
        show L ∈ (hyBlock _).refs
        exact mem_hyBlock_refs.mpr (by omega)
      exact le_trans (by decide) (Finset.card_le_card hsub) }

/-- `Uhy` as a universe of the row's carrier. -/
abbrev uhyU (N : ℕ) : (schemeRule hyP σH Hydrozoan.NonByzantine).Universe :=
  ⟨Uhy N, (Uhy N).noEquivOn_honest⟩

/-- The full view of `Uhy`, as a view of the carrier. -/
abbrev uhyV (N : ℕ) : (schemeRule hyP σH Hydrozoan.NonByzantine).View (uhyU N) :=
  BlockRecord.View.full (Uhy N)

/-- **The family's reactive precondition holds**, at Hydrozoan's
reliability. -/
theorem hyReactive_live (N k : ℕ) (hN : hySlots.slotRound k + 2 ≤ N) :
    reactiveLive hyP σH Hydrozoan.NonByzantine (Hydrozoan.hzReliability (Fin 3)) hySlots
      (uhyV N) Thy k (k + 1) := by
  refine ⟨⟨by decide, by decide⟩, by decide, N, 0, hyReactive N, Nat.le_refl 0,
    (fun n _ => by change 2 * 2 + 5 ≤ 9; omega), Nat.zero_le _,
    BlockRecord.View.coversUpto_full (Uhy N) N, ?_⟩
  intro j hj
  have := hySlots.mono (Nat.lt_succ_iff.mp hj)
  have hw : hyP.waveLength - 1 = 2 := rfl
  omega

/-- **And a reliably-led slot commits**, by the generic `LeaderCommits`. -/
theorem hyReactive_commits (N k : ℕ) (hN : hySlots.slotRound k + 2 ≤ N) :
    ∃ L, Properties.DecidedBelow (schemeRule hyP σH Hydrozoan.NonByzantine) hySlots (k + 1)
      (uhyV N) k (some L) :=
  ReactiveRun.commits (Fin 3) ℕ Unit HybridValid Hydrozoan.NonByzantine hyP σH
    Hydrozoan.NonByzantine (Hydrozoan.hzReliability (Fin 3)) (by decide)
    (fun _ => ⟨by decide, by decide⟩) (by decide) hySlots (uhyV N) Thy k (k + 1)
    (hyReactive_live N k hN) k (Nat.le_refl k) (Nat.lt_succ_self k)
    (by
      have h : ((hySlots.leader k : Fin 3) : ℕ) = k % 2 + 1 := rfl
      rcases Nat.mod_two_eq_zero_or_one k with h2 | h2
      · have : hySlots.leader k = 1 := Fin.ext (by rw [h, h2]; rfl)
        rw [this]; decide
      · have : hySlots.leader k = 2 := Fin.ext (by rw [h, h2]; rfl)
        rw [this]; decide)

end Scheme

end LeanDagTest

#print axioms LeanDagTest.Scheme.hyReactive_commits
