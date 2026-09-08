import LeanDag.Mysticeti.ViewPace
import LeanDagTest.Mysticeti.Growth
import Mathlib.Tactic.FinCases
/-!
# What the view-convergence route cannot do without

Three hypotheses of §6.9 are shown here to be load-bearing, each by a
model in which everything else holds and the conclusion fails: the bound
in `converges`, the starting round `R`, and the reliable set `T`. All
three run on one construction, `Uomit x`, which is `Ugrow` with validator
`x`'s blocks withheld from everyone else's references.

## The bound

`convergesWithin_iff_bounded` (`ViewPace.lean`) factors the network assumption into
a qualitative half — holdings converge at all — and a quantitative one —
from `gst` on the lag is at most `delay`. The development argues that the
second half cannot be dropped: a lag that merely exists cannot be ordered
against a build time, and that comparison is what `hbackoff` performs.

This file makes the argument a theorem, in the only form a necessity claim
can take: a model in which everything *except* the bound holds, and
coverage fails.

`Ugap` is `Ugrow` with one block per round withheld from the references —
validator `2`'s, from everyone but validator `2`. On the network side,
validator `2`'s blocks cross to the others only at `4N + 5`, after every
build in the run. So holdings do converge — they simply converge too late
to be referenced. Every protocol clause is satisfied, which the
`ViewPace` instance certifies field by field, and `ConvergesEventually`
holds from time `0`. Yet `SynchronisedOn (Uomit 2 N) Correct R` fails for
every `R` below the horizon.

The instance carries `gst = 4 * N + 5`, a time after every build in the
run, so `converges` is true of it but vacuously — which is the point.
`synchronisedOn_of_converges` demands `gst ≤ R`, and at such an `R`
coverage is vacuous for want of blocks above it. Nothing is contradicted;
what is shown is that the qualitative half alone carries none of the
weight.
-/

namespace LeanDagTest

open LeanDag

/-- The references of `Ugap`'s block `b`: the round below, less validator
`2`'s block — unless `b`'s own author is validator `2`, who must reference
its own previous block to satisfy the self-parent clause. -/
def omitRefs (x : Fin 4) (b : ℕ) : Finset ℕ :=
  if b % 4 = (x : ℕ) then Finset.Ico (4 * (b / 4) - 4) (4 * (b / 4))
  else (Finset.Ico (4 * (b / 4) - 4) (4 * (b / 4))).erase (4 * (b / 4) - 4 + (x : ℕ))

theorem mem_omitRefs {x : Fin 4} {b i : ℕ} :
    i ∈ omitRefs x b ↔
      (4 * (b / 4) - 4 ≤ i ∧ i < 4 * (b / 4)) ∧
        (b % 4 = (x : ℕ) ∨ i ≠ 4 * (b / 4) - 4 + (x : ℕ)) := by
  unfold omitRefs
  by_cases h : b % 4 = (x : ℕ)
  · simp only [h, if_true, Finset.mem_Ico, true_or, and_true, if_pos]
  · simp only [if_neg h, Finset.mem_erase, Finset.mem_Ico]
    constructor
    · rintro ⟨hne, hlo, hhi⟩; exact ⟨⟨hlo, hhi⟩, Or.inr hne⟩
    · rintro ⟨⟨hlo, hhi⟩, hor⟩
      exact ⟨hor.resolve_left h, hlo, hhi⟩

/-- The DAG of the round-robin scheme, with validator `x` excluded from
everyone else's references.

Only the two clauses the reference set controls are proved here; the rest
of validity is `rrUniverse`'s, since the block layout is the shared one. -/
def Uomit (x : Fin 4) (N : ℕ) : BlockUniverse (Fin 4) ℕ Unit :=
  rrUniverse N (omitRefs x)
    (fun b i hi => (mem_omitRefs.mp hi).1)
    (by
      -- the three validators other than `x` are always referenced
      intro i h
      have hsub : (Finset.univ.erase x) ⊆
          creators (rrBlock (omitRefs x)) (rrBlock (omitRefs x) i) := by
        intro y hy
        rw [Finset.mem_erase] at hy
        have hyx : (y : ℕ) ≠ (x : ℕ) := fun hc => hy.1 (Fin.ext hc)
        have hylt := y.isLt
        have hxlt := x.isLt
        simp only [creators, creatorsOf, rrBlock_refs, Finset.mem_image]
        refine ⟨4 * (i / 4) - 4 + (y : ℕ), ?_, ?_⟩
        · rw [mem_omitRefs]; omega
        · apply Fin.ext
          simp only [rrBlock_creator_val]
          omega
      have hcard : (Finset.univ.erase x).card = 3 := by
        rw [Finset.card_erase_of_mem (Finset.mem_univ x), Finset.card_univ]
        rfl
      have := Finset.card_le_card hsub
      omega)
    (by
      -- `x` is exempt from its own erasure, so every author keeps a parent
      intro i h
      have hxlt := x.isLt
      rw [mem_omitRefs]
      by_cases h2 : i % 4 = (x : ℕ)
      · exact ⟨by omega, Or.inl h2⟩
      · exact ⟨by omega, Or.inr (by omega)⟩)

@[simp] theorem uomit_ids (x : Fin 4) (N : ℕ) :
    (Uomit x N).ids = Finset.range (4 * (N + 1)) := rfl
@[simp] theorem uomit_block (x : Fin 4) (N : ℕ) :
    (Uomit x N).block = rrBlock (omitRefs x) := rfl

/-- **Coverage fails whenever the omitted validator is inside the set.**
`y`'s block of round `R+1` does not reference `x`'s block of round `R`.
This is the shared negative fact behind both witnesses below. -/
theorem uomit_not_synchronisedOn {N : ℕ} {x y : Fin 4} (hxy : y ≠ x)
    {T : Finset (Fin 4)} (hx : x ∈ T) (hy : y ∈ T) (R : ℕ) (hR : R < N) :
    ¬ SynchronisedOn (Uomit x N) T R := by
  intro hsync
  have hxlt := x.isLt
  have hylt := y.isLt
  have hyx : (y : ℕ) ≠ (x : ℕ) := fun hc => hxy (Fin.ext hc)
  have hbmem : (4 * (R + 1) + (y : ℕ)) ∈ (Uomit x N).ids := by
    simp only [uomit_ids, Finset.mem_range]; omega
  have hamem : (4 * R + (x : ℕ)) ∈ (Uomit x N).ids := by
    simp only [uomit_ids, Finset.mem_range]; omega
  have hbc : ((Uomit x N).block (4 * (R + 1) + (y : ℕ))).creator = y := by
    apply Fin.ext; simp only [uomit_block, rrBlock_creator_val]; omega
  have hac : ((Uomit x N).block (4 * R + (x : ℕ))).creator = x := by
    apply Fin.ext; simp only [uomit_block, rrBlock_creator_val]; omega
  have := hsync R (le_refl R) _ hbmem
    (by simp only [uomit_block, rrBlock_round]; omega)
    (by rw [hbc]; exact hy) _ hamem
    (by simp only [uomit_block, rrBlock_round]; omega)
    (by rw [hac]; exact hx)
  simp only [uomit_block, rrBlock_refs, mem_omitRefs] at this
  omega

/-- What `v` holds at time `t`. Validator `2`'s blocks reach nobody else
before `4 * N + 5` — after every build in the run, since the last is at
`3 + 4 * N` — while every other block arrives one tick after it is built,
and a validator's own blocks are in hand at once.

The one-tick delivery of the others is what makes the model *coherent*: a
validator that holds a block holds what that block was built on
(`holds_closed`), and a model in which nothing at all crossed before
`4 * N + 5` could not satisfy that, since every validator holds its own
blocks from the start and those reference the round below. Validator `2`
is starved of references throughout, which is the whole construction, and
`converges` still binds only from `4 * N + 5`. -/
def gapHolds (N : ℕ) (v : Fin 4) (t : ℕ) : Finset ℕ :=
  (Finset.range (4 * (N + 1))).filter fun b =>
    (b % 4 ≠ 2 ∧ b + 1 ≤ t) ∨ (b % 4 = (v : ℕ) ∧ b ≤ t) ∨ 4 * N + 5 ≤ t

/-- **And coverage fails anyway**, at every round the horizon leaves room
for: validator `1`'s block of round `R+1` does not reference validator
`2`'s block of round `R`, and both authors are correct. -/
theorem ugap_not_synchronisedOn {N : ℕ} (R : ℕ) (hR : R < N) :
    ¬ SynchronisedOn (Uomit 2 N) (Correct : Finset (Fin 4)) R :=
  uomit_not_synchronisedOn (x := 2) (y := 1) (by decide) (by decide) (by decide) R hR

/-! ## The reliable set is forced

Coverage is derived over a set `T`, never over all of `Correct` outright.
That relativisation is a property of the setting: with a proper subset
`T ⊊ Correct`, coverage over `T` is *derivable* while coverage over
`Correct` is *false*, and the second statement is about the DAG alone.

`Uomit 3` withholds validator `3`'s blocks from everyone's references.
Taking `T = {1, 2}` — two correct validators, with the correct validator
`3` outside — every clause holds at `gst = 0` with a real bound of `1`,
so unlike the model above the network assumption is satisfied properly
rather than vacuously. -/

theorem mem_T12_bounds {v : Fin 4} (hv : v ∈ ({1, 2} : Finset (Fin 4))) :
    1 ≤ (v : ℕ) ∧ (v : ℕ) ≤ 2 := by fin_cases hv <;> exact ⟨by decide, by decide⟩

/-- What `v` holds at `t`: its own blocks from their build times, every
non-`3` block one tick after its build — the bound `delay = 1`, met
properly — and validator `3`'s blocks never. The starvation is permanent,
so no bound is at issue for the starved author. -/
def starveHolds (N : ℕ) (v : Fin 4) (t : ℕ) : Finset ℕ :=
  (Finset.range (4 * (N + 1))).filter fun b =>
    (b % 4 ≠ 3 ∧ b + 1 ≤ t) ∨ (b % 4 = (v : ℕ) ∧ b ≤ t)

/-- **And coverage over `Correct` is false.** Validator `3` is correct and
outside `T`, and nobody references its blocks. -/
theorem ustarve_not_synchronisedOn {N : ℕ} (hN : 0 < N) :
    ¬ SynchronisedOn (Uomit 3 N) (Correct : Finset (Fin 4)) 0 :=
  uomit_not_synchronisedOn (x := 3) (y := 1) (by decide) (by decide) (by decide) 0 hN

/-! ## The same three witnesses, over the partial schedule

The route the development is converging on is `ViewPace`, so the
necessity claims must be stated over it — otherwise deleting the older
structures would delete the evidence while keeping the conclusions. The
models are the same; only the certifying instance changes, and `top := N`
throughout, since every validator of `Uomit` builds every round. -/

/-- Every clause of the partial-schedule structure, with `gst` beyond
every build in the run — deliberately, which is the point: `converges`
is true of it but vacuously. -/
def ugapPace (N : ℕ) : ViewPace (Uomit 2 N) (Correct : Finset (Fin 4)) N where
  top _ := N
  built v n := (v : ℕ) + 4 * n
  timeout _ := 4
  gst := 4 * N + 5
  delay := 1
  rounds_le b hb := by
    simp only [uomit_ids, Finset.mem_range] at hb
    simp only [uomit_block, rrBlock_round]
    omega
  built_of_le_top v hv n hn := rrUniverse_populatedOn _ _ _ _ _ _ hn v hv
  le_top_of_built _ _ b hb _ := by
    simp only [uomit_ids, Finset.mem_range] at hb
    simp only [uomit_block, rrBlock_round]
    omega
  waits _ _ _ _ := by omega
  timeout_pos _ := by omega
  latest n := 3 + 4 * n
  built_le_latest v _ _ _ := by have := v.isLt; omega
  proc := 0
  refs_held v _ n b hb hbc hbr := by
    have hv4 := v.isLt
    intro j hj
    simp only [uomit_ids, Finset.mem_range] at hb
    simp only [uomit_block, rrBlock_round] at hbr
    simp only [uomit_block, rrBlock_refs, mem_omitRefs] at hj
    have hbc' : b % 4 = (v : ℕ) := by
      have := congrArg (fun (x : Fin 4) => (x : ℕ)) hbc
      simpa using this
    simp only [gapHolds, Finset.mem_filter, Finset.mem_range]
    refine ⟨by omega, ?_⟩
    by_cases hj2 : j % 4 = 2
    · exact Or.inr (Or.inl ⟨by omega, by omega⟩)
    · exact Or.inl ⟨hj2, by omega⟩
  holds := gapHolds N
  holds_sub _ _ := by
    simp only [gapHolds, uomit_ids]; exact Finset.filter_subset _ _
  holds_closed v _ t b hb j hj := by
    have hv4 := v.isLt
    simp only [gapHolds, Finset.mem_filter, Finset.mem_range] at hb ⊢
    simp only [uomit_block, rrBlock_refs, mem_omitRefs] at hj
    refine ⟨by omega, ?_⟩
    rcases hb.2 with ⟨hb1, hb2⟩ | ⟨hb1, hb2⟩ | h
    · exact Or.inl ⟨by omega, by omega⟩
    · by_cases hj2 : j % 4 = 2
      · exact Or.inr (Or.inl ⟨by omega, by omega⟩)
      · exact Or.inl ⟨hj2, by omega⟩
    · exact Or.inr (Or.inr h)
  holds_own v _ n _ b hb hbc hbr := by
    have hv := v.isLt
    simp only [uomit_ids, Finset.mem_range] at hb
    simp only [uomit_block, rrBlock_round] at hbr
    have hbc' : b % 4 = (v : ℕ) := by
      have := congrArg (fun (x : Fin 4) => (x : ℕ)) hbc
      simpa using this
    simp only [gapHolds, Finset.mem_filter, Finset.mem_range]
    exact ⟨hb, Or.inr (Or.inl ⟨hbc', by omega⟩)⟩
  holds_mono v s t hst := by
    intro b hb
    simp only [gapHolds, Finset.mem_filter, Finset.mem_range] at hb ⊢
    refine ⟨hb.1, ?_⟩
    rcases hb.2 with ⟨h1, h2⟩ | ⟨h1, h2⟩ | h
    · exact Or.inl ⟨h1, by omega⟩
    · exact Or.inr (Or.inl ⟨h1, by omega⟩)
    · exact Or.inr (Or.inr (by omega))
  converges v _ w _ t ht := by
    intro b hb
    simp only [gapHolds, Finset.mem_filter, Finset.mem_range] at hb ⊢
    exact ⟨hb.1, Or.inr (Or.inr (by omega))⟩
  references v _ n hn c hc hcc hcr a ha har := by
    have hv := v.isLt
    simp only [uomit_ids, Finset.mem_range] at hc
    simp only [uomit_block, rrBlock_round] at hcr har
    have hcc' : c % 4 = (v : ℕ) := by
      have := congrArg (fun (x : Fin 4) => (x : ℕ)) hcc
      simpa using this
    simp only [gapHolds, Finset.mem_filter, Finset.mem_range] at ha
    simp only [uomit_block, rrBlock_refs, mem_omitRefs]
    -- validator 2's blocks reach nobody else in time; everything else of
    -- the round below is held, and referenced
    rcases ha.2 with ⟨h1, h2⟩ | ⟨h1, h2⟩ | h
    · exact ⟨by omega, Or.inr (by omega)⟩
    · by_cases hv2 : (v : ℕ) = 2
      · exact ⟨by omega, Or.inl (by omega)⟩
      · exact ⟨by omega, Or.inr (by omega)⟩
    · omega
  advances _ _ _ hn _ _ := hn
  catchup v hv n hn b hb hbT hbr t hgst hheld := by
    have hv4 := v.isLt
    simp only [uomit_ids, Finset.mem_range] at hb
    simp only [uomit_block, rrBlock_round] at hbr
    refine ⟨hn, ?_⟩
    change 4 * N + 5 ≤ t at hgst
    change (v : ℕ) + 4 * n ≤ t + 0
    omega

/-- **V10 over the partial schedule.** Holdings converge from time `0`,
every clause of `ViewPace` holds, and coverage fails at every round below
the horizon: the bound in `converges` is what carries coverage, on this
route as on the others. -/
theorem ugapPace_convergesEventually (N : ℕ) :
    ConvergesEventually (ugapPace N).holds (Correct : Finset (Fin 4)) := by
  intro v _ w _ t
  refine ⟨4 * N + 5, ?_⟩
  intro b hb
  simp only [ugapPace, gapHolds, Finset.mem_filter, Finset.mem_range] at hb ⊢
  exact ⟨hb.1, Or.inr (Or.inr (by omega))⟩

theorem bound_is_necessary_pace {N : ℕ} (hN : 0 < N) :
    ConvergesEventually (ugapPace N).holds (Correct : Finset (Fin 4)) ∧
      ¬ SynchronisedOn (Uomit 2 N) (Correct : Finset (Fin 4)) 0 :=
  ⟨ugapPace_convergesEventually N, ugap_not_synchronisedOn 0 hN⟩

/-- **V11 over the partial schedule** — the form the claim takes once the
untimed bridge is gone: `gst ≤ R` cannot be dropped from the coverage
theorems, engine or headline. The instance satisfies the engine's drift
and backoff hypotheses at `R = 0` outright — spread `3`, `3 + 1 ≤ 4` —
and the headline's quorum bound too; coverage at `0` is false, and only
`gst ≤ 0` fails, so it is the working hypothesis. -/
theorem gst_is_forced_pace {N : ℕ} (hN : 0 < N) :
    DriftOn (ugapPace N).built (Correct : Finset (Fin 4)) 0 3 N ∧
      (∀ n, 0 ≤ n → 3 + (ugapPace N).delay ≤ (ugapPace N).timeout n) ∧
      ¬ SynchronisedOn (Uomit 2 N) (Correct : Finset (Fin 4)) 0 :=
  ⟨fun v _ w _ n _ _ => by
      have hv := v.isLt; have hw := w.isLt
      change (w : ℕ) + 4 * n ≤ ((v : ℕ) + 4 * n) + 3
      omega,
   fun n _ => by change 3 + 1 ≤ 4; omega,
   ugap_not_synchronisedOn 0 hN⟩

/-- Over the two-member reliable set, with the network assumption met
properly: `gst = 0`, bound `1` — unlike `ugapPace`, nothing vacuous. -/
def ustarvePace (N : ℕ) : ViewPace (Uomit 3 N) ({1, 2} : Finset (Fin 4)) N where
  top _ := N
  built v n := (v : ℕ) + 4 * n
  timeout _ := 4
  gst := 0
  delay := 1
  rounds_le b hb := by
    simp only [uomit_ids, Finset.mem_range] at hb
    simp only [uomit_block, rrBlock_round]
    omega
  built_of_le_top v hv n hn := rrUniverse_populatedOn _ _ _ _ _ _ hn v hv
  le_top_of_built _ _ b hb _ := by
    simp only [uomit_ids, Finset.mem_range] at hb
    simp only [uomit_block, rrBlock_round]
    omega
  waits _ _ _ _ := by omega
  timeout_pos _ := by omega
  latest n := 2 + 4 * n
  built_le_latest v hv _ _ := by obtain ⟨_, _⟩ := mem_T12_bounds hv; omega
  proc := 0
  refs_held v hv n b hb hbc hbr := by
    obtain ⟨h1, h2⟩ := mem_T12_bounds hv
    intro j hj
    simp only [uomit_ids, Finset.mem_range] at hb
    simp only [uomit_block, rrBlock_round] at hbr
    simp only [uomit_block, rrBlock_refs, mem_omitRefs] at hj
    have hbc' : b % 4 = (v : ℕ) := by
      have := congrArg (fun (x : Fin 4) => (x : ℕ)) hbc
      simpa using this
    simp only [starveHolds, Finset.mem_filter, Finset.mem_range]
    exact ⟨by omega, Or.inl ⟨by omega, by omega⟩⟩
  holds := starveHolds N
  holds_sub _ _ := by
    simp only [starveHolds, uomit_ids]; exact Finset.filter_subset _ _
  holds_closed v hv t b hb j hj := by
    obtain ⟨h1, h2⟩ := mem_T12_bounds hv
    simp only [starveHolds, Finset.mem_filter, Finset.mem_range] at hb ⊢
    simp only [uomit_block, rrBlock_refs, mem_omitRefs] at hj
    refine ⟨by omega, Or.inl ⟨by omega, ?_⟩⟩
    rcases hb.2 with ⟨_, h⟩ | ⟨_, h⟩ <;> omega
  holds_own v hv n _ b hb hbc hbr := by
    obtain ⟨h1, h2⟩ := mem_T12_bounds hv
    simp only [uomit_ids, Finset.mem_range] at hb
    simp only [uomit_block, rrBlock_round] at hbr
    have hb4 : b % 4 = (v : ℕ) := by
      have := congrArg (fun (x : Fin 4) => (x : ℕ)) hbc
      simpa [uomit_block] using this
    simp only [starveHolds, Finset.mem_filter, Finset.mem_range]
    exact ⟨hb, Or.inr ⟨hb4, by omega⟩⟩
  holds_mono v s t hst := by
    intro b hb
    simp only [starveHolds, Finset.mem_filter, Finset.mem_range] at hb ⊢
    rcases hb.2 with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact ⟨hb.1, Or.inl ⟨h1, by omega⟩⟩
    · exact ⟨hb.1, Or.inr ⟨h1, by omega⟩⟩
  converges v hv w hw t _ := by
    obtain ⟨_, _⟩ := mem_T12_bounds hv
    obtain ⟨_, _⟩ := mem_T12_bounds hw
    intro b hb
    simp only [starveHolds, Finset.mem_filter, Finset.mem_range] at hb ⊢
    refine ⟨hb.1, Or.inl ?_⟩
    rcases hb.2 with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact ⟨h1, by omega⟩
    · exact ⟨by omega, by omega⟩
  references v hv n hn c hc hcc hcr a ha har := by
    obtain ⟨h1, h2⟩ := mem_T12_bounds hv
    simp only [uomit_ids, Finset.mem_range] at hc
    simp only [uomit_block, rrBlock_round] at hcr har
    simp only [starveHolds, Finset.mem_filter, Finset.mem_range] at ha
    simp only [uomit_block, rrBlock_refs, mem_omitRefs]
    refine ⟨by omega, Or.inr ?_⟩
    rcases ha.2 with ⟨ha1, ha2⟩ | ⟨ha1, ha2⟩
    · omega
    · omega
  advances _ _ _ hn _ _ := hn
  catchup v hv n hn b hb hbT hbr t _ hheld := by
    obtain ⟨hv1, hv2⟩ := mem_T12_bounds hv
    simp only [uomit_ids, Finset.mem_range] at hb
    simp only [uomit_block, rrBlock_round] at hbr
    have hb4 : 1 ≤ b % 4 ∧ b % 4 ≤ 2 := by
      obtain ⟨hbT1, hbT2⟩ := mem_T12_bounds hbT
      have : (((Uomit 3 N).block b).creator : ℕ) = b % 4 := by
        simp [uomit_block]
      omega
    simp only [starveHolds, Finset.mem_filter, Finset.mem_range] at hheld
    refine ⟨hn, ?_⟩
    rcases hheld.2 with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> omega

/-- Coverage over `T = {1, 2}` is **derived** — through the coverage
engine, which asks neither `T ⊆ Correct` nor a quorum. The drift-free
headline is out of reach here by design: two validators are no quorum,
so the collapse cannot feed it, and the drift bound is supplied
explicitly — which is exactly why the engine stays public. -/
theorem ustarvePace_synchronisedOn (N : ℕ) :
    SynchronisedOn (Uomit 3 N) ({1, 2} : Finset (Fin 4)) 0 :=
  (ustarvePace N).synchronisedOn_of_driftOn (D := 1)
    (fun v hv w hw n _ _ => by
      obtain ⟨_, _⟩ := mem_T12_bounds hv
      obtain ⟨_, _⟩ := mem_T12_bounds hw
      change (w : ℕ) + 4 * n ≤ ((v : ℕ) + 4 * n) + 1
      omega)
    (le_refl 0) (fun n _ => by change 1 + 1 ≤ 4; omega)

/-- **V12 over the partial schedule.** The reliable set cannot be
widened: with `T ⊊ Correct`, the `ViewPace` route yields coverage over
`T` and coverage over `Correct` is false — a statement about the DAG,
independent of any structure. -/
theorem reliable_set_is_forced_pace {N : ℕ} (hN : 0 < N) :
    ({1, 2} : Finset (Fin 4)) ⊂ (Correct : Finset (Fin 4)) ∧
      SynchronisedOn (Uomit 3 N) ({1, 2} : Finset (Fin 4)) 0 ∧
      ¬ SynchronisedOn (Uomit 3 N) (Correct : Finset (Fin 4)) 0 :=
  ⟨by decide, ustarvePace_synchronisedOn N, ustarve_not_synchronisedOn hN⟩

#print axioms ugap_not_synchronisedOn
#print axioms bound_is_necessary_pace
#print axioms gst_is_forced_pace
#print axioms ustarvePace_synchronisedOn
#print axioms reliable_set_is_forced_pace

#print axioms ugap_not_synchronisedOn

end LeanDagTest
