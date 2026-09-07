import LeanDag.Reactive.Mysticeti
import LeanDag.Reactive.Odontoceti
import LeanDag.Reactive.MysticetiProperties
import LeanDagTest.Mysticeti.Quantitative
/-!
# The reactive schedule, witnessed

A `ReactiveM` instance on `Ugrow`, at constants chosen to exhibit the
point of the reactive rule: every build happens at spacing `6`, strictly
inside the timeout `9`, so **no validator ever waits out a timeout** —
the fallback branches of `vote_or_wait` and `cert_or_wait` are never
taken, and both are discharged by their reactive exits. The timeout is
`9 = 2Δ + proc` exactly: the drift-free backoff hypothesis of the
liveness theorems is met with equality.

`Ugrow`'s blocks reference the whole round below, so every block votes
for every leader block and every round-`(n+2)` block certifies; the
reactive exits are therefore available at every slot, which is what the
model is for. The fast-path constants are honest rather than generous:
processing `5` is the least value `prompt_vote` admits here — a
validator's shortcut to its *own* block lets the trigger fire a tick
before the slowest peer's block would force it — so `D + δ + proc = 10`
exceeds the timeout `9`, the sufficient condition of
`no_timeout_of_fast` is deliberately unmet, and its conclusion is
discharged directly by the run (`ugrowReactive_early`).
`ugrowReactive_fast` exhibits the latency theorem itself.

Since the unification the structure extends `PaceCore`, so the witness
asserts no blocks: production is derived, and the `top` clauses are the
layout facts every pace witness carries.
-/

namespace LeanDagTest

open LeanDag

-- `Growth` installs the constant-leader `fairSlots` globally; this file
-- works on the rotating schedule, so it wins synthesis here.
attribute [local instance 2000] rrSlots

/-- What `v` holds at time `t` on the `6`-spaced schedule: block `b`
(built at `b % 4 + 6 * (b / 4)`) has arrived once `delay = 2` has passed,
and a validator holds its own block from the moment it builds. -/
def reactHolds (N : ℕ) (v : Fin 4) (t : ℕ) : Finset ℕ :=
  (Finset.range (4 * (N + 1))).filter fun b =>
    b % 4 + 6 * (b / 4) + 2 ≤ t ∨ (b % 4 = (v : ℕ) ∧ b % 4 + 6 * (b / 4) ≤ t)

/-- The reactive witness: `Ugrow` on the round-robin schedule, builds at
spacing `6` inside a timeout of `9 = 2Δ + proc`. -/
def ugrowReactive (N : ℕ) : ReactiveM (Ugrow N) {1, 2, 3} N where
  top _ := N
  built v n := (v : ℕ) + 6 * n
  timeout _ := 9
  proc := 5
  gst := 0
  delay := 2
  rounds_le b hb := by
    simp only [ugrow_ids, Finset.mem_range] at hb
    simp only [ugrow_block, rrBlock_round]; omega
  built_of_le_top v hv n hn := rrUniverse_populatedOn _ _ _ _ _ _ hn v hv
  le_top_of_built _ _ b hb _ := by
    simp only [ugrow_ids, Finset.mem_range] at hb
    simp only [ugrow_block, rrBlock_round]; omega
  timeout_pos _ := by omega
  latest n := 3 + 6 * n
  built_le_latest v _ _ _ := by have := v.isLt; omega
  built_lt _ _ _ _ := by omega
  deadline _ _ _ _ := by omega
  refs_held v hv n b hb hbc hbr := by
    obtain ⟨h1, h3⟩ := mem_T_bounds hv
    intro j hj
    simp only [ugrow_ids, Finset.mem_range] at hb
    simp only [ugrow_block, rrBlock_round] at hbr
    simp only [ugrow_block, mem_growBlock_refs] at hj
    simp only [reactHolds, Finset.mem_filter, Finset.mem_range]
    exact ⟨by omega, Or.inl (by omega)⟩
  holds := reactHolds N
  holds_sub _ _ := by
    simp only [reactHolds, ugrow_ids]; exact Finset.filter_subset _ _
  holds_closed v hv t b hb j hj := by
    obtain ⟨h1, h3⟩ := mem_T_bounds hv
    simp only [reactHolds, Finset.mem_filter, Finset.mem_range] at hb ⊢
    simp only [ugrow_block, mem_growBlock_refs] at hj
    have hjd : j / 4 + 1 = b / 4 := by omega
    refine ⟨by omega, Or.inl ?_⟩
    rcases hb.2 with h | ⟨_, h⟩ <;> omega
  holds_own v hv n _ b hb hbc hbr := by
    obtain ⟨h1, h3⟩ := mem_T_bounds hv
    have hv4 := v.isLt
    simp only [ugrow_ids, Finset.mem_range] at hb
    simp only [ugrow_block, rrBlock_round] at hbr
    have hb4 : b % 4 = (v : ℕ) := by
      have := congrArg (fun (x : Fin 4) => (x : ℕ)) hbc
      simpa [ugrow_block] using this
    simp only [reactHolds, Finset.mem_filter, Finset.mem_range]
    exact ⟨hb, Or.inr ⟨hb4, by omega⟩⟩
  holds_mono v s t hst := by
    intro b hb
    simp only [reactHolds, Finset.mem_filter, Finset.mem_range] at hb ⊢
    exact ⟨hb.1, by omega⟩
  converges v _ w _ t _ := by
    intro b hb
    simp only [reactHolds, Finset.mem_filter, Finset.mem_range] at hb ⊢
    refine ⟨hb.1, Or.inl ?_⟩
    rcases hb.2 with h | h
    · omega
    · omega
  advances _ _ _ hn _ _ := hn
  catchup v hv n hn b hb hbT hbr t _ hheld := by
    have hv4 := v.isLt
    simp only [ugrow_ids, Finset.mem_range] at hb
    simp only [ugrow_block, rrBlock_round] at hbr
    simp only [reactHolds, Finset.mem_filter, Finset.mem_range] at hheld
    refine ⟨hn, ?_⟩
    change (v : ℕ) + 6 * n ≤ t + 5
    rcases hheld.2 with h | ⟨_, h⟩ <;> omega
  vote_or_wait v hv k hN _ L hL c hc hcc hcr := by
    -- the reactive exit is always available: every block references the
    -- whole round below, the leader block among it
    left
    obtain ⟨h1, h3⟩ := mem_T_bounds hv
    obtain ⟨hmem, hround, -⟩ := hL
    simp only [ugrow_ids, Finset.mem_range] at hmem hc
    simp only [ugrow_block, rrBlock_round] at hround hcr
    simp only [ugrow_block, mem_growBlock_refs]
    omega
  prompt_vote v hv k hN hlead L hL t hbuilt hheld hall := by
    obtain ⟨h1, h3⟩ := mem_T_bounds hv
    have hv4 := v.isLt
    -- the trigger includes every reliable round-`r` block; blocks `2`
    -- and `3` of the round bound `t` from below far enough for `proc = 5`
    have h2 := hall (4 * rrSlots.slotRound k + 2)
      (by simp only [ugrow_ids, Finset.mem_range]; omega)
      (by
        have : ((Ugrow N).block (4 * rrSlots.slotRound k + 2)).creator = (2 : Fin 4) := by
          apply Fin.ext
          simp only [ugrow_block, rrBlock_creator_val]
          omega
        rw [this]; decide)
      (by simp only [ugrow_block, rrBlock_round]; omega)
    have h3' := hall (4 * rrSlots.slotRound k + 3)
      (by simp only [ugrow_ids, Finset.mem_range]; omega)
      (by
        have : ((Ugrow N).block (4 * rrSlots.slotRound k + 3)).creator = (3 : Fin 4) := by
          apply Fin.ext
          simp only [ugrow_block, rrBlock_creator_val]
          omega
        rw [this]; decide)
      (by simp only [ugrow_block, rrBlock_round]; omega)
    simp only [reactHolds, Finset.mem_filter, Finset.mem_range] at h2 h3'
    have e2 : (4 * rrSlots.slotRound k + 2) % 4 = 2 := by omega
    have d2 : (4 * rrSlots.slotRound k + 2) / 4 = rrSlots.slotRound k := by omega
    have e3 : (4 * rrSlots.slotRound k + 3) % 4 = 3 := by omega
    have d3 : (4 * rrSlots.slotRound k + 3) / 4 = rrSlots.slotRound k := by omega
    rw [e2, d2] at h2
    rw [e3, d3] at h3'
    change (v : ℕ) + 6 * (rrSlots.slotRound k + 1) ≤ t + 5
    rcases h2.2 with ha | ⟨hb, hc⟩ <;> rcases h3'.2 with hd | ⟨he, hf⟩ <;> omega
  cert_or_wait v hv k hN _ L hL c hc hcc hcr := by
    -- likewise: every round-`(r+2)` block references the whole round
    -- `(r+1)`, and every round-`(r+1)` block votes, so it certifies
    left
    obtain ⟨h1, h3⟩ := mem_T_bounds hv
    obtain ⟨hmem, hround, -⟩ := hL
    simp only [ugrow_ids, Finset.mem_range] at hmem hc
    simp only [ugrow_block, rrBlock_round] at hround hcr
    show (Fintype.card (Fin 4) - Faults.f (Fin 4)) ≤ _
    have hsub : ({0, 1, 2, 3} : Finset (Fin 4)) ⊆
        creatorsOf (Ugrow N).block (carriedVotes (Ugrow N) (IsVote (Ugrow N)) c L) := by
      intro x _
      have hx4 := x.isLt
      refine mem_creatorsOf.mpr ⟨4 * (rrSlots.slotRound k + 1) + (x : ℕ), ?_, ?_⟩
      · rw [carriedVotes, Finset.mem_filter]
        constructor
        · simp only [ugrow_block, mem_growBlock_refs]
          omega
        · unfold IsVote
          simp only [ugrow_block, mem_growBlock_refs]
          omega
      · apply Fin.ext
        simp only [ugrow_block, rrBlock_creator_val]
        omega
    have hcard : ({0, 1, 2, 3} : Finset (Fin 4)).card = 4 := by decide
    have := Finset.card_le_card hsub
    have hf : Faults.f (Fin 4) = 1 := rfl
    have hn : Fintype.card (Fin 4) = 4 := rfl
    omega

/-- **Reactive liveness, on data.** Slot `1` (leader `1`, reliable) is
committed by the full view, at spacing `6` with a timeout of
`9 = 2Δ + proc`, met with equality — and no drift hypothesis: the
collapsed spread is derived inside the theorem. Production appears in no
field: the structure derives it. -/
theorem ugrowReactive_decided (N : ℕ) (hN : rrSlots.slotRound 1 + 2 ≤ N) :
    ∃ L, IsLeaderBlock (S := rrSlots) (Ugrow N) 1 L ∧
      Decided (S := rrSlots) (Ugrow N) (View.full (Ugrow N)) 1 (some L) :=
  (ugrowReactive N).decided (R := 0) (by decide) (by decide)
    (le_refl 0) (fun n _ => by change 2 * 2 + 5 ≤ 9; omega)
    (Nat.zero_le _) hN (by decide)

/-- **No timeout fires, on data**: every build is strictly inside the
deadline — the conclusion of `no_timeout_of_fast`, held by this run at
every round. -/
theorem ugrowReactive_early (N : ℕ) :
    ∀ v ∈ ({1, 2, 3} : Finset (Fin 4)), ∀ n,
      (ugrowReactive N).built v (n + 1)
        < (ugrowReactive N).built v n + (ugrowReactive N).timeout n := by
  intro v _ n
  change (v : ℕ) + 6 * (n + 1) < ((v : ℕ) + 6 * n) + 9
  omega

/-- **The latency theorem, on data.** Slot `1` sits at round `3`; its
leader block is `13`. Every reliable validator builds round `4` within
`D + δ + proc = 3 + 2 + 5` of entering round `3` — the conclusion of
`built_succ_le_of_fast`, with the timeout appearing nowhere. -/
theorem ugrowReactive_fast (N : ℕ) (hN : 4 ≤ N) :
    ∀ v ∈ ({1, 2, 3} : Finset (Fin 4)),
      (ugrowReactive N).built v 4 ≤ (ugrowReactive N).built v 3 + 10 := by
  have hL : IsLeaderBlock (Ugrow N) 1 13 := by
    refine ⟨?_, ?_, ?_⟩
    · simp only [ugrow_ids, Finset.mem_range]; omega
    · simp only [ugrow_block, rrBlock_round, rrSlots_slotRound]
    · apply Fin.ext
      rw [rrSlots_leader_val]
      simp only [ugrow_block, rrBlock_creator_val]
  have h := (ugrowReactive N).built_succ_le_of_fast (k := 1) (D := 3) (δ := 2)
    (fun v _ b hb hbT hbr => by
      simp only [ugrow_ids, Finset.mem_range] at hb
      simp only [ugrow_block, rrBlock_round, rrSlots_slotRound] at hbr
      have hb4 : ((Ugrow N).block b).creator = (⟨b % 4, by omega⟩ : Fin 4) := by
        apply Fin.ext
        simp only [ugrow_block, rrBlock_creator_val]
      rw [hb4]
      change b ∈ reactHolds N v ((b % 4 : ℕ) + 6 * rrSlots.slotRound 1 + 2)
      simp only [reactHolds, Finset.mem_filter, Finset.mem_range, rrSlots_slotRound]
      exact ⟨by omega, Or.inl (by omega)⟩)
    (fun u hu v hv => by
      obtain ⟨_, _⟩ := mem_T_bounds hu
      obtain ⟨_, _⟩ := mem_T_bounds hv
      change (u : ℕ) + 6 * (3 * 1) ≤ ((v : ℕ) + 6 * (3 * 1)) + 3
      omega)
    (by simp only [rrSlots_slotRound]; omega) (by decide) hL (by decide)
  intro v hv
  have hvle := h v hv
  simp only [rrSlots_slotRound, show (ugrowReactive N).proc = 5 from rfl] at hvle
  have h34 : (3 : ℕ) * 1 + 1 = 4 := by norm_num
  have h31 : (3 : ℕ) * 1 = 3 := by norm_num
  rw [h34, h31] at hvle
  omega

/-- Round-robin returns to every reliable validator: `k' = 4k + v` is at
or past `k` and led by `v`. -/
theorem rrSlots_fairToEach : FairToEach (S := rrSlots) ({1, 2, 3} : Finset (Fin 4)) := by
  intro v hv k
  refine ⟨4 * k + (v : ℕ), by omega, ?_⟩
  apply Fin.ext
  rw [rrSlots_leader_val]
  have := v.isLt
  omega

/-- **RS5 on data.** Validator `2`'s round-`1` block (id `6`) enters the
agreed ledger through a slot led by `2` itself, above round `1` — with no
coverage anywhere: the commit is reactive, and the reach runs down `2`'s
own self-parent chain. -/
example : ∃ k', 1 < rrSlots.slotRound k' ∧ rrSlots.leader k' = 2 ∧
    ∀ N, rrSlots.slotRound k' + 2 ≤ N →
      ∃ L, IsLeaderBlock (S := rrSlots) (Ugrow N) k' L ∧
        Decided (S := rrSlots) (Ugrow N) (View.full (Ugrow N)) k' (some L) ∧
        Reaches (Ugrow N) L 6 ∧
        ∀ (g : ℕ → Option ℕ) (n : ℕ), g k' = some L → k' < n →
          6 ∈ ledgerSet (Ugrow N) g n := by
  obtain ⟨k', hm, _, hlead, h⟩ :=
    ReactiveM.committed_of_correct_block (S := rrSlots) (BlockId := ℕ)
      (Payload := Unit) (by decide) (by decide) rrSlots_fairToEach
      (u := 2) (by decide) 0 1 (Nat.zero_le 1)
  refine ⟨k', hm, hlead, fun N hN => ?_⟩
  refine h (Ugrow N) N (ugrowReactive N) (le_refl 0)
    (fun n _ => by change 2 * 2 + 5 ≤ 9; omega) hN 6 ?_ ?_ ?_
  · simp only [ugrow_ids, Finset.mem_range]
    have := rrSlots.mono (Nat.zero_le k')
    omega
  · apply Fin.ext
    simp only [ugrow_block, rrBlock_creator_val]
    decide
  · simp only [ugrow_block, rrBlock_round]

/-! ## The reactive precondition is inhabited

`Properties/Live.lean` guards `LeaderCommits` by asking that the rule's
own precondition be reachable from coverage and production. Reactive
Mysticeti cannot meet that antecedent, and does not want to: the point
of the reactive discipline is to commit *without* waiting for the main
line, so `SynchronisedOn` is false in a reactive execution by design
(`Reactive/Basic.lean`). `reactiveLive` is guarded the other admissible
way instead — by a witness. `ugrowReactive` is a reactive execution, and
below it satisfies the precondition and yields a verdict, so
`leaderCommits_reactive` is not a statement about an empty hypothesis.
-/

/-- **`reactiveLive` holds on this execution**, at the single-slot
window `LeaderCommits` reads. -/
theorem ugrowReactiveLive (N k : ℕ) (hN : rrSlots.slotRound k + 2 ≤ N) :
    MysticetiProperties.reactiveLive (S := rrSlots) (U := Ugrow N)
      (View.full (Ugrow N)) ({1, 2, 3} : Finset (Fin 4)) k (k + 1) := by
  refine ⟨by decide, by decide, N, 0, ugrowReactive N, Nat.le_refl 0,
    (fun n _ => by change 2 * 2 + 5 ≤ 9; omega), Nat.zero_le _,
    View.coversUpto_full (Ugrow N) N, ?_⟩
  intro j hj
  have := rrSlots.mono (Nat.lt_succ_iff.mp hj)
  omega

/-- **And the verdict it yields.** The consumer test for the pair: a
reliably-led slot of this execution is committed, with the bound
`LeaderCommits` promises. -/
theorem ugrowReactive_leaderCommits (N k : ℕ) (hN : rrSlots.slotRound k + 2 ≤ N)
    (hlead : rrSlots.leader k ∈ ({1, 2, 3} : Finset (Fin 4))) :
    ∃ L, Properties.DecidedBelow (MysticetiProperties.mysticetiRule (Payload := Unit))
      rrSlots (k + 1) (View.full (Ugrow N)) k (some L) :=
  MysticetiProperties.leaderCommits_reactive rrSlots (View.full (Ugrow N))
    ({1, 2, 3} : Finset (Fin 4)) k (k + 1) (ugrowReactiveLive N k hN) k
    (Nat.le_refl k) (Nat.lt_succ_self k) hlead

#print axioms ugrowReactiveLive
#print axioms ugrowReactive_leaderCommits
#print axioms ugrowReactive_decided
#print axioms ugrowReactive_fast
#print axioms LeanDag.ReactiveM.decided
#print axioms LeanDag.Odontoceti.reactive_decided
#print axioms LeanDag.ReactivePace.no_timeout_of_fast
#print axioms rrSlots_fairToEach
#print axioms LeanDag.ReactiveM.committed_of_correct_block

end LeanDagTest
