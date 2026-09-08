import LeanDagTest.Mysticeti.ViewPace
import LeanDagTest.Reactive.Model
import LeanDag.FinWhale.View
import LeanDag.FinWhale.Reactive
import LeanDag.FinWhale.Validity
import LeanDag.FinWhale.Creation
import LeanDag.FinWhale.Procedure.Protocol
/-!
# FinWhale witnesses — the pacing structure under liveness

`LeanDag/FinWhale/Liveness.lean` derives coverage and production from a
`ViewPace`, and the liveness capstones are stated over one. This file
exhibits an execution that is such a structure, so that those theorems
run on a model rather than on an unfilled premise.

The committee is FinWhale's smallest: `f = 1` and `p = 1` give
`n = 3f + 2p − 1 = 4`, which is the committee the development's own
pacing witness (`LeanDagTest/ViewPace.lean`) is built over. `Ugrow N` is
that execution — four blocks a round, each referencing the whole round
below — and `ugrowSkewCorrect N` is its `ViewPace` over the correct
validators.

What has to be shown here is that the same blocks satisfy FinWhale's
validity rule, which adds the leader clause to Mysticeti's. They do, and
for a reason the layout settles rather than the protocol: an identifier
fixes both the round and the author, so a round holds one block per
validator and the leader's block two rounds down is unique. Nothing in
the parent sets can disagree about it.

At `p = 1` the slow-path quorum and the validity quorum coincide, which
is why the `Fin 9` witnesses of `Model.lean` exist beside this one.
-/

namespace LeanDagTest

namespace FinWhalePace

open LeanDag LeanDag.FinWhale

/-- One fast-path slot at four validators: `n + 1 = 3f + 2p = 5`. -/
local instance growParams : Params (Fin 4) where
  p := 1
  p_pos := by omega
  p_le_f := by decide
  card_add_one := by decide

/-- Round robin, shifted so that round `0` is led by validator `1`:
validator `0` is the Byzantine one here. -/
def growLeader : ℕ → Fin 4 := fun r => ⟨(r + 1) % 4, Nat.mod_lt _ (by omega)⟩

/-- **The grown execution is a FinWhale DAG**, at any leader schedule.
The first three validity clauses are Mysticeti's, and hold of it already;
the leader clause is FinWhale's, and the layout gives it — an identifier
fixes both the round and the author, so the leader's block two rounds
down is unique whatever the schedule names. -/
def DgrowFor (lead : ℕ → Fin 4) (N : ℕ) : Dag (Fin 4) ℕ Unit where
  ids := (Ugrow N).ids
  block := (Ugrow N).block
  complete := (Ugrow N).complete
  valid := by
    intro i hi
    refine ⟨((Ugrow N).valid i hi).predecessor, ((Ugrow N).valid i hi).distinct_creators,
      ((Ugrow N).valid i hi).quorum, ?_⟩
    intro v
    refine Or.inl ?_
    intro p hp q hq x hx y hy hxl hyl
    -- the parents sit in one round, so their references sit in one round
    simp only [ugrow_block, growBlock_refs, Finset.mem_Ico] at hp hq hx hy
    -- and inside a round an author has one block
    have hval : x % 4 = y % 4 := by
      have := congrArg (fun (v : Fin 4) => (v : ℕ)) (hxl.trans hyl.symm)
      simpa [ugrow_block] using this
    omega
  no_equivocation := (Ugrow N).no_equivocation

@[simp] theorem dgrowFor_ids (lead : ℕ → Fin 4) (N : ℕ) :
    (DgrowFor lead N).ids = (Ugrow N).ids := rfl

@[simp] theorem dgrowFor_block (lead : ℕ → Fin 4) (N : ℕ) :
    (DgrowFor lead N).block = (Ugrow N).block := rfl

/-- The execution under the shifted schedule. -/
abbrev Dgrow (N : ℕ) : Dag (Fin 4) ℕ Unit := DgrowFor growLeader N

@[simp] theorem dgrow_ids (N : ℕ) : (Dgrow N).ids = (Ugrow N).ids := rfl

@[simp] theorem dgrow_block (N : ℕ) : (Dgrow N).block = (Ugrow N).block := rfl

/-- The blocks are the ones `Ugrow` lays out: id `1` is validator `1`'s
genesis block, and validator `1` leads round `0`. -/
example : ((Dgrow 5).block 1).round = 0 ∧ ((Dgrow 5).block 1).creator = 1 ∧
    growLeader 0 = 1 := by decide

/-- And validator `1` is correct, so round `0` has an honest leader. -/
example : ((Dgrow 5).block 1).creator ∈ (Correct : Finset (Fin 4)) := by decide

/-- **The bridge on data.** Coverage and production over the correct
validators, from `ugrowSkewCorrect` — view convergence, the drift bound
and the backoff — and nothing else. This is a compatibility statement,
not FinWhale's liveness route: the coverage it yields is bought by the
waiting floor, which FinWhale's pacemaker does not have. -/
example : SynchronisedFrom (Dgrow 5).block (Dgrow 5).ids (Correct : Finset (Fin 4)) 0 :=
  synchronised_of_viewPace (D := Dgrow 5) (ugrowSkewCorrect 5) rfl rfl (by decide)
    (fun n _ => Nat.le_refl _)

example : ∀ r ≤ 5, PopulatedFrom (Dgrow 5).block (Dgrow 5).ids (Correct : Finset (Fin 4)) r :=
  populated_of_viewPace (D := Dgrow 5) (ugrowSkewCorrect 5) rfl rfl

/-! ## The reactive schedule

`ViewPace` above is the full-timeout discipline. FinWhale's pacemaker is
reactive — C1 and C3 fire early, and the `2∆` timeout is only the
fallback — so the faithful structure is `ReactivePace`, and the arc's
reactive route runs off it.

The same execution serves. `Ugrow` has every block reference the whole
round below, so both of the reactive wait clauses hold by their *first*
disjunct: the exit is always available, and no fallback argument is
needed. The trunk is reused from the development's own reactive witness;
what is rebuilt here is the schedule — FinWhale names a leader every
round, where Mysticeti's witness names one every three. -/

/-- One leader per round, which is FinWhale's schedule. -/
@[reducible] def fwSlots : Slots (Fin 4) :=
  Slots.uniformSingle 1 (by omega) (fun k => ⟨k % 4, by omega⟩)

attribute [local instance 3000] fwSlots

@[simp] theorem fwSlots_slotRound (k : ℕ) : fwSlots.slotRound k = k := by simp

/-- The leader schedule the reactive execution runs. -/
def reactLeader : ℕ → Fin 4 := fun k => ⟨k % 4, by omega⟩

/-- The execution under that schedule. -/
abbrev Dreact (N : ℕ) : Dag (Fin 4) ℕ Unit := DgrowFor reactLeader N

/-- **Every block votes.** A round-`(r+1)` block of this layout
references the whole of round `r`. -/
theorem ugrow_votes {N r : ℕ} {c L : ℕ}
    (hcr : ((Ugrow N).block c).round = r + 1)
    (hLr : ((Ugrow N).block L).round = r) : L ∈ ((Ugrow N).block c).refs := by
  simp only [ugrow_block, rrBlock_round] at hcr hLr
  simp only [ugrow_block, mem_growBlock_refs]
  omega

/-- **And every round-`(r+2)` block certifies.** Its parents are the
whole of round `r + 1`, and each of them votes, so the votes it carries
are the whole committee. -/
theorem ugrow_certifies {N r : ℕ} {c L : ℕ} (hc : c ∈ (Ugrow N).ids)
    (hcr : ((Ugrow N).block c).round = r + 2)
    (hLr : ((Ugrow N).block L).round = r) : Certifies (Ugrow N) c L := by
  have hfilter : votesIn (Ugrow N) c L = ((Ugrow N).block c).refs := by
    refine Finset.filter_true_of_mem fun q hq => ?_
    have hqids : q ∈ (Ugrow N).ids := (Ugrow N).complete c hc q hq
    have hqr : ((Ugrow N).block q).round = r + 1 := by
      have := (Ugrow N).round_of_mem_refs hc hq
      omega
    exact ugrow_votes hqr hLr
  show quorumCard (Fin 4) ≤ (creatorsOf (Ugrow N).block (votesIn (Ugrow N) c L)).card
  rw [hfilter]
  exact ((Ugrow N).valid c hc).quorum (by omega)

/-- The trunk — views, convergence, the progress and catch-up rules — is
the development's own reactive witness, read at its own schedule; the
structure below rebuilds only the schedule-dependent clauses. -/
def fwPaceCore (N : ℕ) : PaceCore (Ugrow N) {1, 2, 3} N :=
  ReactivePace.toPaceCore (S := rrSlots) (ReactiveM.toReactivePace (S := rrSlots) (ugrowReactive N))

@[simp] theorem fwPaceCore_built (N : ℕ) (v : Fin 4) (n : ℕ) :
    (fwPaceCore N).built v n = (v : ℕ) + 6 * n := rfl

@[simp] theorem fwPaceCore_timeout (N : ℕ) (n : ℕ) : (fwPaceCore N).timeout n = 9 := rfl

@[simp] theorem fwPaceCore_proc (N : ℕ) : (fwPaceCore N).proc = 5 := rfl

@[simp] theorem fwPaceCore_holds (N : ℕ) (v : Fin 4) (t : ℕ) :
    (fwPaceCore N).holds v t = reactHolds N v t := rfl

/-- **The reactive witness at FinWhale's schedule.** -/
def fwReactive (N : ℕ) : ReactiveM (Ugrow N) {1, 2, 3} N :=
  { fwPaceCore N with
    built_lt := fun _ _ _ _ => by simp only [fwPaceCore_built]; omega
    deadline := fun _ _ _ _ => by simp only [fwPaceCore_built, fwPaceCore_timeout]; omega
    vote_or_wait := fun v hv k hN _ L hL c hc hcc hcr =>
      Or.inl (ugrow_votes hcr hL.2.1)
    prompt_vote := fun v hv k hN hlead L hL t hbuilt hheld hall => by
      obtain ⟨h1, h3⟩ := mem_T_bounds hv
      have hv4 := v.isLt
      have h2 := hall (4 * k + 2)
        (by
          have hk : fwSlots.slotRound k = k := by simp
          simp only [ugrow_ids, Finset.mem_range]
          rw [hk] at hN; omega)
        (by
          have : ((Ugrow N).block (4 * k + 2)).creator = (2 : Fin 4) := by
            apply Fin.ext
            simp only [ugrow_block, rrBlock_creator_val]
            omega
          rw [this]; decide)
        (by simp only [ugrow_block, rrBlock_round, fwSlots_slotRound]; omega)
      have h3' := hall (4 * k + 3)
        (by
          have hk : fwSlots.slotRound k = k := by simp
          simp only [ugrow_ids, Finset.mem_range]
          rw [hk] at hN; omega)
        (by
          have : ((Ugrow N).block (4 * k + 3)).creator = (3 : Fin 4) := by
            apply Fin.ext
            simp only [ugrow_block, rrBlock_creator_val]
            omega
          rw [this]; decide)
        (by simp only [ugrow_block, rrBlock_round, fwSlots_slotRound]; omega)
      simp only [fwPaceCore_holds, reactHolds, Finset.mem_filter, Finset.mem_range] at h2 h3'
      have e2 : (4 * k + 2) % 4 = 2 := by omega
      have d2 : (4 * k + 2) / 4 = k := by omega
      have e3 : (4 * k + 3) % 4 = 3 := by omega
      have d3 : (4 * k + 3) / 4 = k := by omega
      rw [e2, d2] at h2
      rw [e3, d3] at h3'
      show (v : ℕ) + 6 * (fwSlots.slotRound k + 1) ≤ t + 5
      simp only [fwSlots_slotRound]
      rcases h2.2 with ha | ⟨hb, hc⟩ <;> rcases h3'.2 with hd | ⟨he, hf⟩ <;> omega
    cert_or_wait := fun v hv k hN _ L hL c hc hcc hcr =>
      Or.inl (ugrow_certifies hc hcr hL.2.1) }

/-- The same, over `Correct`. -/
def fwReactiveCorrect (N : ℕ) : ReactiveM (Ugrow N) (Correct : Finset (Fin 4)) N := by
  rw [show (Correct : Finset (Fin 4)) = {1, 2, 3} from by decide]
  exact fwReactive N

/-- **The liveness interface, off the reactive schedule.** Every
correct-led slot below the horizon carries a direct commit — with no
coverage assumption anywhere, since a reactive builder has none. -/
example (N : ℕ) : CommitsCorrectLeaders (Slots.identity reactLeader) (Dreact N) 0 N :=
  commits_of_reactive (FS := Slots.identity reactLeader) (D := Dreact N) (fwReactiveCorrect N)
    rfl rfl
    (fun k => by simp) (fun _ => rfl) (fun k => rfl) rfl (Nat.le_refl _)
    (fun n _ => Nat.le_refl _)

/-- And the fast path on the same schedule. Round `1` is led by validator
`1`, which is correct, and its block is id `5`: at most `p = 1` Byzantine
validator makes the correct validators' votes an `n − p` fast commit. -/
example (N : ℕ) (hN : 2 ≤ N) : FastCommit (Dreact N) 5 :=
  fastCommit_of_reactive (D := Dreact N) (k := 1) (R := 0)
    (fwReactiveCorrect N).toReactivePace rfl rfl rfl (by decide) (Nat.le_refl _)
    (fun n _ => Nat.le_refl _) (by omega) (by simpa using hN) (by decide)
    ⟨by simp only [ugrow_ids, Finset.mem_range]; omega, by simp,
      by apply Fin.ext; simp only [ugrow_block, rrBlock_creator_val]; rfl⟩

@[simp] theorem fwReactiveCorrect_built (N : ℕ) (v : Fin 4) (n : ℕ) :
    (fwReactiveCorrect N).built v n = (v : ℕ) + 6 * n := rfl

@[simp] theorem fwReactiveCorrect_holds (N : ℕ) (v : Fin 4) (t : ℕ) :
    (fwReactiveCorrect N).holds v t = reactHolds N v t := rfl

@[simp] theorem fwReactiveCorrect_delay (N : ℕ) : (fwReactiveCorrect N).delay = 2 := rfl

@[simp] theorem fwReactiveCorrect_proc (N : ℕ) : (fwReactiveCorrect N).proc = 5 := rfl

/-- **δ-propagation on this execution**: a block reaches every validator
within `delay = 2` of its build. -/
theorem fwReactive_delta (N : ℕ) (r : ℕ) :
    ∀ v ∈ (Correct : Finset (Fin 4)), ∀ b ∈ (Ugrow N).ids,
      ((Ugrow N).block b).creator ∈ (Correct : Finset (Fin 4)) →
      ((Ugrow N).block b).round = fwSlots.slotRound r →
      b ∈ (fwReactiveCorrect N).holds v
        ((fwReactiveCorrect N).built (((Ugrow N).block b).creator) (fwSlots.slotRound r) + 2) := by
  intro v _ b hb _ hbr
  simp only [ugrow_ids, Finset.mem_range] at hb
  simp only [ugrow_block, rrBlock_round, fwSlots_slotRound] at hbr
  simp only [fwReactiveCorrect_holds, reactHolds, Finset.mem_filter, Finset.mem_range]
  refine ⟨hb, Or.inl ?_⟩
  simp only [fwReactiveCorrect_built, ugrow_block, rrBlock_creator_val, fwSlots_slotRound]
  omega

/-- **Definition 1 on data.** The fast commit of round `1`'s leader
block, together with the bound on when its votes were built: within
`Δ + δ + 2·proc` of round entry, with the timeout nowhere in it. -/
example (N : ℕ) (hN : 2 ≤ N) :
    FastCommit (Dreact N) 5 ∧
      ∀ v ∈ (Correct : Finset (Fin 4)), (fwReactiveCorrect N).built v 2 ≤
        (fwReactiveCorrect N).built v 1 + (fwReactiveCorrect N).delay + 2 +
          2 * (fwReactiveCorrect N).proc :=
  fastCommit_latency (D := Dreact N) (k := 1) (R := 0) (δ := 2)
    (fwReactiveCorrect N).toReactivePace rfl rfl rfl (by decide) (Nat.le_refl _)
    (fun n _ => Nat.le_refl _) (by omega) (by simpa using hN) (by decide)
    ⟨by simp only [ugrow_ids, Finset.mem_range]; omega, by simp,
      by apply Fin.ext; simp only [ugrow_block, rrBlock_creator_val]; rfl⟩
    (fwReactive_delta N 1)

/-! ## Validity's step, without coverage

Every block of this layout references the whole round below, its author's
own block among it, so the execution has the paper's self-parent edge.
That is all Validity needs: a correct validator's block lies in the
causal history of its own later blocks, and the rotation makes that
validator a leader once a cycle. -/

theorem selfParented_Dreact (N : ℕ) : SelfParented (Dreact N) := by
  intro b hb hround
  simp only [dgrowFor_ids, ugrow_ids, Finset.mem_range] at hb
  simp only [dgrowFor_block, ugrow_block, rrBlock_round] at hround
  refine ⟨4 * (b / 4) - 4 + b % 4, ?_, ?_⟩
  · simp only [dgrowFor_block, ugrow_block, mem_growBlock_refs]
    omega
  · apply Fin.ext
    simp only [dgrowFor_block, ugrow_block, rrBlock_creator_val]
    omega

/-- Validator `1`'s genesis block lies in the causal history of its
round-`1` block — by the self-parent chain, with no reference to what
else either block cited. -/
example (N : ℕ) (hN : 1 ≤ N) : ReachesFrom (Dreact N).block 5 1 :=
  reaches_of_same_creator (selfParented_Dreact N)
    (by simp only [dgrowFor_ids, ugrow_ids, Finset.mem_range]; omega)
    (by simp only [dgrowFor_ids, ugrow_ids, Finset.mem_range]; omega)
    (by simp only [dgrowFor_block, ugrow_block]; decide)
    (by simp only [dgrowFor_block, ugrow_block]; decide)
    (by simp only [dgrowFor_block, ugrow_block]; decide)

/-! ## The creation rule, on data

The reactive witness above takes the vote and certificate clauses as
given. `Creation` derives them from C1, C2 and C3 instead, and the same
execution carries one — with two triggers in play, so the derivation's
two interesting cases are both exercised.

Validator `3` builds by C3: at its build time it holds the round's blocks
from validators `0`, `1` and itself, which is `n − f = 3`. Everyone else
builds by C1, holding the leader's block and a quorum of votes. The
induction then runs through validator `1`, which is correct, builds
strictly earlier, and votes. -/

@[simp] theorem dreact_leader (N n : ℕ) : ((reactLeader n : Fin 4) : ℕ) = n % 4 := rfl

/-- Validator `3` catches up on the round's own blocks; the rest build on
the leader and its votes. -/
def fwTrigger : Fin 4 → ℕ → Trigger := fun v _ =>
  if (v : ℕ) = 3 then Trigger.roundQuorum else Trigger.leaderAndQuorum

/-- **The creation rule, on the grown execution.** -/
def fwCreation (N : ℕ) : Creation (Ugrow N) {1, 2, 3} N reactLeader :=
  { fwPaceCore N with
    built_lt := fun _ _ _ _ => by simp only [fwPaceCore_built]; omega
    trigger := fwTrigger
    holds_built := by
      intro v _ t b hb _
      simp only [fwPaceCore_holds, reactHolds, Finset.mem_filter, Finset.mem_range] at hb
      simp only [fwPaceCore_built, ugrow_block, rrBlock_creator_val, rrBlock_round]
      rcases hb.2 with h | ⟨-, h⟩ <;> omega
    builds_distinct := by
      intro u _ v _ n hne
      have : (u : ℕ) ≠ (v : ℕ) := fun h => hne (Fin.ext h)
      simp only [fwPaceCore_built]
      omega
    c1_leader := by
      intro v hv n hN _ L hL hLr hLc
      obtain ⟨h1, h3⟩ := mem_T_bounds hv
      simp only [ugrow_ids, Finset.mem_range] at hL
      simp only [ugrow_block, rrBlock_round] at hLr
      have hLv : L % 4 = n % 4 := by
        have := congrArg (fun (x : Fin 4) => (x : ℕ)) hLc
        simpa [ugrow_block, dreact_leader] using this
      simp only [fwPaceCore_holds, reactHolds, Finset.mem_filter, Finset.mem_range,
        fwPaceCore_built]
      exact ⟨hL, Or.inl (by omega)⟩
    c1_votes := by
      intro v hv n hN _ L hL hLr hLc
      obtain ⟨h1, h3⟩ := mem_T_bounds hv
      simp only [ugrow_ids, Finset.mem_range] at hL
      simp only [ugrow_block, rrBlock_round] at hLr
      refine Or.inl ⟨Finset.univ, by decide, fun u _ => ⟨4 * (n + 1) + (u : ℕ), ?_, ?_, ?_, ?_, ?_⟩⟩
      · simp only [ugrow_ids, Finset.mem_range]; have := u.isLt; omega
      · simp only [fwPaceCore_holds, reactHolds, Finset.mem_filter, Finset.mem_range,
          fwPaceCore_built]
        have := u.isLt
        exact ⟨by omega, Or.inl (by omega)⟩
      · apply Fin.ext
        simp only [ugrow_block, rrBlock_creator_val]
        have := u.isLt; omega
      · simp only [ugrow_block, rrBlock_round]; have := u.isLt; omega
      · simp only [ugrow_block, mem_growBlock_refs]
        have := u.isLt; omega
    c2_wait := by
      intro v _ n htrig
      -- no block of this execution is created by the timeout
      exfalso
      simp only [fwTrigger] at htrig
      split at htrig <;> exact absurd htrig (by decide)
    c3_quorum := by
      intro v hv n hN htrig
      obtain ⟨h1, h3⟩ := mem_T_bounds hv
      have hv3 : (v : ℕ) = 3 := by
        simp only [fwTrigger] at htrig
        split at htrig
        · assumption
        · exact absurd htrig (by decide)
      refine ⟨{0, 1, 3}, by decide, fun u hu => ⟨4 * (n + 1) + (u : ℕ), ?_, ?_, ?_, ?_⟩⟩
      · simp only [ugrow_ids, Finset.mem_range]; have := u.isLt; omega
      · simp only [fwPaceCore_holds, reactHolds, Finset.mem_filter, Finset.mem_range,
          fwPaceCore_built]
        have := u.isLt
        have hu' : (u : ℕ) = 0 ∨ (u : ℕ) = 1 ∨ (u : ℕ) = 3 := by
          simp only [Finset.mem_insert, Finset.mem_singleton] at hu
          rcases hu with rfl | rfl | rfl
          exacts [Or.inl rfl, Or.inr (Or.inl rfl), Or.inr (Or.inr rfl)]
        refine ⟨by omega, ?_⟩
        rcases hu' with h | h | h
        · exact Or.inl (by omega)
        · exact Or.inl (by omega)
        · exact Or.inr ⟨by omega, by omega⟩
      · apply Fin.ext
        simp only [ugrow_block, rrBlock_creator_val]
        have := u.isLt; omega
      · simp only [ugrow_block, rrBlock_round]; have := u.isLt; omega
    selects_leader := by
      intro v _ n _ c hc _ hcr L hL hLr _ _
      simp only [ugrow_ids, Finset.mem_range] at hc hL
      simp only [ugrow_block, rrBlock_round] at hcr hLr
      simp only [ugrow_block, mem_growBlock_refs]
      omega
    selects_votes := by
      intro v _ n _ c hc _ hcr L _ _ _ b hb hbr _ hbvote
      -- the held block is itself a parent here, every block of this
      -- layout referencing the whole round below
      refine ⟨b, ?_, rfl, hbvote⟩
      simp only [ugrow_ids, Finset.mem_range] at hc hb
      simp only [ugrow_block, rrBlock_round] at hcr hbr
      simp only [ugrow_block, mem_growBlock_refs]
      omega }

/-- **The liveness interface, from the creation rule.** No wait clause is
assumed: the votes and the certificates come out of C1 and C3. -/
theorem fwCommits (N : ℕ) : CommitsCorrectLeaders (Slots.identity reactLeader) (Dreact N) 0 N :=
  commits_of_creation (S := Slots.identity reactLeader) (D := Dreact N) (fwCreation N) rfl rfl
    (by decide)
    (fun _ => rfl) (Nat.le_refl _) (fun n _ => Nat.le_refl _)

/-- The rotation of this execution is round robin. -/
theorem fwDreactRoundRobin (N : ℕ) : RoundRobin reactLeader := by
  refine ⟨Equiv.refl (Fin 4), fun r => ?_⟩
  apply Fin.ext
  show r % 4 = ZMod.val ((r : ZMod 4))
  exact (ZMod.val_natCast (n := 4) r).symm

/-! ## A run of the protocol

Everything the four properties are stated over, on this execution: the
blocks, the schedule that carried them, the rotation, the self-parent
edge, and the tie-break — which need not be assumed either, `chooseLeast`
being one.

That the bundle is inhabited is the point. `Run` gathers ten conditions,
and a structure nothing satisfies would make every property above it
vacuous. -/
noncomputable def fwRun (N : ℕ) : Run (Fin 4) ℕ Unit where
  dag := Dreact N
  sched := (Slots.identity reactLeader)
  roundId := fun _ => rfl
  paced := Ugrow N
  ids_eq := rfl
  block_eq := rfl
  horizon := N
  rounds_le := by
    intro b hb
    simp only [dgrowFor_ids, ugrow_ids, Finset.mem_range] at hb
    simp only [dgrowFor_block, ugrow_block, rrBlock_round]
    omega
  paceHorizon := N
  pace := fwPaceCore N
  rounds_advance := by
    intro u _ n _
    simp only [fwPaceCore_built]
    omega
  stable := 0
  gst_le := Nat.le_refl _
  liveHorizon := N
  commits := fwCommits N
  live_le := Nat.le_refl _
  roundRobin := fwDreactRoundRobin N
  selfParented := selfParented_Dreact N

/-- **Agreement on data.** Two correct validators of the run deliver the
same sequence. The horizon is what Lemma 22's window asks for: `3f + 5`
rounds above the slot, with `f = 1` here. -/
example (N : ℕ) (hN : 9 ≤ N) {v w : Fin 4} (hv : v ∈ (Correct : Finset (Fin 4)))
    (hw : w ∈ (Correct : Finset (Fin 4))) :
    (fwRun N).delivers hv 1 = (fwRun N).delivers hw 1 :=
  (fwRun N).agreement hv hw (by show max 1 0 + (3 * 1 + 5) ≤ N; omega)

/-- **Integrity on data**, which asks nothing of the run at all. -/
example (N : ℕ) {v : Fin 4} (hv : v ∈ (Correct : Finset (Fin 4))) (k : ℕ) :
    ((fwRun N).delivers hv k).Nodup :=
  (fwRun N).integrity hv k

/-! ## The arc's axioms, on the routes this file supplies -/

#print axioms LeanDag.FinWhale.Creation.lemma18
#print axioms LeanDag.FinWhale.Creation.lemma19
#print axioms LeanDag.FinWhale.commits_of_creation
#print axioms LeanDag.FinWhale.theorem26_of_selfParent
#print axioms LeanDag.FinWhale.Run.agreement
#print axioms LeanDag.FinWhale.Run.totalOrder
#print axioms LeanDag.FinWhale.Run.integrity
#print axioms LeanDag.FinWhale.Run.validity

end FinWhalePace

end LeanDagTest
