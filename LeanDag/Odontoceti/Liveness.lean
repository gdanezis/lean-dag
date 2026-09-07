import LeanDag.Odontoceti.Decision
import LeanDag.Mysticeti.Liveness
import Mathlib.Data.Finset.Max

/-!
# Odontoceti: liveness

`odontoceti.md` §5, OP4 — O7 through O10. The two-round rule's liveness
is *simpler* than Mysticeti's, which is the protocol's whole point:

* **O7** (`directCommit_of_leader_mem`, `decided_of_leader_mem`) —
  post-`R`, a correct leader's block is referenced by every correct
  decision-round block (`SynchronisedOn`, one step), so its supporters
  include a full quorum: **two** populated rounds against Mysticeti's
  three.
* **O8** (`SpansEligible`, `spansEligible_two`) — under a pipelined
  identity-round schedule a run of **two** consecutive committed slots
  spans eligibility for everything below: a slot cannot anchor on the
  round immediately above it, but the second slot of the run clears
  `slotRound + 2`. Two consecutive honest leaders is the thesis's
  Lemma 10; the schedule fact itself is hypothesized (`FairRunOn`), in
  house style.
* **O9** (`decided_below_of_committed_run`) — a run of committed slots
  clears every slot below it, by the nearest-eligible-committed-anchor
  induction. The indirect commit picks the **least** passing candidate
  (`Finset.min'`), which is exactly what the canonicity premise of
  `Decided.indirectCommit` asks for.
* **O10** (`all_decided_below_of_fairRun`) — the composition, under
  enforceable hypotheses only: `Live`, `DeliversQuorum`,
  `SynchronisedOn`, and a recurring run of `c` correct-led slots. Note
  the horizon: the run's last slot needs rounds up to
  `slotRound + 1` — one round of certificates fewer than Mysticeti's
  `+ 2`.

Every decision-valued statement concludes on a validator's own view,
caught up to the horizon it reads (`View.CoversUpto`): the direct
commit's supporters sit one round above the leader, so a caught-up view
holds them (`directCommitIn_of_coversUpto`), and the descent is
view-parametric. The full view is caught up to every horizon
(`View.coversUpto_full`), so the whole-universe reading is the special
case; under eventual DAG synchrony (`liveness.md` §4.2) every correct
validator's view is caught up once delivery has reached the horizon,
which is what makes the statement one about validators.
-/

namespace LeanDag

namespace Odontoceti

variable {Validator : Type} [Fintype Validator] [DecidableEq Validator]
variable [F : Faults5 Validator]
variable {BlockId : Type} [LinearOrder BlockId] {Payload : Type}
variable {U : BlockUniverse Validator BlockId Payload}
variable [S : Slots Validator]
variable {T : Finset Validator} {L : BlockId} {k R N : ℕ}

/-! ## O7 — honest leaders commit directly, in one step -/

/-- **The commit argument, stated once** — the two-round counterpart of
`directCommit_of_certifiesAt`. A quorum-sized `T` whose blocks one round
above `r` all vote for `L` directly commits it: a vote *is* a support,
each `v ∈ T` has a supporting block by production, and `T`'s cardinality
does the counting. Both pacing disciplines end here — the full-timeout
one arriving through `votesAt_of_synchronisedOn`, the reactive one
through `ReactivePace.votes`. -/
theorem directCommit_of_votesAt {r : ℕ}
    (hcard : quorumCard Validator ≤ T.card)
    (hpop1 : PopulatedOn U T (r + 1))
    (hv : VotesAt U T r L) :
    DirectCommit U L r := by
  refine le_trans hcard (Finset.card_le_card ?_)
  intro w hw
  obtain ⟨b, hb, hbc, hbr⟩ := hpop1 w hw
  exact mem_supporters.mpr ⟨b, hb, hbr, hv w hw b hb hbc hbr, hbc⟩

/-- **O7, commit half (thesis Lemma 8 + Corollary 9).** Post-`R`, a
`T`-led slot is directly committed: `SynchronisedOn` makes every `T`
block at the decision round reference the leader's block, and `T`
carries a quorum. Two populated rounds — propose and decide — and one
synchronised step, routed through the targeted interface. -/
theorem directCommit_of_leader_mem
    (hcard : quorumCard Validator ≤ T.card)
    (hs : SynchronisedOn U T R) (hR : R ≤ S.slotRound k)
    (hpop0 : PopulatedOn U T (S.slotRound k))
    (hpop1 : PopulatedOn U T (S.slotRound k + 1))
    (hlead : S.leader k ∈ T) :
    ∃ L, IsLeaderBlock U k L ∧ DirectCommit U L (S.slotRound k) := by
  obtain ⟨L, hL, hLc, hLr⟩ := hpop0 (S.leader k) hlead
  exact ⟨L, ⟨hL, hLr, hLc⟩,
    directCommit_of_votesAt hcard hpop1
      (votesAt_of_synchronisedOn hs hR hL hLr (by rw [hLc]; exact hlead))⟩

/-- A view caught up to the decision round sees every supporter, so a
direct commit in the universe is a direct commit in the view. -/
theorem directCommitIn_of_coversUpto {V : View Validator BlockId Payload U} {r : ℕ}
    (h : DirectCommit U L r) (hcov : V.CoversUpto (r + 1)) :
    DirectCommitIn U V L r :=
  HoldsAtLeast.of_coversUpto
    (fun q hq => ⟨(mem_votesFor.mp hq).1, (mem_votesFor.mp hq).2.1.le⟩) hcov h

/-- **O7, as a decision** — on any view caught up to the decision
round. -/
theorem decided_of_leader_mem
    (hcard : quorumCard Validator ≤ T.card)
    (hs : SynchronisedOn U T R) (hR : R ≤ S.slotRound k)
    (hpop0 : PopulatedOn U T (S.slotRound k))
    (hpop1 : PopulatedOn U T (S.slotRound k + 1))
    (V : View Validator BlockId Payload U)
    (hcov : V.CoversUpto (S.slotRound k + 1))
    (hlead : S.leader k ∈ T) :
    ∃ L, IsLeaderBlock U k L ∧ Decided U V k (some L) := by
  obtain ⟨L, hLb, hdc⟩ :=
    directCommit_of_leader_mem hcard hs hR hpop0 hpop1 hlead
  exact ⟨L, hLb, Decided.directCommit hLb (directCommitIn_of_coversUpto hdc hcov)⟩

/-- The same at `T := Correct`. -/
theorem decided_of_correct_leader (hs : Synchronised U R)
    (hR : R ≤ S.slotRound k)
    (hpop0 : Populated U (S.slotRound k))
    (hpop1 : Populated U (S.slotRound k + 1))
    (V : View Validator BlockId Payload U)
    (hcov : V.CoversUpto (S.slotRound k + 1))
    (hlead : S.leader k ∈ (Correct : Finset Validator)) :
    ∃ L, IsLeaderBlock U k L ∧ Decided U V k (some L) :=
  decided_of_leader_mem card_correct hs hR hpop0 hpop1 V hcov hlead

/-! ## O8, O9 — spanning and the descent

A run of `c` slots spanning eligibility is the relation's
`AnchoredRule.SpansEligible`; under a pipelined identity-round schedule
`c = 2` spans (`spansEligible_of_identity`): slot `b − 1` cannot anchor
on slot `b` — one round is one too close — but slot `b + 1` clears
`slotRound + 2`, which is why the thesis's Lemma 10 asks for **two
consecutive** honest leaders. And O9 (thesis Lemma 11), that every slot
below a committed run of eligible span is decided, is the relation's
`decided_below_of_committed_run` at `Odontoceti.exists_least`. -/

end Odontoceti

end LeanDag
