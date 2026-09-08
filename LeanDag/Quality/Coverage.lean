import LeanDag.DoS.Density
import LeanDag.Mysticeti.Properties
import LeanDag.Properties.Arcs.Quality
/-!
# Chain quality: asynchronous coverage

`chain-quality.md` §3, CQP1 — **CQ1**, **CQ2**, **CQ3**. Every commit
flushes the entire causal cone of the committed leader, and the quorum
structure forces every layer of a valid cone to carry blocks from all
but at most `f` of the correct validators — with no synchrony
assumption and no populated rounds in the hypotheses. The metric is
per-round author coverage rather than a block count, which an
equivocator could inflate. The generic arc lives in
`Properties/Arcs/Quality.lean`; this file names the core's instance.
-/

namespace LeanDag

open LeanDag.Properties LeanDag.Properties.Arcs

variable {Validator : Type} [Fintype Validator] [DecidableEq Validator]
variable [F : Faults Validator]
variable {BlockId : Type} [DecidableEq BlockId] {Payload : Type}
variable {U : BlockUniverse Validator BlockId Payload}
variable {b L : BlockId} {δ : ℕ}

/-! The correct validators whose round-`δ` block a cone carries are
`Arcs.coveredAt` at the core's rule and reliability — the complement,
within `Correct`, of `missingAt` (`Arcs.coveredAt_eq_sdiff`). -/

/-- **CQ1, the count.** A valid block's cone covers all but at most `f`
of the correct validators, at every round below it. Purely structural:
density (D25) plus the partition. -/
theorem card_coveredAt_ge (hb : b ∈ U.ids) (hδ : δ < (U.block b).round) :
    (Correct : Finset Validator).card - F.f ≤ (Arcs.coveredAt (MysticetiProperties.mysticetiRule (Payload := Payload))
      (coreReliability Validator) U b δ).card :=
  Arcs.card_coveredAt_ge (R := MysticetiProperties.mysticetiRule)
    MysticetiProperties.quorate hb hδ

/-! ## Where the arc depends on the rule

Exactly one step: a committed block is a candidate at the slot's round,
which is `Properties.CommitsCandidate` (`Properties/Candidate.lean`).
Everything above is about valid DAGs alone. -/

section Decided

variable [S : Slots Validator]

/-- **The arc's one rule-dependent step**: a committed block is a block.
`Properties.CommitsCandidate` at the core. -/
theorem mem_ids_of_decided {V : View Validator BlockId Payload U}
    {k : ℕ} (h : Decided U V k (some L)) : L ∈ U.ids :=
  (MysticetiProperties.commitsCandidate (Payload := Payload) S U V k L h).1

/-- **CQ1.** A committed leader's flush covers all but at most `f` of
the correct validators at every round below it — any route, any view,
no synchrony. -/
theorem card_coveredAt_ge_of_decided {V : View Validator BlockId Payload U}
    {k : ℕ} (h : Decided U V k (some L)) (hδ : δ < (U.block L).round) :
    (Correct : Finset Validator).card - F.f ≤ (Arcs.coveredAt (MysticetiProperties.mysticetiRule (Payload := Payload))
      (coreReliability Validator) U L δ).card :=
  Arcs.card_coveredAt_ge_of_decided (R := MysticetiProperties.mysticetiRule)
    MysticetiProperties.quorate
    MysticetiProperties.commitsCandidate h hδ

/-- **CQ2 (the half, exactly).** Every commit carries, at every round
below it, blocks from at least half of the correct validators:
`|Correct| ≤ 2·|covered|`, since `|Correct| ≥ 2f + 1`. -/
theorem card_correct_le_two_mul_coveredAt_of_decided
    {V : View Validator BlockId Payload U} {k : ℕ}
    (h : Decided U V k (some L)) (hδ : δ < (U.block L).round) :
    (Correct : Finset Validator).card ≤ 2 * (Arcs.coveredAt (MysticetiProperties.mysticetiRule (Payload := Payload))
      (coreReliability Validator) U L δ).card :=
  Arcs.card_correct_le_two_mul_coveredAt_of_decided
    (R := MysticetiProperties.mysticetiRule) MysticetiProperties.quorate
    MysticetiProperties.commitsCandidate
    (by
      simp only [coreReliability_correct, coreReliability_slack]
      have := two_f_add_one_le_card_correct (Validator := Validator)
      omega) h hδ

/-- A cone block of a committed slot is in the ledger — the one
unfolding both CQ3 and CQ6 rest on. -/
theorem mem_ledgerSet_of_mem_history {g : ℕ → Option BlockId} {n k : ℕ}
    (hg : g k = some L) (hk : k < n) (hL : L ∈ U.ids)
    (hb : b ∈ history U L) : b ∈ ledgerSet U g n :=
  Arcs.mem_ledgerSetOf_of_mem_history (R := MysticetiProperties.mysticetiRule) hg hk hL hb

/-- **CQ3 (ledger coverage, cumulative).** For a verdict assignment `g`
of a view with a committed slot `k < n` whose leader sits at round `r`:
for every `δ < r`, at least `|Correct| − f` correct validators each
have a round-`δ` block in the ledger `ledgerSet U g n`. The set is
exhibited (`coveredAt`), so no choice and no decidability of the
ledger is needed; view-independence is `ledgerSet_agree`. -/
theorem ledger_coverage {V : View Validator BlockId Payload U}
    {g : ℕ → Option BlockId} {n k : ℕ}
    (hdec : Decided U V k (some L)) (hg : g k = some L) (hk : k < n)
    (hδ : δ < (U.block L).round) :
    ∃ S : Finset Validator, S ⊆ (Correct : Finset Validator) ∧
      (Correct : Finset Validator).card - F.f ≤ S.card ∧
      ∀ v ∈ S, ∃ i ∈ ledgerSet U g n,
        (U.block i).creator = v ∧ (U.block i).round = δ :=
  Arcs.ledger_coverage MysticetiProperties.quorate
    MysticetiProperties.commitsCandidate hdec hg hk hδ

end Decided

end LeanDag
