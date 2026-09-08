import LeanDag.Properties.Arcs.Quality
import LeanDag.FinWhale.Carrier
import LeanDag.Hydrozoan.Helpers.Commit
import LeanDag.Odontoceti.Carrier
import LeanDag.Nemo.Carrier
import LeanDag.Hybrid.Carrier
import LeanDag.OptimalHydrozoan.Carrier
import LeanDag.MahiMahi.Carrier
/-!
# Chain quality for a second and third rule

`docs/target-properties.md` §11.4's last item, checked. The arc is
stated once over `Properties.DagRule`
(`LeanDag/Properties/Arcs/Quality.lean`); the core instantiates it in
`LeanDag/Quality/`. What this file checks is that a rule which never had
the arc gets it by application — no induction, no density proof of its
own, and nothing about its decision relation beyond
`CommitsCandidate`.

**FinWhale** takes the whole of it, including the "at least half"
packaging: its committee is `n = 3f + 2p − 1` with `p ≥ 1`, so
`|Correct| ≥ 2f + 1` and `2f ≤ |Correct|` as CQ2 asks.

**Hydrozoan** takes the coverage bound. It does *not* take CQ2 in
general, and the reason is a real feature of its committee rather than a
gap in the arc: the slack is `f + c` and the bound is
`n ≥ 3f + 2c + k + 1`, which gives `2(f + c) ≤ |Correct|` only when
`c ≤ k + 1`. `card_coveredAt_ge` is the statement that holds at every
configuration, and CQ2 takes the extra condition as a hypothesis for
exactly this reason. Optimal-Hydrozoan is the same universe and the
same fault model, so it lands the same way.

**Odontoceti** and **Hybrid** take the whole of it, both being the
core's `BlockUniverse` at their own committees. **Nemo** takes it at a
different shape again: crash-only, nobody equivocates, so the reliable
set is everyone and the slack is what a majority may miss.

`scripts/audit-mechanisms.py` is what asked for these: the properties
were there and nobody had collected them.
-/

namespace LeanDagTest

open LeanDag LeanDag.Properties LeanDag.Properties.Arcs

section FinWhale

variable {Validator : Type} [Fintype Validator] [DecidableEq Validator]
variable [F : Faults Validator] [P : LeanDag.FinWhale.Params Validator]
variable {BlockId : Type} [LinearOrder BlockId] {Payload : Type}

/-- **CQ1 for FinWhale.** A committed leader's flush covers all but `f`
of the correct validators at every round below it. -/
theorem finWhale_card_coveredAt_ge_of_decided (S : Slots Validator)
    {D : LeanDag.FinWhale.Dag Validator BlockId Payload}
    {V : (LeanDag.FinWhaleProperties.finWhaleRule (Payload := Payload)).View D}
    {k : ℕ} {L : BlockId} {δ : ℕ}
    (h : (LeanDag.FinWhaleProperties.finWhaleRule (Payload := Payload)).Decided S V k (some L))
    (hδ : δ < (D.block L).round) :
    (Correct : Finset Validator).card - F.f ≤
      (coveredAt (LeanDag.FinWhaleProperties.finWhaleRule (Payload := Payload))
        (coreReliability Validator) D L δ).card :=
  card_coveredAt_ge_of_decided LeanDag.FinWhaleProperties.quorate LeanDag.FinWhaleProperties.commitsCandidate h hδ

/-- **CQ2 for FinWhale.** At least half the correct validators, every
round below every commit. -/
theorem finWhale_card_correct_le_two_mul (S : Slots Validator)
    {D : LeanDag.FinWhale.Dag Validator BlockId Payload}
    {V : (LeanDag.FinWhaleProperties.finWhaleRule (Payload := Payload)).View D}
    {k : ℕ} {L : BlockId} {δ : ℕ}
    (h : (LeanDag.FinWhaleProperties.finWhaleRule (Payload := Payload)).Decided S V k (some L))
    (hδ : δ < (D.block L).round) :
    (Correct : Finset Validator).card ≤
      2 * (coveredAt (LeanDag.FinWhaleProperties.finWhaleRule (Payload := Payload))
        (coreReliability Validator) D L δ).card :=
  card_correct_le_two_mul_coveredAt_of_decided LeanDag.FinWhaleProperties.quorate LeanDag.FinWhaleProperties.commitsCandidate
    (by
      simp only [coreReliability_correct, coreReliability_slack]
      have := two_f_add_one_le_card_correct (Validator := Validator)
      omega) h hδ

end FinWhale

section Hydrozoan

variable {Replica : Type} [Fintype Replica] [DecidableEq Replica]
variable [F : LeanDag.Hydrozoan.Faults Replica]
variable {BlockId : Type} [DecidableEq BlockId] [LinearOrder BlockId]

/-- **CQ1 for Hydrozoan**, at its own fault model: all but `f + c` of
the reliable replicas, at every round below a commit. -/
theorem hydrozoan_card_coveredAt_ge_of_decided (S : Slots Replica)
    {U : LeanDag.Hydrozoan.BlockUniverse Replica BlockId}
    {V : LeanDag.Hydrozoan.View U} {k : ℕ} {L : BlockId} {δ : ℕ}
    (h : (LeanDag.Hydrozoan.rule (Replica := Replica) (BlockId := BlockId)).Decided S V k (some L))
    (hδ : δ < (U.block L).round) :
    (LeanDag.Hydrozoan.Correct : Finset Replica).card - (F.f + F.c) ≤
      (coveredAt (LeanDag.Hydrozoan.rule (Replica := Replica) (BlockId := BlockId))
        (LeanDag.Hydrozoan.hzReliability Replica) U L δ).card :=
  card_coveredAt_ge_of_decided LeanDag.Hydrozoan.quorate
    LeanDag.Hydrozoan.commitsCandidate h hδ

end Hydrozoan

section Odontoceti

variable {Validator : Type} [Fintype Validator] [DecidableEq Validator]
variable [F : Faults5 Validator]
variable {B : Type} [LinearOrder B] {Payload : Type}

/-- **CQ2 for Odontoceti.** Its universe is the core's, so the fault
model is too; only the committee bound differs. -/
theorem odontoceti_card_correct_le_two_mul (S : Slots Validator)
    {U : BlockUniverse Validator B Payload}
    {V : LeanDag.View Validator B Payload U} {k : ℕ} {L : B} {δ : ℕ}
    (h : (LeanDag.OdontocetiProperties.odontocetiRule (Payload := Payload)).Decided
      S V k (some L))
    (hδ : δ < (U.block L).round) :
    (Correct : Finset Validator).card ≤
      2 * (coveredAt (LeanDag.OdontocetiProperties.odontocetiRule (Payload := Payload))
        (coreReliability Validator) U L δ).card :=
  card_correct_le_two_mul_coveredAt_of_decided LeanDag.OdontocetiProperties.quorate LeanDag.OdontocetiProperties.commitsCandidate
    (by
      simp only [coreReliability_correct, coreReliability_slack]
      have := two_f_add_one_le_card_correct (Validator := Validator)
      omega) h hδ

end Odontoceti

section Hybrid

variable {Validator : Type} [Fintype Validator] [DecidableEq Validator]
variable [H : LeanDag.HybridFaults Validator]
variable {B : Type} [LinearOrder B] {Payload : Type}

/-- **CQ2 for Hybrid**, at the derived model `f = fb + fc`. -/
theorem hybrid_card_correct_le_two_mul (kt : ℕ) (S : Slots Validator)
    {U : (LeanDag.HybridProperties.hybridRule (Payload := Payload) kt).Universe}
    {V : (LeanDag.HybridProperties.hybridRule (Payload := Payload) kt).View U}
    {k : ℕ} {L : B} {δ : ℕ}
    (h : (LeanDag.HybridProperties.hybridRule (Payload := Payload) kt).Decided S V k (some L))
    (hδ : δ < (U.val.block L).round) :
    (Correct : Finset Validator).card ≤
      2 * (coveredAt (LeanDag.HybridProperties.hybridRule (Payload := Payload) kt)
        (coreReliability Validator) U L δ).card :=
  card_correct_le_two_mul_coveredAt_of_decided (LeanDag.HybridProperties.quorate kt) (LeanDag.HybridProperties.commitsCandidate kt)
    (by
      simp only [coreReliability_correct, coreReliability_slack]
      have := two_f_add_one_le_card_correct (Validator := Validator)
      omega) h hδ

end Hybrid

section Nemo

variable {Validator : Type} [Fintype Validator] [DecidableEq Validator]
variable {B : Type} [DecidableEq B] {Payload : Type}

/-- **CQ1 for Nemo.** Crash-only and equivocation-free, so the reliable
set is every validator and the slack is what a majority may miss. -/
theorem nemo_card_coveredAt_ge_of_decided (hn : 0 < Fintype.card Validator)
    (S : Slots Validator) {U : LeanDag.Nemo.Universe Validator B Payload}
    {V : LeanDag.Nemo.View Validator B Payload U} {k : ℕ} {L : B} {δ : ℕ}
    (h : (LeanDag.NemoProperties.nemoRule (Payload := Payload)).Decided S V k (some L))
    (hδ : δ < (U.block L).round) :
    (LeanDag.NemoProperties.nemoReliability Validator hn).correct.card -
        (LeanDag.NemoProperties.nemoReliability Validator hn).slack ≤
      (coveredAt (LeanDag.NemoProperties.nemoRule (Payload := Payload))
        (LeanDag.NemoProperties.nemoReliability Validator hn) U L δ).card :=
  card_coveredAt_ge_of_decided (LeanDag.NemoProperties.quorate hn) LeanDag.NemoProperties.commitsCandidate h hδ

end Nemo

section OptimalHydrozoan

variable {Replica : Type} [Fintype Replica] [DecidableEq Replica]
variable [O : LeanDag.OptimalHydrozoan.OptimalFaults Replica]
variable {B : Type} [DecidableEq B]

/-- **CQ1 for Optimal-Hydrozoan**, at Hydrozoan's fault model. -/
theorem optimal_card_coveredAt_ge_of_decided (S : Slots Replica)
    {U : (LeanDag.OptimalHydrozoanProperties.optimalRule (BlockId := B)).Universe}
    {V : (LeanDag.OptimalHydrozoanProperties.optimalRule (BlockId := B)).View U}
    {k : ℕ} {L : B} {δ : ℕ}
    (h : (LeanDag.OptimalHydrozoanProperties.optimalRule (BlockId := B)).Decided S V k (some L))
    (hδ : δ < (U.block L).round) :
    (LeanDag.Hydrozoan.Correct : Finset Replica).card - (O.f + O.c) ≤
      (coveredAt (LeanDag.OptimalHydrozoanProperties.optimalRule (BlockId := B))
        (LeanDag.Hydrozoan.hzReliability Replica) U L δ).card :=
  card_coveredAt_ge_of_decided LeanDag.OptimalHydrozoanProperties.quorate
    LeanDag.OptimalHydrozoanProperties.commitsCandidate h hδ

end OptimalHydrozoan

section MahiMahi

variable {Validator : Type} [Fintype Validator] [DecidableEq Validator]
variable [F : Faults Validator]
variable {B : Type} [LinearOrder B] {Payload : Type}

/-- **CQ2 for Mahi-Mahi**, at every wave width: its universe is the
core's, so the fault model is the core's and the arc applies whole. -/
theorem mahiMahi_card_correct_le_two_mul (w : ℕ) (S : Slots Validator)
    {U : BlockUniverse Validator B Payload}
    {V : LeanDag.View Validator B Payload U} {k : ℕ} {L : B} {δ : ℕ}
    (h : (LeanDag.MahiMahiProperties.mahiMahiRule (Payload := Payload) w).Decided
      S V k (some L))
    (hδ : δ < (U.block L).round) :
    (Correct : Finset Validator).card ≤
      2 * (coveredAt (LeanDag.MahiMahiProperties.mahiMahiRule (Payload := Payload) w)
        (coreReliability Validator) U L δ).card :=
  card_correct_le_two_mul_coveredAt_of_decided (LeanDag.MahiMahiProperties.quorate w) (LeanDag.MahiMahiProperties.commitsCandidate w)
    (by
      simp only [coreReliability_correct, coreReliability_slack]
      have := two_f_add_one_le_card_correct (Validator := Validator)
      omega) h hδ

end MahiMahi

#print axioms LeanDagTest.finWhale_card_coveredAt_ge_of_decided
#print axioms LeanDagTest.finWhale_card_correct_le_two_mul
#print axioms LeanDagTest.hydrozoan_card_coveredAt_ge_of_decided
#print axioms LeanDagTest.odontoceti_card_correct_le_two_mul
#print axioms LeanDagTest.hybrid_card_correct_le_two_mul
#print axioms LeanDagTest.nemo_card_coveredAt_ge_of_decided
#print axioms LeanDagTest.optimal_card_coveredAt_ge_of_decided
#print axioms LeanDagTest.mahiMahi_card_correct_le_two_mul

end LeanDagTest
