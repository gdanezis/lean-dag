import LeanDag.Scheme.HybridRow.Statement
import LeanDag.Scheme.Model.Async
/-!
# Every row, safe and live — statement

`docs/scheme.md` §12. The family's theorems are stated over any row
meeting their hypotheses; here every row is shown to meet them, so each is
safe, live under partial synchrony and, if asynchronous, ready for the
count of §11. At every local vote:

* **On the core's universes** (`CoreRows`), `n ≥ 3f + 1`: Cordial Miners
  PS and Async are safe and live (progress and inclusion).
* **Under the hybrid fault model** (`HybridRows`), `n ≥ 3f + 2c + k + 1`,
  on records that also ask self-reference (`HybridValid`): Orcaella and
  Async Orcaella from `n ≥ 5f + 3c + 1`, Hybrid Mysticeti, Hybrid
  Mahi-Mahi at every wave of three or more, and, with no Byzantine
  replica, Nemo-Nemo and Async Nemo-Nemo, are safe and live.
* **The asynchronous rows are ready for the count** (`AsyncRows`): Mahi-Mahi
  at waves four and five, Blue Bottle Async, Cordial Miners Async, Async
  Orcaella, Async Nemo-Nemo and Hybrid Mahi-Mahi at waves four and five
  meet `Params.AsyncReady` at `q = n − f − c`, at one buffer round or two.

Statements only; the proofs are `Proof.lean`.
-/

namespace LeanDag

namespace Scheme

namespace Rows

open Properties

/-- A row's carrier at the core's fault model is safe and lives. -/
def SafeLivesCore {Validator BlockId Payload : Type} [Fintype Validator] [DecidableEq Validator]
    [LinearOrder BlockId] [Faults Validator] (p : Params)
    (σ : VoteSel Validator BlockId Payload ValidWrt Correct) : Prop :=
  Safe (schemeRule p σ Correct) ∧
    Support.Lives (R := schemeRule p σ Correct) (familySupport p σ Correct)
      (coreReliability Validator)

/-- A row's carrier at the hybrid fault model, with self-reference, is safe
and lives. -/
def SafeLivesHybrid {Replica BlockId : Type} [Fintype Replica] [DecidableEq Replica]
    [LinearOrder BlockId] [Hydrozoan.Faults Replica] (p : Params)
    (σ : VoteSel Replica BlockId Unit HybridValid Hydrozoan.NonByzantine) : Prop :=
  Safe (schemeRule p σ Hydrozoan.NonByzantine) ∧
    Support.Lives (R := schemeRule p σ Hydrozoan.NonByzantine)
      (familySupport p σ Hydrozoan.NonByzantine) (Hydrozoan.hzReliability Replica)

/-- **Cordial Miners, safe and live on the core's universes.** -/
def CoreRows : Prop :=
  ∀ (Validator BlockId Payload : Type) [Fintype Validator] [DecidableEq Validator]
    [LinearOrder BlockId] [F : Faults Validator]
    (σ : VoteSel Validator BlockId Payload ValidWrt Correct), σ.Local →
    SafeLivesCore (Params.cordialMinersPS (Fintype.card Validator) F.f) σ ∧
      SafeLivesCore (Params.cordialMinersAsync (Fintype.card Validator) F.f) σ

/-- **The rows with crash faults, safe and live under the hybrid fault
model.** -/
def HybridRows : Prop :=
  ∀ (Replica BlockId : Type) [Fintype Replica] [DecidableEq Replica] [LinearOrder BlockId]
    [F : Hydrozoan.Faults Replica]
    (σ : VoteSel Replica BlockId Unit HybridValid Hydrozoan.NonByzantine), σ.Local →
    (5 * F.f + 3 * F.c + 1 ≤ Fintype.card Replica →
      SafeLivesHybrid (Params.orcaella (Fintype.card Replica) F.f F.c) σ ∧
        SafeLivesHybrid (Params.asyncOrcaella (Fintype.card Replica) F.f F.c) σ) ∧
    SafeLivesHybrid (Params.hybridMysticeti (Fintype.card Replica) F.f F.c) σ ∧
    (∀ w, 3 ≤ w → SafeLivesHybrid (Params.hybridMahiMahi w (Fintype.card Replica) F.f F.c) σ) ∧
    (F.f = 0 →
      SafeLivesHybrid (Params.nemoNemo (Fintype.card Replica) F.c) σ ∧
        SafeLivesHybrid (Params.asyncNemoNemo (Fintype.card Replica) F.c) σ)

/-- **The asynchronous rows are ready for the count**, at `q = n − f − c`:
one buffer round for Mahi-Mahi and Hybrid Mahi-Mahi at wave four, Blue
Bottle Async, Async Orcaella and Async Nemo-Nemo; two for Mahi-Mahi and
Hybrid Mahi-Mahi at wave five and Cordial Miners Async. -/
def AsyncRows : Prop :=
  ∀ n f c : ℕ,
    (3 * f + 1 ≤ n →
      (Params.mahiMahi 4 n f).AsyncReady n f (n - f) 1 ∧
      (Params.mahiMahi 5 n f).AsyncReady n f (n - f) 2 ∧
      (Params.cordialMinersAsync n f).AsyncReady n f (n - f) 2) ∧
    (5 * f + 1 ≤ n → (Params.blueBottleAsync n f).AsyncReady n f (n - f) 1) ∧
    (5 * f + 3 * c + 1 ≤ n → (Params.asyncOrcaella n f c).AsyncReady n f (n - f - c) 1) ∧
    (2 * c + 1 ≤ n → (Params.asyncNemoNemo n c).AsyncReady n 0 (n - c) 1) ∧
    (3 * f + 2 * c + 1 ≤ n →
      (Params.hybridMahiMahi 4 n f c).AsyncReady n f (n - f - c) 1 ∧
      (Params.hybridMahiMahi 5 n f c).AsyncReady n f (n - f - c) 2)

/-- Every row, safe and live. -/
def Statement : Prop := CoreRows ∧ HybridRows ∧ AsyncRows

end Rows

end Scheme

end LeanDag
