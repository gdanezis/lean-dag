import Mathlib.Data.Fintype.Card
import Mathlib.Data.Finset.Card

/-!
# Validators, Byzantine faults, and the two thresholds

Trusted core: the system model of the paper's Preliminaries and the two
thresholds every rule of both protocols counts against. Definitions
only — every lemma about them lives in `Helpers/`.

A static set of `n` validators, of which at most `f` are Byzantine; the
rest are correct. Byzantine validators may deviate arbitrarily — in the
structural model this surfaces as authoring several blocks in one round
and as stances that follow no rule. There is no crash class: the paper
has none.

The paper fixes `n = 3f + 1` and writes every threshold of the first
protocol as `2f + 1`, then fixes `n = 5f + 1` and writes `4f + 1` and
`2f + 1`. The arc states both protocols over the committee bound alone
(D1 of `docs/red-snapper.md`) with two thresholds:

* `quorum = n − f` — the certificate threshold at `n ≥ 3f + 1` and the
  full-certificate threshold at `n ≥ 5f + 1`; two quorums share at least
  `n − 2f ≥ f + 1` validators, hence a correct one.
* `half = 2f + 1` — the skip and unlock threshold at `n ≥ 3f + 1`, and
  the half-certificate and refutation threshold at `n ≥ 5f + 1`; it is
  the revocation threshold of the paper's Theorem "vote revocation" at
  `C = n − f` (`Revocation/Statement.lean`).

At the tight committee `n = 3f + 1` the two coincide (`n − f = 2f + 1`),
which is why the paper writes one number there. The second protocol's
committee bound is the mixin `Five`; it is exactly the exposure
condition of the paper's Corollary "exposure for `C = Q = n − f`".
-/

namespace LeanDag

namespace RedSnapper

/-- The fault model: at most `f` of `n ≥ 3f + 1` validators are
Byzantine.

`byzantine` is the *actual* fault assignment of a run; `f` is what the
protocol is configured to tolerate. -/
class Faults (Validator : Type*) [Fintype Validator] [DecidableEq Validator] where
  /-- The Byzantine fault bound. -/
  f : ℕ
  /-- The Byzantine validators: may deviate arbitrarily, in particular
  equivocate and declare stances that follow no rule. -/
  byzantine : Finset Validator
  /-- There are at least `3f + 1` validators. -/
  card_validators : 3 * f + 1 ≤ Fintype.card Validator
  /-- At most `f` validators are Byzantine. -/
  card_byzantine : byzantine.card ≤ f

section Thresholds

variable (Validator : Type*) [Fintype Validator] [DecidableEq Validator] [F : Faults Validator]

/-- `quorum = n − f`: the number of distinct authors a transaction
certificate counts at `n ≥ 3f + 1`, and a full certificate or a full
unlock certificate at `n ≥ 5f + 1`. Also the least number of distinct
round-parent authors a block references (`ValidWrt.quorum`). -/
def quorum : ℕ := Fintype.card Validator - F.f

/-- `half = 2f + 1`: the number of distinct authors a skip certificate or
an unlock certificate counts at `n ≥ 3f + 1`, and a half certificate or
a refutation at `n ≥ 5f + 1`. The revocation threshold for certificates
of size `n − f`. -/
def half : ℕ := 2 * F.f + 1

/-- The committee bound of the second protocol, `n ≥ 5f + 1`, as a mixin
on `Faults`: results of the `5f + 1` section take `[Five Validator]`,
those of the `3f + 1` section do not. -/
class Five : Prop where
  /-- There are at least `5f + 1` validators. -/
  card_validators : 5 * F.f + 1 ≤ Fintype.card Validator

end Thresholds

section Pools

variable {Validator : Type*} [Fintype Validator] [DecidableEq Validator] [F : Faults Validator]

/-- The correct validators: everyone not Byzantine. The pool that every
quorum-intersection argument lands in, and that liveness counts. -/
def Correct : Finset Validator := F.byzantineᶜ

end Pools

end RedSnapper

end LeanDag
