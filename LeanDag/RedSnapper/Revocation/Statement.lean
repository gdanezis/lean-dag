import LeanDag.RedSnapper.Model.Faults
import LeanDag.RedSnapper.Model.Revocation

/-!
# The limits of vote revocation — statement

RS1: the paper's protocol-independent section, "Fundamental limits of
vote revocation", in full, and its corollaries at the arc's two
thresholds.

* **The support bound.** In any profile the supporters of `x` and the
  opposers of `x` number at most `n + f` together: a correct validator
  is in at most one of the two sets, a Byzantine one in at most both.
  This is the whole mechanism of the section.
* **Theorem "vote revocation threshold".** If `R ≥ n + f − C + 1`
  validators oppose `x`, fewer than `C` support it, so no certificate of
  size `C` for `x` exists — stated subtraction-free as
  `n + f + 1 ≤ R + C → supporters < C` — and the threshold is tight: at
  `R = n + f − C` some profile still carries `C` supporters.
* **Theorem "exposure of the revocation threshold".** Every collection
  of `Q` voters contains `R` supporters of `x` or `R` opposers, in every
  profile, if and only if `⌈Q/2⌉ ≥ R`.
* **Corollary "strict threshold".** A threshold `R < C` sufficient for
  revocation exists iff `2C > n + f + 1`.
* **Corollaries at `C = n − f`.** At the arc's `quorum`, the minimum
  revocation threshold is `half = 2f + 1`; it is strictly below the
  quorum iff `n ≥ 3f + 2`; and a quorum of votes always exposes it iff
  `n ≥ 5f + 1` — the `Five` premise of the second protocol
  (`docs/red-snapper.md` §0, D1).

Tightness and the reverse exposure direction are existence claims; the
witness profiles are exhibited over `Fin n`.
-/

namespace LeanDag

namespace RedSnapper

namespace Revocation

section Profiles

variable {Validator Value : Type*} [Fintype Validator] [DecidableEq Validator]
  [DecidableEq Value]

/-- **The support bound**: `|supporters x| + |opposers x| ≤ n + f`. -/
def SupportBound (P : Profile Validator Value) (x : Value) : Prop :=
  (supporters P x).card + (opposers P x).card ≤ Fintype.card Validator + P.f

/-- **Revocation is sufficient** at `R ≥ n + f − C + 1`: if that many
validators oppose `x`, fewer than `C` support it, so no certificate of
size `C` for `x` can have formed anywhere — hidden or not. Stated
subtraction-free: `n + f + 1 ≤ |opposers x| + C`. -/
def Sufficient (P : Profile Validator Value) (x : Value) (C : ℕ) : Prop :=
  Fintype.card Validator + P.f + 1 ≤ (opposers P x).card + C →
    (supporters P x).card < C

/-- **A collection of `Q` voters exposes one side at `R`**: every set of
`Q` validators that have voted contains at least `R` supporters of `x`
or at least `R` opposers of `x`.

A Byzantine voter of `S` that voted both ways is counted on both sides,
so for one profile this is more permissive than what a validator holding
`S`'s votes observes; `ExposureIff` quantifies over every profile and is
exactly the paper's theorem, but a protocol consuming exposure locally
must count one vote per validator itself. -/
def Exposes (P : Profile Validator Value) (x : Value) (Q R : ℕ) : Prop :=
  ∀ S : Finset Validator, S ⊆ voters P → S.card = Q →
    R ≤ (S ∩ supporters P x).card ∨ R ≤ (S ∩ opposers P x).card

end Profiles

/-- **The threshold is tight**: at `R = n + f − C` opposers — stated as
`|opposers| + C = n + f` — some profile on `n` validators with fault
bound `f` still carries `C` supporters of the value, so no smaller
threshold suffices. Two values suffice: `true` is the value voted, `false`
its rival. -/
def Tight (n f C : ℕ) : Prop :=
  ∃ P : Profile (Fin n) Bool, P.f = f ∧
    (opposers P true).card + C = n + f ∧ C ≤ (supporters P true).card

/-- **Exposure, both directions**: every profile on every validator type
exposes one side of `x` among any `Q` voters at threshold `R` if and only
if `⌈Q/2⌉ ≥ R`, written `R ≤ (Q + 1) / 2` in floor division. -/
def ExposureIff (Q R : ℕ) : Prop :=
  (∀ (Validator Value : Type) [Fintype Validator] [DecidableEq Validator]
      [DecidableEq Value] (P : Profile Validator Value) (x : Value),
      Exposes P x Q R) ↔
    R ≤ (Q + 1) / 2

/-- **A strict threshold exists** — some `R < C` with `R ≥ n + f − C + 1`,
subtraction-free `n + f + 1 ≤ C + R` — if and only if `2C > n + f + 1`. -/
def StrictThresholdIff (n f C : ℕ) : Prop :=
  (∃ R, n + f + 1 ≤ C + R ∧ R < C) ↔ n + f + 1 < 2 * C

section Committee

variable (Validator : Type*) [Fintype Validator] [DecidableEq Validator] [F : Faults Validator]

/-- **The revocation threshold at `C = quorum` is `half`**: `R` opposers
suffice, `n + f + 1 ≤ quorum + R`, exactly when `half ≤ R`. -/
def ThresholdAtQuorum : Prop :=
  ∀ R, Fintype.card Validator + F.f + 1 ≤ quorum Validator + R ↔ half Validator ≤ R

/-- **The threshold is strict at `C = quorum`** — `half < quorum` — if and
only if `n ≥ 3f + 2`. At the tight committee `n = 3f + 1` the two
coincide and revocation needs a full quorum of opposers. -/
def StrictAtQuorum : Prop :=
  half Validator < quorum Validator ↔ 3 * F.f + 2 ≤ Fintype.card Validator

/-- **A quorum of votes exposes the threshold** — `⌈quorum/2⌉ ≥ half` —
if and only if `n ≥ 5f + 1`. The right-hand side is the `Five` premise:
this is where the second protocol's committee comes from. -/
def ExposureAtQuorum : Prop :=
  half Validator ≤ (quorum Validator + 1) / 2 ↔ 5 * F.f + 1 ≤ Fintype.card Validator

end Committee

/-- The limits of vote revocation: the support bound and sufficiency for
every profile, tightness for every `f ≤ C ≤ n`, the exposure
characterisation for every `Q` and `R`, the strict-threshold corollary
for every `n`, `f`, `C`, and the three corollaries at the arc's
thresholds for every fault configuration. -/
def Statement : Prop :=
  (∀ (Validator Value : Type) [Fintype Validator] [DecidableEq Validator]
      [DecidableEq Value] (P : Profile Validator Value) (x : Value) (C : ℕ),
      SupportBound P x ∧ Sufficient P x C) ∧
  (∀ n f C : ℕ, f ≤ C → C ≤ n → Tight n f C) ∧
  (∀ Q R : ℕ, ExposureIff Q R) ∧
  (∀ n f C : ℕ, StrictThresholdIff n f C) ∧
  (∀ (Validator : Type) [Fintype Validator] [DecidableEq Validator] [Faults Validator],
      ThresholdAtQuorum Validator ∧ StrictAtQuorum Validator ∧ ExposureAtQuorum Validator)

end Revocation

end RedSnapper

end LeanDag
