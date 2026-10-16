import Mathlib.Data.Nat.Basic
/-!
# The unified decider — its parameters

`docs/scheme.md` §1: one decider for the uncertified-DAG rules of the
Mysticeti codebase, parameterised by the flat record below. A row of the
scheme's table is a `Params` built from the committee size `n`, the
Byzantine bound `f` and the crash bound `c`; the safety and liveness
conditions the scheme states for a row are `TwoRound`, `ThreeRound` and
`Live`.

Definitions only; the claims about them are `Scheme/Table/Statement.lean`.
-/

namespace LeanDag

namespace Scheme

/-- **The parameters of one decider.** `waveLength` rounds per wave; when
`voteIsCert` a vote is its own certificate; thresholds count distinct
authors. -/
structure Params where
  /-- Rounds per wave: propose, buffer rounds, vote, decision. -/
  waveLength : ℕ
  /-- A vote is a certificate, and the vote round is the decision round. -/
  voteIsCert : Bool
  /-- Certificates a direct commit needs. -/
  commitThreshold : ℕ
  /-- Blames a direct skip needs. -/
  skipThreshold : ℕ
  /-- Votes a certificate needs. -/
  certThreshold : ℕ
  /-- Certificates in the anchor's history an indirect commit needs. -/
  linkSize : ℕ

namespace Params

/-! ## The rows of the table -/

/-- Cordial Miners, partially synchronous: `n = 3f + 1`, no direct skip. -/
def cordialMinersPS (n f : ℕ) : Params := ⟨3, false, n - f, n, n - f, 1⟩

/-- Cordial Miners, asynchronous: two buffer rounds. -/
def cordialMinersAsync (n f : ℕ) : Params := ⟨5, false, n - f, n, n - f, 1⟩

/-- Mysticeti: `n = 3f + 1`. -/
def mysticeti (n f : ℕ) : Params := ⟨3, false, n - f, n - f, n - f, 1⟩

/-- Mahi-Mahi, at wave `w`, four or five. -/
def mahiMahi (w n f : ℕ) : Params := ⟨w, false, n - f, n - f, n - f, 1⟩

/-- Blue Bottle, partially synchronous: `n = 5f + 1`, two rounds. -/
def blueBottlePS (n f : ℕ) : Params := ⟨2, true, n - f, n - f, n - f, n - 3 * f⟩

/-- Blue Bottle, asynchronous: one buffer round. -/
def blueBottleAsync (n f : ℕ) : Params := ⟨3, true, n - f, n - f, n - f, n - 3 * f⟩

/-- Orcaella: `n = 5f + 3c + 1`, Byzantine and crash faults apart. -/
def orcaella (n f c : ℕ) : Params :=
  ⟨2, true, n - f - c, 4 * f + 2 * c + 1, n - f - c, n - 3 * f - 2 * c⟩

/-- Nemo-Nemo: crash faults only, `n = 2c + 1`, no direct skip. -/
def nemoNemo (n c : ℕ) : Params := ⟨2, true, n - c, n, n - c, 1⟩

/-- Async Orcaella (derived): Orcaella with one buffer round. -/
def asyncOrcaella (n f c : ℕ) : Params :=
  ⟨3, true, n - f - c, 4 * f + 2 * c + 1, n - f - c, n - 3 * f - 2 * c⟩

/-- Async Nemo-Nemo (derived). -/
def asyncNemoNemo (n c : ℕ) : Params := ⟨3, true, n - c, n, n - c, 1⟩

/-- Hybrid Mysticeti (derived): `n = 3f + 2c + 1`, three rounds. -/
def hybridMysticeti (n f c : ℕ) : Params :=
  ⟨3, false, 2 * f + c + 1, (n + f + 1) / 2, (n + f + 2) / 2, 1⟩

/-- Hybrid Mahi-Mahi (derived), at wave `w`. -/
def hybridMahiMahi (w n f c : ℕ) : Params :=
  ⟨w, false, 2 * f + c + 1, (n + f + 1) / 2, (n + f + 2) / 2, 1⟩

/-! ## The conditions the scheme states -/

/-- **The two-round inequalities**, with `q` references per block: a direct
skip is consistent with a later indirect commit, a direct commit with an
indirect decision on a twin, and a direct commit is found again through any
anchor (`link ≤ commit + q − n − f`, stated without subtraction). -/
def TwoRound (p : Params) (n f q : ℕ) : Prop :=
  n + f + 1 ≤ p.skipThreshold + p.linkSize ∧
  n + f + 1 ≤ p.commitThreshold + p.linkSize ∧
  p.linkSize + n + f ≤ p.commitThreshold + q

/-- **The three-round inequalities**: certificates are unique, a direct
skip excludes a certificate, and a direct commit is found again through
any anchor. -/
def ThreeRound (p : Params) (n f q : ℕ) : Prop :=
  n + f + 1 ≤ 2 * p.certThreshold ∧
  n + f + 1 ≤ p.skipThreshold + p.certThreshold ∧
  n + f + 1 ≤ p.commitThreshold + q

/-- **The two-round inequalities where nobody equivocates**: the two-round
inequalities at `f = 0` without the one against an equivocating twin. -/
def TwoRoundCrash (p : Params) (n q : ℕ) : Prop :=
  n + 1 ≤ p.skipThreshold + p.linkSize ∧
  p.linkSize + n ≤ p.commitThreshold + q

/-- **The three-round inequalities where nobody equivocates**: the
three-round inequalities at `f = 0` without the one making certificates
unique. -/
def ThreeRoundCrash (p : Params) (n q : ℕ) : Prop :=
  n + 1 ≤ p.skipThreshold + p.certThreshold ∧
  n + 1 ≤ p.commitThreshold + q

/-- **The rows the inequalities cover**: a two-round row with a positive
link meeting `TwoRound n f q`, a three-round row with a link of one
certificate meeting `ThreeRound n f q`, and at `f = 0` the same with
`TwoRoundCrash n q`, or with `ThreeRoundCrash n q` and a positive
certificate threshold. -/
def Covered (p : Params) (n f q : ℕ) : Prop :=
  (p.voteIsCert = true ∧ 2 ≤ p.waveLength ∧ 1 ≤ p.linkSize ∧ p.TwoRound n f q) ∨
  (p.voteIsCert = false ∧ 3 ≤ p.waveLength ∧ p.linkSize = 1 ∧ p.ThreeRound n f q) ∨
  (p.voteIsCert = true ∧ 2 ≤ p.waveLength ∧ 1 ≤ p.linkSize ∧ f = 0 ∧ p.TwoRoundCrash n q) ∨
  (p.voteIsCert = false ∧ 3 ≤ p.waveLength ∧ p.linkSize = 1 ∧ 1 ≤ p.certThreshold ∧ f = 0 ∧
    p.ThreeRoundCrash n q)

/-- **Liveness**: every threshold is reachable by the correct validators. -/
def Live (p : Params) (n f c : ℕ) : Prop :=
  p.commitThreshold ≤ n - f - c ∧ p.skipThreshold ≤ n - f - c ∧ p.certThreshold ≤ n - f - c

end Params

end Scheme

end LeanDag
