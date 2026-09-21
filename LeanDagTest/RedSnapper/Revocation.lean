import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Fintype.Powerset
import LeanDag.RedSnapper.Revocation.Statement
import LeanDagTest.RedSnapper.Model

/-!
# Witness: vote profiles, the threshold, and exposure

Every definition of `Model/Revocation.lean` and every claim of
`Revocation/Statement.lean` exercised on concrete profiles by `decide`,
before anything is proved from them.

* **`split`**: four validators, two values, validator `0` Byzantine and
  voting both ways, `1` for `true`, `2` for `false`, `3` silent. The
  Byzantine validator is a supporter *and* an opposer, which is the slack
  `f` in the support bound; the silent one is in neither set and not a
  voter. `Exposes` is pinned true at `(Q, R) = (3, 2)` and false at
  `(3, 3)`.
* **`tightFour`**: the paper's tightness construction at `n = 4`, `f = 1`,
  `C = 3`: `R = n + f − C = 2` opposers, the Byzantine one also
  supporting, and `C = 3` supporters — a certificate survives the
  threshold minus one. Applied to `Tight 4 1 3`.
* **`even`**: four correct validators split two and two. No collection
  of all four exposes a side at `3`, matching `⌈4/2⌉ = 2 < 3`; every one
  does at `2`.
* **`revoked`**: exactly `R = n + f − C + 1 = 3` opposers at `C = 3`, so
  the premise of `Sufficient` is live and the conclusion does the work;
  one opposer fewer (`tightFour`) and the conclusion fails.
* **`three`**: three candidate values, the Byzantine validator voting two
  rivals at once; it is one opposer, and rivals to different values all
  count.
* **`slack`**: fewer actual Byzantine validators than the bound.
* **The seam**: at the tight `5f + 1` committee `half ≤ ⌈quorum/2⌉`
  holds; at the tight `3f + 1` committee it fails — the two sides of
  `ExposureAtQuorum`, one each — and every named corollary is
  instantiated at `Fin 4`, `Fin 5`, `Fin 6`.

The hardening batch after the vacuity audit: `Exposes` over a `Q` below
the voter count, so that `∀ S` ranges over several subsets; the support
bound attained at `n + f`, so that the Byzantine slack is indispensable;
`Sufficient` with its premise true; `Tight` refuted outside `f ≤ C ≤ n`;
and the left-hand side of `ExposureIff` refuted at `(4, 3)`.
-/

namespace LeanDagTest

namespace RedSnapper

open LeanDag LeanDag.RedSnapper LeanDag.RedSnapper.Revocation

/-- Validator `0` Byzantine and voting both ways, `1` for `true`, `2` for
`false`, `3` silent. -/
def split : Profile (Fin 4) Bool where
  f := 1
  byzantine := {0}
  card_byzantine := by decide
  votes := fun v =>
    if v = 0 then {true, false} else if v = 1 then {true} else if v = 2 then {false} else ∅
  honest_single := by decide

example : supporters split true = {0, 1} := by decide
example : opposers split true = {0, 2} := by decide
example : voters split = {0, 1, 2} := by decide

-- The support bound with the Byzantine validator counted twice:
-- `2 + 2 ≤ 4 + 1`.
example : SupportBound split true := by unfold SupportBound; decide

-- Sufficiency at `C = 3`: two opposers are below the threshold
-- `n + f − C + 1 = 3`, so the implication holds vacuously. At `C = 2`
-- the conclusion `2 < 2` is false, so the support bound must refuse the
-- premise `4 + 1 + 1 ≤ 2 + 2` — pinned.
example : Sufficient split true 3 := by unfold Sufficient; decide
example : ¬ (4 + 1 + 1 ≤ (opposers split true).card + 2) := by decide

-- Any three voters expose a side at `2`, not at `3`.
example : Exposes split true 3 2 := by unfold Exposes; decide
example : ¬ Exposes split true 3 3 := by unfold Exposes; decide

/-- The tightness construction at `n = 4`, `f = 1`, `C = 3`: opposers
`{0, 1}` with the Byzantine `0` also supporting, supporters `{0, 2, 3}`. -/
def tightFour : Profile (Fin 4) Bool where
  f := 1
  byzantine := {0}
  card_byzantine := by decide
  votes := fun v => if v = 0 then {true, false} else if v = 1 then {false} else {true}
  honest_single := by decide

-- `R = 2 = n + f − C` opposers and `C = 3` supporters at once.
example : (opposers tightFour true).card + 3 = 4 + 1 ∧
    3 ≤ (supporters tightFour true).card := by decide

example : Tight 4 1 3 := by
  unfold Tight
  exact ⟨tightFour, by decide, by decide, by decide⟩

/-- Four correct validators, two for `true` and two for `false`. -/
def even : Profile (Fin 4) Bool where
  f := 0
  byzantine := ∅
  card_byzantine := by decide
  votes := fun v => if v = 0 ∨ v = 1 then {true} else {false}
  honest_single := by decide

-- `⌈4/2⌉ = 2`: all four voters expose a side at `2` and not at `3`.
example : Exposes even true 4 2 := by unfold Exposes; decide
example : ¬ Exposes even true 4 3 := by unfold Exposes; decide
example : 2 ≤ (4 + 1) / 2 ∧ ¬ (3 ≤ (4 + 1) / 2) := by decide

-- The strict-threshold corollary at `n = 4`, `f = 1`: `C = 4` admits
-- `R = 2` (`2C = 8 > 6`); `C = 3`, the quorum at the tight `3f + 1`
-- committee, admits nothing below it (`2C = 6`, not above `6`).
example : ∃ R, 4 + 1 + 1 ≤ 4 + R ∧ R < 4 := ⟨2, by decide⟩
example : ¬ ∃ R, 4 + 1 + 1 ≤ 3 + R ∧ R < 3 := fun ⟨_, h⟩ => by omega

-- The seam: exposure at a quorum holds at the tight `5f + 1` committee
-- and fails at the tight `3f + 1` one.
example : half (Fin 6) ≤ (quorum (Fin 6) + 1) / 2 := by decide
example : ¬ (half (Fin 4) ≤ (quorum (Fin 4) + 1) / 2) := by decide

-- And the threshold at a quorum is `half` in both: `n + f + 1 ≤ quorum + R`
-- first holds at `R = 3`.
example : 4 + 1 + 1 ≤ quorum (Fin 4) + 3 ∧ ¬ (4 + 1 + 1 ≤ quorum (Fin 4) + 2) := by decide
example : 6 + 1 + 1 ≤ quorum (Fin 6) + 3 ∧ ¬ (6 + 1 + 1 ≤ quorum (Fin 6) + 2) := by decide

-- --- hardening batch -------------------------------------------------

-- `Exposes` at a `Q` below the voter count: `∀ S` now ranges over the six
-- pairs of `even`. Each pair exposes a side at `1`; the pair `{0, 2}`
-- splits one and one, so not at `2` — although the pair `{0, 1}` does,
-- which an `∃ S` reading would accept.
example : Exposes even true 2 1 := by unfold Exposes; decide
example : ¬ Exposes even true 2 2 := by unfold Exposes; decide
example : 2 ≤ (({0, 1} : Finset (Fin 4)) ∩ supporters even true).card := by decide

-- The support bound attained: `tightFour` has `3 + 2 = 5 = n + f`, above
-- `n`. The Byzantine slack is indispensable.
example : (supporters tightFour true).card + (opposers tightFour true).card = 4 + 1 := by
  decide
example : ¬ ((supporters tightFour true).card + (opposers tightFour true).card ≤
    Fintype.card (Fin 4)) := by decide
example : SupportBound tightFour true := by unfold SupportBound; decide

/-- `0` Byzantine both ways, `1` and `2` for `false`, `3` for `true`:
exactly `R = n + f − C + 1 = 3` opposers at `C = 3`, two supporters. -/
def revoked : Profile (Fin 4) Bool where
  f := 1
  byzantine := {0}
  card_byzantine := by decide
  votes := fun v => if v = 0 then {true, false} else if v = 3 then {true} else {false}
  honest_single := by decide

-- The premise of `Sufficient` is live and the conclusion holds.
example : 4 + 1 + 1 ≤ (opposers revoked true).card + 3 := by decide
example : (supporters revoked true).card < 3 := by decide
example : Sufficient revoked true 3 := by unfold Sufficient; decide

-- One opposer fewer, and a certificate of size `3` survives: the
-- threshold, not slack, does the work.
example : 4 + 1 ≤ (opposers tightFour true).card + 3 ∧
    ¬ ((supporters tightFour true).card < 3) := by decide

/-- Three values: `0` Byzantine voting both rivals `1` and `2`, `1` for
`0`, `2` for `1`, `3` for `2`. -/
def three : Profile (Fin 4) (Fin 3) where
  f := 1
  byzantine := {0}
  card_byzantine := by decide
  votes := fun v => if v = 0 then {1, 2} else if v = 1 then {0} else if v = 2 then {1} else {2}
  honest_single := by decide

-- The Byzantine validator is one opposer of `0`; rivals to different
-- values all count.
example : opposers three 0 = {0, 2, 3} := by decide
example : supporters three 0 = {1} := by decide
example : Exposes three 0 3 2 := by unfold Exposes; decide

/-- Fewer actual Byzantine validators than the bound. -/
def slack : Profile (Fin 4) Bool where
  f := 1
  byzantine := ∅
  card_byzantine := by decide
  votes := even.votes
  honest_single := by decide

example : SupportBound slack true := by unfold SupportBound; decide

-- `Tight` is refuted outside `f ≤ C ≤ n`: above `n` no certificate can
-- form, below `f` no threshold can be met.
example : ¬ Tight 4 1 5 := fun ⟨P, _, _, h⟩ => by
  have := Finset.card_le_univ (supporters P true)
  simp at this
  omega
example : ¬ Tight 4 2 1 := fun ⟨P, _, h, _⟩ => by
  have := Finset.card_le_univ (opposers P true)
  simp at this
  omega

-- The left-hand side of `ExposureIff` refuted at `(Q, R) = (4, 3)` by
-- `even`, tying the profile to the Prop it witnesses.
example : ¬ (∀ (V W : Type) [Fintype V] [DecidableEq V] [DecidableEq W]
    (P : Profile V W) (x : W), Exposes P x 4 3) :=
  fun h => (by unfold Exposes; decide : ¬ Exposes even true 4 3) (h _ _ even true)

-- The named corollaries, instantiated: both sides false at the tight
-- `3f + 1` committee, both true at `5f + 1`, and split at `n = 5`.
example : StrictAtQuorum (Fin 4) := by unfold StrictAtQuorum; decide
example : StrictAtQuorum (Fin 5) := by unfold StrictAtQuorum; decide
example : StrictAtQuorum (Fin 6) := by unfold StrictAtQuorum; decide
example : ExposureAtQuorum (Fin 4) := by unfold ExposureAtQuorum; decide
example : ExposureAtQuorum (Fin 5) := by unfold ExposureAtQuorum; decide
example : ExposureAtQuorum (Fin 6) := by unfold ExposureAtQuorum; decide
example : ExposureAtQuorum (Fin 11) := by unfold ExposureAtQuorum; decide
example : ThresholdAtQuorum (Fin 4) := by
  intro R
  simp only [quorum, half, Fintype.card_fin]
  change 4 + 1 + 1 ≤ 4 - 1 + R ↔ 2 * 1 + 1 ≤ R
  omega
example : StrictThresholdIff 4 1 3 := ⟨fun ⟨_, h⟩ => by omega, fun h => by omega⟩
example : StrictThresholdIff 4 1 4 := ⟨fun _ => by omega, fun _ => ⟨2, by omega⟩⟩

end RedSnapper

end LeanDagTest
