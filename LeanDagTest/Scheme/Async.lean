import LeanDag.Scheme.Async.Proof
import LeanDag.Scheme.Model.LeastSel
import LeanDagTest.MahiMahi.Model
/-!
# The asynchronous rows on data

Four validators, validator `0` Byzantine, `f = 1`, `q = 3`
(`LeanDagTest/Model.lean`), at the Mahi-Mahi row and the least vote.

* On `full4` every round-`0` block is good at waves four and five.
* `starve4` starves validator `1`'s round-`0` block: it is referenced only
  along validator `1`'s own chain, and every other block references
  `{0, 2, 3}` one round down. The good set is `{0, 2, 3}` at one, two and
  three buffer rounds alike (waves four, five and six), its honest part
  `2 = q − f`: the count of two buffer rounds is tight, and a third buffer
  round adds nothing.
-/

namespace LeanDagTest

namespace Scheme

open LeanDag LeanDag.Scheme

/-- The least vote on the four-validator universes. -/
abbrev σ4 : VoteSel (Fin 4) (Fin 24) Unit ValidWrt Correct := leastSel

example : goodAt (Params.mahiMahi 4 4 1) σ4 full4 0 = {0, 1, 2, 3} := by decide
example : goodAt (Params.mahiMahi 5 4 1) σ4 full4 0 = {0, 1, 2, 3} := by decide

/-- Validator `v`'s round-`m` block references, one round down, `{0, 1, 2}`
for `v = 1` and `{0, 2, 3}` otherwise. -/
def starveRefs (m v : ℕ) : Finset (Fin 24) :=
  Finset.univ.filter (fun j : Fin 24 => j.val / 4 + 1 = m ∧
    (if v = 1 then j.val % 4 ≠ 3 else j.val % 4 ≠ 1))

/-- Block `4m + v` is validator `v`'s round-`m` block. -/
def starveBlk : Fin 24 → Block (Fin 4) (Fin 24) Unit := fun i =>
  { round := i.val / 4, creator := ⟨i.val % 4, Nat.mod_lt _ (by omega)⟩,
    refs := starveRefs (i.val / 4) (i.val % 4), payload := () }

/-- Six rounds starving validator `1`'s round-`0` block. -/
def starve4 : BlockUniverse (Fin 4) (Fin 24) Unit where
  ids := Finset.univ
  block := starveBlk
  complete := by decide
  valid := by decide
  no_equivocation := by decide

example : goodAt (Params.mahiMahi 4 4 1) σ4 starve4 0 = {0, 2, 3} := by decide
example : goodAt (Params.mahiMahi 5 4 1) σ4 starve4 0 = {0, 2, 3} := by decide
example : goodAt (Params.mahiMahi 6 4 1) σ4 starve4 0 = {0, 2, 3} := by decide
example : (goodAt (Params.mahiMahi 6 4 1) σ4 starve4 0 ∩ Correct).card = 3 - 1 := by decide

/-- The two-buffer count on the core's universe at the Mahi-Mahi row of wave
five: its hypotheses on the record are the fault model's, and it gives
`f + 1` honest good validators. -/
example {Validator : Type} [Fintype Validator] [DecidableEq Validator] [F : Faults Validator]
    {BlockId : Type} [LinearOrder BlockId] {Payload : Type}
    (σ : VoteSel Validator BlockId Payload ValidWrt Correct)
    (U : BlockUniverse Validator BlockId Payload) (r : ℕ) (T : Finset Validator)
    (hT : T.Nonempty) (hpop3 : PopulatedOn U T (r + 3)) (hpop : PopulatedOn U T (r + 4))
    (hcm : quorumCard Validator ≤ T.card) :
    quorumCard Validator ≤
      (goodAt (Params.mahiMahi 5 (Fintype.card Validator) F.f) σ U r ∩ Correct).card + F.f :=
  Async.goodCard Validator BlockId Payload ValidWrt (quorumCard Validator) Correct F.f _ σ U r T
    card_compl_correct_le (by have := F.card_validators; omega) (by simp [Params.mahiMahi])
    (fun _ => ⟨by simp [Params.mahiMahi], by simp [Params.mahiMahi]⟩)
    (by simp [Params.voteOffset, Params.mahiMahi]) hT hpop3 (by simpa [Params.mahiMahi] using hpop)
    (by simpa [Params.mahiMahi] using hcm)

/-! The one-buffer double count `|T|·(q − f) + G·(n − q) ≤ G·|T| + |honest|·(n − q)` at
`|T| = |honest| = n − f` gives the paper's worst-case cores: Blue Bottle Async at `f = 1`
(`n = 6`, `q = 5`) `G ≥ 4`, Mahi-Mahi at `f = 1` (`n = 4`, `q = 3`) `G ≥ 2`, and at `f = 2`
(`n = 7`, `q = 5`) `G ≥ 2`. -/
example (G : ℕ) (h : 5 * (5 - 1) + G * (6 - 5) ≤ G * 5 + 5 * (6 - 5)) : 4 ≤ G := by omega
example (G : ℕ) (h : 3 * (3 - 1) + G * (4 - 3) ≤ G * 3 + 3 * (4 - 3)) : 2 ≤ G := by omega
example (G : ℕ) (h : 5 * (5 - 2) + G * (7 - 5) ≤ G * 5 + 5 * (7 - 5)) : 2 ≤ G := by omega

end Scheme

end LeanDagTest

#print axioms LeanDag.Scheme.Async.holds
