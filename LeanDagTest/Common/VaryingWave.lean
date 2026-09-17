import LeanDagTest.Mysticeti.Model
import LeanDag.Common.Anchored.Band
/-!
# A wave that varies with the round

`AnchoredRule.waveAt` is a function of the slot's round, and every rule in the tree sets a
constant. This file supplies the instance that is not constant, so that the hypotheses a varying
wave forces are neither empty nor free:

* `banded` asks the wave to be the same at every round, and `altRule_not_banded` shows why: the
  band shifts every round by a constant, and a rule reading its wave at the round it is asked
  about does not survive that shift. The witness decides a slot in one frame and leaves it
  undecided in the same frame moved one round up, with the two universes agreeing on every band;
* what the band gives with no offset survives all the same, `altRule_extendLaws` and
  `altRule_persist`;
* and `spansEligible_of_identity` takes a bound in place of a constant, `altRule_spansEligible`.

`altRule` reads one reference at the slot's own decision round, skips nothing and has no rung, so
a `some` verdict has the direct rule as its only route. That is what makes the refutation a case
analysis rather than an induction; a protocol's rule is not meant here, only a rule the structure
admits.

The committee is the standard witness one, validator `0` Byzantine and `f = 1`
(`LeanDagTest/Mysticeti/Model.lean`), whose global `Slots (Fin 4)` is not this file's, so every
statement names its schedule.
-/

namespace LeanDagTest

namespace VaryingWave

open LeanDag LeanDag.Properties

set_option maxRecDepth 4096

/-! ## The wave, and the two frames of one schedule -/

/-- **A wave that alternates with the round**: one round above an even round, none above an odd
one. -/
def altWave : ℕ → ℕ := fun r => if r % 2 = 0 then 1 else 0

/-- One slot per round, slot `k` at round `k`, led by `(k + 1) % 4`. -/
@[reducible]
def altSlots : Slots (Fin 4) := Slots.identity (fun k => ⟨(k + 1) % 4, Nat.mod_lt _ (by omega)⟩)

/-- **The same schedule a round up**: slot `k` at round `k + 1`, under the same leaders. This is
the frame a band with offsets `g = 1`, `g' = 0` puts the first one in. -/
@[reducible]
def altSlots' : Slots (Fin 4) where
  slotRound := fun k => k + 1
  leader := fun k => ⟨(k + 1) % 4, Nat.mod_lt _ (by omega)⟩
  mono := fun _ _ h => Nat.succ_le_succ h
  unbounded := fun n => ⟨n, by omega⟩
  keyed := fun a b h => by
    have hr : a + 1 = b + 1 := congrArg Prod.fst h
    omega

/-! ## Two universes, one a round above the other

`av3` is a four-round ladder on ids `0` to `15`, block `4m + v` being validator `v`'s round-`m`
block and every non-genesis block referencing the whole round below. `av4` holds the same ids one
round up, on a fresh bottom layer `16` to `19` that the band's floor leaves unconstrained. -/

/-- The ladder: block `4m + v` at round `m`, referencing all four blocks of the round below. -/
def avBlk : Fin 20 → Block (Fin 4) (Fin 20) Unit := fun i =>
  { round := (i : ℕ) / 4, creator := ⟨(i : ℕ) % 4, Nat.mod_lt _ (by omega)⟩,
    refs := if (i : ℕ) < 4 then ∅ else
      (Finset.univ.filter (fun j : Fin 20 => (j : ℕ) / 4 + 1 = (i : ℕ) / 4)),
    payload := () }

/-- The same ladder a round up, with a fresh genesis layer at round `0` for the old bottom layer
to reference. -/
def avBlk' : Fin 20 → Block (Fin 4) (Fin 20) Unit := fun i =>
  if (i : ℕ) < 16 then
    { round := (i : ℕ) / 4 + 1, creator := ⟨(i : ℕ) % 4, Nat.mod_lt _ (by omega)⟩,
      refs := if (i : ℕ) < 4 then {16, 17, 18, 19} else
        (Finset.univ.filter (fun j : Fin 20 => (j : ℕ) / 4 + 1 = (i : ℕ) / 4)),
      payload := () }
  else
    { round := 0, creator := ⟨(i : ℕ) % 4, Nat.mod_lt _ (by omega)⟩, refs := ∅,
      payload := () }

/-- **The lower frame**: four rounds, ids `0` to `15`. -/
def av3 : BlockUniverse (Fin 4) (Fin 20) Unit where
  ids := Finset.univ.filter (fun i : Fin 20 => (i : ℕ) < 16)
  block := avBlk
  complete := by decide
  valid := by decide
  no_equivocation := by decide

/-- **The upper frame**: the same ids a round up, on a genesis layer of their own. -/
def av4 : BlockUniverse (Fin 4) (Fin 20) Unit where
  ids := Finset.univ
  block := avBlk'
  complete := by decide
  valid := by decide
  no_equivocation := by decide

/-! ## The rule -/

/-- **A rule reading one reference at the slot's own decision round**: the candidate proposed at
round `r` is committed where a block of the view sits at `r + altWave r` and references it. No
direct skip and no rung, so a `some` verdict comes from the direct rule alone. -/
def altRule : AnchoredRule (Fin 4) (Fin 20) Unit ValidWrt (Correct : Finset (Fin 4)) where
  waveAt := altWave
  Commit := fun U V L r =>
    ∃ c ∈ V.ids, (U.block c).round = r + altWave r ∧ L ∈ (U.block c).refs
  decCommit := fun _ _ _ _ => inferInstance
  Skip := fun _ _ _ _ => False
  rungs := 0
  Link := fun _ _ _ _ _ _ => False
  tie := fun _ _ _ => False

-- The wave is not the same at every round, which is what every other rule in the tree is.
example : altRule.waveAt 0 = 1 := rfl
example : altRule.waveAt 1 = 0 := rfl
example : ¬ ∀ r r', altRule.waveAt r = altRule.waveAt r' := fun h => by
  have := h 0 1
  simp [altRule, altWave] at this

/-! ## The verdict, and its absence a round up -/

/-- **Slot `0` commits in the lower frame**: it sits at round `0`, whose wave is one, and the
round-one blocks reference its candidate, block `1`. -/
theorem alt_decided : altRule.Decided (S := altSlots) av3 (View.full av3) 0 (some 1) :=
  AnchoredRule.Decided.directCommit (S := altSlots) (by decide) (by decide)

/-- **And has no verdict in the upper frame**: the same slot sits at round `1`, whose wave is
zero, so the rule reads the slot's own round, where the blocks reference the fresh genesis layer
and not the candidate. No rung is left to reach it by. -/
theorem alt_not_decided : ¬ altRule.Decided (S := altSlots') av4 (View.full av4) 0 (some 1) := by
  intro h
  cases h with
  | directCommit _ hc => exact absurd hc (by decide)
  | indirectCommit _ _ _ _ hi _ _ _ _ => exact absurd hi (Nat.not_lt_zero _)

/-- Every block of the lower frame sits one round up in the upper one, under the same author. -/
theorem av_block_shift : ∀ b : Fin 20, b ∈ av3.ids →
    (av4.block b).round + 0 = (av3.block b).round + 1 ∧
      (av4.block b).creator = (av3.block b).creator := by decide

/-- And carries its references, except at the bottom layer, which the band's floor excludes. -/
theorem av_refs_shift : ∀ b : Fin 20, b ∈ av3.ids → 1 < (av3.block b).round + 1 →
    (av4.block b).refs = (av3.block b).refs := by decide

/-- **The two frames agree on every band above the slot's round.** The floor is the slot's round
in the common frame, so the fresh genesis layer sits below it and the old bottom layer sits at it,
where the references clause does not reach. -/
theorem alt_agreeBand (top : ℕ) : AgreeBand altRule.toDagRule av3 av4 1 (top + 1) 1 0 where
  mem := fun b _ _ _ => Finset.mem_univ b
  block := fun b hb _ => av_block_shift b hb
  refs := fun b hb hlo _ => av_refs_shift b hb hlo

/-- **A rule whose wave varies with the round is not banded**: the hypothesis `banded` takes,
that the wave be the same at every round, cannot be dropped. -/
theorem altRule_not_banded : ¬ Banded altRule.toDagRule := by
  intro hb
  obtain ⟨top, ht⟩ := hb altSlots av3 (View.full av3) 0 (some 1) alt_decided
  refine alt_not_decided (ht 1 0 0 0 altSlots' av4 (View.full av4) 0 rfl ?_ ?_
    (alt_agreeBand top) (fun b _ _ _ => Finset.mem_univ b))
  · intro m m' hm _
    have : m = m' := by omega
    subst this
    rfl
  · intro m m' hm _
    have : m = m' := by omega
    subst this
    rfl

/-! ## What survives the varying wave

The band's offsets are what the wave breaks; an extension moves no round, so persistence holds
here as it does for a constant wave. -/

/-- **What the rule owes an extension**: a view that grew still holds the referencing block, and
the record that grew denotes it alike. The rungs are empty, so the two link laws are free. -/
theorem altRule_extendLaws : altRule.ExtendLaws where
  commit_ext := fun {_ U U' V _ _ _} he hV _ hc => by
    obtain ⟨c, hcV, hcr, hcL⟩ := hc
    have hblk : U'.block c = U.block c := he.block c (V.subset_ids hcV)
    exact ⟨c, hV c hcV, by rw [hblk]; exact hcr, by rw [hblk]; exact hcL⟩
  skip_ext := fun _ _ hs => hs.elim
  link_ext := fun _ _ _ _ => Iff.rfl
  link_novel_ext := fun _ _ _ _ _ hlink => hlink.elim

/-- **A verdict survives an extension**, at the varying wave. -/
theorem altRule_persist : Persist altRule.toDagRule := AnchoredRule.persist altRule_extendLaws

/-- **Eligibility spans at the bound**: two consecutive slots reach past everything below them,
the wave never exceeding one. A bound is what a varying wave supplies where a constant wave
supplies itself. -/
theorem altRule_spansEligible : altRule.SpansEligible (S := altSlots) 2 :=
  altRule.spansEligible_of_identity (S := altSlots) (fun _ => rfl) (w := 1)
    (fun r => by unfold altRule altWave; dsimp only; split <;> omega)

/-! ## Axioms

Nothing here should ever acquire an axiom beyond the standard three. -/

#print axioms av3
#print axioms av4
#print axioms altRule_not_banded
#print axioms altRule_persist

end VaryingWave

end LeanDagTest
