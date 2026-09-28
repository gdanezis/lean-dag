import LeanDagTest.RedSnapper.Coin
import LeanDag.RedSnapper.Five.Agreement.Proof
import LeanDag.RedSnapper.Five.CoinSuccess.Proof
import LeanDag.RedSnapper.Five.RecoveryTermination.Proof
import LeanDagTest.RedSnapper.FreezeHardening

/-!
# Witness hardening: coin rounds and termination

Adopted from the Phase 9 vacuity audit.

* **`U6CoinDev`** — the read-point amendment to `CoinRule` is
  *necessary*, not cosmetic: under the original self-read adopt clauses
  (reconstructed here as `OldCoinRule`), a refuted target's own block is
  constrained by nothing — its declaration satisfies the adoption
  hypothesis it is supposed to discharge — so the target deviates to
  `⊥`, the old rule holds, the amended rule refuses, every other
  `CoinConcentrated` premise stays live, and round `ρ + 2` certifies
  nothing: with the self-read, the concentrated lemma is false.
* **`U6CoinFroze`** — the conditioning claim is literal: a frozen
  validator holding its frozen value against a refutation falsifies
  `CoinRule` while `FreezeDiscipline` still holds — the rule holding
  *is* the paper's "no correct validator has yet frozen".
* **`U6CoinBadT`** — the `half` numerator is tight: a target outside
  the holder set satisfies the rule (both `⊥`-holders adopt its `⊥`)
  and *neither* certificate forms — the good set cannot be enlarged in
  the concentrated regime; also the `adopt_bot` clause fired on the
  concentrated skeleton.
* **`U6CoinR1`** — the measurability boundary: agreement up to
  `ρ − 1` does not transfer the round-`ρ` holder sets.
* **`U6CoinNoSt`** — `StancedAt` is load-bearing: one silent correct
  validator satisfies every other premise and caps round `ρ + 2` below
  the quorum.
* **`U4Frag`** — finding-19/20 continued: at the tight `3f + 1`
  committee a `2/1` split leaves *nobody* movable, `CoinRule` holds for
  every target, and both `CoinFragmented` and `CoinSuccessCount` are
  false — the paper's `(4f+1) − 2f ≥ 2f+1` movability argument failing
  below `5f + 1`, in DAG form.
* **`CertifiedAt`** pins its disjunct: a full unlock certificate does
  not certify an ACK value, nor a full certificate `⊥`.
-/

namespace LeanDagTest

namespace RedSnapper

open LeanDag LeanDag.RedSnapper LeanDag.RedSnapper.CoinSuccess

set_option maxRecDepth 32768
set_option synthInstance.maxSize 4096

/-! ### The amendment is necessary: the self-read rule lets the target deviate -/

/-- The OLD (pre-amendment) rule: the adopt clauses read the target's
value at the constrained block `b` itself. -/
structure OldCoinRule (U : Universe (Fin 6) (Fin 19) (Fin 4) (Fin 2)) (w : Fin 6)
    (o : Fin 2) (ρ : ℕ) : Prop where
  keep : ∀ b ∈ U.ids, (U.block b).author ∈ (Correct : Finset (Fin 6)) →
    (U.block b).round = ρ + 1 →
    ∀ p ∈ (U.block b).parents, (U.block p).author = (U.block b).author →
    ∀ s : Stance (Fin 4), StanceIs U (U.block b).author o p (some s) →
      ¬ IsRefutation U b o s →
      StanceIs U (U.block b).author o b (some s)
  adopt_ack : ∀ b ∈ U.ids, (U.block b).author ∈ (Correct : Finset (Fin 6)) →
    (U.block b).round = ρ + 1 →
    ∀ p ∈ (U.block b).parents, (U.block p).author = (U.block b).author →
    ∀ s : Stance (Fin 4), StanceIs U (U.block b).author o p (some s) →
      IsRefutation U b o s →
      ∀ tx : Fin 4, StanceIs U w o b (some (Stance.ack tx)) → IsCandidate U b o tx →
        StanceIs U (U.block b).author o b (some (Stance.ack tx))
  adopt_bot : ∀ b ∈ U.ids, (U.block b).author ∈ (Correct : Finset (Fin 6)) →
    (U.block b).round = ρ + 1 →
    ∀ p ∈ (U.block b).parents, (U.block p).author = (U.block b).author →
    ∀ s : Stance (Fin 4), StanceIs U (U.block b).author o p (some s) →
      IsRefutation U b o s →
      StanceIs U w o b (some Stance.bot) →
      StanceIs U (U.block b).author o b (some Stance.bot)

/-- Computable form of the OLD rule. -/
def OldCoinRuleDec (U : Universe (Fin 6) (Fin 19) (Fin 4) (Fin 2)) (w : Fin 6)
    (o : Fin 2) (ρ : ℕ) : Prop :=
  (∀ b ∈ U.ids, (U.block b).author ∈ (Correct : Finset (Fin 6)) →
    (U.block b).round = ρ + 1 →
    ∀ p ∈ (U.block b).parents, (U.block p).author = (U.block b).author →
    ∀ s : Stance (Fin 4), StanceSomeDec U (U.block b).author o p s →
      ¬ IsRefutationDec U b o s →
      StanceSomeDec U (U.block b).author o b s) ∧
  (∀ b ∈ U.ids, (U.block b).author ∈ (Correct : Finset (Fin 6)) →
    (U.block b).round = ρ + 1 →
    ∀ p ∈ (U.block b).parents, (U.block p).author = (U.block b).author →
    ∀ s : Stance (Fin 4), StanceSomeDec U (U.block b).author o p s →
      IsRefutationDec U b o s →
      ∀ tx : Fin 4, StanceSomeDec U w o b (Stance.ack tx) → tx ∈ candidates U b o →
        StanceSomeDec U (U.block b).author o b (Stance.ack tx)) ∧
  ∀ b ∈ U.ids, (U.block b).author ∈ (Correct : Finset (Fin 6)) →
    (U.block b).round = ρ + 1 →
    ∀ p ∈ (U.block b).parents, (U.block p).author = (U.block b).author →
    ∀ s : Stance (Fin 4), StanceSomeDec U (U.block b).author o p s →
      IsRefutationDec U b o s →
      StanceSomeDec U w o b Stance.bot →
        StanceSomeDec U (U.block b).author o b Stance.bot

set_option synthInstance.maxSize 8192 in
instance (U : Universe (Fin 6) (Fin 19) (Fin 4) (Fin 2)) (w : Fin 6) (o : Fin 2)
    (ρ : ℕ) : Decidable (OldCoinRuleDec U w o ρ) := by
  unfold OldCoinRuleDec; infer_instance

theorem oldCoinRule_of_dec {U : Universe (Fin 6) (Fin 19) (Fin 4) (Fin 2)} {w : Fin 6}
    {o : Fin 2} {ρ : ℕ} (h : OldCoinRuleDec U w o ρ) : OldCoinRule U w o ρ := by
  obtain ⟨h1, h2, h3⟩ := h
  refine ⟨fun b hb hc hr p hp hap s hst href => ?_,
    fun b hb hc hr p hp hap s hst href tx hstw hcand => ?_,
    fun b hb hc hr p hp hap s hst href hstw => ?_⟩
  · exact (stanceSomeDec_iff hb).mpr (h1 b hb hc hr p hp hap s
      ((stanceSomeDec_iff (U.complete b hb p hp)).mp hst)
      (fun hr' => href ((isRefutation_iff hb).mpr hr')))
  · exact (stanceSomeDec_iff hb).mpr (h2 b hb hc hr p hp hap s
      ((stanceSomeDec_iff (U.complete b hb p hp)).mp hst)
      ((isRefutation_iff hb).mp href) tx
      ((stanceSomeDec_iff hb).mp hstw)
      ((mem_candidates_iff hb).mpr hcand))
  · exact (stanceSomeDec_iff hb).mpr (h3 b hb hc hr p hp hap s
      ((stanceSomeDec_iff (U.complete b hb p hp)).mp hst)
      ((isRefutation_iff hb).mp href)
      ((stanceSomeDec_iff hb).mp hstw))

/-- `lkCoin` with the target's round-2 block additionally referencing
the Byzantine round-1 block (so the target itself is refuted) and
deviating to `⊥`. -/
def lkCoinDev : Fin 19 → Block (Fin 6) (Fin 19) (Fin 4) (Fin 2) := fun i =>
  if (i : ℕ) = 12 then
    { round := 2, author := 0, parents := {6, 7, 8, 9, 10, 11}, txs := ∅,
      declares := fun o => if o = 0 then some .bot else none }
  else lkCoin i

def U6CoinDev : Universe (Fin 6) (Fin 19) (Fin 4) (Fin 2) where
  ids := Finset.univ.erase 18
  block := lkCoinDev
  complete := by decide
  valid := by decide
  no_equivocation := by decide
  self_parent := by decide

-- The target is genuinely refuted at its own block, and deviates.
example : IsRefutation U6CoinDev 12 0 (.ack 0) :=
  (isRefutation_iff (by decide)).mpr (by decide)
example : StanceIs U6CoinDev 0 0 12 (some .bot) :=
  (stanceSomeDec_iff (by decide)).mpr (by decide)

-- The OLD rule holds — the b-read is circular on the target's own
-- block, so the deviation passes.
example : OldCoinRule U6CoinDev 0 0 1 := oldCoinRule_of_dec (by decide)

-- The AMENDED rule refuses the very same universe.
example : ¬ CoinRule U6CoinDev 0 0 1 := fun h => absurd (coinRule_iff.mp h) (by decide)

-- Every other `CoinConcentrated` premise holds, target 0 ∈ H = {0,1,2} ...
example : FreezeDiscipline U6CoinDev := freezeDiscipline_iff.mpr (by decide)
example : PopulatedOn U6CoinDev (Correct : Finset (Fin 6)) 1 := by
  unfold PopulatedOn; decide
example : PopulatedOn U6CoinDev (Correct : Finset (Fin 6)) 2 := by
  unfold PopulatedOn; decide
example : SynchronisedOn U6CoinDev (Correct : Finset (Fin 6)) 1 := by
  unfold SynchronisedOn; decide
example : StancedAt U6CoinDev 0 1 := stancedAt_iff.mpr (by decide)
example : ∀ v ∈ ({0, 1, 2} : Finset (Fin 6)), HoldsAt U6CoinDev v 0 1 (.ack 0) := by
  intro v hv
  exact holdsAt_iff.mpr (by revert v hv; decide)
example : ({0, 1, 2} : Finset (Fin 6)) ⊆ (Correct : Finset (Fin 6)) ∧
    half (Fin 6) ≤ ({0, 1, 2} : Finset (Fin 6)).card ∧
    (0 : Fin 6) ∈ ({0, 1, 2} : Finset (Fin 6)) := by decide

-- ... and the conclusion FAILS: round 3 certifies nothing (4 ACK
-- stances < quorum 5, 1 ⊥ stance < 5). The OLD-rule form of
-- `CoinConcentrated` is therefore false — the amendment is necessary.
private theorem dev_nocert : ∀ x : Stance (Fin 4), ¬ CertifiedAtDec U6CoinDev 0 x 3 := by
  decide
example : ¬ CertifiedAt U6CoinDev 0 (.ack 0) 3 :=
  fun h => dev_nocert _ (certifiedAt_iff.mp h)

/-! ### Frozen holdout, bad-target tightness, the measurability boundary, and StancedAt -/

/-! ## B: the frozen holdout falsifies `CoinRule` -/

/-- `lkCoin` with validator 3 frozen at round 1 (marker on its `⊥`
declaration) and holding `⊥` at round 2 against the refutation. -/
def lkCoinFroze : Fin 19 → Block (Fin 6) (Fin 19) (Fin 4) (Fin 2) := fun i =>
  if (i : ℕ) = 9 then
    { round := 1, author := 3, parents := {0, 1, 2, 3, 4}, txs := ∅,
      declares := fun o => if o = 0 then some .bot else none,
      freezes := fun o => if o = 0 then some 0 else none }
  else if (i : ℕ) = 15 then
    { round := 2, author := 3, parents := {6, 7, 8, 9, 10}, txs := ∅,
      declares := fun o => if o = 0 then some .bot else none }
  else lkCoin i

def U6CoinFroze : Universe (Fin 6) (Fin 19) (Fin 4) (Fin 2) where
  ids := Finset.univ.erase 18
  block := lkCoinFroze
  complete := by decide
  valid := by decide
  no_equivocation := by decide
  self_parent := by decide

-- The freeze machinery is satisfied: the marker declares, and the
-- frozen value persists.
example : FreezeDiscipline U6CoinFroze := freezeDiscipline_iff.mpr (by decide)
example : Frozen U6CoinFroze 0 3 0 15 := (frozen_iff (by decide)).mpr (by decide)

-- The frozen value IS refuted at the holdout block ...
example : IsRefutation U6CoinFroze 15 0 .bot :=
  (isRefutation_iff (by decide)).mpr (by decide)
example : StanceIs U6CoinFroze 3 0 15 (some .bot) :=
  (stanceSomeDec_iff (by decide)).mpr (by decide)

-- ... and `CoinRule` is FALSE of this execution: the rule holding is
-- exactly the "no correct validator has yet frozen" conditioning.
example : ¬ CoinRule U6CoinFroze 0 0 1 := fun h => absurd (coinRule_iff.mp h) (by decide)

/-! ## C: a bad target genuinely fails — the `half` numerator is tight -/

/-- `lkCoin` with the coin landing on validator 3 (a `⊥`-holder outside
the ACK holder set): the two refuted `⊥`-holders adopt the target's
`⊥`, the unrefuted ACK holders keep. -/
def lkCoinBadT : Fin 19 → Block (Fin 6) (Fin 19) (Fin 4) (Fin 2) := fun i =>
  if (i : ℕ) = 15 then
    { round := 2, author := 3, parents := {6, 7, 8, 9, 10}, txs := ∅,
      declares := fun o => if o = 0 then some .bot else none }
  else if (i : ℕ) = 16 then
    { round := 2, author := 4, parents := {6, 7, 8, 9, 10}, txs := ∅,
      declares := fun o => if o = 0 then some .bot else none }
  else lkCoin i

def U6CoinBadT : Universe (Fin 6) (Fin 19) (Fin 4) (Fin 2) where
  ids := Finset.univ.erase 18
  block := lkCoinBadT
  complete := by decide
  valid := by decide
  no_equivocation := by decide
  self_parent := by decide

-- Every premise holds with target 3 ...
example : FreezeDiscipline U6CoinBadT := freezeDiscipline_iff.mpr (by decide)
example : CoinRule U6CoinBadT 3 0 1 := coinRule_iff.mpr (by decide)
example : PopulatedOn U6CoinBadT (Correct : Finset (Fin 6)) 1 := by
  unfold PopulatedOn; decide
example : PopulatedOn U6CoinBadT (Correct : Finset (Fin 6)) 2 := by
  unfold PopulatedOn; decide
example : SynchronisedOn U6CoinBadT (Correct : Finset (Fin 6)) 1 := by
  unfold SynchronisedOn; decide
example : StancedAt U6CoinBadT 0 1 := stancedAt_iff.mpr (by decide)
example : (3 : Fin 6) ∈ (Correct : Finset (Fin 6)) := by decide
example : HoldsAt U6CoinBadT 3 0 1 .bot := holdsAt_iff.mpr (by decide)

-- ... and NO value certifies at round 3: following a target outside
-- the `half`-sized holder set fails, so the good-target count cannot
-- exceed the numerator `half` in the concentrated regime.
private theorem badT_nocert : ∀ x : Stance (Fin 4),
    ¬ CertifiedAtDec U6CoinBadT 0 x 3 := by decide
example : ∀ x : Stance (Fin 4), ¬ CertifiedAt U6CoinBadT 0 x 3 :=
  fun x h => badT_nocert x (certifiedAt_iff.mp h)

-- (For contrast: `CoinRule` for a target inside the holder set is
-- false of this execution — the universe encodes the draw of 3.)
example : ¬ CoinRule U6CoinBadT 0 0 1 := fun h => absurd (coinRule_iff.mp h) (by decide)

/-! ## D: the measurability bound is tight -/

/-- `lkCoin` with validator 0's round-1 declaration flipped to `⊥` —
the two universes differ AT the attempt round `ρ = 1`. -/
def lkCoinR1 : Fin 19 → Block (Fin 6) (Fin 19) (Fin 4) (Fin 2) := fun i =>
  if (i : ℕ) = 6 then
    { round := 1, author := 0, parents := {0, 1, 2, 3, 4}, txs := ∅,
      declares := fun o => if o = 0 then some .bot else none }
  else lkCoin i

def U6CoinR1 : Universe (Fin 6) (Fin 19) (Fin 4) (Fin 2) where
  ids := Finset.univ.erase 18
  block := lkCoinR1
  complete := by decide
  valid := by decide
  no_equivocation := by decide
  self_parent := by decide

private instance : DecidableEq (Block (Fin 6) (Fin 19) (Fin 4) (Fin 2)) := fun x y =>
  decidable_of_iff (x.round = y.round ∧ x.author = y.author ∧ x.parents = y.parents ∧
    x.txs = y.txs ∧ x.declares = y.declares ∧ x.freezes = y.freezes) (by
      constructor
      · rintro ⟨h1, h2, h3, h4, h5, h6⟩
        cases x
        cases y
        simp_all
      · rintro rfl
        exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩)

-- They agree up to round 0 but NOT up to round 1 ...
example : AgreeUpto U6Coin U6CoinR1 0 where
  ids := by decide
  block := by decide
example : ¬ AgreeUpto U6Coin U6CoinR1 1 := fun h =>
  absurd (h.block 6 (by decide) (by decide)) (by decide)

-- ... and their round-1 holder sets DIFFER: agreement up to `ρ - 1`
-- does not transfer the round-`ρ` holder sets — `d = ρ` is the exact
-- boundary of `CoinMeasurable`.
example : HoldsAtDec U6Coin 0 0 1 (.ack 0) ∧ ¬ HoldsAtDec U6CoinR1 0 0 1 (.ack 0) := by
  decide

/-! ## E: `StancedAt` is load-bearing -/

/-- `lkCoin` with validator 4 never declaring: no stance at round 1,
silent at round 2. -/
def lkCoinNoSt : Fin 19 → Block (Fin 6) (Fin 19) (Fin 4) (Fin 2) := fun i =>
  if (i : ℕ) = 10 then
    { round := 1, author := 4, parents := {0, 1, 2, 3, 4}, txs := ∅,
      declares := fun _ => none }
  else if (i : ℕ) = 16 then
    { round := 2, author := 4, parents := {6, 7, 8, 9, 10}, txs := ∅,
      declares := fun _ => none }
  else lkCoin i

def U6CoinNoSt : Universe (Fin 6) (Fin 19) (Fin 4) (Fin 2) where
  ids := Finset.univ.erase 18
  block := lkCoinNoSt
  complete := by decide
  valid := by decide
  no_equivocation := by decide
  self_parent := by decide

-- The stanced premise fails ...
example : ¬ StancedAt U6CoinNoSt 0 1 := fun h => absurd (stancedAt_iff.mp h) (by decide)

-- ... every OTHER premise of `CoinConcentrated` holds at target 0,
-- H = {0, 1, 2} ...
example : FreezeDiscipline U6CoinNoSt := freezeDiscipline_iff.mpr (by decide)
example : CoinRule U6CoinNoSt 0 0 1 := coinRule_iff.mpr (by decide)
example : PopulatedOn U6CoinNoSt (Correct : Finset (Fin 6)) 1 := by
  unfold PopulatedOn; decide
example : PopulatedOn U6CoinNoSt (Correct : Finset (Fin 6)) 2 := by
  unfold PopulatedOn; decide
example : SynchronisedOn U6CoinNoSt (Correct : Finset (Fin 6)) 1 := by
  unfold SynchronisedOn; decide
example : ∀ v ∈ ({0, 1, 2} : Finset (Fin 6)), HoldsAt U6CoinNoSt v 0 1 (.ack 0) := by
  intro v hv
  exact holdsAt_iff.mpr (by revert v hv; decide)

-- ... and the conclusion FAILS: the never-stanced validator's silence
-- caps the round-3 count at 4 < 5.
example : ¬ CertifiedAt U6CoinNoSt 0 (.ack 0) 3 := fun h =>
  absurd (certifiedAt_iff.mp h) (by decide)

/-! ## F: `U6Frag`'s adoption reads the target, not the mover -/

-- Mover 0's own round-1 value was `ack 0`, it was refuted, and its
-- round-2 declaration is the TARGET's `⊥` read through the target's
-- round-1 block — a mutant reading the mover's own value would demand
-- `ack 0` here and is falsified by the committed witness.
example : StanceIs U6Frag 0 0 6 (some (.ack 0)) :=
  (stanceSomeDec_iff (by decide)).mpr (by decide)
example : IsRefutation U6Frag 12 0 (.ack 0) :=
  (isRefutation_iff (by decide)).mpr (by decide)
example : StanceIs U6Frag 0 0 12 (some .bot) :=
  (stanceSomeDec_iff (by decide)).mpr (by decide)
example : StanceIs U6Frag 2 0 8 (some .bot) :=
  (stanceSomeDec_iff (by decide)).mpr (by decide)

/-! ### The `Five` gate is tight: the fragmented case and the count fail at the 3f+1 committee -/

/-- Ids 0–9, 10 junk. Genesis 0–2 (authors 1–3; tx 0 and tx 1 both
disseminated — the conflict is visible). Round 1: authors 1, 2 declare
`ack 0`, author 3 declares `⊥`. Round 2: all silent (nobody movable).
Round 3: one correct block. The Byzantine validator 0 is absent. -/
def lk4Frag : Fin 11 → Block (Fin 4) (Fin 11) (Fin 4) (Fin 2) := fun i =>
  if h : (i : ℕ) < 3 then
    { round := 0, author := ⟨i + 1, by omega⟩, parents := ∅,
      txs := if (i : ℕ) = 0 then {0} else if (i : ℕ) = 1 then {1} else ∅,
      declares := fun _ => none }
  else if h : (i : ℕ) < 6 then
    { round := 1, author := ⟨i - 2, by omega⟩, parents := {0, 1, 2}, txs := ∅,
      declares := fun o =>
        if o = 0 then (if (i : ℕ) = 5 then some .bot else some (.ack 0)) else none }
  else if h : (i : ℕ) < 9 then
    { round := 2, author := ⟨i - 5, by omega⟩, parents := {3, 4, 5}, txs := ∅,
      declares := fun _ => none }
  else if (i : ℕ) = 9 then
    { round := 3, author := 1, parents := {6, 7, 8}, txs := ∅,
      declares := fun _ => none }
  else
    { round := 0, author := 1, parents := ∅, txs := ∅, declares := fun _ => none }

def U4Frag : Universe (Fin 4) (Fin 11) (Fin 4) (Fin 2) where
  ids := Finset.univ.erase 10
  block := lk4Frag
  complete := by decide
  valid := by decide
  no_equivocation := by decide
  self_parent := by decide

-- The premises, all live.
private theorem u4_fd : FreezeDisciplineDec U4Frag := by decide
private theorem u4_rule_all : ∀ w : Fin 4, CoinRuleDec U4Frag w 0 1 := by decide
private theorem u4_pop1 : PopulatedOn U4Frag (Correct : Finset (Fin 4)) 1 := by
  unfold PopulatedOn; decide
private theorem u4_pop2 : PopulatedOn U4Frag (Correct : Finset (Fin 4)) 2 := by
  unfold PopulatedOn; decide
private theorem u4_sync : SynchronisedOn U4Frag (Correct : Finset (Fin 4)) 1 := by
  unfold SynchronisedOn; decide
private theorem u4_stanced : StancedAtDec U4Frag 0 1 := by decide

-- No value has `half = 3` correct holders (the split is 2 / 1).
private theorem u4_noconc_card : ∀ x : Stance (Fin 4),
    ((Correct : Finset (Fin 4)).filter
      (fun v => HoldsAtDec U4Frag v 0 1 x)).card + 1 ≤ half (Fin 4) := by decide

private theorem u4_noconc : ∀ x : Stance (Fin 4), ¬ ∃ H : Finset (Fin 4),
    H ⊆ (Correct : Finset (Fin 4)) ∧ half (Fin 4) ≤ H.card ∧
      ∀ v ∈ H, HoldsAt U4Frag v 0 1 x := by
  rintro x ⟨H, hsub, hcard, hall⟩
  have hHsub : H ⊆ (Correct : Finset (Fin 4)).filter
      (fun v => HoldsAtDec U4Frag v 0 1 x) := fun v hv =>
    Finset.mem_filter.mpr ⟨hsub hv, holdsAt_iff.mp (hall v hv)⟩
  have h1 := Finset.card_le_card hHsub
  have h2 := u4_noconc_card x
  omega

-- The target 3 (correct, holding `⊥`) can only hold `⊥`, and nothing
-- certifies at round 3.
private theorem u4_holds_only_bot : ∀ x : Stance (Fin 4),
    HoldsAtDec U4Frag 3 0 1 x → x = .bot := by decide
private theorem u4_nocert : ∀ x : Stance (Fin 4), ¬ CertifiedAtDec U4Frag 0 x 3 := by
  decide

-- `CoinFragmented` is FALSE at the 3f+1 committee.
example : ¬ CoinFragmented U4Frag := by
  intro h
  obtain ⟨x, hx, hc⟩ := h 3 0 1 (freezeDiscipline_iff.mpr u4_fd)
    (coinRule_iff.mpr (u4_rule_all 3)) u4_pop1 u4_pop2 u4_sync
    (stancedAt_iff.mpr u4_stanced) u4_noconc (by decide)
  have := u4_holds_only_bot x (holdsAt_iff.mp hx)
  subst this
  exact u4_nocert _ (certifiedAt_iff.mp hc)

-- `CoinSuccessCount` is FALSE at the 3f+1 committee: nobody is
-- refuted, so `CoinRule` holds for EVERY target, yet no target
-- certifies — no good set of size `half` can exist.
example : ¬ CoinSuccessCount U4Frag := by
  intro h
  obtain ⟨G, hcard, hG⟩ := h 0 1 (freezeDiscipline_iff.mpr u4_fd)
    u4_pop1 u4_pop2 u4_sync (stancedAt_iff.mpr u4_stanced)
  have hpos : 0 < G.card := lt_of_lt_of_le (by decide : 0 < half (Fin 4)) hcard
  obtain ⟨w, hw⟩ := Finset.card_pos.mp hpos
  obtain ⟨x, hx⟩ := hG w hw (coinRule_iff.mpr (u4_rule_all w))
  exact u4_nocert x (certifiedAt_iff.mp hx)

-- The committee indeed fails the `Five` bound (the guard the Statement
-- places on exactly these two Props).
example : ¬ (5 * fourValidators.f + 1 ≤ Fintype.card (Fin 4)) := by decide

/-! ### `CertifiedAt` cannot certify the wrong disjunct -/

example : CertifiedAt U6Frag 0 .bot 3 ∧ ¬ CertifiedAt U6Frag 0 (.ack 0) 3 :=
  ⟨certifiedAt_iff.mpr (by decide), fun h => absurd (certifiedAt_iff.mp h) (by decide)⟩

example : CertifiedAt U6Coin 0 (.ack 0) 3 ∧ ¬ CertifiedAt U6Coin 0 .bot 3 :=
  ⟨certifiedAt_iff.mpr (by decide), fun h => absurd (certifiedAt_iff.mp h) (by decide)⟩

-- The `StancedAt` half of the measurability transfer, pinned on the
-- committed `AgreeUpto` pair.
example : StancedAtDec U6Coin 0 1 ∧ StancedAtDec U6CoinBad 0 1 := by decide

end RedSnapper

end LeanDagTest
