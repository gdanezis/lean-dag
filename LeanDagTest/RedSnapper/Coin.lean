import LeanDag.RedSnapper.Helpers.Coin
import LeanDagTest.RedSnapper.Freeze

/-!
# Witness: coin rounds and termination premises

The coin lemma's two cases, end to end over `sixValidators`
(`quorum = 5`, `half = 3`, Byzantine `5`), with `ρ = 1`, plus the
termination Props' premises made live on the committed `U6Rec`.

* **`U6Coin`** — the concentrated case. Round 1 splits three ACKs for
  `tx 0` (the holder set `H = {0, 1, 2}`, exactly `half`) against two
  `⊥`; the target is validator `0 ∈ H`. Round 2: the three holders are
  unrefuted (two anti-votes < `half`) and keep — two silently, one by
  republishing; the two `⊥`-holders see three ACK-stances, a refutation
  of `⊥`, and adopt the target's value read through its round-1 block —
  two genuine `⊥ → ack` coin moves. Round 3: the single correct block
  references five `ack 0` stances — a full certificate; `CertifiedAt`
  holds at `ρ + 2` and every `CoinConcentrated` premise is pinned live.
* **`U6CoinBad` / `U6CoinBad2`** — `CoinRule` refused clause by clause:
  a refuted mover adopting a value the target does not hold, and an
  unrefuted keeper switching bare.
* **`U6Frag`** — the fragmented case: stances split `2 / 2 / 1`
  (no value reaches `half` correct holders — the premise pinned by
  exhaustive `decide` over all stances and holder sets); every correct
  validator is refuted, all five adopt the target's `⊥`, and round 3
  carries a full unlock certificate.
* **Measurability** — `U6Coin` and `U6CoinBad` differ only at round 2,
  so they agree up to the attempt round `ρ = 1`: `AgreeUpto` holds, the
  round-1 holder sets coincide (every `v`, every `x`), and the round-2
  ones do not — the boundary of the transfer.
* **Termination premises on `U6Rec`** — the committed recovery pipeline
  is certificate-free (no full certificate for any transaction, no full
  unlock certificate, anywhere), its markers are visible from every
  correct validator at the resolving anchor, and no anchor at or before
  the trigger sees a quorum: `TriggerExists`, `ResolutionExists` and
  `RecoveryDecides` instantiate on it, and their conclusions are the
  `TriggerAt`/`ResolvesFiveAt`/verdict pins already committed in
  `Freeze.lean`.
-/

namespace LeanDagTest

namespace RedSnapper

open LeanDag LeanDag.RedSnapper LeanDag.RedSnapper.CoinSuccess

set_option maxRecDepth 32768
set_option synthInstance.maxSize 4096

/-- Nineteen ids, id 18 junk: the concentrated coin round described in
the module docstring. -/
def lkCoin : Fin 19 → Block (Fin 6) (Fin 19) (Fin 4) (Fin 2) := fun i =>
  if h : (i : ℕ) < 6 then
    { round := 0, author := ⟨i, by omega⟩, parents := ∅,
      txs := if (i : ℕ) = 0 then {0} else if (i : ℕ) = 1 then {1} else ∅,
      declares := fun _ => none }
  else if (i : ℕ) = 6 then
    { round := 1, author := 0, parents := {0, 1, 2, 3, 4}, txs := ∅,
      declares := fun o => if o = 0 then some (.ack 0) else none }
  else if (i : ℕ) = 7 then
    { round := 1, author := 1, parents := {0, 1, 2, 3, 4}, txs := ∅,
      declares := fun o => if o = 0 then some (.ack 0) else none }
  else if (i : ℕ) = 8 then
    { round := 1, author := 2, parents := {0, 1, 2, 3, 4}, txs := ∅,
      declares := fun o => if o = 0 then some (.ack 0) else none }
  else if (i : ℕ) = 9 then
    { round := 1, author := 3, parents := {0, 1, 2, 3, 4}, txs := ∅,
      declares := fun o => if o = 0 then some .bot else none }
  else if (i : ℕ) = 10 then
    { round := 1, author := 4, parents := {0, 1, 2, 3, 4}, txs := ∅,
      declares := fun o => if o = 0 then some .bot else none }
  else if (i : ℕ) = 11 then
    { round := 1, author := 5, parents := {1, 2, 3, 4, 5}, txs := ∅,
      declares := fun o => if o = 0 then some (.ack 1) else none }
  else if (i : ℕ) = 12 then
    { round := 2, author := 0, parents := {6, 7, 8, 9, 10}, txs := ∅,
      declares := fun _ => none }
  else if (i : ℕ) = 13 then
    { round := 2, author := 1, parents := {6, 7, 8, 9, 10}, txs := ∅,
      declares := fun o => if o = 0 then some (.ack 0) else none }
  else if (i : ℕ) = 14 then
    { round := 2, author := 2, parents := {6, 7, 8, 9, 10}, txs := ∅,
      declares := fun _ => none }
  else if (i : ℕ) = 15 then
    { round := 2, author := 3, parents := {6, 7, 8, 9, 10}, txs := ∅,
      declares := fun o => if o = 0 then some (.ack 0) else none }
  else if (i : ℕ) = 16 then
    { round := 2, author := 4, parents := {6, 7, 8, 9, 10}, txs := ∅,
      declares := fun o => if o = 0 then some (.ack 0) else none }
  else if (i : ℕ) = 17 then
    { round := 3, author := 0, parents := {12, 13, 14, 15, 16}, txs := ∅,
      declares := fun _ => none }
  else
    { round := 0, author := 0, parents := ∅, txs := ∅, declares := fun _ => none }

def U6Coin : Universe (Fin 6) (Fin 19) (Fin 4) (Fin 2) where
  ids := Finset.univ.erase 18
  block := lkCoin
  complete := by decide
  valid := by decide
  no_equivocation := by decide
  self_parent := by decide

-- The premises of `CoinConcentrated`, live at `ρ = 1` with target 0.
example : FreezeDiscipline U6Coin := freezeDiscipline_iff.mpr (by decide)
example : CoinRule U6Coin 0 0 1 := coinRule_iff.mpr (by decide)
example : PopulatedOn U6Coin (Correct : Finset (Fin 6)) 1 := by
  unfold PopulatedOn; decide
example : PopulatedOn U6Coin (Correct : Finset (Fin 6)) 2 := by
  unfold PopulatedOn; decide
example : SynchronisedOn U6Coin (Correct : Finset (Fin 6)) 1 := by
  unfold SynchronisedOn; decide
example : StancedAt U6Coin 0 1 := stancedAt_iff.mpr (by decide)
example : ∀ v ∈ ({0, 1, 2} : Finset (Fin 6)), HoldsAt U6Coin v 0 1 (.ack 0) := by
  intro v hv
  exact holdsAt_iff.mpr (by revert v hv; decide)

-- The movers: a refutation of `⊥` at each, none of `ack 0` at the
-- keepers; two genuine `⊥ → ack` coin moves.
example : IsRefutation U6Coin 15 0 .bot := (isRefutation_iff (by decide)).mpr (by decide)
example : ¬ IsRefutation U6Coin 12 0 (.ack 0) := fun h =>
  absurd ((isRefutation_iff (by decide)).mp h) (by decide)
example : StanceIs U6Coin 3 0 15 (some (.ack 0)) :=
  (stanceSomeDec_iff (by decide)).mpr (by decide)

-- The conclusion: round `ρ + 2` certifies the held value.
example : CertifiedAt U6Coin 0 (.ack 0) 3 := certifiedAt_iff.mpr (by decide)
example : IsFullCert U6Coin 17 0 := (isFullCert_iff (by decide)).mpr (by decide)

/-- `lkCoin` with the mover 15 adopting a value the target does not
hold. -/
def lkCoinBad : Fin 19 → Block (Fin 6) (Fin 19) (Fin 4) (Fin 2) := fun i =>
  if (i : ℕ) = 15 then
    { round := 2, author := 3, parents := {6, 7, 8, 9, 10}, txs := ∅,
      declares := fun o => if o = 0 then some (.ack 1) else none }
  else lkCoin i

def U6CoinBad : Universe (Fin 6) (Fin 19) (Fin 4) (Fin 2) where
  ids := Finset.univ.erase 18
  block := lkCoinBad
  complete := by decide
  valid := by decide
  no_equivocation := by decide
  self_parent := by decide

example : ¬ CoinRule U6CoinBad 0 0 1 := fun h => absurd (coinRule_iff.mp h) (by decide)

/-- `lkCoin` with the unrefuted keeper 13 switching bare. -/
def lkCoinBad2 : Fin 19 → Block (Fin 6) (Fin 19) (Fin 4) (Fin 2) := fun i =>
  if (i : ℕ) = 13 then
    { round := 2, author := 1, parents := {6, 7, 8, 9, 10}, txs := ∅,
      declares := fun o => if o = 0 then some .bot else none }
  else lkCoin i

def U6CoinBad2 : Universe (Fin 6) (Fin 19) (Fin 4) (Fin 2) where
  ids := Finset.univ.erase 18
  block := lkCoinBad2
  complete := by decide
  valid := by decide
  no_equivocation := by decide
  self_parent := by decide

example : ¬ CoinRule U6CoinBad2 0 0 1 := fun h => absurd (coinRule_iff.mp h) (by decide)

/-- The fragmented table: stances `2 / 2 / 1`, target 2 at `⊥`, all
five refuted and adopting. -/
def lkFrag : Fin 19 → Block (Fin 6) (Fin 19) (Fin 4) (Fin 2) := fun i =>
  if h : (i : ℕ) < 6 then
    { round := 0, author := ⟨i, by omega⟩, parents := ∅,
      txs := if (i : ℕ) = 0 then {0} else if (i : ℕ) = 1 then {1} else ∅,
      declares := fun _ => none }
  else if (i : ℕ) = 6 then
    { round := 1, author := 0, parents := {0, 1, 2, 3, 4}, txs := ∅,
      declares := fun o => if o = 0 then some (.ack 0) else none }
  else if (i : ℕ) = 7 then
    { round := 1, author := 1, parents := {0, 1, 2, 3, 4}, txs := ∅,
      declares := fun o => if o = 0 then some (.ack 0) else none }
  else if (i : ℕ) = 8 then
    { round := 1, author := 2, parents := {0, 1, 2, 3, 4}, txs := ∅,
      declares := fun o => if o = 0 then some .bot else none }
  else if (i : ℕ) = 9 then
    { round := 1, author := 3, parents := {0, 1, 2, 3, 4}, txs := ∅,
      declares := fun o => if o = 0 then some .bot else none }
  else if (i : ℕ) = 10 then
    { round := 1, author := 4, parents := {0, 1, 2, 3, 4}, txs := ∅,
      declares := fun o => if o = 0 then some (.ack 1) else none }
  else if (i : ℕ) = 11 then
    { round := 1, author := 5, parents := {1, 2, 3, 4, 5}, txs := ∅,
      declares := fun _ => none }
  else if h2 : 12 ≤ (i : ℕ) ∧ (i : ℕ) ≤ 16 then
    { round := 2, author := ⟨(i : ℕ) - 12, by omega⟩, parents := {6, 7, 8, 9, 10},
      txs := ∅, declares := fun o => if o = 0 then some .bot else none }
  else if (i : ℕ) = 17 then
    { round := 3, author := 0, parents := {12, 13, 14, 15, 16}, txs := ∅,
      declares := fun _ => none }
  else
    { round := 0, author := 0, parents := ∅, txs := ∅, declares := fun _ => none }

def U6Frag : Universe (Fin 6) (Fin 19) (Fin 4) (Fin 2) where
  ids := Finset.univ.erase 18
  block := lkFrag
  complete := by decide
  valid := by decide
  no_equivocation := by decide
  self_parent := by decide

example : FreezeDiscipline U6Frag := freezeDiscipline_iff.mpr (by decide)
example : CoinRule U6Frag 2 0 1 := coinRule_iff.mpr (by decide)
example : StancedAt U6Frag 0 1 := stancedAt_iff.mpr (by decide)

-- No value has `half` correct holders at round 1 — exhaustively: the
-- correct holder count of every value stays below `half`.
private theorem frag_noconc : ∀ x : Stance (Fin 4),
    ((Correct : Finset (Fin 6)).filter
      (fun v => HoldsAtDec U6Frag v 0 1 x)).card + 1 ≤ half (Fin 6) := by decide

example : ∀ x : Stance (Fin 4), ¬ ∃ H : Finset (Fin 6),
    H ⊆ (Correct : Finset (Fin 6)) ∧ half (Fin 6) ≤ H.card ∧
      ∀ v ∈ H, HoldsAt U6Frag v 0 1 x := by
  rintro x ⟨H, hsub, hcard, hall⟩
  have hHsub : H ⊆ (Correct : Finset (Fin 6)).filter
      (fun v => HoldsAtDec U6Frag v 0 1 x) := fun v hv =>
    Finset.mem_filter.mpr ⟨hsub hv, holdsAt_iff.mp (hall v hv)⟩
  have h1 := Finset.card_le_card hHsub
  have h2 := frag_noconc x
  omega

-- All five adopt the target's `⊥`; round 3 carries the full unlock
-- certificate.
example : CertifiedAt U6Frag 0 .bot 3 := certifiedAt_iff.mpr (by decide)
example : IsFullUnlockCert U6Frag 17 0 := (isFullUnlockCert_iff (by decide)).mpr (by decide)

-- Measurability: `U6Coin` and `U6CoinBad` differ only above the attempt
-- round, so they agree up to it — and their round-1 holder sets
-- coincide while the round-2 ones do not.
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

example : AgreeUpto U6Coin U6CoinBad 1 where
  ids := by decide
  block := by decide

example : ∀ (v : Fin 6) (x : Stance (Fin 4)),
    HoldsAtDec U6Coin v 0 1 x ↔ HoldsAtDec U6CoinBad v 0 1 x := by decide
example : HoldsAtDec U6Coin 3 0 2 (.ack 0) ∧ ¬ HoldsAtDec U6CoinBad 3 0 2 (.ack 0) := by
  decide

-- Termination premises, live on the committed recovery pipeline: the
-- universe is certificate-free, and the markers are visible from every
-- correct validator at the resolving anchor.
private theorem rec_nocert : ∀ tx : Fin 4, ∀ C ∈ U6Rec.ids,
    ¬ IsFullCertDec U6Rec C tx := by decide
private theorem rec_nounlock : ∀ C ∈ U6Rec.ids, ¬ IsFullUnlockCertDec U6Rec C 0 := by
  decide
private theorem rec_frozen_all : ∀ v ∈ (Correct : Finset (Fin 6)),
    FrozenDec U6Rec 6 v 0 17 := by decide
private theorem rec_noquorum_below : ∀ i' ≤ 1, ∀ a',
    (ARec.seq)[i']? = some a' → ¬ FreezeQuorumDec U6Rec 6 0 a' := by decide

example : ∀ tx : Fin 4, LeanDag.RedSnapper.Transactions.input tx = 0 →
    ∀ C ∈ U6Rec.ids, ¬ IsFullCert U6Rec C tx :=
  fun tx _ C hC h => rec_nocert tx C hC ((isFullCert_iff hC).mp h)
example : ∀ C ∈ U6Rec.ids, ¬ IsFullUnlockCert U6Rec C 0 :=
  fun C hC h => rec_nounlock C hC ((isFullUnlockCert_iff hC).mp h)
example : ∀ v ∈ (Correct : Finset (Fin 6)), Frozen U6Rec 6 v 0 17 :=
  fun v hv => (frozen_iff (by decide)).mpr (rec_frozen_all v hv)
example : ∀ i' ≤ 1, ∀ a', (ARec.seq)[i']? = some a' → ¬ FreezeQuorum U6Rec 6 0 a' :=
  fun i' hi' a' hla' h => rec_noquorum_below i' hi' a' hla'
    ((freezeQuorum_iff (anchor_mem hla')).mp h)

end RedSnapper

end LeanDagTest
