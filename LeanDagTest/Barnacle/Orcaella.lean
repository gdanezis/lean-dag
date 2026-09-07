import LeanDagTest.Hybrid.Model
import LeanDag.Barnacle.Orcaella.Proof
import LeanDag.Barnacle.Helpers.Cover
/-!
# Barnacle over Orcaella — the base witnesses

The fourth instantiation, evaluated on concrete DAGs before its
theorems are used, on the four-validator hybrid committee of
`LeanDagTest/Hybrid.lean` (`Uhyb4`: `fb = 0, fc = 1`, validator `3`
crashes after genesis):

* the interface's universe actually formed: `Ohyb4` is `Uhyb4` with its
  `HonestNoEquiv` witness, the subtype the statement bundles;
* the window count at wave length two under a crash: with the anchor at
  round `3` and a three-round interval, the count-one window is healthy
  (`observed = expected = 2`) and the count-four window is not
  (`observed 6` against `expected 8` — the crashed validator's slots
  never commit), so the AIMD rule holds at one and backs off from four;
* Orcaella's own `Good` on `Ohyb4`, and its descent law yielding a
  committed round-`1` slot — by pigeonhole on the reliable set, which
  may *contain* the crashed validator (`T` is bounded by cardinality
  only), unlike the sunny Odontoceti script;
* the laws through `Orcaella.holds`: agreement of any view's verdict
  with the full view's, at the admissible threshold `2`;
* the mixed committee's admissible interval on data: at the tight
  `n = 9` the interval is the singleton `{4}`;
* the negatives: `Good` fails one round past the universe; a reliable
  set containing the crashed validator populates no round; **no descent
  law holds at slack `0`** — the slack `fb + fc` is exact at `n = 4`;
  and `Ubad`, a lawful universe in which the *crash-prone* validator
  equivocates — `BlockUniverse.no_equivocation` constrains only the
  fully-correct class — separates `HonestNoEquiv` from the base
  clauses: the subtype is a real restriction, not a no-op.

This file must not import `LeanDagTest.Model` or anything that pulls it
in (e.g. `LeanDagTest.Barnacle.Instances`): that file installs a
competing `Faults (Fin 4)` with `byzantine = {0}`, and every `decide`
below would silently judge the wrong fault classes. The pins right
after the imports guard the resolution.
-/

namespace LeanDagTest

namespace Barnacle

namespace OrcaellaBase

set_option maxRecDepth 2000000

open LeanDag LeanDag.Barnacle LeanDag.Hybrid

/-! ## The instance pins: the derived hybrid classes are in force -/

example : (Faults.byzantine (Validator := Fin 4)) = {3} := by decide
example : (Correct : Finset (Fin 4)) = {0, 1, 2} := by decide
example : Hybrid.q (Fin 4) = 3 := by decide

/-! ## The mixed committee's interval, on data: a singleton at the
tight `n = 9` -/

example : Admissible (Fin 9) 4 := by decide
example : ¬ Admissible (Fin 9) 3 := by decide
example : ¬ Admissible (Fin 9) 5 := by decide

/-! ## The universe of the instantiation, formed -/

/-- Orcaella over the four-validator committee, at the (only)
admissible threshold. -/
abbrev bnOrc : BaseRule (Fin 4) (Fin 13) Unit := orcaella 2

/-- The subtype universe: `Uhyb4` with its `HonestNoEquiv` witness. -/
def Ohyb4 : bnOrc.Universe := ⟨Uhyb4, by decide⟩

/-! ## The window count at wave length two -/

/-- Three-round interval, at most four leaders. -/
def orcPo : Params := ⟨3, 4, 96, 100, by decide, by decide⟩

def orcLeader4 : ℕ → Fin 4 := roundRobin 4 (by omega)

theorem orcWin4 : Keyed orcLeader4 4 := roundRobin_keyed 4 (by omega)

-- Anchor `10` (round `3`, author `0`); the window is rounds `0` to `3`.
-- At count one, rounds `0` and `1` score — round `2`'s only supporter in
-- the window is the anchor itself, and round `3` has no next round. At
-- count four, the same two rounds score at every leader but the crashed
-- one: six commits against an expected eight.
example : observed bnOrc orcPo orcLeader4 orcWin4 Ohyb4 10 1 (by decide) (by decide) = 2 := by
  decide
example : observed bnOrc orcPo orcLeader4 orcWin4 Ohyb4 10 4 (by decide) (by decide) = 6 := by
  decide
example : expected bnOrc orcPo 1 = 2 := by decide
example : expected bnOrc orcPo 4 = 8 := by decide
example : Aimd.rule bnOrc orcPo orcLeader4 orcWin4 1 0 Ohyb4 (bnOrc.full Ohyb4) 10 = (2, 0) := by
  decide
example : Aimd.rule bnOrc orcPo orcLeader4 orcWin4 4 0 Ohyb4 (bnOrc.full Ohyb4) 10 = (3, 1) := by
  decide

/-! ## Orcaella's `Good` on `Ohyb4`, and its descent law -/

/-- The model's own synchrony from round `0`, over the fully-correct
class. -/
theorem ohyb4_sync : SynchronisedOn Uhyb4 {0, 1, 2} 0 := by
  intro n hn b hb hround hbT a ha hround' haT
  have h3 : ∀ b : Fin 13, (Uhyb4.block b).round ≤ 3 := by decide
  have hn2 : n ≤ 2 := by have := h3 b; omega
  interval_cases n <;> revert b a <;> decide

theorem ohyb4_good :
    (orcaellaLive (Validator := Fin 4) (BlockId := Fin 13) (Payload := Unit) 2).Good
      Ohyb4 0 3 :=
  ⟨{0, 1, 2}, ⟨by decide, by decide⟩, ohyb4_sync, fun r h1 h2 => by interval_cases r <;> decide⟩

/-- Through `Orcaella.holds`: the good set commits a round-`1` slot.
`goodLeaders` bounds `T` by cardinality only — three of four — so `T`
may contain the crashed validator, whose slots never commit; but `T`
must also meet `{0, 1, 2}`, and at count `4` every validator leads a
slot of round `1`. -/
theorem ohyb4_commit :
    ∃ κ, (Sched orcLeader4 orcWin4 4 (by decide) (by decide)).slotRound κ = 1 ∧
      ∃ L, bnOrc.Decided (Sched orcLeader4 orcWin4 4 (by decide) (by decide))
        (bnOrc.full Ohyb4) κ (some L) := by
  obtain ⟨T, hcard, hT0⟩ :=
    (LeanDag.Barnacle.Orcaella.holds.2.1 (Fin 4) (Fin 13) Unit 2 (by decide)).goodLeaders
      Ohyb4 0 3 ohyb4_good
  have hT := fun (S : Slots (Fin 4)) κ => hT0 S (bnOrc.full Ohyb4) κ
    (coversUpto_full (LeanDag.Barnacle.Orcaella.holds.1 (Fin 4) (Fin 13) Unit 2 (by decide))
      Ohyb4 3)
  have h3 : 3 ≤ T.card := by
    have h := hcard
    simp only [Fintype.card_fin] at h
    change 4 ≤ T.card + 1 at h
    omega
  have hmeet : ∃ v : Fin 4, v ∈ T ∧ v ≠ 3 := by
    by_contra hno
    have hsub : T ⊆ {3} := fun v hv => Finset.mem_singleton.mpr (by
      by_contra hne
      exact hno ⟨v, hv, hne⟩)
    have := Finset.card_le_card hsub
    simp at this
    omega
  obtain ⟨v, hv, hv3⟩ := hmeet
  fin_cases v
  · exact ⟨7, by decide, hT _ 7 (by omega) (by decide) hv⟩
  · exact ⟨4, by decide, hT _ 4 (by omega) (by decide) hv⟩
  · exact ⟨5, by decide, hT _ 5 (by omega) (by decide) hv⟩
  · exact absurd rfl hv3

/-! ## The laws, on `Ohyb4` -/

/-- Agreement through `Orcaella.holds`: the direct commit of slot `1`
pins every view's verdict. -/
example : ∀ (V : bnOrc.View Ohyb4) (v : Option (Fin 13)),
    bnOrc.Decided hyb4Slots V 1 v → v = some 5 := fun V v h =>
  (LeanDag.Barnacle.Orcaella.holds.1 (Fin 4) (Fin 13) Unit 2 (by decide)).agree hyb4Slots V
    (bnOrc.full Ohyb4) 1 v (some 5) h uhyb4_slot1

/-! ## The negatives -/

-- `Good` fails one round past the universe: the only reliable set is
-- `{0, 1, 2}`, and it populates no round `4`.
example :
    ¬ (orcaellaLive (Validator := Fin 4) (BlockId := Fin 13) (Payload := Unit) 2).Good
      Ohyb4 0 4 := by
  rintro ⟨T, ⟨hsub, hcard⟩, hsync, hpop⟩
  have hne : T.Nonempty := Finset.card_pos.mp (by change 3 ≤ T.card at hcard; omega)
  obtain ⟨v, hv⟩ := hne
  obtain ⟨b, hb, hbc, hbr⟩ := hpop 4 (by omega) (by omega) v hv
  have hno : ∀ b : Fin 13, (Uhyb4.block b).round ≠ 4 := by decide
  exact hno b hbr

-- A reliable set containing the crashed validator populates nothing
-- past genesis: the mixed bound enters only through the reliable set.
example : ¬ PopulatedOn Uhyb4 {0, 1, 3} 1 := by decide

/-- **The slack `fb + fc` is exact at `n = 4`**: no descent law holds at
slack `0` — a full committee would put the crashed validator in every
reliable set, and its round-`1` slot commits for nobody. -/
theorem not_descent_zero :
    ¬ (orcaellaLive (Validator := Fin 4) (BlockId := Fin 13) (Payload := Unit) 2).Descent 0 := by
  intro hD
  obtain ⟨T, hcard, hT⟩ := hD.goodLeaders Ohyb4 0 3 ohyb4_good
  have hTuniv : T = Finset.univ :=
    Finset.eq_univ_of_card T (le_antisymm (Finset.card_le_univ T) (by simpa using hcard))
  obtain ⟨L, hL⟩ := hT (Sched orcLeader4 orcWin4 4 (by decide) (by decide)) (bnOrc.full Ohyb4) 6
    (coversUpto_full (LeanDag.Barnacle.Orcaella.holds.1 (Fin 4) (Fin 13) Unit 2 (by decide))
      Ohyb4 3)
    (by omega) (by decide) (by rw [hTuniv]; exact Finset.mem_univ _)
  have hcand := (LeanDag.Barnacle.Orcaella.holds.1 (Fin 4) (Fin 13) Unit 2 (by decide)).candidates
    _ _ _ 6 L hL
  have hall : ∀ L : Fin 13, ¬ bnOrc.IsLeaderBlock
      (Sched orcLeader4 orcWin4 4 (by decide) (by decide)) Ohyb4 6 L := by decide
  exact hall L hcand

/-! ## `Ubad` — the crash-prone equivocator the subtype excludes -/

/-- Genesis from all four; at round `1` the correct validators author
one block each, and the *crash-prone* validator `3` authors **two**
(ids `7` and `8`, one author, one round). -/
def badBlk : Fin 9 → Block (Fin 4) (Fin 9) Unit := fun i =>
  if h : (i : ℕ) < 4 then
    { round := 0, creator := ⟨i, by omega⟩, refs := ∅, payload := () }
  else if h : (i : ℕ) < 7 then
    { round := 1, creator := ⟨(i : ℕ) - 4, by omega⟩, refs := {0, 1, 2}, payload := () }
  else
    { round := 1, creator := 3, refs := {1, 2, 3}, payload := () }

/-- A **lawful** universe: `no_equivocation` constrains only the
fully-correct class `{0, 1, 2}`, and the twins' author `3` is outside
it. -/
def Ubad : BlockUniverse (Fin 4) (Fin 9) Unit where
  ids := Finset.univ
  block := badBlk
  complete := by decide
  valid := by decide
  no_equivocation := by decide

-- … and yet the hybrid model's assumption fails: `3` is honest — not
-- Byzantine — and equivocates. `Ubad` inhabits `BlockUniverse` but not
-- the instantiation's subtype: the bundled clause is load-bearing.
example : ¬ HonestNoEquiv Ubad := by decide

#print axioms ohyb4_commit
#print axioms not_descent_zero

end OrcaellaBase

end Barnacle

end LeanDagTest
