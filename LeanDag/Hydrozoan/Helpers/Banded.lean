import LeanDag.Hydrozoan.Helpers.Carrier
import LeanDag.Hydrozoan.Helpers.SlotAgreement
import LeanDag.Hydrozoan.SlotAgreement.Proof
import LeanDag.Properties.Band
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Data.Finset.Lattice.Fold

/-!
# Hydrozoan's rules read a band of rounds

Not part of the audit surface. The transfer lemmas `Properties.Banded`
needs of this protocol, replacing the two families this file was split
from: one for `Persist`, over extensions, and one for `Local`, over
agreement above a round. `AgreeBand` covers both, so there is one family;
the induction over the derivation is the relation's, at the band laws
at the end of the file, and persistence and locality are corollaries.

**One-directionality is the whole difference.** `AgreeAbove` compares
membership with an iff, and the lemmas it supported were equalities of
sets. A band is one-directional — the larger universe may hold blocks
the band did not, which is what a fill does — so those become
containments, which is all the counting rules need, and the negative
clauses of the two anchored skips need a new argument: a candidate the
band did not carry is invisible to an old anchor, because the anchor's
cone never leaves the blocks the band already had.

The guards are the ones the earlier file recorded. A **candidate** is
read at the slot's own round, so `lo ≤ round` suffices. A **vote** is
read from a block's refs, and a band compares refs only strictly
above `lo`, so counting votes needs `lo < round`. A **certificate**
counts votes cast by its own refs, so it needs `lo + 1 < round`. The
ceiling is new and uniform: every read must also sit at or below `hi`.
-/

namespace LeanDag

namespace Hydrozoan

open LeanDag.Properties

variable {Replica : Type} [Fintype Replica] [DecidableEq Replica]
variable {BlockId : Type} [DecidableEq BlockId]
variable [LeanDag.Hydrozoan.Faults Replica]
variable {U U' : LeanDag.Hydrozoan.BlockUniverse Replica BlockId} {lo hi g g' : ℕ}

/-! The lemmas are stated for **any** anchored rule on Hydrozoan's
record, so that Optimal-Hydrozoan, which shares the blocks, votes,
certificates and slotBlames, reads them at its own carrier. -/

variable {R : AnchoredRule Replica BlockId Unit ValidWrt (NonByzantine : Finset Replica)}

/-! ## Blocks

The band's projections are the relation's `band_*` lemmas; what is
Hydrozoan's own is its round layer and its votes. -/

/-- A round layer inside the band is carried across. Containment, not
equality: `U'` may hold blocks there that `U` did not. -/
theorem blocksAt_bnd (h : AgreeBand R.toDagRule U U' lo hi g g') {n n' : ℕ}
    (hnn : n + g = n' + g') (h1 : lo ≤ n + g) (h2 : n + g ≤ hi) :
    blocksAt U n ⊆ blocksAt U' n' := by
  intro b hb
  simp only [blocksAt, Finset.mem_filter] at hb ⊢
  have hbr := (AnchoredRule.band_block h hb.1 (by omega) (by omega)).1
  exact ⟨AnchoredRule.band_mem h hb.1 (by omega) (by omega), by omega⟩

theorem isVote_bnd (h : AgreeBand R.toDagRule U U' lo hi g g') {b L : BlockId} (hb : b ∈ U.ids)
    (h1 : lo < (U.block b).round + g) (h2 : (U.block b).round + g ≤ hi) :
    IsVote U' b L ↔ IsVote U b L := by
  unfold IsVote
  rw [AnchoredRule.band_refs h hb h1 h2]

/-- What a block of `U'` at a band round supplies, when it is a block
the band already had. -/
theorem of_mem_blocksAt_old (h : AgreeBand R.toDagRule U U' lo hi g g') {b : BlockId} {n n' : ℕ}
    (hnn : n + g = n' + g') (h1 : lo ≤ n + g) (h2 : n + g ≤ hi) (hbU : b ∈ U.ids)
    (hb : b ∈ blocksAt U' n') : (U.block b).round = n := by
  obtain ⟨hbm, hbr⟩ := Finset.mem_filter.mp hb
  have := (AnchoredRule.band_block' h hbU hbm (by omega) (by omega)).1
  omega


variable [S : LeanDag.Slots Replica]

/-! ## The two anchored tests

Each in three parts: forward, back for a candidate the band already
had, and — the clause a one-directional band forces and the earlier
`AgreeAbove` family never needed — that a candidate the band did not
carry passes neither test, because the anchor's cone never leaves the
blocks the band had and an old voter names only old blocks. -/

theorem weakLinked_bnd (h : AgreeBand R.toDagRule U U' lo hi g g') {A L : BlockId} {n n' : ℕ}
    (hA : A ∈ U.ids) (hAlo : lo ≤ (U.block A).round + g)
    (hAhi : (U.block A).round + g ≤ hi) (hnn : n + g = n' + g')
    (h1 : lo ≤ n + g) (h2 : n + 1 + g ≤ hi)
    (hw : LeanDag.Hydrozoan.WeakLinked U A L n) :
    LeanDag.Hydrozoan.WeakLinked U' A L n' := by
  obtain ⟨s, hs, hcard⟩ := hw
  have hsU : ∀ b ∈ s, b ∈ U.ids ∧ (U.block b).round = n + 1 := fun b hb =>
    ⟨(Finset.mem_filter.mp (hs b hb).1).1, (Finset.mem_filter.mp (hs b hb).1).2⟩
  refine ⟨s, fun b hb => ?_, ?_⟩
  · obtain ⟨hbA, hbv, hbre⟩ := hs b hb
    obtain ⟨hbU, hbr⟩ := hsU b hb
    have hlink : (R.toDagRule.block U b).round = (U.block b).round := rfl
    exact ⟨blocksAt_bnd h (n := n + 1) (n' := n' + 1) (by omega) (by omega) (by omega) hbA,
      (isVote_bnd h hbU (by omega) (by omega)).mpr hbv,
      AgreeBand.reaches_of h hA hAhi hbre (by omega)⟩
  · rw [AnchoredRule.creatorsOf_band h (fun b hb => ⟨(hsU b hb).1, by have := (hsU b hb).2; omega,
      by have := (hsU b hb).2; omega⟩)]
    exact hcard

theorem weakLinked_bnd_old (h : AgreeBand R.toDagRule U U' lo hi g g') {A L : BlockId} {n n' : ℕ}
    (hA : A ∈ U.ids) (hAlo : lo ≤ (U.block A).round + g)
    (hAhi : (U.block A).round + g ≤ hi) (hnn : n + g = n' + g')
    (h1 : lo ≤ n + g) (h2 : n + 1 + g ≤ hi)
    (hw : LeanDag.Hydrozoan.WeakLinked U' A L n') :
    LeanDag.Hydrozoan.WeakLinked U A L n := by
  obtain ⟨s, hs, hcard⟩ := hw
  have hsU : ∀ b ∈ s, b ∈ U.ids ∧ (U.block b).round = n + 1 := by
    intro b hb
    obtain ⟨hbA, -, hbre⟩ := hs b hb
    have hbr' : (U'.block b).round = n' + 1 := (Finset.mem_filter.mp hbA).2
    have hlink : (R.toDagRule.block U' b).round = (U'.block b).round := rfl
    obtain ⟨hbU, -, hbeq⟩ := AgreeBand.reaches_old h hA hAlo hAhi hbre (by omega)
    have hbe : (U.block b).round + g = (U'.block b).round + g' := hbeq
    exact ⟨hbU, by omega⟩
  refine ⟨s, fun b hb => ?_, ?_⟩
  · obtain ⟨hbA, hbv, hbre⟩ := hs b hb
    obtain ⟨hbU, hbr⟩ := hsU b hb
    have hlink : (R.toDagRule.block U' b).round = (U'.block b).round := rfl
    have hbr'' : (U'.block b).round = n' + 1 := (Finset.mem_filter.mp hbA).2
    obtain ⟨-, hbreU, -⟩ := AgreeBand.reaches_old h hA hAlo hAhi hbre (by omega)
    exact ⟨Finset.mem_filter.mpr ⟨hbU, hbr⟩,
      (isVote_bnd h hbU (by omega) (by omega)).mp hbv, hbreU⟩
  · rw [← AnchoredRule.creatorsOf_band h (fun b hb => ⟨(hsU b hb).1, by have := (hsU b hb).2; omega,
      by have := (hsU b hb).2; omega⟩)]
    exact hcard

theorem not_weakLinked_bnd_novel (h : AgreeBand R.toDagRule U U' lo hi g g') {A L : BlockId} {n n' : ℕ}
    (hA : A ∈ U.ids) (hAlo : lo ≤ (U.block A).round + g)
    (hAhi : (U.block A).round + g ≤ hi) (hnn : n + g = n' + g')
    (h1 : lo ≤ n + g) (h2 : n + 1 + g ≤ hi) (hL : L ∉ U.ids) :
    ¬ LeanDag.Hydrozoan.WeakLinked U' A L n' := by
  rintro ⟨s, hs, hcard⟩
  have hsempty : s = ∅ := by
    rw [Finset.eq_empty_iff_forall_notMem]
    intro b hb
    obtain ⟨hbA, hbv, hbre⟩ := hs b hb
    have hbr' : (U'.block b).round = n' + 1 := (Finset.mem_filter.mp hbA).2
    have hlink : (R.toDagRule.block U' b).round = (U'.block b).round := rfl
    obtain ⟨hbU, -, hbeq⟩ := AgreeBand.reaches_old h hA hAlo hAhi hbre (by omega)
    have hbr : (U.block b).round = n + 1 := by
      have hbe : (U.block b).round + g = (U'.block b).round + g' := hbeq
      omega
    have hbvU : IsVote U b L :=
      (isVote_bnd h hbU (by omega) (by omega)).mp hbv
    exact hL (U.complete b hbU L hbvU)
  rw [hsempty] at hcard
  simp only [LeanDag.creatorsOf, Finset.image_empty, Finset.card_empty,
    Nat.le_zero] at hcard
  have : 0 < LeanDag.Hydrozoan.qWeak Replica := by
    unfold LeanDag.Hydrozoan.qWeak; omega
  omega

/-! ## The band laws

What the relation's band induction asks of the rules: each direct
predicate and each rung carries across the band, and a candidate the
band did not carry is linked from no old anchor. -/

section Laws

variable [LinearOrder BlockId]

omit S in
theorem hydrozoanBandLaws : (hydrozoanAnchored Replica BlockId).BandLaws where
  commit_band := by
    intro S S' U U' lo hi g g' V V' k k' L h hkk hlk hlo hhi hV _ hc
    simp only [hydrozoanAnchored_waveAt] at hhi
    rcases hc with hc | hc
    · exact Or.inl (AnchoredRule.holdsAtLeast_votesFor_band h hV (by omega) (by omega) (by omega) hc)
    · exact Or.inr (AnchoredRule.holdsAtLeast_certificatesAt_band h hV (by omega) (by omega)
        (by omega) (AnchoredRule.isVote_band_at h (by omega) (by omega)) hc)
  skip_band := by
    intro S S' U U' lo hi g g' V V' k k' h hkk hlk hlo hhi hV hs
    simp only [hydrozoanAnchored_waveAt] at hhi
    exact AnchoredRule.holdsAtLeast_slotBlamers_band h hkk hlk hlo.le (by omega) hV hs
  link_band := by
    intro S S' U U' lo hi g g' A L k k' i h hA hAlo hAhi hkk _ hlo hhi hi hL
    simp only [hydrozoanAnchored_waveAt] at hhi
    rcases i with _ | _ | i
    · exact AnchoredRule.linkedVia_certificatesAt_band h hA hAlo hAhi (by omega) (by omega)
        (by omega) (AnchoredRule.isVote_band_at h (by omega) (by omega))
    · exact ⟨fun h' => weakLinked_bnd_old h hA hAlo hAhi hkk (by omega) (by omega) h',
        fun h' => weakLinked_bnd h hA hAlo hAhi hkk (by omega) (by omega) h'⟩
    · exact absurd hi (by change ¬ (i + 1 + 1 < 2); omega)
  link_novel := by
    intro S S' U U' lo hi g g' A L k k' i h hA hAlo hAhi hkk _ hlo hhi hi _ hLo
    simp only [hydrozoanAnchored_waveAt] at hhi
    rcases i with _ | _ | i
    · exact AnchoredRule.not_linkedVia_certificatesAt_band_novel h hA hAlo hAhi
        (n := S.slotRound k + 2) (by omega) (by omega) (by omega)
        (AnchoredRule.not_isVote_band_novel h hLo) (by unfold qCert; omega)
    · exact not_weakLinked_bnd_novel h hA hAlo hAhi hkk (by omega) (by omega) hLo
    · exact absurd hi (by change ¬ (i + 1 + 1 < 2); omega)

omit S in
/-- **Hydrozoan reads a band**: the relation's band at its laws. -/
theorem banded : Banded (rule (Replica := Replica) (BlockId := BlockId)) :=
  AnchoredRule.banded hydrozoanBandLaws (fun _ _ => rfl)

end Laws

end Hydrozoan

end LeanDag
