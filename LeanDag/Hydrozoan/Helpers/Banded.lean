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
    LeanDag.Hydrozoan.IsVote U' b L ↔ LeanDag.Hydrozoan.IsVote U b L := by
  unfold LeanDag.Hydrozoan.IsVote
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

/-! ## The counting rules -/

theorem votesSet_bnd (h : AgreeBand R.toDagRule U U' lo hi g g') {L : BlockId} {n n' : ℕ}
    (hnn : n + g = n' + g') (h1 : lo < n + g) (h2 : n + g ≤ hi) :
    ((blocksAt U n).filter fun b => LeanDag.Hydrozoan.IsVote U b L)
      ⊆ ((blocksAt U' n').filter fun b =>
          LeanDag.Hydrozoan.IsVote U' b L) := by
  intro b hb
  obtain ⟨hbA, hbv⟩ := Finset.mem_filter.mp hb
  have hbU : b ∈ U.ids := (Finset.mem_filter.mp hbA).1
  have hbr : (U.block b).round = n := (Finset.mem_filter.mp hbA).2
  exact Finset.mem_filter.mpr ⟨blocksAt_bnd h hnn (by omega) (by omega) hbA,
    (isVote_bnd h hbU (by omega) (by omega)).mpr hbv⟩

theorem supportersInView_bnd (h : AgreeBand R.toDagRule U U' lo hi g g')
    {V : LeanDag.Hydrozoan.View U} {V' : LeanDag.Hydrozoan.View U'}
    (hv : ∀ b, b ∈ V.ids → lo ≤ (U.block b).round + g → (U.block b).round + g ≤ hi →
      b ∈ V'.ids)
    {L : BlockId} {n n' : ℕ} (hnn : n + g = n' + g') (h1 : lo < n + g) (h2 : n + g ≤ hi) :
    supportersIn U V L n
      ⊆ supportersIn U' V' L n' := by
  intro a ha
  unfold supportersIn LeanDag.creatorsOf at ha ⊢
  obtain ⟨b, hb, hba⟩ := Finset.mem_image.mp ha
  obtain ⟨hbf, hbV⟩ := Finset.mem_inter.mp hb
  obtain ⟨hbA, hbv⟩ := Finset.mem_filter.mp hbf
  have hbU : b ∈ U.ids := (Finset.mem_filter.mp hbA).1
  have hbr : (U.block b).round = n := (Finset.mem_filter.mp hbA).2
  refine Finset.mem_image.mpr ⟨b, Finset.mem_inter.mpr ⟨Finset.mem_filter.mpr
    ⟨blocksAt_bnd h hnn (by omega) (by omega) hbA,
      (isVote_bnd h hbU (by omega) (by omega)).mpr hbv⟩,
    hv b hbV (by omega) (by omega)⟩, ?_⟩
  rw [(AnchoredRule.band_block h hbU (by omega) (by omega)).2]; exact hba

/-- Two rounds of slack: a certificate counts votes cast by its own
refs. -/
theorem voteBlocks_bnd (h : AgreeBand R.toDagRule U U' lo hi g g') {C L : BlockId}
    (hC : C ∈ U.ids) (h1 : lo + 1 < (U.block C).round + g)
    (h2 : (U.block C).round + g ≤ hi) :
    LeanDag.Hydrozoan.voteBlocks U' C L = LeanDag.Hydrozoan.voteBlocks U C L := by
  unfold LeanDag.Hydrozoan.voteBlocks
  rw [AnchoredRule.band_refs h hC (by omega) h2]
  refine Finset.filter_congr fun b hb => ?_
  have hbU := U.complete C hC b hb
  have hbr := (U.valid C hC).predecessor b hb
  simpa using isVote_bnd h hbU (by omega) (by omega)

theorem isCertificate_bnd (h : AgreeBand R.toDagRule U U' lo hi g g') {C L : BlockId}
    (hC : C ∈ U.ids) (h1 : lo + 1 < (U.block C).round + g)
    (h2 : (U.block C).round + g ≤ hi) :
    LeanDag.Hydrozoan.IsCertificate U' C L ↔ LeanDag.Hydrozoan.IsCertificate U C L := by
  unfold LeanDag.Hydrozoan.IsCertificate
  rw [voteBlocks_bnd h hC h1 h2, AnchoredRule.creatorsOf_band h]
  intro b hb
  have hbp := (Finset.mem_filter.mp hb).1
  have := (U.valid C hC).predecessor b hbp
  exact ⟨U.complete C hC b hbp, by omega, by omega⟩

theorem certificates_bnd (h : AgreeBand R.toDagRule U U' lo hi g g') {L : BlockId} {n n' : ℕ}
    (hnn : n + g = n' + g') (h1 : lo ≤ n + g) (h2 : n + 2 + g ≤ hi) :
    LeanDag.Hydrozoan.certificates U L n ⊆ LeanDag.Hydrozoan.certificates U' L n' := by
  intro C hC
  obtain ⟨hCA, hCc⟩ := Finset.mem_filter.mp hC
  have hCU : C ∈ U.ids := (Finset.mem_filter.mp hCA).1
  have hCr : (U.block C).round = n + 2 := (Finset.mem_filter.mp hCA).2
  exact Finset.mem_filter.mpr ⟨blocksAt_bnd h (by omega) (by omega) (by omega) hCA,
    (isCertificate_bnd h hCU (by omega) (by omega)).mpr hCc⟩

/-- And back, for a certificate the band already had. -/
theorem certificates_bnd_old (h : AgreeBand R.toDagRule U U' lo hi g g') {L : BlockId} {n n' : ℕ}
    (hnn : n + g = n' + g') (h1 : lo ≤ n + g) (h2 : n + 2 + g ≤ hi) {C : BlockId}
    (hCU : C ∈ U.ids) (hC : C ∈ LeanDag.Hydrozoan.certificates U' L n') :
    C ∈ LeanDag.Hydrozoan.certificates U L n := by
  obtain ⟨hCA, hCc⟩ := Finset.mem_filter.mp hC
  have hCr : (U.block C).round = n + 2 :=
    of_mem_blocksAt_old h (n := n + 2) (n' := n' + 2) (by omega) (by omega) (by omega) hCU hCA
  exact Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨hCU, hCr⟩,
    (isCertificate_bnd h hCU (by omega) (by omega)).mp hCc⟩

theorem certifiersInView_bnd (h : AgreeBand R.toDagRule U U' lo hi g g')
    {V : LeanDag.Hydrozoan.View U} {V' : LeanDag.Hydrozoan.View U'}
    (hv : ∀ b, b ∈ V.ids → lo ≤ (U.block b).round + g → (U.block b).round + g ≤ hi →
      b ∈ V'.ids)
    {L : BlockId} {n n' : ℕ} (hnn : n + g = n' + g') (h1 : lo ≤ n + g)
    (h2 : n + 2 + g ≤ hi) :
    LeanDag.Hydrozoan.certifiersInView U V L n
      ⊆ LeanDag.Hydrozoan.certifiersInView U' V' L n' := by
  intro a ha
  unfold LeanDag.Hydrozoan.certifiersInView LeanDag.Hydrozoan.certificatesInView
    LeanDag.creatorsOf at ha ⊢
  obtain ⟨C, hC, hCa⟩ := Finset.mem_image.mp ha
  obtain ⟨hCc, hCV⟩ := Finset.mem_inter.mp hC
  have hCU : C ∈ U.ids := (Finset.mem_filter.mp (Finset.mem_filter.mp hCc).1).1
  have hCr : (U.block C).round = n + 2 := (Finset.mem_filter.mp (Finset.mem_filter.mp hCc).1).2
  refine Finset.mem_image.mpr ⟨C, Finset.mem_inter.mpr
    ⟨certificates_bnd h hnn h1 h2 hCc, hv C hCV (by omega) (by omega)⟩, ?_⟩
  rw [(AnchoredRule.band_block h hCU (by omega) (by omega)).2]; exact hCa

/-- **The blame set is carried across.** A blamer references no
candidate, its refs are the refs it had, and a candidate the band
did not carry is not among them — so it slotBlames the slot still. -/
theorem blamesInView_bnd (h : AgreeBand R.toDagRule U U' lo hi g g')
    {V : LeanDag.Hydrozoan.View U} {V' : LeanDag.Hydrozoan.View U'}
    (hv : ∀ b, b ∈ V.ids → lo ≤ (U.block b).round + g → (U.block b).round + g ≤ hi →
      b ∈ V'.ids)
    {S S' : LeanDag.Slots Replica} {k k' : ℕ}
    (hkk : S.slotRound k + g = S'.slotRound k' + g') (hlead : S.leader k = S'.leader k')
    (h1 : lo ≤ S.slotRound k + g) (h2 : S.slotRound k + 1 + g ≤ hi) :
    slotBlamesIn (S := S) U V k
      ⊆ slotBlamesIn (S := S') U' V' k' := by
  intro a ha
  unfold slotBlamesIn LeanDag.creatorsOf at ha ⊢
  obtain ⟨b, hb, hba⟩ := Finset.mem_image.mp ha
  obtain ⟨hbf, hbV⟩ := Finset.mem_inter.mp hb
  obtain ⟨hbA, hbn⟩ := Finset.mem_filter.mp hbf
  have hbU : b ∈ U.ids := (Finset.mem_filter.mp hbA).1
  have hbr : (U.block b).round = votingRound (S := S) Replica k :=
    (Finset.mem_filter.mp hbA).2
  have hvr : votingRound (S := S) Replica k = S.slotRound k + 1 := rfl
  have hvr' : votingRound (S := S') Replica k' = S'.slotRound k' + 1 := rfl
  refine Finset.mem_image.mpr ⟨b, Finset.mem_inter.mpr ⟨Finset.mem_filter.mpr
    ⟨blocksAt_bnd h (n := votingRound (S := S) Replica k)
        (n' := votingRound (S := S') Replica k')
        (by omega) (by omega) (by omega) hbA,
      ?_⟩, hv b hbV (by omega) (by omega)⟩, ?_⟩
  · rw [AnchoredRule.band_refs h hbU (by omega) (by omega)]
    intro j hj hjL
    have hjU : j ∈ U.ids := U.complete b hbU j hj
    exact hbn j hj (AnchoredRule.isLeaderBlock_band_old h hkk hlead (by omega) (by omega) hjU hjL)
  · rw [(AnchoredRule.band_block h hbU (by omega) (by omega)).2]; exact hba

/-! ## The two anchored tests

Each in three parts: forward, back for a candidate the band already
had, and — the clause a one-directional band forces and the earlier
`AgreeAbove` family never needed — that a candidate the band did not
carry passes neither test, because the anchor's cone never leaves the
blocks the band had and an old voter names only old blocks. -/

theorem certifiedIn_bnd (h : AgreeBand R.toDagRule U U' lo hi g g') {A L : BlockId} {n n' : ℕ}
    (hA : A ∈ U.ids) (hAlo : lo ≤ (U.block A).round + g)
    (hAhi : (U.block A).round + g ≤ hi) (hnn : n + g = n' + g')
    (h1 : lo ≤ n + g) (h2 : n + 2 + g ≤ hi)
    (hc : LeanDag.Hydrozoan.CertifiedIn U A L n) :
    LeanDag.Hydrozoan.CertifiedIn U' A L n' := by
  obtain ⟨C, hC, hre⟩ := hc
  have hCr : (U.block C).round = n + 2 := (Finset.mem_filter.mp (Finset.mem_filter.mp hC).1).2
  have hlink : (R.toDagRule.block U C).round = (U.block C).round := rfl
  exact ⟨C, certificates_bnd h hnn h1 h2 hC,
    AgreeBand.reaches_of h hA hAhi hre (by omega)⟩

theorem certifiedIn_bnd_old (h : AgreeBand R.toDagRule U U' lo hi g g') {A L : BlockId} {n n' : ℕ}
    (hA : A ∈ U.ids) (hAlo : lo ≤ (U.block A).round + g)
    (hAhi : (U.block A).round + g ≤ hi) (hnn : n + g = n' + g')
    (h1 : lo ≤ n + g) (h2 : n + 2 + g ≤ hi)
    (hc : LeanDag.Hydrozoan.CertifiedIn U' A L n') :
    LeanDag.Hydrozoan.CertifiedIn U A L n := by
  obtain ⟨C, hC, hre⟩ := hc
  have hCr' : (U'.block C).round = n' + 2 := (Finset.mem_filter.mp (Finset.mem_filter.mp hC).1).2
  have hlink : (R.toDagRule.block U' C).round = (U'.block C).round := rfl
  obtain ⟨hCU, hreU, -⟩ := AgreeBand.reaches_old h hA hAlo hAhi hre (by omega)
  exact ⟨C, certificates_bnd_old h hnn h1 h2 hCU hC, hreU⟩

theorem not_certifiedIn_bnd_novel (h : AgreeBand R.toDagRule U U' lo hi g g') {A L : BlockId}
    {n n' : ℕ} (hA : A ∈ U.ids) (hAlo : lo ≤ (U.block A).round + g)
    (hAhi : (U.block A).round + g ≤ hi) (hnn : n + g = n' + g')
    (h1 : lo ≤ n + g) (h2 : n + 2 + g ≤ hi) (hL : L ∉ U.ids) :
    ¬ LeanDag.Hydrozoan.CertifiedIn U' A L n' := by
  rintro ⟨C, hC, hre⟩
  have hCr' : (U'.block C).round = n' + 2 := (Finset.mem_filter.mp (Finset.mem_filter.mp hC).1).2
  have hlink : (R.toDagRule.block U' C).round = (U'.block C).round := rfl
  obtain ⟨hCU, -, hCeq⟩ := AgreeBand.reaches_old h hA hAlo hAhi hre (by omega)
  have hCr : (U.block C).round = n + 2 := by
    have hce : (U.block C).round + g = (U'.block C).round + g' := hCeq
    omega
  have hcert : LeanDag.Hydrozoan.IsCertificate U' C L := (Finset.mem_filter.mp hC).2
  rw [isCertificate_bnd h hCU (by omega) (by omega)] at hcert
  unfold LeanDag.Hydrozoan.IsCertificate at hcert
  have hempty : LeanDag.Hydrozoan.voteBlocks U C L = ∅ := by
    rw [Finset.eq_empty_iff_forall_notMem]
    intro b hb
    obtain ⟨hbp, hbv⟩ := Finset.mem_filter.mp hb
    exact hL (U.complete b (U.complete C hCU b hbp) L hbv)
  rw [hempty] at hcert
  simp only [LeanDag.creatorsOf, Finset.image_empty, Finset.card_empty,
    Nat.le_zero] at hcert
  have : 0 < LeanDag.Hydrozoan.qCert Replica := by
    unfold LeanDag.Hydrozoan.qCert; omega
  omega

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
    have hbvU : LeanDag.Hydrozoan.IsVote U b L :=
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
    simp only [hydrozoanAnchored_wave] at hhi
    rcases hc with hc | hc
    · exact Or.inl (le_trans hc (Finset.card_le_card
        (supportersInView_bnd h (fun b hb h1 h2 => hV b hb (by omega) (by omega))
          (n := S.slotRound k + 1) (n' := S'.slotRound k' + 1) (by omega) (by omega)
          (by omega))))
    · exact Or.inr (le_trans hc (Finset.card_le_card
        (certifiersInView_bnd h (fun b hb h1 h2 => hV b hb (by omega) (by omega))
          (n := S.slotRound k) (n' := S'.slotRound k') (by omega) (by omega) (by omega))))
  skip_band := by
    intro S S' U U' lo hi g g' V V' k k' h hkk hlk hlo hhi hV hs
    simp only [hydrozoanAnchored_wave] at hhi
    exact le_trans hs (Finset.card_le_card
      (blamesInView_bnd h (fun b hb h1 h2 => hV b hb (by omega) (by omega))
        hkk hlk (by omega) (by omega)))
  link_band := by
    intro S S' U U' lo hi g g' A L k k' i h hA hAlo hAhi hkk _ hlo hhi hi hL
    simp only [hydrozoanAnchored_wave] at hhi
    rcases i with _ | _ | i
    · exact ⟨fun h' => certifiedIn_bnd_old h hA hAlo hAhi hkk (by omega) (by omega) h',
        fun h' => certifiedIn_bnd h hA hAlo hAhi hkk (by omega) (by omega) h'⟩
    · exact ⟨fun h' => weakLinked_bnd_old h hA hAlo hAhi hkk (by omega) (by omega) h',
        fun h' => weakLinked_bnd h hA hAlo hAhi hkk (by omega) (by omega) h'⟩
    · exact absurd hi (by change ¬ (i + 1 + 1 < 2); omega)
  link_novel := by
    intro S S' U U' lo hi g g' A L k k' i h hA hAlo hAhi hkk _ hlo hhi hi _ hLo
    simp only [hydrozoanAnchored_wave] at hhi
    rcases i with _ | _ | i
    · exact not_certifiedIn_bnd_novel h hA hAlo hAhi hkk (by omega) (by omega) hLo
    · exact not_weakLinked_bnd_novel h hA hAlo hAhi hkk (by omega) (by omega) hLo
    · exact absurd hi (by change ¬ (i + 1 + 1 < 2); omega)

omit S in
/-- **Hydrozoan reads a band**: the relation's band at its laws. -/
theorem banded : Banded (rule (Replica := Replica) (BlockId := BlockId)) :=
  AnchoredRule.banded hydrozoanBandLaws

end Laws

end Hydrozoan

end LeanDag
