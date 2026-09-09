import LeanDag.Common.Anchored
import LeanDag.Common.History
import LeanDag.Properties.Band
import LeanDag.Properties.Agree
import LeanDag.Properties.Derived.Frame
import LeanDag.Properties.Candidate
import LeanDag.Properties.Optional.Direct
import LeanDag.Properties.Commit
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Data.Finset.Lattice.Fold

/-!
# An anchored rule as a carrier, and its band

`AnchoredRule.toDagRule` is the carrier of an anchored rule: the record
as universe, the record's views, the relation as verdict. The properties
that every such carrier has are proved here once — agreement, the
candidate and direct-commit properties, the indirect property, and
**the band**: a verdict reads a band of rounds, so it survives any
transformation that preserves that band.

The band induction is one proof over the derivation, and what it asks
of a rule is `BandLaws`: that its direct commit, direct skip and link
rungs carry across a band that covers the rounds they read, and that a
candidate the band did not carry is linked at no rung. Each rule proves
those four facts about its own counting predicates; the rest is here.
-/

namespace LeanDag

open Properties

variable {Validator : Type} [Fintype Validator] [DecidableEq Validator]
variable {BlockId : Type} [DecidableEq BlockId] {Payload : Type}
variable {P : Validity Validator BlockId Payload} {honest : Finset Validator}

namespace AnchoredRule

variable (R : AnchoredRule Validator BlockId Payload P honest)

/-! ## The carrier -/

/-- **An anchored rule as a carrier**: the record as universe, the record's
views, the relation as the verdict. -/
def toDagRule [P.Mechanised] : DagRule Validator BlockId Payload where
  Universe := BlockRecord Validator BlockId Payload P honest
  View := fun U => U.View
  block := fun U i => U.block i
  ids := fun U => U.ids
  viewIds := fun V => V.ids
  viewSound := fun V => V.subset_ids
  viewComplete := fun V => V.complete
  causal := fun U => U.causal
  Decided := fun S _ V k v => R.Decided (S := S) _ V k v

variable [P.Mechanised]

@[simp] theorem toDagRule_ids (U : BlockRecord Validator BlockId Payload P honest) :
    R.toDagRule.ids U = U.ids := rfl
@[simp] theorem toDagRule_block (U : BlockRecord Validator BlockId Payload P honest) :
    R.toDagRule.block U = U.block := rfl
@[simp] theorem toDagRule_viewIds {U : BlockRecord Validator BlockId Payload P honest}
    (V : U.View) : R.toDagRule.viewIds V = V.ids := rfl
theorem toDagRule_decided {S : Slots Validator} {U : BlockRecord Validator BlockId Payload P honest}
    {V : U.View} {k : ℕ} {v : Option BlockId} :
    R.toDagRule.Decided S V k v ↔ R.Decided (S := S) U V k v := Iff.rfl
theorem toDagRule_isCandidate {S : Slots Validator}
    {U : BlockRecord Validator BlockId Payload P honest} {k : ℕ} {L : BlockId} :
    R.toDagRule.IsCandidate S U k L ↔ IsLeaderBlock (S := S) U k L := Iff.rfl

/-- **An anchored rule read through a projection, as a carrier**: any
type `X` whose elements project to records, the projections' views, the
relation at the projection as the verdict. For a rule at a validity
weaker than the universe's, and for a rule whose laws hold only under an
invariant. -/
def toDagRuleVia {X : Type} (f : X → BlockRecord Validator BlockId Payload P honest) :
    DagRule Validator BlockId Payload where
  Universe := X
  View := fun U => (f U).View
  block := fun U i => (f U).block i
  ids := fun U => (f U).ids
  viewIds := fun V => V.ids
  viewSound := fun V => V.subset_ids
  viewComplete := fun V => V.complete
  causal := fun U => (f U).causal
  Decided := fun S U V k v => R.Decided (S := S) (f U) V k v

/-- **An anchored rule under an invariant, as a carrier**: the records
satisfying `I` as universes. -/
abbrev toDagRuleOn (I : BlockRecord Validator BlockId Payload P honest → Prop) :
    DagRule Validator BlockId Payload :=
  R.toDagRuleVia (fun U : {U : BlockRecord Validator BlockId Payload P honest // I U} => U.val)

variable {R} {I : BlockRecord Validator BlockId Payload P honest → Prop}

/-- **Two views decide alike.** -/
theorem agree (hl : R.Laws) : Agree R.toDagRule :=
  fun S _ _ V₂ _ _ _ h₁ h₂ => decided_unique (S := S) hl trivial h₁ V₂ _ h₂

/-- **Two views decide alike**, under the invariant. -/
theorem agreeOn {J : Slots Validator → BlockRecord Validator BlockId Payload P honest → Prop}
    (hl : R.Laws J) (hJ : ∀ S U, I U → J S U) : Agree (R.toDagRuleOn I) :=
  fun S U _ V₂ _ _ _ h₁ h₂ => decided_unique (S := S) hl (hJ S U.val U.property) h₁ V₂ _ h₂

/-- **A commit names the slot's candidate**, under the invariant. -/
theorem commitsCandidateOn : CommitsCandidate (R.toDagRuleOn I) :=
  fun S _ _ _ _ hd => isLeaderBlock_of_decided (S := S) hd

/-- **And a direct commit is a verdict**, under the invariant. -/
theorem commitsDirectOn :
    CommitsDirect (R.toDagRuleOn I) (fun {U} V L r => R.Commit U.val V L r) :=
  fun S _ _ _ _ hc hd => Decided.directCommit (S := S) hc hd

variable {X : Type} {f : X → BlockRecord Validator BlockId Payload P honest}

/-- **Two views decide alike**, through a projection whose images satisfy
the laws' invariant. -/
theorem agreeVia {J : Slots Validator → BlockRecord Validator BlockId Payload P honest → Prop}
    (hl : R.Laws J) (hJ : ∀ S U, J S (f U)) : Agree (R.toDagRuleVia f) :=
  fun S U _ V₂ _ _ _ h₁ h₂ => decided_unique (S := S) hl (hJ S U) h₁ V₂ _ h₂

/-- **A commit names the slot's candidate**, through a projection. -/
theorem commitsCandidateVia : CommitsCandidate (R.toDagRuleVia f) :=
  fun S _ _ _ _ hd => isLeaderBlock_of_decided (S := S) hd

/-- **And a direct commit is a verdict**, through a projection. -/
theorem commitsDirectVia :
    CommitsDirect (R.toDagRuleVia f) (fun {U} V L r => R.Commit (f U) V L r) :=
  fun S _ _ _ _ hc hd => Decided.directCommit (S := S) hc hd

/-- **A commit names the slot's candidate.** -/
theorem commitsCandidate : CommitsCandidate R.toDagRule :=
  fun S _ _ _ _ hd => isLeaderBlock_of_decided (S := S) hd

/-- **And a direct commit is a verdict.** -/
theorem commitsDirect : CommitsDirect R.toDagRule (fun {U} V L r => R.Commit U V L r) :=
  fun S _ _ _ _ hc hd => Decided.directCommit (S := S) hc hd

/-! ## The indirect property -/

/-- **The indirect rule is a property.** Given the anchor, the verdict is
determined by the rungs: the first rung holding a candidate commits the
tie-break's choice, and no rung holding any skips. The verdict survives
a reassignment of leaders elsewhere, since the case split reads only
slot `i`'s candidates and the anchor's history. What it needs of the
tie is that a nonempty rung has a choice, `hleast`. -/
theorem indirect (hcongr : R.LinkCongr)
    (hleast : ∀ {S : Slots Validator} {U : BlockRecord Validator BlockId Payload P honest}
      {A : BlockId} {i k : ℕ}, i < R.rungs →
      (∃ L, IsLeaderBlock (S := S) U k L ∧ R.Link i U A L S k) →
      ∃ L, IsLeaderBlock (S := S) U k L ∧ R.Link i U A L S k ∧
        R.Least (S := S) U A i k L) :
    Indirect R.toDagRule (fun sr i j => sr i + R.wave + 1 ≤ sr j) := by
  classical
  intro S U V i j A helig hj hmid
  have he : R.Eligible (S := S) i j := R.eligible_iff.mpr helig
  have hlt : i < j := R.lt_of_eligible he
  have heq : ∀ (S' : Slots Validator), S'.slotRound = S.slotRound → ∀ x y,
      R.Eligible (S := S') x y ↔ R.Eligible (S := S) x y := by
    intro S' hround x y
    simp only [Eligible, EligibleAt, hround]
  have hcand : ∀ (S' : Slots Validator), S'.slotRound = S.slotRound →
      S'.leader i = S.leader i → ∀ L,
      IsLeaderBlock (S := S') U i L ↔ IsLeaderBlock (S := S) U i L := by
    intro S' hround hlead L
    simp only [IsLeaderBlock, hround, hlead]
  -- the first rung holding a candidate, if any
  by_cases hc : ∃ r, r < R.rungs ∧ ∃ L, IsLeaderBlock (S := S) U i L ∧
      R.Link r U A L S i
  · obtain ⟨r, hr, hrL⟩ := hc
    -- take the least such rung
    have hex : ∃ r, r < R.rungs ∧ ∃ L, IsLeaderBlock (S := S) U i L ∧
        R.Link r U A L S i := ⟨r, hr, hrL⟩
    let r₀ := Nat.find hex
    have hr₀ := Nat.find_spec hex
    have hmin : ∀ r', r' < r₀ → ¬ ∃ L, IsLeaderBlock (S := S) U i L ∧
        R.Link r' U A L S i := fun r' hr' =>
      fun hL => Nat.find_min hex hr' ⟨lt_trans hr' hr₀.1, hL⟩
    obtain ⟨L, hL, hlink, hLmin⟩ := hleast hr₀.1 hr₀.2
    refine ⟨some L, fun S' hround hlead hj' hmid' => ?_⟩
    refine Decided.indirectCommit (S := S') (i := r₀) hlt ((heq S' hround i j).mpr he) hj'
      (fun i' h1 h2 h3 => hmid' i' h1 h2 (R.eligible_iff (S := S) |>.mp ((heq S' hround i i').mp h3)))
      hr₀.1 ?_ ((hcand S' hround hlead L).mpr hL)
      (hcongr (S₁ := S) (S₂ := S') (congrFun hround i).symm hlead.symm hlink) ?_
    · intro r' hr' L' hL' hlink'
      have hlink' := hcongr (S₁ := S') (S₂ := S) (congrFun hround i) hlead hlink'
      exact hmin r' hr' ⟨L', (hcand S' hround hlead L').mp hL', hlink'⟩
    · intro L' hL' hlink'
      have hlink' := hcongr (S₁ := S') (S₂ := S) (congrFun hround i) hlead hlink'
      exact hLmin L' ((hcand S' hround hlead L').mp hL') hlink'
  · push Not at hc
    refine ⟨none, fun S' hround hlead hj' hmid' => ?_⟩
    refine Decided.indirectSkip (S := S') hlt ((heq S' hround i j).mpr he) hj'
      (fun i' h1 h2 h3 => hmid' i' h1 h2 (R.eligible_iff (S := S) |>.mp ((heq S' hround i i').mp h3)))
      ?_
    intro r hr L hL hlink
    have hlink := hcongr (S₁ := S') (S₂ := S) (congrFun hround i) hlead hlink
    exact hc r hr L ((hcand S' hround hlead L).mp hL) hlink

/-- The indirect property under the invariant: the same case split, at
the record inside. -/
theorem indirectVia {X : Type} {f : X → BlockRecord Validator BlockId Payload P honest}
    (hcongr : R.LinkCongr)
    (hleast : ∀ {S : Slots Validator} {U : BlockRecord Validator BlockId Payload P honest}
      {A : BlockId} {i k : ℕ}, i < R.rungs →
      (∃ L, IsLeaderBlock (S := S) U k L ∧ R.Link i U A L S k) →
      ∃ L, IsLeaderBlock (S := S) U k L ∧ R.Link i U A L S k ∧
        R.Least (S := S) U A i k L) :
    Indirect (R.toDagRuleVia f) (fun sr i j => sr i + R.wave + 1 ≤ sr j) :=
  fun S U V i j A helig hj hmid => indirect hcongr hleast S (U := f U) V i j A helig hj hmid

theorem indirectOn (hcongr : R.LinkCongr)
    (hleast : ∀ {S : Slots Validator} {U : BlockRecord Validator BlockId Payload P honest}
      {A : BlockId} {i k : ℕ}, i < R.rungs →
      (∃ L, IsLeaderBlock (S := S) U k L ∧ R.Link i U A L S k) →
      ∃ L, IsLeaderBlock (S := S) U k L ∧ R.Link i U A L S k ∧
        R.Least (S := S) U A i k L) :
    Indirect (R.toDagRuleOn I) (fun sr i j => sr i + R.wave + 1 ≤ sr j) :=
  fun S U V i j A helig hj hmid => indirect hcongr hleast S (U := U.val) V i j A helig hj hmid

/-! ## The band -/

section Band

variable {U U' : BlockRecord Validator BlockId Payload P honest} {lo hi g g' : ℕ}
variable {S S' : Slots Validator}

/-! The band's three field projections, in the record's vocabulary: the
generic forms speak of `R.toDagRule.block U`, which is `U.block` by
definition but a distinct atom to `omega`. -/

theorem band_mem (h : AgreeBand R.toDagRule U U' lo hi g g') {b : BlockId}
    (hb : b ∈ U.ids) (h1 : lo ≤ (U.block b).round + g) (h2 : (U.block b).round + g ≤ hi) :
    b ∈ U'.ids := h.mem b hb h1 h2

theorem band_block (h : AgreeBand R.toDagRule U U' lo hi g g') {b : BlockId}
    (hb : b ∈ U.ids) (h1 : lo ≤ (U.block b).round + g) (h2 : (U.block b).round + g ≤ hi) :
    (U'.block b).round + g' = (U.block b).round + g ∧
      (U'.block b).creator = (U.block b).creator :=
  h.block b hb (Or.inl ⟨h1, h2⟩)

theorem band_block' (h : AgreeBand R.toDagRule U U' lo hi g g') {b : BlockId}
    (hb : b ∈ U.ids) (hb' : b ∈ U'.ids)
    (h1 : lo ≤ (U'.block b).round + g') (h2 : (U'.block b).round + g' ≤ hi) :
    (U'.block b).round + g' = (U.block b).round + g ∧
      (U'.block b).creator = (U.block b).creator :=
  h.block b hb (Or.inr ⟨hb', h1, h2⟩)

theorem band_refs (h : AgreeBand R.toDagRule U U' lo hi g g') {b : BlockId}
    (hb : b ∈ U.ids) (h1 : lo < (U.block b).round + g) (h2 : (U.block b).round + g ≤ hi) :
    (U'.block b).refs = (U.block b).refs := h.refs b hb h1 h2

/-- A round layer of `U` lands on the layer of `U'` the shift names. -/
theorem blocksAt_band (h : AgreeBand R.toDagRule U U' lo hi g g') {r r' : ℕ}
    (hrr : r + g = r' + g') (h1 : lo ≤ r + g) (h2 : r + g ≤ hi) :
    blocksAt U r ⊆ blocksAt U' r' := by
  intro b hb
  rw [mem_blocksAt] at hb ⊢
  have hbb := band_block h hb.1 (by omega) (by omega)
  exact ⟨band_mem h hb.1 (by omega) (by omega), by omega⟩

/-- The creators of a set of in-band blocks are what they were. -/
theorem creatorsOf_band (h : AgreeBand R.toDagRule U U' lo hi g g') {s : Finset BlockId}
    (hs : ∀ b ∈ s, b ∈ U.ids ∧ lo ≤ (U.block b).round + g ∧ (U.block b).round + g ≤ hi) :
    creatorsOf U'.block s = creatorsOf U.block s :=
  Finset.image_congr fun i hi' => (band_block h (hs i hi').1 (hs i hi').2.1 (hs i hi').2.2).2

/-- A candidate of a slot is a candidate of the slot the shift names. -/
theorem isLeaderBlock_band (h : AgreeBand R.toDagRule U U' lo hi g g') {k k' : ℕ} {L : BlockId}
    (hkk : S.slotRound k + g = S'.slotRound k' + g') (hlk : S.leader k = S'.leader k')
    (h1 : lo ≤ S.slotRound k + g) (h2 : S.slotRound k + g ≤ hi)
    (hL : IsLeaderBlock (S := S) U k L) : IsLeaderBlock (S := S') U' k' L := by
  obtain ⟨hm, hr, hc⟩ := hL
  have hb := AgreeBand.block_band h (R := R.toDagRule) hm (by simp only [toDagRule_block]; omega)
    (by simp only [toDagRule_block]; omega)
  simp only [toDagRule_block] at hb
  exact ⟨AgreeBand.mem_band h hm (by simp only [toDagRule_block]; omega)
    (by simp only [toDagRule_block]; omega), by omega, by rw [hb.2, hc, hlk]⟩

/-- An old candidate of the shifted slot was a candidate of the slot. -/
theorem isLeaderBlock_band_old (h : AgreeBand R.toDagRule U U' lo hi g g') {k k' : ℕ}
    (hkk : S.slotRound k + g = S'.slotRound k' + g') (hlk : S.leader k = S'.leader k')
    (h1 : lo ≤ S.slotRound k + g) (h2 : S.slotRound k + g ≤ hi) {L : BlockId}
    (hLU : L ∈ U.ids) (hL : IsLeaderBlock (S := S') U' k' L) :
    IsLeaderBlock (S := S) U k L := by
  obtain ⟨hm, hr, hc⟩ := hL
  have hb := AgreeBand.block_band' h (R := R.toDagRule) hLU hm
    (by simp only [toDagRule_block]; omega) (by simp only [toDagRule_block]; omega)
  simp only [toDagRule_block] at hb
  exact ⟨hLU, by omega, by rw [← hb.2, hc, ← hlk]⟩

/-- **A band restricts to views**: two views holding the band's blocks
alike are in the band themselves, since a view's blocks are its
record's. What a rule's band laws can be read at, for a direct
predicate a view evaluates. -/
theorem agreeBand_view (h : AgreeBand R.toDagRule U U' lo hi g g') {V : U.View} {V' : U'.View}
    (hV : ∀ b, b ∈ V.ids → lo ≤ (U.block b).round + g → (U.block b).round + g ≤ hi →
      b ∈ V'.ids) :
    AgreeBand R.toDagRule V.toRecord V'.toRecord lo hi g g' where
  mem := fun b hb h1 h2 => hV b hb h1 h2
  block := fun b hb hor => h.block b (V.subset_ids hb)
    (hor.imp id (fun ⟨hb', h1, h2⟩ => ⟨V'.subset_ids hb', h1, h2⟩))
  refs := fun b hb h1 h2 => h.refs b (V.subset_ids hb) h1 h2

/-! ### Votes, certificates and links across the band

Every rule's direct commit is a threshold on a set the view holds, and
every rung a link to a set in the anchor's cone; the sets transport
across the band here, once. The one hypothesis a rule supplies is that
its vote relation agrees across the band (`isVote_band` for the plain
vote). -/

/-- A plain vote reads the voter's references, which the band preserves. -/
theorem isVote_band (h : AgreeBand R.toDagRule U U' lo hi g g') {b L : BlockId} (hb : b ∈ U.ids)
    (h1 : lo < (U.block b).round + g) (h2 : (U.block b).round + g ≤ hi) :
    IsVote U' b L ↔ IsVote U b L := by
  unfold IsVote; rw [band_refs h hb h1 h2]

/-- The votes for `L` at an in-band round are votes at the shifted round. -/
theorem votesFor_band (h : AgreeBand R.toDagRule U U' lo hi g g') {L : BlockId} {n n' : ℕ}
    (hnn : n + g = n' + g') (h1 : lo < n + g) (h2 : n + g ≤ hi) :
    votesFor U L n ⊆ votesFor U' L n' := by
  intro q hq
  rw [mem_votesFor] at hq ⊢
  obtain ⟨hqU, hqr, hqL⟩ := hq
  have hb := band_block h hqU (by omega) (by omega)
  exact ⟨band_mem h hqU (by omega) (by omega), by omega,
    by rw [band_refs h hqU (by omega) (by omega)]; exact hqL⟩

/-- **What a view holds of an in-band set, the shifted view holds of the
shifted set**: the authors are what they were. -/
theorem heldAuthors_band (h : AgreeBand R.toDagRule U U' lo hi g g') {V : U.View} {V' : U'.View}
    (hV : ∀ b, b ∈ V.ids → lo ≤ (U.block b).round + g → (U.block b).round + g ≤ hi →
      b ∈ V'.ids)
    {s s' : Finset BlockId}
    (hs : ∀ b ∈ s, b ∈ U.ids ∧ lo ≤ (U.block b).round + g ∧ (U.block b).round + g ≤ hi)
    (hss : s ⊆ s') : heldAuthors U V s ⊆ heldAuthors U' V' s' := by
  intro w hw
  obtain ⟨b, hb, hbV, hbc⟩ := mem_heldAuthors.mp hw
  obtain ⟨hbU, hb1, hb2⟩ := hs b hb
  exact mem_heldAuthors.mpr ⟨b, hss hb, hV b hbV hb1 hb2,
    by rw [(band_block h hbU hb1 hb2).2]; exact hbc⟩

/-- A direct rule's threshold, held of an in-band set, is held of the
shifted set in the shifted view. -/
theorem holdsAtLeast_band (h : AgreeBand R.toDagRule U U' lo hi g g') {V : U.View} {V' : U'.View}
    (hV : ∀ b, b ∈ V.ids → lo ≤ (U.block b).round + g → (U.block b).round + g ≤ hi →
      b ∈ V'.ids)
    {s s' : Finset BlockId}
    (hs : ∀ b ∈ s, b ∈ U.ids ∧ lo ≤ (U.block b).round + g ∧ (U.block b).round + g ≤ hi)
    (hss : s ⊆ s') {t : ℕ} (hc : HoldsAtLeast U V t s) : HoldsAtLeast U' V' t s' :=
  le_trans hc (Finset.card_le_card (heldAuthors_band h hV hs hss))

/-- Supporters held at an in-band round transport. -/
theorem holdsAtLeast_votesFor_band (h : AgreeBand R.toDagRule U U' lo hi g g')
    {V : U.View} {V' : U'.View}
    (hV : ∀ b, b ∈ V.ids → lo ≤ (U.block b).round + g → (U.block b).round + g ≤ hi →
      b ∈ V'.ids)
    {L : BlockId} {n n' : ℕ} (hnn : n + g = n' + g') (h1 : lo < n + g) (h2 : n + g ≤ hi)
    {t : ℕ} (hc : HoldsAtLeast U V t (votesFor U L n)) :
    HoldsAtLeast U' V' t (votesFor U' L n') :=
  holdsAtLeast_band h hV
    (fun b hb => by
      obtain ⟨hbU, hbr, -⟩ := mem_votesFor.mp hb
      exact ⟨hbU, by omega, by omega⟩)
    (votesFor_band h hnn h1 h2) hc

section Certificates

variable {Vote Vote' : BlockId → BlockId → Prop} [∀ b L, Decidable (Vote b L)]
  [∀ b L, Decidable (Vote' b L)]

/-- The votes an in-band block carries are the votes it carried, when the
vote relations agree on its references; two rounds of slack. -/
theorem carriedVotes_band (h : AgreeBand R.toDagRule U U' lo hi g g') {C L : BlockId}
    (hC : C ∈ U.ids) (h1 : lo < (U.block C).round + g) (h2 : (U.block C).round + g ≤ hi)
    (hvote : ∀ b ∈ (U.block C).refs, (Vote' b L ↔ Vote b L)) :
    carriedVotes U' Vote' C L = carriedVotes U Vote C L := by
  unfold carriedVotes
  rw [band_refs h hC h1 h2]
  exact Finset.filter_congr fun b hb => hvote b hb

theorem carriesVotes_band (h : AgreeBand R.toDagRule U U' lo hi g g') {t : ℕ} {C L : BlockId}
    (hC : C ∈ U.ids) (h1 : lo < (U.block C).round + g) (h2 : (U.block C).round + g ≤ hi)
    (hvote : ∀ b ∈ (U.block C).refs, (Vote' b L ↔ Vote b L)) :
    CarriesVotes U' Vote' t C L ↔ CarriesVotes U Vote t C L := by
  unfold CarriesVotes
  rw [carriedVotes_band h hC h1 h2 hvote, creatorsOf_band h]
  intro b hb
  have hbm := (mem_carriedVotes.mp hb).1
  have hbU := U.complete C hC b hbm
  have := U.round_of_mem_refs hC hbm
  exact ⟨hbU, by omega, by omega⟩

/-- An in-band block is a certificate at the shifted round exactly when
it was one. -/
theorem mem_certificatesAt_band (h : AgreeBand R.toDagRule U U' lo hi g g') {t : ℕ}
    {L C : BlockId} {n n' : ℕ} (hC : C ∈ U.ids) (hr : (U.block C).round = n)
    (hnn : n + g = n' + g') (h1 : lo < n + g) (h2 : n + g ≤ hi)
    (hvote : ∀ b ∈ (U.block C).refs, (Vote' b L ↔ Vote b L)) :
    C ∈ certificatesAt U' Vote' t L n' ↔ C ∈ certificatesAt U Vote t L n := by
  simp only [mem_certificatesAt]
  have hb := band_block h hC (by omega) (by omega)
  rw [carriesVotes_band h hC (by omega) (by omega) hvote]
  exact ⟨fun hx => ⟨hC, hr, hx.2.2⟩,
    fun hx => ⟨band_mem h hC (by omega) (by omega), by omega, hx.2.2⟩⟩

/-- The certificates at an in-band round transport. -/
theorem certificatesAt_band (h : AgreeBand R.toDagRule U U' lo hi g g') {t : ℕ} {L : BlockId}
    {n n' : ℕ} (hnn : n + g = n' + g') (h1 : lo < n + g) (h2 : n + g ≤ hi)
    (hvote : ∀ C ∈ U.ids, (U.block C).round = n →
      ∀ b ∈ (U.block C).refs, (Vote' b L ↔ Vote b L)) :
    certificatesAt U Vote t L n ⊆ certificatesAt U' Vote' t L n' := by
  intro C hC
  obtain ⟨hCU, hCr, -⟩ := mem_certificatesAt.mp hC
  exact (mem_certificatesAt_band h hCU hCr hnn h1 h2 (hvote C hCU hCr)).mpr hC

/-- Certificates held in view transport. -/
theorem holdsAtLeast_certificatesAt_band (h : AgreeBand R.toDagRule U U' lo hi g g')
    {V : U.View} {V' : U'.View}
    (hV : ∀ b, b ∈ V.ids → lo ≤ (U.block b).round + g → (U.block b).round + g ≤ hi →
      b ∈ V'.ids)
    {t : ℕ} {L : BlockId} {n n' : ℕ} (hnn : n + g = n' + g') (h1 : lo < n + g)
    (h2 : n + g ≤ hi)
    (hvote : ∀ C ∈ U.ids, (U.block C).round = n →
      ∀ b ∈ (U.block C).refs, (Vote' b L ↔ Vote b L))
    {t' : ℕ} (hc : HoldsAtLeast U V t' (certificatesAt U Vote t L n)) :
    HoldsAtLeast U' V' t' (certificatesAt U' Vote' t L n') :=
  holdsAtLeast_band h hV
    (fun C hC => by
      obtain ⟨hCU, hCr, -⟩ := mem_certificatesAt.mp hC
      exact ⟨hCU, by omega, by omega⟩)
    (certificatesAt_band h hnn h1 h2 hvote) hc

/-- **The anchor links what it linked.** -/
theorem linkedVia_certificatesAt_band (h : AgreeBand R.toDagRule U U' lo hi g g') {A : BlockId}
    (hA : A ∈ U.ids) (hAlo : lo ≤ (U.block A).round + g) (hAhi : (U.block A).round + g ≤ hi)
    {t : ℕ} {L : BlockId} {n n' : ℕ} (hnn : n + g = n' + g') (h1 : lo < n + g)
    (h2 : n + g ≤ hi)
    (hvote : ∀ C ∈ U.ids, (U.block C).round = n →
      ∀ b ∈ (U.block C).refs, (Vote' b L ↔ Vote b L)) :
    LinkedVia U' A (certificatesAt U' Vote' t L n') ↔
      LinkedVia U A (certificatesAt U Vote t L n) := by
  constructor
  · rintro ⟨C, hC, hre⟩
    have hCr' : (U'.block C).round = n' := (mem_certificatesAt.mp hC).2.1
    have hCrR : (R.toDagRule.block U' C).round = n' := hCr'
    obtain ⟨hCU, hreU, hCeq⟩ := AgreeBand.reaches_old h hA hAlo hAhi hre (by omega)
    have hCeq' : (U.block C).round + g = (U'.block C).round + g' := hCeq
    exact ⟨C, (mem_certificatesAt_band h hCU (by omega) hnn h1 h2 (hvote C hCU (by omega))).mp hC,
      hreU⟩
  · rintro ⟨C, hC, hre⟩
    obtain ⟨hCU, hCr, -⟩ := mem_certificatesAt.mp hC
    have hCrR : (R.toDagRule.block U C).round = n := hCr
    exact ⟨C, (mem_certificatesAt_band h hCU hCr hnn h1 h2 (hvote C hCU hCr)).mpr hC,
      AgreeBand.reaches_of h hA hAhi hre (by omega)⟩

/-- **A candidate the band did not carry is certified from no old
anchor.** `hnov` is the rule's reason no old in-band block votes for a
novel candidate (`not_isVote_band_novel` for the plain vote). -/
theorem not_linkedVia_certificatesAt_band_novel (h : AgreeBand R.toDagRule U U' lo hi g g')
    {A : BlockId} (hA : A ∈ U.ids) (hAlo : lo ≤ (U.block A).round + g)
    (hAhi : (U.block A).round + g ≤ hi) {t : ℕ} {L : BlockId} {n n' : ℕ}
    (hnn : n + g = n' + g') (h1 : lo + 1 < n + g) (h2 : n + g ≤ hi)
    (hnov : ∀ b ∈ U.ids, lo < (U.block b).round + g → (U.block b).round + g ≤ hi →
      ¬ Vote' b L) (ht : 0 < t) :
    ¬ LinkedVia U' A (certificatesAt U' Vote' t L n') := by
  rintro ⟨C, hC, hre⟩
  obtain ⟨-, hCr', hcert⟩ := mem_certificatesAt.mp hC
  have hCrR : (R.toDagRule.block U' C).round = n' := hCr'
  obtain ⟨hCU, -, hCeq⟩ := AgreeBand.reaches_old h hA hAlo hAhi hre (by omega)
  have hCeq' : (U.block C).round + g = (U'.block C).round + g' := hCeq
  obtain ⟨b, hb, hv⟩ := exists_vote_of_carriesVotes ht hcert
  rw [band_refs h hCU (by omega) (by omega)] at hb
  have hbU := U.complete C hCU b hb
  have := U.round_of_mem_refs hCU hb
  exact hnov b hbU (by omega) (by omega) hv

/-- No old in-band block plainly votes for a candidate the band did not
carry: its references are the references it had, all old. -/
theorem not_isVote_band_novel (h : AgreeBand R.toDagRule U U' lo hi g g') {L : BlockId}
    (hL : L ∉ U.ids) :
    ∀ b ∈ U.ids, lo < (U.block b).round + g → (U.block b).round + g ≤ hi → ¬ IsVote U' b L :=
  fun b hbU h1 h2 hv => not_isVote_of_notMem hL b hbU ((isVote_band h hbU h1 h2).mp hv)

/-- The plain vote agrees across the band at every in-band certificate:
what `hvote` is for every rule but Mahi-Mahi. -/
theorem isVote_band_at (h : AgreeBand R.toDagRule U U' lo hi g g') {L : BlockId} {n : ℕ}
    (h1 : lo + 1 < n + g) (h2 : n + g ≤ hi) :
    ∀ C ∈ U.ids, (U.block C).round = n → ∀ b ∈ (U.block C).refs,
      (IsVote U' b L ↔ IsVote U b L) := by
  intro C hC hCr b hb
  have hbU := U.complete C hC b hb
  have := U.round_of_mem_refs hC hb
  exact isVote_band h hbU (by omega) (by omega)

end Certificates

/-- **The anchor's cone of supporters is the cone it was.** -/
theorem coneSupporters_band (h : AgreeBand R.toDagRule U U' lo hi g g') {A L : BlockId}
    (hA : A ∈ U.ids) (hAlo : lo ≤ (U.block A).round + g) (hAhi : (U.block A).round + g ≤ hi)
    {n n' : ℕ} (hnn : n + g = n' + g') (h1 : lo < n + g) (h2 : n + g ≤ hi) :
    coneSupporters U' A L n' = coneSupporters U A L n := by
  have hA' : A ∈ U'.ids := band_mem h hA hAlo hAhi
  have hset : coneVotesFor U' A L n' = coneVotesFor U A L n := by
    ext q
    simp only [coneVotesFor, Finset.mem_filter, mem_votesFor]
    constructor
    · rintro ⟨⟨hqU', hqr', hqL⟩, hqh⟩
      have hqre : ReachesFrom U'.block A q := (mem_history_iff (U := U') hA').mp hqh
      have hqrR : (R.toDagRule.block U' q).round = n' := hqr'
      obtain ⟨hqU, hqreU, hqeq⟩ := AgreeBand.reaches_old h hA hAlo hAhi hqre (by omega)
      have hqeq' : (U.block q).round + g = (U'.block q).round + g' := hqeq
      refine ⟨⟨hqU, by omega, ?_⟩, (mem_history_iff (U := U) hA).mpr hqreU⟩
      rwa [band_refs h hqU (by omega) (by omega)] at hqL
    · rintro ⟨⟨hqU, hqr, hqL⟩, hqh⟩
      have hqre : ReachesFrom U.block A q := (mem_history_iff (U := U) hA).mp hqh
      have hqrR : (R.toDagRule.block U q).round = n := hqr
      have hb := band_block h hqU (by omega) (by omega)
      refine ⟨⟨band_mem h hqU (by omega) (by omega), by omega, ?_⟩,
        (mem_history_iff (U := U') hA').mpr (AgreeBand.reaches_of h hA hAhi hqre (by omega))⟩
      rw [band_refs h hqU (by omega) (by omega)]; exact hqL
  unfold coneSupporters
  rw [hset]
  refine creatorsOf_band h fun b hb => ?_
  obtain ⟨hbU, hbr, -⟩ := mem_votesFor.mp (Finset.mem_filter.mp hb).1
  exact ⟨hbU, by omega, by omega⟩

/-- **A candidate the band did not carry has no supporters in an old
anchor's cone**: an old block references only old blocks. -/
theorem coneSupporters_band_novel (h : AgreeBand R.toDagRule U U' lo hi g g') {A L : BlockId}
    (hA : A ∈ U.ids) (hAlo : lo ≤ (U.block A).round + g) (hAhi : (U.block A).round + g ≤ hi)
    {n n' : ℕ} (hnn : n + g = n' + g') (h1 : lo < n + g) (h2 : n + g ≤ hi) (hL : L ∉ U.ids) :
    coneSupporters U' A L n' = ∅ := by
  rw [coneSupporters_band h hA hAlo hAhi hnn h1 h2, Finset.eq_empty_iff_forall_notMem]
  intro v hv
  obtain ⟨q, hq, -, hqL, -, -⟩ := mem_coneSupporters.mp hv
  exact hL (U.complete q hq L hqL)

/-- **Blame carries across the band**: a blamer the view held is a blamer
of the shifted record, every candidate it could reference being old. -/
theorem slotBlamesIn_band (h : AgreeBand R.toDagRule U U' lo hi g g')
    {V : U.View} {V' : U'.View} {k k' : ℕ} (hkk : S.slotRound k + g = S'.slotRound k' + g')
    (hlead : S.leader k = S'.leader k') (hlo : lo ≤ S.slotRound k + g)
    (hhi : S.slotRound k + 1 + g ≤ hi)
    (hV : ∀ b, b ∈ V.ids → lo ≤ (U.block b).round + g → (U.block b).round + g ≤ hi →
      b ∈ V'.ids) :
    slotBlamesIn (S := S) U V k ⊆ slotBlamesIn (S := S') U' V' k' := by
  intro w hw
  obtain ⟨q, hq, hvq⟩ := Finset.mem_image.mp hw
  obtain ⟨hqf, hqV⟩ := Finset.mem_inter.mp hq
  rw [mem_slotBlamers (S := S)] at hqf
  obtain ⟨hqU, hqr, hqn⟩ := hqf
  refine Finset.mem_image.mpr ⟨q, ?_, ?_⟩
  · rw [Finset.mem_inter, mem_slotBlamers (S := S')]
    refine ⟨⟨band_mem h hqU (by omega) (by omega), ?_, ?_⟩, hV q hqV (by omega) (by omega)⟩
    · have := band_block h hqU (by omega) (by omega); omega
    · rw [band_refs h hqU (by omega) (by omega)]
      intro j hj hjL
      exact hqn j hj (isLeaderBlock_band_old h hkk hlead (by omega) (by omega)
        (U.complete q hqU j hj) hjL)
  · rw [(band_block h hqU (by omega) (by omega)).2]; exact hvq

/-- Blamers of a slot held in view transport. -/
theorem holdsAtLeast_slotBlamers_band (h : AgreeBand R.toDagRule U U' lo hi g g')
    {V : U.View} {V' : U'.View} {k k' : ℕ} (hkk : S.slotRound k + g = S'.slotRound k' + g')
    (hlead : S.leader k = S'.leader k') (hlo : lo ≤ S.slotRound k + g)
    (hhi : S.slotRound k + 1 + g ≤ hi)
    (hV : ∀ b, b ∈ V.ids → lo ≤ (U.block b).round + g → (U.block b).round + g ≤ hi →
      b ∈ V'.ids)
    {t : ℕ} (hs : HoldsAtLeast U V t (slotBlamers (S := S) U k)) :
    HoldsAtLeast U' V' t (slotBlamers (S := S') U' k') :=
  le_trans hs (Finset.card_le_card (slotBlamesIn_band h hkk hlead hlo hhi hV))

/-- **What a rule owes the band**: its direct commit, its direct skip and
its link rungs carry across a band covering the rounds they read, and a
candidate the band did not carry is linked at no rung. -/
structure BandLaws : Prop where
  commit_band : ∀ {S S' : Slots Validator} {U U' : BlockRecord Validator BlockId Payload P honest}
    {lo hi g g' : ℕ} {V : U.View} {V' : U'.View} {k k' : ℕ} {L : BlockId},
    AgreeBand R.toDagRule U U' lo hi g g' →
    S.slotRound k + g = S'.slotRound k' + g' → S.leader k = S'.leader k' →
    lo = S.slotRound k + g → S.slotRound k + R.wave + g ≤ hi →
    (∀ b, b ∈ V.ids → lo ≤ (U.block b).round + g → (U.block b).round + g ≤ hi → b ∈ V'.ids) →
    IsLeaderBlock (S := S) U k L →
    R.Commit U V L (S.slotRound k) → R.Commit U' V' L (S'.slotRound k')
  skip_band : ∀ {S S' : Slots Validator} {U U' : BlockRecord Validator BlockId Payload P honest}
    {lo hi g g' : ℕ} {V : U.View} {V' : U'.View} {k k' : ℕ},
    AgreeBand R.toDagRule U U' lo hi g g' →
    S.slotRound k + g = S'.slotRound k' + g' → S.leader k = S'.leader k' →
    lo = S.slotRound k + g → S.slotRound k + R.wave + g ≤ hi →
    (∀ b, b ∈ V.ids → lo ≤ (U.block b).round + g → (U.block b).round + g ≤ hi → b ∈ V'.ids) →
    R.Skip U V S k → R.Skip U' V' S' k'
  /-- An old anchor links what it linked, at every rung. -/
  link_band : ∀ {S S' : Slots Validator} {U U' : BlockRecord Validator BlockId Payload P honest}
    {lo hi g g' : ℕ} {A L : BlockId} {k k' i : ℕ},
    AgreeBand R.toDagRule U U' lo hi g g' → A ∈ U.ids →
    lo ≤ (U.block A).round + g → (U.block A).round + g ≤ hi →
    S.slotRound k + g = S'.slotRound k' + g' → S.leader k = S'.leader k' →
    lo ≤ S.slotRound k + g → S.slotRound k + R.wave + g ≤ hi → i < R.rungs →
    IsLeaderBlock (S := S) U k L →
    (R.Link i U' A L S' k' ↔ R.Link i U A L S k)
  /-- A candidate the band did not carry is linked from no old anchor. -/
  link_novel : ∀ {S S' : Slots Validator} {U U' : BlockRecord Validator BlockId Payload P honest}
    {lo hi g g' : ℕ} {A L : BlockId} {k k' i : ℕ},
    AgreeBand R.toDagRule U U' lo hi g g' → A ∈ U.ids →
    lo ≤ (U.block A).round + g → (U.block A).round + g ≤ hi →
    S.slotRound k + g = S'.slotRound k' + g' → S.leader k = S'.leader k' →
    lo ≤ S.slotRound k + g → S.slotRound k + R.wave + g ≤ hi → i < R.rungs →
    IsLeaderBlock (S := S') U' k' L → L ∉ U.ids → ¬ R.Link i U' A L S' k'

variable (hb : R.BandLaws)
include hb

/-- Rung emptiness carries across the band. -/
theorem rungEmpty_band (h : AgreeBand R.toDagRule U U' lo hi g g') {A : BlockId} {k k' i : ℕ}
    (hA : A ∈ U.ids) (hAlo : lo ≤ (U.block A).round + g) (hAhi : (U.block A).round + g ≤ hi)
    (hkk : S.slotRound k + g = S'.slotRound k' + g') (hlk : S.leader k = S'.leader k')
    (hlo : lo ≤ S.slotRound k + g) (hhi : S.slotRound k + R.wave + g ≤ hi) (hi : i < R.rungs)
    (he : R.RungEmpty (S := S) U A i k) : R.RungEmpty (S := S') U' A i k' := by
  intro L hL hlink
  by_cases hLo : L ∈ U.ids
  · have hL' := isLeaderBlock_band_old h hkk hlk hlo (by omega) hLo hL
    exact he L hL' ((hb.link_band h hA hAlo hAhi hkk hlk hlo hhi hi hL').mp hlink)
  · exact hb.link_novel h hA hAlo hAhi hkk hlk hlo hhi hi hL hLo hlink

/-- The tie-break's choice carries across the band. -/
theorem least_band (h : AgreeBand R.toDagRule U U' lo hi g g') {A L : BlockId} {k k' i : ℕ}
    (hA : A ∈ U.ids) (hAlo : lo ≤ (U.block A).round + g) (hAhi : (U.block A).round + g ≤ hi)
    (hkk : S.slotRound k + g = S'.slotRound k' + g') (hlk : S.leader k = S'.leader k')
    (hlo : lo ≤ S.slotRound k + g) (hhi : S.slotRound k + R.wave + g ≤ hi) (hi : i < R.rungs)
    (hm : R.Least (S := S) U A i k L) : R.Least (S := S') U' A i k' L := by
  intro L' hL' hlink
  by_cases hLo : L' ∈ U.ids
  · have hL'' := isLeaderBlock_band_old h hkk hlk hlo (by omega) hLo hL'
    exact hm L' hL'' ((hb.link_band h hA hAlo hAhi hkk hlk hlo hhi hi hL'').mp hlink)
  · exact absurd hlink (hb.link_novel h hA hAlo hAhi hkk hlk hlo hhi hi hL' hLo)

/-- **Every verdict reads a band of rounds.** One induction over the
derivation. The direct cases read the slot's wave and stop; the indirect
cases read the anchor's derivation and the intermediates', and the top
is the largest of those. -/
theorem banded_aux {V : U.View} {k : ℕ} {v : Option BlockId}
    (hd : R.Decided (S := S) U V k v) :
    ∃ top, S.slotRound k + R.wave ≤ top ∧
      ∀ (g g' d d' : ℕ) (S' : Slots Validator)
        (U' : BlockRecord Validator BlockId Payload P honest) (V' : U'.View) (k' : ℕ),
        k + d' = k' + d →
        (∀ m m', m + d' = m' + d → S.slotRound m ≤ top →
          S.slotRound m + g = S'.slotRound m' + g') →
        (∀ m m', m + d' = m' + d → S.slotRound m ≤ top → S.leader m = S'.leader m') →
        AgreeBand R.toDagRule U U' (S.slotRound k + g) (top + g) g g' →
        (∀ b, b ∈ V.ids → S.slotRound k ≤ (U.block b).round →
          (U.block b).round ≤ top → b ∈ V'.ids) →
        R.Decided (S := S') U' V' k' v := by
  classical
  induction hd with
  | @directCommit k L hL hc =>
      refine ⟨S.slotRound k + R.wave, le_refl _, ?_⟩
      intro g g' d d' S' U' V' k' hkd hsch hlead hab hV
      have hkk : S.slotRound k + g = S'.slotRound k' + g' := hsch k k' hkd (by omega)
      have hlk : S.leader k = S'.leader k' := hlead k k' hkd (by omega)
      exact Decided.directCommit (S := S')
        (isLeaderBlock_band hab hkk hlk (by omega) (by omega) hL)
        (hb.commit_band hab hkk hlk rfl (by omega)
          (fun b hb h1 h2 => hV b hb (by omega) (by omega)) hL hc)
  | @directSkip k hs =>
      refine ⟨S.slotRound k + R.wave, le_refl _, ?_⟩
      intro g g' d d' S' U' V' k' hkd hsch hlead hab hV
      have hkk : S.slotRound k + g = S'.slotRound k' + g' := hsch k k' hkd (by omega)
      have hlk : S.leader k = S'.leader k' := hlead k k' hkd (by omega)
      exact Decided.directSkip (S := S')
        (hb.skip_band hab hkk hlk rfl (by omega)
          (fun b hb h1 h2 => hV b hb (by omega) (by omega)) hs)
  | @indirectCommit k j A L i hkj helig hanchor hmid hi hemp hL hlink hmin ihj ihmid =>
      obtain ⟨topj, htopj, hjt⟩ := ihj
      set f : ℕ → ℕ := fun m =>
        if hh : k < m ∧ m < j ∧ R.Eligible (S := S) k m then
          (ihmid m hh.1 hh.2.1 hh.2.2).choose else 0 with hf
      set top := max topj ((Finset.Ico (k + 1) j).sup f) with htop
      have hAL : IsLeaderBlock (S := S) U j A := isLeaderBlock_of_decided hanchor
      have hkey : ∀ m (h1 : k < m) (h2 : m < j) (h3 : R.Eligible (S := S) k m),
          (ihmid m h1 h2 h3).choose ≤ top := by
        intro m h1 h2 h3
        have heqf : f m = (ihmid m h1 h2 h3).choose := by
          simp only [hf]; exact dif_pos ⟨h1, h2, h3⟩
        rw [← heqf, htop]
        exact le_trans (Finset.le_sup (Finset.mem_Ico.mpr ⟨by omega, h2⟩)) (le_max_right _ _)
      have htj : topj ≤ top := by rw [htop]; exact le_max_left _ _
      have helig' := R.eligible_iff.mp helig
      have htopk : S.slotRound k + R.wave ≤ top := by omega
      refine ⟨top, htopk, ?_⟩
      intro g g' d d' S' U' V' k' hkd hsch hlead hab hV
      have hkk : S.slotRound k + g = S'.slotRound k' + g' := hsch k k' hkd (by omega)
      have hlk : S.leader k = S'.leader k' := hlead k k' hkd (by omega)
      have hjd : j + d' = (j - k + k') + d := by omega
      have hjtop : S.slotRound j ≤ top := by omega
      have hjj : S.slotRound j + g = S'.slotRound (j - k + k') + g' :=
        hsch j _ hjd hjtop
      have hAhi : (U.block A).round + g ≤ top + g := by rw [hAL.2.1]; omega
      have hAlo : S.slotRound k + g ≤ (U.block A).round + g := by rw [hAL.2.1]; omega
      refine Decided.indirectCommit (S := S') (i := i) (by omega) (by
          rw [R.eligible_iff]; omega)
        (hjt g g' d d' S' U' V' (j - k + k') hjd
          (fun m m' hm hbnd => hsch m m' hm (by omega))
          (fun m m' hm hb => hlead m m' hm (by omega))
          (hab.mono (by omega) (by omega))
          (fun b hb h1 h2 => hV b hb (by omega) (by omega))) ?_ hi ?_
        (isLeaderBlock_band hab hkk hlk (by omega) (by omega) hL) ?_ ?_
      · intro i' h1 h2 h3
        have hi'd : (i' - k' + k) + d' = i' + d := by omega
        have hki : k < i' - k' + k := by omega
        have hij : i' - k' + k < j := by omega
        have helg : R.Eligible (S := S) k (i' - k' + k) := by
          have hii := hsch _ i' hi'd
            (le_trans (S.mono (Nat.le_of_lt hij)) hjtop)
          rw [R.eligible_iff (S := S')] at h3
          rw [R.eligible_iff (S := S)]; omega
        have hk2 := hkey _ hki hij helg
        obtain ⟨htopi, hit⟩ := (ihmid _ hki hij helg).choose_spec
        have hkr : S.slotRound k ≤ S.slotRound (i' - k' + k) := S.mono (by omega)
        exact hit g g' d d' S' U' V' i' hi'd
          (fun m m' hm hbnd => hsch m m' hm (by omega))
          (fun m m' hm hb => hlead m m' hm (by omega))
          (hab.mono (by omega) (by omega))
          (fun b hb ha1 ha2 => hV b hb (by omega) (by omega))
      · intro i' hi'
        exact rungEmpty_band hb hab hAL.1 hAlo hAhi hkk hlk (by omega) (by omega)
          (lt_trans hi' hi) (hemp i' hi')
      · exact (hb.link_band hab hAL.1 hAlo hAhi hkk hlk (by omega) (by omega) hi hL).mpr hlink
      · exact least_band hb hab hAL.1 hAlo hAhi hkk hlk (by omega) (by omega) hi hmin
  | @indirectSkip k j A hkj helig hanchor hmid hnone ihj ihmid =>
      obtain ⟨topj, htopj, hjt⟩ := ihj
      set f : ℕ → ℕ := fun m =>
        if hh : k < m ∧ m < j ∧ R.Eligible (S := S) k m then
          (ihmid m hh.1 hh.2.1 hh.2.2).choose else 0 with hf
      set top := max topj ((Finset.Ico (k + 1) j).sup f) with htop
      have hAL : IsLeaderBlock (S := S) U j A := isLeaderBlock_of_decided hanchor
      have hkey : ∀ m (h1 : k < m) (h2 : m < j) (h3 : R.Eligible (S := S) k m),
          (ihmid m h1 h2 h3).choose ≤ top := by
        intro m h1 h2 h3
        have heqf : f m = (ihmid m h1 h2 h3).choose := by
          simp only [hf]; exact dif_pos ⟨h1, h2, h3⟩
        rw [← heqf, htop]
        exact le_trans (Finset.le_sup (Finset.mem_Ico.mpr ⟨by omega, h2⟩)) (le_max_right _ _)
      have htj : topj ≤ top := by rw [htop]; exact le_max_left _ _
      have helig' := R.eligible_iff.mp helig
      have htopk : S.slotRound k + R.wave ≤ top := by omega
      refine ⟨top, htopk, ?_⟩
      intro g g' d d' S' U' V' k' hkd hsch hlead hab hV
      have hkk : S.slotRound k + g = S'.slotRound k' + g' := hsch k k' hkd (by omega)
      have hlk : S.leader k = S'.leader k' := hlead k k' hkd (by omega)
      have hjd : j + d' = (j - k + k') + d := by omega
      have hjtop : S.slotRound j ≤ top := by omega
      have hjj : S.slotRound j + g = S'.slotRound (j - k + k') + g' :=
        hsch j _ hjd hjtop
      have hAhi : (U.block A).round + g ≤ top + g := by rw [hAL.2.1]; omega
      have hAlo : S.slotRound k + g ≤ (U.block A).round + g := by rw [hAL.2.1]; omega
      refine Decided.indirectSkip (S := S') (by omega) (by
          rw [R.eligible_iff]; omega)
        (hjt g g' d d' S' U' V' (j - k + k') hjd
          (fun m m' hm hbnd => hsch m m' hm (by omega))
          (fun m m' hm hb => hlead m m' hm (by omega))
          (hab.mono (by omega) (by omega))
          (fun b hb h1 h2 => hV b hb (by omega) (by omega))) ?_ ?_
      · intro i' h1 h2 h3
        have hi'd : (i' - k' + k) + d' = i' + d := by omega
        have hki : k < i' - k' + k := by omega
        have hij : i' - k' + k < j := by omega
        have helg : R.Eligible (S := S) k (i' - k' + k) := by
          have hii := hsch _ i' hi'd
            (le_trans (S.mono (Nat.le_of_lt hij)) hjtop)
          rw [R.eligible_iff (S := S')] at h3
          rw [R.eligible_iff (S := S)]; omega
        have hk2 := hkey _ hki hij helg
        obtain ⟨htopi, hit⟩ := (ihmid _ hki hij helg).choose_spec
        have hkr : S.slotRound k ≤ S.slotRound (i' - k' + k) := S.mono (by omega)
        exact hit g g' d d' S' U' V' i' hi'd
          (fun m m' hm hbnd => hsch m m' hm (by omega))
          (fun m m' hm hb => hlead m m' hm (by omega))
          (hab.mono (by omega) (by omega))
          (fun b hb ha1 ha2 => hV b hb (by omega) (by omega))
      · intro i hi
        exact rungEmpty_band hb hab hAL.1 hAlo hAhi hkk hlk (by omega) (by omega) hi
          (hnone i hi)

/-- **A directly decided slot's band is tight**: its top is exactly the
slot's own round plus a wave. `banded_aux` gives an upper end that the
derivation determines, and for a direct commit or a direct skip that
derivation reads the slot's own wave and nothing above it. This is what
a mechanism needs when the bound it can afford is fixed in advance
rather than read off the derivation. -/
theorem banded_direct {V : U.View} {k : ℕ} {v : Option BlockId}
    (hd : R.Decided (S := S) U V k v)
    (hdir : (∃ L, v = some L ∧ IsLeaderBlock (S := S) U k L ∧
        R.Commit U V L (S.slotRound k)) ∨ (v = none ∧ R.Skip U V S k)) :
    ∀ (g g' d d' : ℕ) (S' : Slots Validator)
      (U' : BlockRecord Validator BlockId Payload P honest) (V' : U'.View) (k' : ℕ),
      k + d' = k' + d →
      (∀ m m', m + d' = m' + d → S.slotRound m ≤ S.slotRound k + R.wave →
        S.slotRound m + g = S'.slotRound m' + g') →
      (∀ m m', m + d' = m' + d → S.slotRound m ≤ S.slotRound k + R.wave →
        S.leader m = S'.leader m') →
      AgreeBand R.toDagRule U U' (S.slotRound k + g) (S.slotRound k + R.wave + g) g g' →
      (∀ b, b ∈ V.ids → S.slotRound k ≤ (U.block b).round →
        (U.block b).round ≤ S.slotRound k + R.wave → b ∈ V'.ids) →
      R.Decided (S := S') U' V' k' v := by
  intro g g' d d' S' U' V' k' hkd hsch hlead hab hV
  have hkk : S.slotRound k + g = S'.slotRound k' + g' := hsch k k' hkd (by omega)
  have hlk : S.leader k = S'.leader k' := hlead k k' hkd (by omega)
  rcases hdir with ⟨L, hv, hL, hc⟩ | ⟨hv, hs⟩
  · subst hv
    exact Decided.directCommit (S := S')
      (isLeaderBlock_band hab hkk hlk (by omega) (by omega) hL)
      (hb.commit_band hab hkk hlk rfl (by omega)
        (fun b hb h1 h2 => hV b hb (by omega) (by omega)) hL hc)
  · subst hv
    exact Decided.directSkip (S := S')
      (hb.skip_band hab hkk hlk rfl (by omega)
        (fun b hb h1 h2 => hV b hb (by omega) (by omega)) hs)

/-- **A directly decided slot is settled within its own wave**, at a
frame. `banded_direct` says the band's top is the slot's round plus a
wave; this reads that as a bound in rounds, so a schedule agreeing with
this one that far — its widths as well as its leaders — decides the slot
the same way. It is what `Integration.SettlesInTwoEpochs` asks, at the
slots a rule decides directly, and it is a theorem rather than an
assumption. -/
theorem decidedFrameBelow_direct {F : Frame} {a : ℕ → ℕ → Validator}
    {hkf : ∀ r i j, i < F.width r → j < F.width r → a r i = a r j → i = j}
    {V : U.View} {k : ℕ} {v : Option BlockId}
    (hS : S = F.toSlots a hkf) (hd : R.Decided (S := S) U V k v)
    (hdir : (∃ L, v = some L ∧ IsLeaderBlock (S := S) U k L ∧
        R.Commit U V L (S.slotRound k)) ∨ (v = none ∧ R.Skip U V S k)) :
    Properties.DecidedFrameBelow R.toDagRule F a (F.roundOf k + R.wave + 1) V k v := by
  subst hS
  intro F' a' hk' hw ha
  refine banded_direct hb hd hdir 0 0 0 0 (F'.toSlots a' hk') U V k rfl ?_ ?_
    Properties.AgreeBand.refl (fun b hb _ _ => hb)
  · intro m m' hm hbnd
    have hmm : m = m' := by omega
    subst hmm
    simp only [Nat.add_zero, Frame.toSlots_slotRound] at *
    exact (Frame.roundOf_congr hw (by omega)).symm
  · intro m m' hm hbnd
    have hmm : m = m' := by omega
    subst hmm
    simp only [Frame.toSlots_slotRound] at hbnd
    have hro : F'.roundOf m = F.roundOf m := Frame.roundOf_congr hw (by omega)
    have hcum : F'.cum (F.roundOf m) = F.cum (F.roundOf m) := Frame.cum_congr hw (by omega)
    show a (F.roundOf m) _ = a' (F'.roundOf m) _
    rw [hro, hcum]
    exact (ha (F.roundOf m) _ (by omega) (F.pos_lt_width m)).symm

/-- **An anchored rule is banded.** -/
theorem banded : Banded R.toDagRule := by
  intro S U V k v hd
  obtain ⟨top, -, ht⟩ := banded_aux hb (S := S) hd
  exact ⟨top, fun g g' d d' S' U' V' k' hkd hsch hlead hab hV =>
    ht g g' d d' S' U' V' k' hkd hsch hlead hab hV⟩

omit hb in
/-- A band between projections is a band between the records. -/
theorem agreeBand_of_via {X : Type} {f : X → BlockRecord Validator BlockId Payload P honest}
    {U U' : X} {lo hi g g' : ℕ}
    (h : AgreeBand (R.toDagRuleVia f) U U' lo hi g g') :
    AgreeBand R.toDagRule (f U) (f U') lo hi g g' :=
  ⟨h.mem, h.block, h.refs⟩

/-- **The relation reads a band, through a projection.** -/
theorem bandedVia {X : Type} {f : X → BlockRecord Validator BlockId Payload P honest} :
    Banded (R.toDagRuleVia f) := by
  intro S U V k v hd
  obtain ⟨top, -, ht⟩ := banded_aux hb (S := S) hd
  exact ⟨top, fun g g' d d' S' U' V' k' hkd hsch hlead hab hV =>
    ht g g' d d' S' (f U') V' k' hkd hsch hlead (agreeBand_of_via hab) hV⟩

/-- **The relation reads a band, under the invariant.** -/
theorem bandedOn : Banded (R.toDagRuleOn I) := bandedVia hb

end Band

end AnchoredRule

end LeanDag
