import LeanDag.Scheme.Family.Statement
import LeanDag.Scheme.Helpers.Band
import LeanDag.Scheme.Loop.Proof
/-!
# The family's properties — proof

Locality from `Helpers/Local.lean`; the band from the band laws of
`Helpers/Band.lean`, the rule needing nothing of its anchors; the
candidate and indirect properties from the anchored rule; agreement from
the laws of `Helpers/Sufficiency.lean`; safety from the headline.
-/

namespace LeanDag

namespace Scheme

namespace Family

open LeanDag.Properties

theorem leastLocal : LeastLocal := fun _ _ _ _ _ _ _ _ _ => leastSel_local

theorem votedBlockLocal : VotedBlockLocal := by
  intro Validator BlockId Payload _ _ _ P _ honest ord hord σ hσ
  intro R U U' lo hi g g' q a r r' h hq hqlo hqhi hr hrr
  rw [hσ]
  exact votedBlockSel_local (P := P) (honest := honest) hord R h hq hqlo hqhi hr hrr

theorem familyBanded : FamilyBanded := by
  intro Validator BlockId Payload _ _ _ P _ honest Hon p σ hσ hw hl hc
  exact AnchoredRule.bandedOn (schemeBandLaws hσ hw hl hc) (J := fun _ _ => True)
    (fun _ _ => trivial) fun _ _ _ => trivial

theorem familyCandidateIndirect : FamilyCandidateIndirect := by
  intro Validator BlockId Payload _ _ _ P _ honest Hon p σ
  exact ⟨AnchoredRule.commitsCandidateOn,
    AnchoredRule.indirectOn ((schemeAnchored p σ).linkCongr_of_round
      (fun _ U A L r => p.linkSize ≤ (creatorsOf U.block ((certsAt p σ U L r).filter
        (fun C => C ∈ history U A))).card) fun _ _ _ _ _ _ => rfl)
      fun _ h => AnchoredRule.exists_least_of_lt (fun _ _ => Iff.rfl) h⟩

theorem familyQuorateNoEquiv : FamilyQuorateNoEquiv := by
  intro Validator BlockId Payload _ _ _ P _ q _ honest Hon p σ rel
  refine ⟨fun hq U b hb hr => le_trans hq (U.val.creators_quorum hb hr), fun hsub U b c hb hc hbc
    heq hr => U.property b hb c hc (hsub hbc) heq hr⟩

theorem familySelfParent : FamilySelfParent :=
  fun _ _ _ _ _ _ _ _ _ _ U b hb hr => (U.val.valid b hb).self_parent hr

theorem familySafe : FamilySafe := by
  intro Validator BlockId Payload _ _ _ P _ q _ honest Hon f p σ hσ hHon hq hfam
  obtain ⟨hl, -, hc, hlaws⟩ := Loop.family σ hHon hq hfam
  have hw : 2 ≤ p.waveLength := by rcases hfam with ⟨-, hw, -⟩ | ⟨-, hw, -⟩ <;> omega
  have hagree : Agree (schemeRule p σ Hon) := AnchoredRule.agreeOn hlaws (fun _ _ h => h)
  exact ⟨hagree, safety (familyBanded Validator BlockId Payload P honest Hon p σ hσ hw hl hc)
    hagree (familyCandidateIndirect Validator BlockId Payload P honest Hon p σ).1⟩

theorem holds : Statement :=
  ⟨leastLocal, votedBlockLocal, familyBanded, familyCandidateIndirect, familyQuorateNoEquiv,
    familySelfParent, familySafe⟩

end Family

end Scheme

end LeanDag
