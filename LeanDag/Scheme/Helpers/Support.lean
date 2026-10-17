import LeanDag.Scheme.Helpers.Band
import LeanDag.Properties.Deliver
import LeanDag.Properties.Bounded
import LeanDag.Timed.Coverage
/-!
# The family's support: certification is local and commits

Law 1: a certificate reads votes one round below it and the voters'
histories down to the candidate, which a rebase above the settling round
keeps, at a local vote (`isCert_band`). Law 2: a reliable quorum
populating the wave, every member of which certifies the slot's
candidates at the decision round, holds a direct commit in any view
caught up to that round, when the commit threshold is at most the
quorum.
-/

namespace LeanDag

namespace Scheme

open LeanDag.Properties

variable {Validator : Type} [Fintype Validator] [DecidableEq Validator]
variable {BlockId : Type} [LinearOrder BlockId] {Payload : Type}
variable {P : Validity Validator BlockId Payload} {honest : Finset Validator} [P.Mechanised]
variable {p : Params} {σ : VoteSel Validator BlockId Payload P honest} {Hon : Finset Validator}

/-- **Law 1: certification is local.** -/
theorem familySupport_local (hσ : σ.Local) (hw : 2 ≤ p.waveLength) :
    Support.Local (R := schemeRule p σ Hon) (familySupport p σ Hon) := by
  intro U U' G R₀ h c L _ hc hcr hL hLr
  change R₀ + (p.waveLength - 1) ≤ (U.val.block c).round at hcr
  change (U.val.block L).round + (p.waveLength - 1) = (U.val.block c).round at hLr
  have hb := AnchoredRule.agreeBand_of_via (agreeBand_of_rebasedAbove h (U.val.block c).round R₀
    le_rfl)
  exact isCert_band hσ hb hc (by omega) (by omega) hL (by omega)

/-- **A candidate every block of a population certifies is committed** on a
view holding those blocks, when the population meets the commit
threshold. -/
theorem commit_of_certified {T : Finset Validator} {V : U.View} {L : BlockId} {r κ : ℕ}
    (hcm : p.commitThreshold ≤ T.card) (hpop : PopulatedOn U T (r + (p.waveLength - 1)))
    (hcert : ∀ C ∈ U.ids, (U.block C).creator ∈ T → (U.block C).round = r + (p.waveLength - 1) →
      IsCert p σ U C L ∧ C ∈ V.ids) :
    (schemeAnchored p σ).Commit U V L r κ := by
  change p.commitThreshold ≤ (heldAuthors U V (certsAt p σ U L r)).card
  refine le_trans hcm (Finset.card_le_card fun v hv => ?_)
  obtain ⟨C, hC, hCc, hCr⟩ := hpop v hv
  obtain ⟨hcer, hCV⟩ := hcert C hC (hCc ▸ hv) hCr
  exact mem_heldAuthors.mpr ⟨C, Finset.mem_filter.mpr ⟨mem_blocksAt.mpr ⟨hC, hCr⟩, hcer⟩, hCV, hCc⟩

/-- **Law 2: certification commits**, at a commit threshold the quorum
meets. -/
theorem familySupport_commits {rel : Reliability Validator}
    (hlive : p.commitThreshold ≤ Fintype.card Validator - rel.slack) :
    Support.Commits (R := schemeRule p σ Hon) (familySupport p σ Hon) rel := by
  intro S U V T k hq hpop hcert hcov hlead
  letI : Slots Validator := S
  have hw : (familySupport p σ Hon).waveAt (S.kind k) = p.waveLength - 1 := rfl
  obtain ⟨L, hLmem, hLc, hLr⟩ := hpop (S.slotRound k) le_rfl (by omega) (S.leader k) hlead
  have hLlead : IsLeaderBlock U.val k L := ⟨hLmem, hLr, hLc⟩
  have hcommit : (schemeAnchored p σ).Commit U.val V L (S.slotRound k) (S.kind k) :=
    commit_of_certified (le_trans hlive hq.2) (hpop _ (by omega) le_rfl)
      fun C hC hCT hCr => ⟨hcert L hLlead _ hCT C hC rfl hCr, hcov C hC (by
        change (U.val.block C).round ≤ _; rw [hCr, hw])⟩
  refine ⟨L, by omega, AnchoredRule.Decided.directCommit hLlead hcommit, ?_⟩
  intro S' hround hlead' _
  have hS : S'.slotRound k = S.slotRound k := by rw [hround]
  refine AnchoredRule.Decided.directCommit (S := S') ⟨hLmem, by rw [hS]; exact hLr,
    by rw [hlead' k (by omega)]; exact hLc⟩ ?_
  show p.commitThreshold ≤ (heldAuthors U.val V (certsAt p σ U.val L (S'.slotRound k))).card
  rw [hS]
  exact hcommit

/-- **Under coverage, the quorum's blocks reach the candidate**: from one
round above it to the top of the window, layer by layer. -/
theorem reaches_of_coversToward {U : (schemeRule p σ Hon).Universe} {T : Finset Validator}
    {r w : ℕ} {L : BlockId}
    (hpop : ∀ n, r ≤ n → n ≤ r + w → Properties.PopulatedOn (schemeRule p σ Hon) U T n)
    (hct : Timed.CoversToward (schemeRule p σ Hon) U T r w L) (hL : L ∈ U.val.ids)
    (hLr : (U.val.block L).round = r) (hLc : (U.val.block L).creator ∈ T) :
    ∀ m, 1 ≤ m → m ≤ w → ∀ b, b ∈ U.val.ids → (U.val.block b).creator ∈ T →
      (U.val.block b).round = r + m → ReachesFrom U.val.block b L := by
  intro m
  induction m with
  | zero => intro h; omega
  | succ m ih =>
    intro _ hm b hb hbc hbr
    rcases Nat.eq_zero_or_pos m with rfl | hpos
    · exact Relation.ReflTransGen.single
        (hct r le_rfl (by omega) b hb hbc (show (U.val.block b).round = r + 1 by omega) L hL hLc
          hLr Relation.ReflTransGen.refl)
    · obtain ⟨a, ha, hac, har⟩ := hpop (r + m) (by omega) (by omega) _ hLc
      have hac' : (U.val.block a).creator = (U.val.block L).creator := hac
      have hreach := ih hpos (by omega) a ha (by rw [hac']; exact hLc) har
      have hab : a ∈ (U.val.block b).refs :=
        hct (r + m) (by omega) (by omega) b hb hbc (show (U.val.block b).round = r + m + 1 by
          omega) a ha
          (show (U.val.block a).creator ∈ T by rw [hac']; exact hLc) har hreach
      exact Relation.ReflTransGen.head hab hreach

omit [Fintype Validator] in
/-- **A candidate in a voter's history is the voter's vote**, when its author
does not equivocate. -/
theorem votes_of_reaches_record {U : BlockRecord Validator BlockId Payload P honest}
    {H : Finset Validator} (hne : U.NoEquivOn H) {b L : BlockId}
    (hb : b ∈ U.ids) (hL : L ∈ U.ids) (hLc : (U.block L).creator ∈ H)
    (hlt : (U.block L).round < (U.block b).round) (hre : ReachesFrom U.block b L) :
    σ.Votes U b L := by
  have hLh : L ∈ history U b := (mem_history_iff hb).mpr hre
  unfold VoteSel.Votes
  cases hs : σ.sel U b (U.block L).creator (U.block L).round with
  | none => exact absurd rfl (σ.complete U b _ _ hb hlt hs L hLh rfl)
  | some x =>
    obtain ⟨hx, hxc, hxr⟩ := σ.sound U b _ _ x hs
    have hxU := history_subset_ids hb hx
    rw [hne x hxU L hL (by rw [hxc]; exact hLc) hxc hxr]

/-- **An honest candidate in a voter's history is the voter's vote.** -/
theorem votes_of_reaches {U : (schemeRule p σ Hon).Universe} {b L : BlockId}
    (hb : b ∈ U.val.ids) (hL : L ∈ U.val.ids) (hLc : (U.val.block L).creator ∈ Hon)
    (hlt : (U.val.block L).round < (U.val.block b).round) (hre : ReachesFrom U.val.block b L) :
    σ.Votes U.val b L :=
  votes_of_reaches_record U.property hb hL hLc hlt hre

/-- **Law 3: coverage certifies**, at a reliable set inside `Hon` and a
certificate threshold the quorum meets. -/
theorem familySupport_ofCoverage {rel : Reliability Validator} (hHon : rel.correct ⊆ Hon)
    (hw : 2 ≤ p.waveLength) (hw3 : p.voteIsCert = false → 3 ≤ p.waveLength)
    (hcert : p.certThreshold ≤ Fintype.card Validator - rel.slack) :
    Timed.OfCoverage (R := schemeRule p σ Hon) (familySupport p σ Hon) rel := by
  intro U T hq r κ L hpop hct hL hLr hLc c hc hcc hcr
  have hwv : (familySupport p σ Hon).waveAt κ = p.waveLength - 1 := rfl
  rw [hwv] at hpop hct hcr
  have hLr' : (U.val.block L).round = r := hLr
  have hcr' : (U.val.block c).round = r + (p.waveLength - 1) := hcr
  have hLc' : (U.val.block L).creator ∈ T := hLc
  have hcc' : (U.val.block c).creator ∈ T := hcc
  have hreach := reaches_of_coversToward hpop hct hL hLr' hLc'
  have hLH : (U.val.block L).creator ∈ Hon := hHon (hq.1 hLc')
  change IsCert p σ U.val c L
  refine isCert_of_votes σ p (fun _ => votes_of_reaches hc hL hLH (by omega)
      (hreach (p.waveLength - 1) (by omega) le_rfl c hc hcc' hcr'))
    fun hv => ⟨T, le_trans hcert hq.2, fun v hvT => ?_⟩
  have hw3' := hw3 hv
  obtain ⟨a, ha, hac, har⟩ := hpop (r + (p.waveLength - 2)) (by omega) (by omega) v hvT
  have hac' : (U.val.block a).creator = v := hac
  have har' : (U.val.block a).round = r + (p.waveLength - 2) := har
  have hare := hreach (p.waveLength - 2) (by omega) (by omega) a ha (by rw [hac']; exact hvT)
    har'
  have haref : a ∈ (U.val.block c).refs :=
    hct (r + (p.waveLength - 2)) (by omega) (by omega) c hc hcc
      (show (U.val.block c).round = r + (p.waveLength - 2) + 1 by omega) a ha
      (show (U.val.block a).creator ∈ T by rw [hac']; exact hvT) har hare
  exact ⟨a, haref, hac', votes_of_reaches ha hL hLH (by omega) hare⟩

end Scheme

end LeanDag
