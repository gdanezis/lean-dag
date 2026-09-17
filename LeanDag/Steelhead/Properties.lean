import LeanDag.Steelhead.Helpers.Decision
import LeanDag.MahiMahi.Properties
/-!
# Steelhead as a carrier, and the properties its rule gives

`docs/target-properties.md` §11, for the rule at a wavelength function
(`steelhead.md` §6). One carrier per wavelength function, as Mahi-Mahi
has one per width, since `DagRule.Decided` fixes no wave.

**What holds and what does not.** `Agree`, `CommitsCandidate`,
`CommitsDirect`, `Indirect`, `Quorate`, `SelfParent`, `NoEquiv`, and
`Persist` hold at every wavelength function of at least two rounds, each
Mahi-Mahi's fact at the wave of the slot it concerns. `Support` holds
with Mahi-Mahi's certificate and the wave read at the candidate's round;
its `Local` and `Commits` laws at two rounds and above, the timed
model's `OfCoverage` bridge at three and above, the wave-three case by
the core's argument and the higher waves by Mahi-Mahi's. `Banded` does
not hold: a wave that alternates with the round reads an absolute round,
and the band's offset does not preserve it (`docs/target-properties.md`
§3.4c). What the band derives that needs no offset, persistence and view
monotonicity, is proved here through the extension laws; `LocalTruncate`
and the `Safe` headline, which rebase by an arbitrary offset, are not
claimed.
-/

namespace LeanDag

namespace SteelheadProperties

open LeanDag.Properties LeanDag.Steelhead

variable {Validator : Type} [Fintype Validator] [DecidableEq Validator]
variable [F : Faults Validator]
variable {BlockId : Type} [LinearOrder BlockId] {Payload : Type}

/-- **Steelhead as a carrier**, one per wavelength function. -/
def steelheadRule (w : ℕ → ℕ) : DagRule Validator BlockId Payload :=
  (steelheadAnchored Validator BlockId Payload w).toDagRule

/-- **The rule is quorate**, at the core's fault model. -/
theorem quorate (w : ℕ → ℕ) : Quorate (steelheadRule (Validator := Validator)
    (BlockId := BlockId) (Payload := Payload) w) (coreReliability Validator) :=
  fun U => BlockUniverse.quorateOn U

/-- **P3′ at the carrier.** -/
theorem selfParent (w : ℕ → ℕ) : SelfParent (steelheadRule (Validator := Validator)
    (BlockId := BlockId) (Payload := Payload) w) :=
  fun U b hb hr => (U.valid b hb).self_parent hr

/-- **One block per correct author per round.** -/
theorem noEquiv (w : ℕ → ℕ) : NoEquiv (steelheadRule (Validator := Validator)
    (BlockId := BlockId) (Payload := Payload) w) (coreReliability Validator) :=
  fun U b c hb hc hbc heq hr => U.no_equivocation b hb c hc hbc heq hr

/-- **Two views decide alike.** SH2 under the property's name. -/
theorem agree {w : ℕ → ℕ} (hw : ∀ r, 2 ≤ w r) :
    Agree (steelheadRule (Validator := Validator) (BlockId := BlockId) (Payload := Payload) w) :=
  AnchoredRule.agree (steelheadLaws hw)

/-- **A commit names the slot's candidate.** -/
theorem commitsCandidate (w : ℕ → ℕ) :
    CommitsCandidate (steelheadRule (Validator := Validator) (BlockId := BlockId)
      (Payload := Payload) w) :=
  AnchoredRule.commitsCandidate

/-- **And a direct commit is a verdict**, at the slot's own direct
predicate. -/
theorem commitsDirect (w : ℕ → ℕ) :
    CommitsDirect (steelheadRule (Validator := Validator) (BlockId := BlockId)
      (Payload := Payload) w)
      (fun {U} V L r => MahiMahi.DirectCommitIn U V (w r) L r) :=
  AnchoredRule.commitsDirect

open Classical in
/-- **The indirect rule as a property**, with eligibility at each slot's
own wave and no tie to break. -/
theorem indirect {w : ℕ → ℕ} (hw : ∀ r, 1 ≤ w r) :
    Indirect (steelheadRule (Validator := Validator) (BlockId := BlockId) (Payload := Payload) w)
      (fun sr i j => sr i + w (sr i) ≤ sr j) := by
  have h := AnchoredRule.indirect (R := steelheadAnchored Validator BlockId Payload w)
    (Steelhead.linkCongr (w := w)) (fun hi h => Steelhead.exists_least hi h)
  refine h.congr ?_
  intro sr i j
  have := hw (sr i)
  simp only [steelheadAnchored_waveAt]
  omega

/-! ## The extension laws, and persistence

Mahi-Mahi's band laws at the wave of the slot each law concerns, read at
offset zero; the offset band itself is out of reach
(`docs/target-properties.md` §3.4c). -/

/-- An extension of the record is one at any wave's carrier. -/
theorem extends_mm {w : ℕ → ℕ} {U U' : BlockUniverse Validator BlockId Payload} (w' : ℕ)
    (he : Extends (steelheadAnchored Validator BlockId Payload w).toDagRule U U') :
    Extends (MahiMahi.mahiMahiAnchored Validator BlockId Payload w').toDagRule U U' :=
  ⟨he.subset, he.block⟩

/-- **What Steelhead owes an extension**: Mahi-Mahi's band laws at offset
zero, at the wave of the slot. -/
theorem steelheadExtendLaws {w : ℕ → ℕ} (hw : ∀ r, 2 ≤ w r) :
    (steelheadAnchored Validator BlockId Payload w).ExtendLaws where
  commit_ext := fun {S _ _ _ _ k _} he hV hL hc =>
    (MahiMahiProperties.mahiMahiBandLaws (hw (S.slotRound k))).toExtendLaws.commit_ext
      (extends_mm _ he) hV hL hc
  skip_ext := fun {S _ _ _ _ k} he hV hs =>
    (MahiMahiProperties.mahiMahiBandLaws (hw (S.slotRound k))).toExtendLaws.skip_ext
      (extends_mm _ he) hV hs
  link_ext := fun {S _ _ _ _ k _} he hA hi hL =>
    (MahiMahiProperties.mahiMahiBandLaws (hw (S.slotRound k))).toExtendLaws.link_ext
      (extends_mm _ he) hA hi hL
  link_novel_ext := fun {S _ _ _ _ k _} he hA hi hL hLo =>
    (MahiMahiProperties.mahiMahiBandLaws (hw (S.slotRound k))).toExtendLaws.link_novel_ext
      (extends_mm _ he) hA hi hL hLo

/-- **Persistence**: a verdict survives an extension of the record, into
any larger view. -/
theorem persist {w : ℕ → ℕ} (hw : ∀ r, 2 ≤ w r) :
    Persist (steelheadRule (Validator := Validator) (BlockId := BlockId) (Payload := Payload) w) :=
  AnchoredRule.persist (steelheadExtendLaws hw)

/-! ## The support

Mahi-Mahi's certificate, with the certifiers `w r − 1` rounds above a
candidate proposed at `r`. -/

/-- **Steelhead's support**: certifiers at each slot's own decision
round, certification Mahi-Mahi's. -/
def shSupport (w : ℕ → ℕ) : Support (steelheadRule (Validator := Validator) (BlockId := BlockId)
    (Payload := Payload) w) where
  waveAt := fun r => w r - 1
  Certifies := fun U C L => MahiMahi.Certifies U C L

/-- A band at Steelhead's carrier is a band at any wave's. -/
theorem agreeBand_mm {w : ℕ → ℕ} {U U' : BlockUniverse Validator BlockId Payload}
    {lo hi g g' : ℕ} (w' : ℕ)
    (h : AgreeBand (steelheadAnchored Validator BlockId Payload w).toDagRule U U' lo hi g g') :
    AgreeBand (MahiMahi.mahiMahiAnchored Validator BlockId Payload w').toDagRule U U' lo hi g g' :=
  ⟨h.mem, h.block, h.refs⟩

/-- **Law 1**: certification is local, at the wave of the candidate. -/
theorem shSupport_local {w : ℕ → ℕ} (hw : ∀ r, 2 ≤ w r) :
    Support.Local (R := steelheadRule (Validator := Validator) (BlockId := BlockId)
      (Payload := Payload) w) (shSupport w) := by
  intro U U' G R₀ h c L hc hcr hL hLr
  have hw' := hw (BlockRecord.block U L).round
  change R₀ + (w (BlockRecord.block U L).round - 1) ≤ (BlockRecord.block U c).round at hcr
  change (BlockRecord.block U L).round + (w (BlockRecord.block U L).round - 1)
    = (BlockRecord.block U c).round at hLr
  exact MahiMahiProperties.certifies_band (w := w (BlockRecord.block U L).round)
    (agreeBand_mm _ (agreeBand_of_rebasedAbove h (BlockRecord.block U c).round R₀ le_rfl))
    hc (by omega) (by omega) hL (by omega) (by omega)

/-- **Law 2 at wave three**: the core's argument with Mahi-Mahi's vote,
which at one round up is the reference. -/
theorem certifies_three_of_coverage {U : BlockUniverse Validator BlockId Payload}
    {T : Finset Validator} (hcard : quorumCard Validator ≤ T.card) {r : ℕ} {L : BlockId}
    (hpop : ∀ n, r ≤ n → n ≤ r + 2 → Properties.PopulatedOn
      (steelheadRule (Validator := Validator) (BlockId := BlockId) (Payload := Payload)
        (fun _ => 3)) U T n)
    (hct : Timed.CoversToward (steelheadRule (Validator := Validator) (BlockId := BlockId)
      (Payload := Payload) (fun _ => 3)) U T r 2 L)
    (hL : L ∈ U.ids) (hLr : (U.block L).round = r) (hLc : (U.block L).creator ∈ T)
    {c : BlockId} (hc : c ∈ U.ids) (hcc : (U.block c).creator ∈ T)
    (hcr : (U.block c).round = r + 2) : MahiMahi.Certifies U c L := by
  change quorumCard Validator ≤ (creatorsOf U.block (MahiMahi.votesIn U c L)).card
  refine le_trans hcard (Finset.card_le_card ?_)
  intro v hv
  obtain ⟨q, hq', hqc, hqr⟩ := hpop (r + 1) (by omega) (by omega) v hv
  have hqc' : (BlockRecord.block U q).creator = v := hqc
  have hqr' : (BlockRecord.block U q).round = r + 1 := hqr
  have hqT : (BlockRecord.block U q).creator ∈ T := by rw [hqc']; exact hv
  have hvote : L ∈ (BlockRecord.block U q).refs :=
    hct r le_rfl (by omega) q hq' hqT hqr' L hL hLc hLr Relation.ReflTransGen.refl
  have hpar : q ∈ (BlockRecord.block U c).refs :=
    hct (r + 1) (by omega) (by omega) c hc hcc
      (by change (BlockRecord.block U c).round = r + 1 + 1; rw [hcr]) q hq' hqT hqr'
      (Relation.ReflTransGen.single hvote)
  rw [mem_creatorsOf]
  refine ⟨q, Finset.mem_filter.mpr ⟨hpar, ?_⟩, hqc'⟩
  exact (MahiMahi.votes_iff_mem_refs hq' (by omega)).mpr hvote

/-- **Law 2**: coverage certifies, at every wave of at least three
rounds: the core's argument at three, Mahi-Mahi's above. -/
theorem shSupport_ofCoverage {w : ℕ → ℕ} (hw : ∀ r, 3 ≤ w r) :
    Timed.OfCoverage (R := steelheadRule (Validator := Validator) (BlockId := BlockId)
      (Payload := Payload) w) (shSupport w) (coreReliability Validator) := by
  intro U T hq r L hpop hct hL hLr hLc c hc hcc hcr
  by_cases h4 : 4 ≤ w r
  · exact MahiMahiProperties.mmSupport_ofCoverage (w := w r) h4 U T hq r L hpop hct hL hLr hLc
      c hc hcc hcr
  · have h3 : w r = 3 := by have := hw r; omega
    have hcard : quorumCard Validator ≤ T.card := by
      have h2 := hq.2
      change Fintype.card Validator - Faults.f Validator ≤ T.card at h2
      exact h2
    change (BlockRecord.block U c).round = r + (w r - 1) at hcr
    change ∀ n, r ≤ n → n ≤ r + (w r - 1) → _ at hpop
    change Timed.CoversToward _ U T r (w r - 1) L at hct
    rw [h3] at hcr hpop hct
    exact certifies_three_of_coverage hcard hpop hct hL hLr hLc hc hcc hcr

/-- **Law 3**: a quorum's certificates at the slot's decision round are
the direct commit, which a view caught up to that round sees. -/
theorem shSupport_commits {w : ℕ → ℕ} (hw : ∀ r, 2 ≤ w r) :
    Support.Commits (R := steelheadRule (Validator := Validator) (BlockId := BlockId)
      (Payload := Payload) w) (shSupport w) (coreReliability Validator) := by
  intro S U V T k hq hpop hcert hcov hlead
  letI : Slots Validator := S
  have hw' := hw (S.slotRound k)
  have hcard : quorumCard Validator ≤ T.card := by
    have h2 := hq.2
    change Fintype.card Validator - Faults.f Validator ≤ T.card at h2
    exact h2
  have hdr : MahiMahi.decisionRoundAt (w (S.slotRound k)) (S.slotRound k)
      = S.slotRound k + (w (S.slotRound k) - 1) := by
    unfold MahiMahi.decisionRoundAt; omega
  obtain ⟨L, hLmem, hLc, hLr⟩ := hpop (S.slotRound k) le_rfl
    (by change S.slotRound k ≤ S.slotRound k + (w (S.slotRound k) - 1); omega) (S.leader k) hlead
  have hLr' : (BlockRecord.block U L).round = S.slotRound k := hLr
  have hLc' : (BlockRecord.block U L).creator = S.leader k := hLc
  have hdc : MahiMahi.DirectCommit U (w (S.slotRound k)) L (S.slotRound k) := by
    unfold MahiMahi.DirectCommit
    refine le_trans hcard (Finset.card_le_card ?_)
    intro v hv
    obtain ⟨C, hC, hCc, hCr⟩ := hpop (S.slotRound k + (w (S.slotRound k) - 1)) (by omega) le_rfl
      v hv
    have hCr' : (BlockRecord.block U C).round
        = MahiMahi.decisionRoundAt (w (S.slotRound k)) (S.slotRound k) := by
      rw [hdr]; exact hCr
    rw [mem_creatorsOf]
    exact ⟨C, mem_certificatesAt.mpr
      ⟨hC, hCr', hcert L ⟨hLmem, hLr, hLc⟩ v hv C hC hCc hCr⟩, hCc⟩
  have hin : MahiMahi.DirectCommitIn U V (w (S.slotRound k)) L (S.slotRound k) :=
    MahiMahiProperties.directCommitIn_of_coversUpto hdc (by rw [hdr]; exact hcov)
  refine ⟨L, by omega, Steelhead.Decided.directCommit ⟨hLmem, hLr', hLc'⟩ hin, ?_⟩
  intro S' hround hlead'
  refine Steelhead.Decided.directCommit (S := S') ⟨hLmem, ?_, ?_⟩ ?_
  · rw [hround]; exact hLr'
  · rw [hlead' k (by omega)]; exact hLc'
  · change MahiMahi.DirectCommitIn U V (w (S'.slotRound k)) L (S'.slotRound k)
    rw [hround]; exact hin

/-! ## The liveness headline -/

theorem liveness {w : ℕ → ℕ} (hw : ∀ r, 2 ≤ w r) :
    Properties.Support.Lives (shSupport (Validator := Validator) (BlockId := BlockId)
      (Payload := Payload) w) (coreReliability Validator) :=
  Properties.Support.liveness (shSupport_commits hw) (commitsCandidate w) (selfParent w)
    (noEquiv w)

end SteelheadProperties

end LeanDag
