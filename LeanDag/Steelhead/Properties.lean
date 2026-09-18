import LeanDag.Steelhead.Helpers.Decision
import LeanDag.MahiMahi.Properties
import LeanDag.Properties.Derived.Truncate
/-!
# Steelhead as a carrier, and the properties its rule gives

`docs/target-properties.md` §11, for the rule at a wavelength function
(`steelhead.md` §6). One carrier per wavelength function, as Mahi-Mahi
has one per width, since `DagRule.Decided` fixes no wave.

**What holds.** `Agree`, `Banded`, `CommitsCandidate`, `CommitsDirect`,
`Indirect`, `Quorate`, `SelfParent`, `NoEquiv`, and `Persist` hold at
every wavelength function of at least two rounds, each Mahi-Mahi's fact
at the wave of the kind of the slot it concerns. `Support` holds with
Mahi-Mahi's certificate and the wave read at the candidate's kind; its
`Local` and `Commits` laws at two rounds and above, the timed model's
`OfCoverage` bridge at three and above, the wave-three case by the core's
argument and the higher waves by Mahi-Mahi's.

**The band, and what follows from it.** A wave read from the round would
have no band: a rebase shifts every round by a constant and so moves the
read (`docs/target-properties.md` §3.4c). This rule reads its wave at the
slot's kind, which is the schedule's and which a rebase carries
(`docs/kinds.md`), so the band laws are Mahi-Mahi's at the wave of that
kind and `Banded` follows with no condition beyond the `2 ≤ w κ` those
laws already ask. `Persist`, `LocalTruncate` and the `Safe` headline come
with it.
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
theorem agree {w : ℕ → ℕ} (hw : ∀ κ, 2 ≤ w κ) :
    Agree (steelheadRule (Validator := Validator) (BlockId := BlockId) (Payload := Payload) w) :=
  AnchoredRule.agree (steelheadLaws hw)

/-- **A commit names the slot's candidate.** -/
theorem commitsCandidate (w : ℕ → ℕ) :
    CommitsCandidate (steelheadRule (Validator := Validator) (BlockId := BlockId)
      (Payload := Payload) w) :=
  AnchoredRule.commitsCandidate

/-- **And a direct commit is a verdict**, at the slot's own direct
predicate, read at its kind. -/
theorem commitsDirect (w : ℕ → ℕ) :
    CommitsDirect (steelheadRule (Validator := Validator) (BlockId := BlockId)
      (Payload := Payload) w)
      (fun {U} V L r κ => MahiMahi.DirectCommitIn U V (w κ) L r) :=
  AnchoredRule.commitsDirect

open Classical in
/-- **The indirect rule as a property**, with eligibility at the wave of
each slot's own kind and no tie to break. -/
theorem indirect {w : ℕ → ℕ} (hw : ∀ κ, 1 ≤ w κ) :
    Indirect (steelheadRule (Validator := Validator) (BlockId := BlockId) (Payload := Payload) w)
      (fun S i j => S.slotRound i + w (S.kind i) ≤ S.slotRound j) := by
  have h := AnchoredRule.indirect (R := steelheadAnchored Validator BlockId Payload w)
    (Steelhead.linkCongr (w := w)) (fun hi h => Steelhead.exists_least hi h)
  refine h.congr ?_
  intro S i j
  have := hw (S.kind i)
  simp only [steelheadAnchored_waveAt]
  omega

/-! ## The band, persistence, and safety

Mahi-Mahi's band laws at the wave of the kind of the slot each law
concerns. The band's own kind agreement is what rewrites the target
slot's wave into the source slot's, so the rule reads a band at any
offset and owes nothing more about the wave
(`docs/target-properties.md` §3.4c, `docs/kinds.md`). -/

/-- A band at Steelhead's carrier is a band at any wave's. -/
theorem agreeBand_mm {w : ℕ → ℕ} {U U' : BlockUniverse Validator BlockId Payload}
    {lo hi g g' : ℕ} (w' : ℕ)
    (h : AgreeBand (steelheadAnchored Validator BlockId Payload w).toDagRule U U' lo hi g g') :
    AgreeBand (MahiMahi.mahiMahiAnchored Validator BlockId Payload w').toDagRule U U' lo hi g g' :=
  ⟨h.mem, h.block, h.refs⟩

/-- **What Steelhead owes the band**: Mahi-Mahi's band laws, each at the
wave of the kind the law's slot has. -/
theorem steelheadBandLaws {w : ℕ → ℕ} (hw : ∀ κ, 2 ≤ w κ) :
    (steelheadAnchored Validator BlockId Payload w).BandLaws where
  commit_band := by
    intro S S' U U' lo hi g g' V V' k k' L hab hkk hlk hkind hlo hhi hV hL hc
    have h := (MahiMahiProperties.mahiMahiBandLaws (hw (S.kind k))).commit_band
      (agreeBand_mm _ hab) hkk hlk hkind hlo hhi hV hL hc
    change MahiMahi.DirectCommitIn U' V' (w (S'.kind k')) L (S'.slotRound k')
    rw [← hkind]; exact h
  skip_band := by
    intro S S' U U' lo hi g g' V V' k k' hab hkk hlk hkind hlo hhi hV hs
    have h := (MahiMahiProperties.mahiMahiBandLaws (hw (S.kind k))).skip_band
      (agreeBand_mm _ hab) hkk hlk hkind hlo hhi hV hs
    change MahiMahi.DirectSkipIn U' V' (w (S'.kind k')) (S'.leader k') (S'.slotRound k')
    rw [← hkind]; exact h
  link_band := by
    intro S S' U U' lo hi g g' A L k k' i hab hA hAlo hAhi hkk hlk hkind hlo hhi hi' hL
    have h := (MahiMahiProperties.mahiMahiBandLaws (hw (S.kind k))).link_band
      (agreeBand_mm _ hab) hA hAlo hAhi hkk hlk hkind hlo hhi hi' hL
    change MahiMahi.CertifiedIn U' (w (S'.kind k')) A L (S'.slotRound k') ↔
      MahiMahi.CertifiedIn U (w (S.kind k)) A L (S.slotRound k)
    rw [← hkind]; exact h
  link_novel := by
    intro S S' U U' lo hi g g' A L k k' i hab hA hAlo hAhi hkk hlk hkind hlo hhi hi' hL hLo
    have h := (MahiMahiProperties.mahiMahiBandLaws (hw (S.kind k))).link_novel
      (agreeBand_mm _ hab) hA hAlo hAhi hkk hlk hkind hlo hhi hi' hL hLo
    change ¬ MahiMahi.CertifiedIn U' (w (S'.kind k')) A L (S'.slotRound k')
    rw [← hkind]; exact h

/-- **The rule reads a band**, at every wavelength function its rules are
stated for. -/
theorem banded {w : ℕ → ℕ} (hw : ∀ κ, 2 ≤ w κ) :
    Banded (steelheadRule (Validator := Validator) (BlockId := BlockId)
      (Payload := Payload) w) :=
  AnchoredRule.banded (steelheadBandLaws hw)

/-- **Truncation is local**: below a horizon the verdicts of a pruned
record are the full one's. -/
theorem localTruncate {w : ℕ → ℕ} (hw : ∀ κ, 2 ≤ w κ) :
    LocalTruncate (steelheadRule (Validator := Validator) (BlockId := BlockId)
      (Payload := Payload) w) :=
  LocalTruncate.of_banded (banded hw)

/-- **What Steelhead owes an extension**: its band laws at offset zero. -/
theorem steelheadExtendLaws {w : ℕ → ℕ} (hw : ∀ κ, 2 ≤ w κ) :
    (steelheadAnchored Validator BlockId Payload w).ExtendLaws :=
  (steelheadBandLaws hw).toExtendLaws

/-- **Persistence**: a verdict survives an extension of the record, into
any larger view. -/
theorem persist {w : ℕ → ℕ} (hw : ∀ κ, 2 ≤ w κ) :
    Persist (steelheadRule (Validator := Validator) (BlockId := BlockId) (Payload := Payload) w) :=
  AnchoredRule.persist (steelheadExtendLaws hw)

/-- **The safety headline**: the band and agreement, at every wavelength
function of at least two rounds. -/
theorem safety {w : ℕ → ℕ} (hw : ∀ κ, 2 ≤ w κ) :
    Properties.Safe (steelheadRule (Validator := Validator) (BlockId := BlockId)
      (Payload := Payload) w) :=
  Properties.safety (banded hw) (agree hw) (commitsCandidate w)

/-! ## The support

Mahi-Mahi's certificate, with the certifiers `w κ − 1` rounds above a
candidate of kind `κ`. -/

/-- **Steelhead's support**: certifiers at each slot's own decision
round, certification Mahi-Mahi's. -/
def shSupport (w : ℕ → ℕ) : Support (steelheadRule (Validator := Validator) (BlockId := BlockId)
    (Payload := Payload) w) where
  waveAt := fun κ => w κ - 1
  Certifies := fun U C L => MahiMahi.Certifies U C L

/-- **Law 1**: certification is local, at the wave of the candidate's
kind. -/
theorem shSupport_local {w : ℕ → ℕ} (hw : ∀ κ, 2 ≤ w κ) :
    Support.Local (R := steelheadRule (Validator := Validator) (BlockId := BlockId)
      (Payload := Payload) w) (shSupport w) := by
  intro U U' G R₀ h c L κ hc hcr hL hLr
  have hw' := hw κ
  change R₀ + (w κ - 1) ≤ (BlockRecord.block U c).round at hcr
  change (BlockRecord.block U L).round + (w κ - 1) = (BlockRecord.block U c).round at hLr
  exact MahiMahiProperties.certifies_band (w := w κ)
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
theorem shSupport_ofCoverage {w : ℕ → ℕ} (hw : ∀ κ, 3 ≤ w κ) :
    Timed.OfCoverage (R := steelheadRule (Validator := Validator) (BlockId := BlockId)
      (Payload := Payload) w) (shSupport w) (coreReliability Validator) := by
  intro U T hq r κ L hpop hct hL hLr hLc c hc hcc hcr
  by_cases h4 : 4 ≤ w κ
  · exact MahiMahiProperties.mmSupport_ofCoverage (w := w κ) h4 U T hq r κ L hpop hct hL hLr hLc
      c hc hcc hcr
  · have h3 : w κ = 3 := by have := hw κ; omega
    have hcard : quorumCard Validator ≤ T.card := by
      have h2 := hq.2
      change Fintype.card Validator - Faults.f Validator ≤ T.card at h2
      exact h2
    change (BlockRecord.block U c).round = r + (w κ - 1) at hcr
    change ∀ n, r ≤ n → n ≤ r + (w κ - 1) → _ at hpop
    change Timed.CoversToward _ U T r (w κ - 1) L at hct
    rw [h3] at hcr hpop hct
    exact certifies_three_of_coverage hcard hpop hct hL hLr hLc hc hcc hcr

/-- **A quorum's certificates at the slot's decision round are a direct
commit**, in a view caught up to that round: the leader's block at the
slot's round is the candidate, and every reliable block at the decision
round certifies it. Law 3's core, stated on its own so that a liveness
argument reads it without the law around it. -/
theorem shSupport_directCommitIn {w : ℕ → ℕ} (hw : ∀ κ, 2 ≤ w κ) (S : Slots Validator)
    {U : BlockUniverse Validator BlockId Payload} (V : View Validator BlockId Payload U)
    {T : Finset Validator} {k : ℕ} (hcard : quorumCard Validator ≤ T.card)
    (hpop : ∀ n, S.slotRound k ≤ n → n ≤ S.slotRound k + (w (S.kind k) - 1) →
      PopulatedOn U T n)
    (hcert : ∀ L, IsLeaderBlock U k L → ∀ v ∈ T, ∀ c, c ∈ U.ids → (U.block c).creator = v →
      (U.block c).round = S.slotRound k + (w (S.kind k) - 1) → MahiMahi.Certifies U c L)
    (hcov : V.CoversUpto (S.slotRound k + (w (S.kind k) - 1))) (hlead : S.leader k ∈ T) :
    ∃ L, IsLeaderBlock U k L ∧
      MahiMahi.DirectCommitIn U V (w (S.kind k)) L (S.slotRound k) := by
  have hw' := hw (S.kind k)
  have hdr : MahiMahi.decisionRoundAt (w (S.kind k)) (S.slotRound k)
      = S.slotRound k + (w (S.kind k) - 1) := by
    unfold MahiMahi.decisionRoundAt; omega
  obtain ⟨L, hLmem, hLc, hLr⟩ := hpop (S.slotRound k) le_rfl (by omega) (S.leader k) hlead
  have hdc : MahiMahi.DirectCommit U (w (S.kind k)) L (S.slotRound k) := by
    unfold MahiMahi.DirectCommit
    refine le_trans hcard (Finset.card_le_card ?_)
    intro v hv
    obtain ⟨C, hC, hCc, hCr⟩ := hpop (S.slotRound k + (w (S.kind k) - 1)) (by omega) le_rfl
      v hv
    have hCr' : (BlockRecord.block U C).round
        = MahiMahi.decisionRoundAt (w (S.kind k)) (S.slotRound k) := by
      rw [hdr]; exact hCr
    rw [mem_creatorsOf]
    exact ⟨C, mem_certificatesAt.mpr
      ⟨hC, hCr', hcert L ⟨hLmem, hLr, hLc⟩ v hv C hC hCc hCr⟩, hCc⟩
  exact ⟨L, ⟨hLmem, hLr, hLc⟩,
    MahiMahiProperties.directCommitIn_of_coversUpto hdc (by rw [hdr]; exact hcov)⟩

/-- **Law 3**: a quorum's certificates at the slot's decision round are
the direct commit, which a view caught up to that round sees. -/
theorem shSupport_commits {w : ℕ → ℕ} (hw : ∀ κ, 2 ≤ w κ) :
    Support.Commits (R := steelheadRule (Validator := Validator) (BlockId := BlockId)
      (Payload := Payload) w) (shSupport w) (coreReliability Validator) := by
  intro S U V T k hq hpop hcert hcov hlead
  letI : Slots Validator := S
  have hcard : quorumCard Validator ≤ T.card := by
    have h2 := hq.2
    change Fintype.card Validator - Faults.f Validator ≤ T.card at h2
    exact h2
  obtain ⟨L, ⟨hLmem, hLr', hLc'⟩, hin⟩ :=
    shSupport_directCommitIn hw S V hcard hpop hcert hcov hlead
  refine ⟨L, by omega, Steelhead.Decided.directCommit ⟨hLmem, hLr', hLc'⟩ hin, ?_⟩
  intro S' hround hlead' hkind
  refine Steelhead.Decided.directCommit (S := S') ⟨hLmem, ?_, ?_⟩ ?_
  · rw [hround]; exact hLr'
  · rw [hlead' k (by omega)]; exact hLc'
  · change MahiMahi.DirectCommitIn U V (w (S'.kind k)) L (S'.slotRound k)
    rw [hround, hkind k (by omega)]; exact hin

/-! ## The liveness headline -/

theorem liveness {w : ℕ → ℕ} (hw : ∀ κ, 2 ≤ w κ) :
    Properties.Support.Lives (shSupport (Validator := Validator) (BlockId := BlockId)
      (Payload := Payload) w) (coreReliability Validator) :=
  Properties.Support.liveness (shSupport_commits hw) (commitsCandidate w) (selfParent w)
    (noEquiv w)

end SteelheadProperties

end LeanDag
