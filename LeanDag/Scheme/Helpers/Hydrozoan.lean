import LeanDag.Scheme.Model.Hydrozoan
import LeanDag.Scheme.Helpers.Rows
import LeanDag.Scheme.Properties
import LeanDag.Scheme.Table.Proof
import LeanDag.Hydrozoan.Helpers.Carrier
/-!
# The Hybrid Mysticeti row on Hydrozoan's universe

On Hydrozoan's universe the row reads as `hydrozoanSlowAnchored`, part by
part: one round up the scheme's votes are references, its certificates
Hydrozoan's at `q_cert = (n + f)/2 + 1`, its commit Hydrozoan's slow
commit at `q_slow = 2f + c + 1`, its blames Hydrozoan's, and its link
Hydrozoan's certificate rung. The scheme's tie-break never fires: two
candidates linked from one anchor have certificates, and certificates
of one slot name one block (`eq_of_certs_three`).

The row meets its inequalities at every `n ≥ 3f + 2c + 1` with
`q = n − f − c` (`Table.HybridAnyCommittee`), so its carrier is safe on
Hydrozoan's records, and its support commits at Hydrozoan's fault model,
whose slack is `f + c`: progress there. On records that also ask
self-reference (`HybridValid`), inclusion follows as well.
-/

namespace LeanDag

namespace Scheme

open Properties

variable {Replica BlockId : Type} [Fintype Replica] [DecidableEq Replica] [LinearOrder BlockId]
variable [F : Hydrozoan.Faults Replica]

omit [LinearOrder BlockId] in
/-- Outside the non-Byzantine replicas are at most `f`. -/
theorem card_compl_nonByzantine :
    (Hydrozoan.NonByzantine : Finset Replica)ᶜ.card ≤ F.f := by
  rw [Hydrozoan.NonByzantine, compl_compl]; exact F.card_byzantine

omit [LinearOrder BlockId] in
/-- The correct replicas are non-Byzantine. -/
theorem correct_subset_nonByzantine :
    (Hydrozoan.Correct : Finset Replica) ⊆ Hydrozoan.NonByzantine := by
  intro v hv
  simp only [Hydrozoan.Correct, Hydrozoan.NonByzantine, Finset.mem_compl, Finset.mem_union,
    not_or] at hv ⊢
  exact hv.1

omit [LinearOrder BlockId] in
/-- The row's certificate threshold is Hydrozoan's `q_cert`. -/
theorem hybridMysticeti_cert :
    (Params.hybridMysticeti (Fintype.card Replica) F.f F.c).certThreshold =
      Hydrozoan.qCert Replica := by
  simp only [Params.hybridMysticeti, Hydrozoan.qCert]; omega

/-- **The row is covered** on Hydrozoan's records: a three-round row
meeting `ThreeRound n f q` at `q = n − f − c`. -/
theorem hybridMysticeti_covered :
    (Params.hybridMysticeti (Fintype.card Replica) F.f F.c).Covered (Fintype.card Replica) F.f
      (Hydrozoan.q Replica) :=
  ((Table.rowsCovered _ _ _).2.2.2.1 (by have := F.card_replicas; omega)).1

section Slow

variable [S : Slots Replica]

omit [LinearOrder BlockId] S in
theorem distinctRefs_hydrozoan {U : Hydrozoan.BlockUniverse Replica BlockId} :
    ∀ b ∈ U.ids, DistinctRefs U b :=
  fun b hb => (U.valid b hb).distinct_creators

/-- **The row reads as Hydrozoan without its fast path.** -/
theorem readAlike_hydrozoanSlow
    (σ : VoteSel Replica BlockId Unit Hydrozoan.ValidWrt Hydrozoan.NonByzantine)
    (U : Hydrozoan.BlockUniverse Replica BlockId) :
    ReadAlike (schemeAnchored (Params.hybridMysticeti (Fintype.card Replica) F.f F.c) σ)
      (hydrozoanSlowAnchored Replica BlockId) U where
  waveAt := fun _ => rfl
  rungs := rfl
  commit := fun V k L hL => by
    show HoldsAtLeast U V _ (certsAt _ σ U L _) ↔ HoldsAtLeast U V _ _
    rw [certsAt_eq_certificatesAt σ _ rfl rfl distinctRefs_hydrozoan hL.2.1, hybridMysticeti_cert]
    rfl
  skip := fun V k => by
    show HoldsAtLeast U V _ (blamersAt _ σ U k) ↔ HoldsAtLeast U V _ _
    rw [blamersAt_eq σ _ rfl k]
    rfl
  link := fun {i k j A L} _ hL hA _ => by
    show _ ≤ (creatorsOf U.block ((certsAt _ σ U L _).filter _)).card ↔ LinkedVia U A _
    rw [certsAt_eq_certificatesAt σ _ rfl rfl distinctRefs_hydrozoan hL.2.1, hybridMysticeti_cert]
    exact one_le_card_iff_linkedVia hA.1 _
  least := fun {i k j A L} hi hL hA he hl => by
    refine ⟨fun _ _ _ _ h => h, fun _ L' hL' hl' hlt => ?_⟩
    have hne : (∀ {L₀ : BlockId}, (schemeAnchored (Params.hybridMysticeti (Fintype.card Replica)
        F.f F.c) σ).Link i U A L₀ S k →
        (certsAt (Params.hybridMysticeti (Fintype.card Replica) F.f F.c) σ U L₀
          (S.slotRound k)).Nonempty) := fun {L₀} h => by
      have h1 : 1 ≤ (creatorsOf U.block ((certsAt (Params.hybridMysticeti (Fintype.card Replica)
          F.f F.c) σ U L₀ (S.slotRound k)).filter (fun C => C ∈ history U A))).card := h
      exact (one_le_card_nonempty h1).mono (Finset.filter_subset _ _)
    have heq := eq_of_certs_three σ rfl (show 3 ≤ 3 by omega)
      U.noEquivOn_honest card_compl_nonByzantine
      (by simp only [Params.hybridMysticeti]; omega) (hne hl) (hne hl')
      (by rw [hL.2.2, hL'.2.2]) (by rw [hL.2.1, hL'.2.1])
    exact lt_irrefl L (heq ▸ hlt)

omit S in
/-- **The row is Hydrozoan without its fast path.** -/
theorem hydrozoanSlow_eq
    (σ : VoteSel Replica BlockId Unit Hydrozoan.ValidWrt Hydrozoan.NonByzantine) :
    (schemeAnchored (Params.hybridMysticeti (Fintype.card Replica) F.f F.c) σ).toDagRule =
      (hydrozoanSlowAnchored Replica BlockId).toDagRule :=
  toDagRule_eq fun S U _ _ _ => (readAlike_hydrozoanSlow (S := S) σ U).decided_iff

end Slow

omit [LinearOrder BlockId] in
/-- A threshold within `q = n − f − c` is within Hydrozoan's fault model. -/
theorem le_q_slack {t : ℕ} (h : t ≤ Hydrozoan.q Replica) :
    t ≤ Fintype.card Replica - (Hydrozoan.hzReliability Replica).slack := by
  show t ≤ Fintype.card Replica - (F.f + F.c)
  unfold Hydrozoan.q at h; omega

/-- A covered row has a wave of at least two, and of three where votes are
certified a round later. -/
theorem covered_waves {p : Params} {n f q : ℕ} (h : p.Covered n f q) :
    2 ≤ p.waveLength ∧ (p.voteIsCert = false → 3 ≤ p.waveLength) := by
  rcases h with ⟨hv, hw, -⟩ | ⟨hv, hw, -⟩ | ⟨hv, hw, -⟩ | ⟨hv, hw, -⟩
  · exact ⟨hw, fun h => absurd (hv.symm.trans h) (by simp)⟩
  · exact ⟨by omega, fun _ => hw⟩
  · exact ⟨hw, fun h => absurd (hv.symm.trans h) (by simp)⟩
  · exact ⟨by omega, fun _ => hw⟩

end Scheme

end LeanDag
