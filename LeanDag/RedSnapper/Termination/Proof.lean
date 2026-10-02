import LeanDag.RedSnapper.Termination.Statement
import LeanDag.RedSnapper.Uncontested.Proof
import LeanDag.RedSnapper.ConflictResolution.Proof
import LeanDag.RedSnapper.TxAgreement.Proof

/-!
# Termination — proof

Generated proof layer; not part of the audit surface. `decidedAgainst`
is a constructor on the release side and `resolveDropRival` with
`alive_of_finalized` on the rival side. For `decided`, the anchor's own
round-`r₀ + 2` block `p` includes the transaction through its author's
round-`r₀ + 1` block. If `p` includes no valid rival it is a certificate
(`isFastCert_of_local_sole`), under the anchor: unconflicted, the anchor
commits by `finalizeOnCommit`; conflicted and alive, by `resolveCommit`;
conflicted and dead, the death is a release below — no rival is
certified, no skip certificate exists — and `releasedDrop` fires. If `p`
includes a valid rival it carries RS5 (`anchorRoute`): a certified alive
candidate under the anchor is the transaction or drops it there, and a
resolution at or below the anchor drops it.
-/

namespace LeanDag

namespace RedSnapper

namespace Termination

open CertificateExclusion

variable {Validator BlockId Tx Obj : Type*} [Fintype Validator] [DecidableEq Validator]
  [DecidableEq BlockId] [F : Faults Validator] [T : Transactions Tx Obj]
  {U : Universe Validator BlockId Tx Obj}

theorem decidedAgainst : DecidedAgainst U := by
  rintro hdisc A V V' i a tx hia hcand (⟨j, hj, hres⟩ | ⟨tx', hconf, hcert, hfin⟩)
  · rcases Nat.lt_or_ge j i with hlt | hge
    · exact .releasedDrop hia hcand hlt hres
    · obtain rfl : j = i := by omega
      exact .resolveDrop hia hres hcand
  · exact .resolveDropRival hia hcand
      ⟨tx', hconf, hconf.2 ▸ isCandidate_of_hasCert hcert, hcert,
        TxAgreement.alive_of_finalized hdisc hfin i⟩

theorem decided : Decided U := by
  intro hdisc hrule tx r₀ R b₀ hval hb₀ hc₀ hr₀ hinc₀ hRr hsync hpop1 hpop3
    A V i a hia hca hra
  have haid : a ∈ U.ids := anchor_mem_ids hia
  -- the anchor's own round-(r₀+2) block includes tx, through its author's r₀+1 block
  obtain ⟨p, hp, hap, hrp, hreach⟩ := exists_own_block_of_le haid hca (m := r₀ + 2)
    (by omega)
  have hpc : (U.block p).author ∈ (Correct : Finset Validator) := hap.symm ▸ hca
  have hincp : Includes U p tx := by
    obtain ⟨b₁, hb₁, hab₁, hrb₁⟩ := hpop1 _ hpc
    have hcb₁ : (U.block b₁).author ∈ (Correct : Finset Validator) := hab₁.symm ▸ hpc
    have hpar₀ : b₀ ∈ (U.block b₁).parents :=
      hsync b₁ hb₁ hcb₁ (by omega) b₀ hb₀ hc₀ (by omega)
    have hpar₁ : b₁ ∈ (U.block p).parents := hsync p hp hpc (by omega) b₁ hb₁ hcb₁ (by omega)
    exact includes_mono (Reaches.of_mem_parents hpar₁ (Reaches.single hpar₀)) hinc₀
  have hcand : IsCandidate U a (T.input tx) tx := ⟨hval, rfl, includes_mono hreach hincp⟩
  by_cases hriv : ∃ tx', T.Valid tx' ∧ Conflict tx tx' ∧ Includes U p tx'
  · -- `p` sees the conflict: RS5 from it
    obtain ⟨tx', hv', hc', hi'⟩ := hriv
    have hconf : Conflicted U p (T.input tx) :=
      ⟨tx, tx', ⟨hval, rfl, hincp⟩, ⟨hv', hc'.2.symm, hi'⟩, hc'.1⟩
    rcases ConflictResolution.anchorRoute hdisc hrule hp hpc hrp hconf (by omega) hsync
        hpop3 hia hca (by omega) with ⟨hconfa, tx₀, hcand₀, hcert₀, hlive₀⟩ | ⟨j, hj, hres⟩
    · by_cases heq : tx₀ = tx
      · subst heq
        exact Or.inl (.resolveCommit hia hconfa hcand hcert₀ hlive₀)
      · exact Or.inr (.resolveDropRival hia hcand
          ⟨tx₀, ⟨fun h => heq h.symm, hcand₀.2.1.symm⟩, hcand₀, hcert₀, hlive₀⟩)
    · right
      rcases Nat.lt_or_ge j i with hlt | hge
      · exact .releasedDrop hia hcand hlt hres
      · obtain rfl : j = i := by omega
        exact .resolveDrop hia hres hcand
  · -- `p` includes no valid rival: it is a certificate, under the anchor
    push Not at hriv
    have hcert : HasCert U a tx :=
      ⟨p, hp, Uncontested.isFastCert_of_local_sole hrule hval hb₀ hc₀ hr₀ hinc₀ hRr hsync
        hpop1 hp hpc hrp hriv, hreach⟩
    by_cases hconf : Conflicted U a (T.input tx)
    · by_cases hdead : DeadAt U A i tx
      · -- certified yet dead: only a release below the anchor can be the cause
        right
        obtain ⟨a₁, -, hdg⟩ := hdead
        obtain ⟨C, hC, hc, -⟩ := hcert
        rcases hdg with ⟨tx', hconf', C', hC', hc', -⟩ | ⟨Cs, hCs, hskip, -⟩ | hrel
        · exact absurd (certUniqueness hdisc C hC C' hC' tx tx' hconf' hc hc') id
        · exact absurd (ackSkipExclusion hdisc C hC Cs hCs tx hc hskip) id
        · obtain ⟨k, hk, hready⟩ := releasedBelow_iff_exists.mp hrel
          obtain ⟨j, hj, hres⟩ := exists_resolvesAt_of_ready hready
          exact .releasedDrop hia hcand (by omega) hres
      · exact Or.inl (.resolveCommit hia hconf hcand hcert hdead)
    · exact Or.inl (.finalizeOnCommit hia hcand hconf hcert)

theorem decidedOrdered : DecidedOrdered U := by
  intro hdisc hrule tx R A V k m i a₀ b₀ a hval hk hinc hkm hm hcb hR hsync hpop1 hpop3
    hia hca hra
  exact decided hdisc hrule tx _ R b₀ hval (anchor_mem_ids hm) hcb rfl
    (includes_mono (anchor_reaches hkm hk hm) hinc) hR hsync hpop1 hpop3 A V i a hia hca hra

theorem holds : Statement := by
  intro Validator BlockId Tx Obj _ _ _ _ _ U
  exact ⟨decidedAgainst, decided, decidedOrdered⟩

end Termination

end RedSnapper

end LeanDag
