import LeanDag.Adaptive.Validity.Statement
/-!
# AL15c — proof

Generated proof layer; not part of the audit surface. The run commits an
anchor at each closed configuration (`anchor_commits`), the candidate law
places that block at the anchor's own round, and the delivery law carries
every good block two rounds below the boundary into its history — the
boundary sitting strictly below that round.
-/

namespace LeanDag

namespace Adaptive

namespace Validity

open Barnacle

theorem holds : Statement := by
  intro Validator BlockId Payload _ _ _ R hR P upd C₀ slack hdel U V K Rn Rnd N hgood
  obtain ⟨T, hcard, hT⟩ := hdel.reaches U Rnd N hgood
  refine ⟨T, hcard, ?_⟩
  intro b hb hbT hRnd hN k hkK hround
  obtain ⟨⟨A, hA⟩, hthr⟩ := Rn.anchor_commits k hkK
  refine ⟨A, hA, ?_⟩
  -- the anchor's block is a candidate of its slot, so it sits at the round
  -- the next configuration starts
  have hstart : Rn.start k ≤ Rn.start (k + 1) := by
    rw [Rn.start_succ k hkK]; omega
  have hdec := Rn.closed k hkK (Rn.anchor k) (by omega) le_rfl
  rw [hA] at hdec
  obtain ⟨hAids, hAr, -⟩ := hR _ _ _ _ A hdec
  refine hT b hb hbT hRnd hN A hAids ?_
  have hlink : (R.toBaseRule.toDagRule.block U A).round = (R.block U A).round := rfl
  rw [← hlink, hAr, Config.sched_slotRound]
  omega


end Validity

end Adaptive

end LeanDag
