import LeanDag.Barnacle.Validity.Statement
import LeanDag.Barnacle.Helpers.Schedule
/-!
# BN14 — proof

Generated proof layer; not part of the audit surface. The run commits an
anchor at each closed configuration (`anchor_commits`), the candidate law
places that block at the round the next configuration starts
(`start_succ`), and the delivery law carries every good block two rounds
below it into its history.
-/

namespace LeanDag

namespace Barnacle

namespace Validity

theorem holds : Statement := by
  intro Validator BlockId Payload _ _ _ R hR P upd C₀ slack hdel U V K Rn Rnd N hgood
  obtain ⟨T, hcard, hT⟩ := hdel.reaches U Rnd N hgood
  refine ⟨T, hcard, ?_⟩
  intro b hb hbT hRnd hN k hkK hround
  obtain ⟨⟨A, hA⟩, hthr⟩ := Rn.anchor_commits k hkK
  refine ⟨A, hA, ?_⟩
  -- the anchor's block is a candidate of its slot, so it sits at the round
  -- the next configuration starts
  have hdec := Rn.closed k hkK (Rn.anchor k) (by omega) (by rw [Rn.start_succ k hkK])
  rw [hA] at hdec
  obtain ⟨hAids, hAr, -⟩ := hR _ _ _ _ A hdec
  refine hT b hb hbT hRnd hN A hAids ?_
  have hlink : (R.toBaseRule.toDagRule.block U A).round = (R.block U A).round := rfl
  rw [← hlink, hAr, Config.sched_slotRound, ← Rn.start_succ k hkK]
  exact hround

end Validity

end Barnacle

end LeanDag
