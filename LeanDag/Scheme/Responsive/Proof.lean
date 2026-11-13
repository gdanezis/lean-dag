import LeanDag.Scheme.Responsive.Statement
import LeanDag.Scheme.AtomicBroadcast.Proof
import LeanDag.Scheme.Table.Proof
import LeanDag.Scheme.Helpers.FullRun
/-!
# Responsive liveness at every partially synchronous row — proof

`Inhabited` is the full run (`Full.run`); `Validity` is `ValidityPS` at the
row, whose coverage is `Table.rowsCovered` and whose certificate and
commit thresholds fit `n − f − c` at the row's committee.
-/

namespace LeanDag

namespace Scheme

namespace Responsive

attribute [local instance] noFaults

open Params

/-- A partially synchronous row's certificate threshold is at most `n`. -/
theorem psRow_cert_le {p : Params} {n f c : ℕ} (h : p.PSRow n f c) : p.certThreshold ≤ n := by
  rcases h with ⟨-, hn, rfl | rfl⟩ | ⟨-, hn, rfl⟩ | ⟨hn, rfl⟩ | ⟨hn, rfl⟩ | ⟨-, hn, rfl⟩ <;>
    simp only [mysticeti, cordialMinersPS, blueBottlePS, orcaella, hybridMysticeti, nemoNemo] <;>
    omega

/-- **A row's certificate fits its parent quorum**, and its commit
threshold is within it. -/
theorem psRow_fits {p : Params} {n f c : ℕ} (h : p.PSRow n f c) :
    p.CertFits (n - f - c) ∧ p.commitThreshold ≤ n - f - c := by
  rcases h with ⟨rfl, hn, rfl | rfl⟩ | ⟨rfl, hn, rfl⟩ | ⟨hn, rfl⟩ | ⟨hn, rfl⟩ | ⟨rfl, hn, rfl⟩ <;>
    simp only [CertFits, mysticeti, cordialMinersPS, blueBottlePS, orcaella, hybridMysticeti,
      nemoNemo, Bool.true_eq_false, Bool.false_eq_true, false_implies, forall_const, true_implies,
      and_true] <;>
    omega

/-- **A row is covered at its parent quorum.** -/
theorem psRow_covered {p : Params} {n f c : ℕ} (h : p.PSRow n f c) :
    p.Covered n f (n - f - c) := by
  have hc := Table.rowsCovered n f c
  rcases h with ⟨rfl, hn, rfl | rfl⟩ | ⟨rfl, hn, rfl⟩ | ⟨hn, rfl⟩ | ⟨hn, rfl⟩ | ⟨rfl, hn, rfl⟩
  · simpa using (hc.1 hn).1
  · simpa using (hc.1 hn).2.2.1
  · simpa using (hc.2.1 hn).1
  · exact (hc.2.2.1 hn).1
  · exact (hc.2.2.2.1 hn).1
  · simpa using (hc.2.2.2.2 (by omega)).1

theorem inhabited : Inhabited := by
  intro n _ p f c hrow _ σ N
  have hq : n - f - c ≤ n := by omega
  refine ⟨Full.record hq N, Full.run (n - f - c) p (psRow_cert_le hrow) σ, rfl, fun r => ?_,
    fun r hr v => ⟨toLex (r, v), Full.mem_record_ids.mpr (by simpa using hr), by simp, by simp⟩⟩
  simp

theorem rowsValidity : RowsValidity := by
  intro Validator BlockId Payload _ _ _ _ P _ honest p f c _ hrow hhon σ wk S U T N R d rs hTh hqT
    hgst hto hP hd hspan P_k m k b₀ hk hm hmc hlead hR hmr hkb hrun hN P_j hj
  have hf := psRow_fits hrow
  have hn : Fintype.card Validator - f - c ≤ Fintype.card Validator := by omega
  exact AtomicBroadcast.validityPS Validator BlockId Payload P (Fintype.card Validator - f - c)
    honest f p σ wk U T N R (Fintype.card Validator - f - c) d rs ⟨hhon, hn, psRow_covered hrow⟩ hf.1
    (le_trans hf.2 hqT) hTh hqT hgst hto hP hd hspan P_k m k b₀ hk hm hmc hlead hR hmr hkb hrun
    hN P_j hj

theorem holds : Statement := ⟨inhabited, rowsValidity⟩

end Responsive

end Scheme

end LeanDag
