import LeanDag.Scheme.Crash.Statement
import LeanDag.Scheme.Responsive.Proof
import LeanDag.Scheme.Reactive.Proof
import LeanDag.Scheme.Helpers.FullRun
import LeanDag.Scheme.AtomicBroadcast.Proof
import LeanDag.Scheme.Model.LeastSel
/-!
# Crash recovery — proof

A crash run read past `max gst tr` is a responsive run
(`CrashRun.toReactive`), so the reactive results apply to it: the liveness
precondition carries over (`Live`), whence `Commits` by
`ReactiveRun.commits`, and Validity by `Responsive.rowsValidity`. The run in
which every validator crashes at once is `Full.crashRun`. Asynchronously, a
crash run is an asynchronous run (`AsyncCrashRun.toAsyncPace`), so Agreement
and Validity are `AtomicBroadcast.agreement` and
`AtomicBroadcast.validityAsync` of it; the timed run with every validator
down, its clock forgotten, inhabits it.
-/

namespace LeanDag

namespace Scheme

namespace Crash

attribute [local instance] noFaults

theorem toReactive : ToReactive := by
  intro Validator BlockId Payload _ _ _ _ P _ honest p σ _ U T N q cr
  exact ⟨cr.toReactive, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem live : Live := by
  intro Validator BlockId Payload _ _ _ _ P _ honest p σ rel S U V T lo K h
  obtain ⟨hT, hTh, N, R₀, cr, hgst, hto, hR, hcov, hN⟩ := h
  exact ⟨hT, hTh, N, R₀, cr.toReactive, hgst, hto, hR, hcov, hN⟩

theorem commits : Commits := by
  intro Validator BlockId Payload _ _ _ _ P _ honest p σ rel hc hcm S U V T lo K h
  exact ReactiveRun.commits Validator BlockId Payload P honest p σ rel hc hcm S V T lo K
    (live Validator BlockId Payload P honest p σ rel S U V T lo K h)

theorem rowsValidity : RowsValidity := by
  intro Validator BlockId Payload _ _ _ _ P _ honest p f c _ hrow hhon σ S U T N R d cr hTh hqT
    hgst hto hP hd hspan P_k m k b₀ hk hm hmc hlead hR hmr hkb hrun hN P_j hj
  exact Responsive.rowsValidity Validator BlockId Payload P honest p f c hrow hhon σ U T N R d
    cr.toReactive hTh hqT hgst hto hP hd hspan P_k m k b₀ hk hm hmc hlead hR hmr hkb hrun hN P_j hj

theorem inhabited : Inhabited := by
  intro n _ p f c hrow _ σ N D
  have hq : n - f - c ≤ n := by omega
  refine ⟨Full.record hq N, Full.crashRun (n - f - c) p (Responsive.psRow_cert_le hrow) σ D,
    rfl, rfl, fun v t h1 hD hup => ?_, fun r => ?_,
    fun r hr v => ⟨toLex (r, v), Full.mem_record_ids.mpr (by simpa using hr), by simp, by simp⟩⟩
  · rcases hup with h | h <;> omega
  · show 2 * 0 + 0 ≤ 1
    omega

theorem asyncToPace : AsyncToPace := by
  intro Validator BlockId Payload _ _ _ P honest U T N q ac
  exact ⟨ac.toAsyncPace, rfl, rfl⟩

theorem asyncAgreement : AsyncAgreement := by
  intro Validator BlockId Payload _ _ _ P _ q _ honest f p σ _ U T N qp ac M ht
  exact AtomicBroadcast.agreement Validator BlockId Payload P q honest f p σ U T N qp
    ac.toAsyncPace M ht

theorem asyncValidity : AsyncValidity := by
  intro Validator BlockId Payload _ _ _ _ P _ q _ honest f p σ U T N qp ac
  exact AtomicBroadcast.validityAsync Validator BlockId Payload P q honest f p σ U T N qp
    ac.toAsyncPace

theorem asyncInhabited : AsyncInhabited := by
  intro n _ q N D hq
  letI : Slots (Fin n) :=
    Slots.uniformSingle 1 (by omega) (fun k => ⟨k % n, Nat.mod_lt _ (NeZero.pos n)⟩)
  let p : Params := ⟨2, true, 0, 0, 0, 0⟩
  let σ : VoteSel (Fin n) (Lex (ℕ × Fin n)) Unit
      (ValidAt q (Clause.distinct.and Clause.selfParent)) Finset.univ := leastSel
  refine ⟨Full.record hq N, (Full.crashRun q p (Nat.zero_le _) σ D).toAsync, rfl,
    fun v t h1 hD hup => ?_,
    fun r hr v => ⟨toLex (r, v), Full.mem_record_ids.mpr (by simpa using hr), by simp, by simp⟩⟩
  rcases hup with h | h <;> omega

theorem holds : Statement :=
  ⟨toReactive, live, commits, rowsValidity, inhabited, asyncToPace, asyncAgreement,
    asyncValidity, asyncInhabited⟩

end Crash

end Scheme

end LeanDag
